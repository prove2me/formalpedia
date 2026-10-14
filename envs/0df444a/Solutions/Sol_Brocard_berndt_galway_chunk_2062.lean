-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2062
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:34:28.014467+00:00
-- url     : https://prove2.me/submissions/99b44a20-618d-43e1-981e-55d876a3325d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 370683453 ≤ n < 370863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 370684703 1250 370683453 370683473
    0x40b07080f250308100e06040b0a0807090f0b0306090d0e15040603150501030c2307141b0405040804030605192306100f14070804140405070306080c060a0309 69
    0x141e0703485411842c400407403034014558080039045804582c15020148108454180650b42c0220700341e0340010060403500001e0661592503200c016580214800412401d030190058144507034a40014080f042291092681c3e598003103c014080703070084074541d400c0314800d0300c842440441c020142c91380100c0301510281c050b0f0055105001080d40c43c1d494484030301c08410100c00400007400e0400065480110103001519880301d141c0380c1c10394094032880c0548400082d140d2080d00f10040c2110880a840402e5a0b1401c040041d140030702d480e980d6139607600d080e01032a4442c903804252a400c1034a150b4940c000780030040c088800c030016490807200c01c00e01c280b15041c002200c0712102c9044010300c0b000000380101c003a280038001c0c3c4825541c02c0e03c054100020403200100d92030030f10300e4101d900403071054501130200c0081011000040005015025045c05490108102c801308042c1d201c1000940c1110818490300885401a804200d1245450009040440400c0c1400b2a403106145d0700c44d110f031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 370685953 1250 370684703 370684747
    0x20a050d050609190c1407080403050609010204051e220f11090303071b03050a080702011209021008070e090906041e15020a050909040506061302040b07080f 69
    0x998085103640030034400c0c0c0195900a0700c281c03001081c0c0c1c2005581104005116103280c0e10306602c070301591400c0da21418401e598101c00619540e12842a031400d0b98042d0b10a200030b6030035101e40c1010600304001072089500700c1d10024001c8200c1c500380400401c5000c54a0101035010500902e80c82c1e49440d103030031400c42c04104150000740600407104080850b941c0901003140f115007400802e6480e20300004441c481074021801c0020b044200000d25001d5925030801002c6020392081131081000072005421424400d072645110581e80c00740c0d0000300c460f43c00010b54488140c0000d0f03010640130b84800c40e005040c030f14104d00c0c0694950041031100100303403610340103688654200001d1180542c84171184485a221440b848030064995800341e02401c03243c01c8501d98002121501c25020328103c0d0810034024000002903d001d040554131010300310341d07040c00b8110403401a0400f004030710032601503a90110140c0d0412420381c44454446e00500440a400301c4204a6952085c001c01c849401e5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 370687203 1250 370685953 370685957
    0x11d1003030f091e0806070306050d080c190b07030b090903090f040b19050a090b011e0e180f011a07032001020415030b0402030f1906091b03060807030506040b040503070204020a 78
    0x4510703001d03d462800f90000c00f1f55080610341b007014405030380da40f0001e60082c0d81000d03219442d2503914001d070b030806101d03070108595000c1240103102080b602c4d1003540d10404d92a00c040101303032501c2091101c4c50070112404000c03a00708001d0200945025980300c64440005440050f042c0e0400d03001c030711800009024074010400e071400c00c002d01c0c986510401c01614400f002404880390740b0002030200c0505c50b5454460105010802c04600d204038030044560b40c00905e44c0300300c1c0e01d01046c0701e948240190781301c406a408500000c07900c0303405500050031030769204c0c019a240031070985040324085004100f621100c0090392044001c4007090010308041c0c1500003e00300c400c0c1c6230400c00f40c01c450701040058002c5d8014820000405151001c0c10341c4105041e80c40c0c401101d0024280000305502e03041400072a180000c1c982c00f42d214083c4010700b680294508024041d280d208055581c20544002452a4005000500040e00c00c140107500030b03100d5001c580c10a051030740050260b8101c10b0300d45c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 370688453 1250 370687203 370687259
    0x5090708191107050106120f0f050c131407020607050d0e0f0714010f0e0906040b060904052509081e0703061a0f090709060e01090305010501030803011d1003030f09 72
    0x1348802881400c0c0203081c04400707000b4201c03c039580d99071444400f1002504c0300348050642814070800340547d00150600a207a03081071001c0c18940c6c0300400039070190207428162500052869800015441d0142e111500e5039420408411009805840100e03180c00050003107044244641c142040504040c00100da0a040c80f070110a0004240410450b60041081000324848080e9221465800c1d0000400e5501191109104001c10f0480c8100703503059401c64540010015910106800246414507142500c0384402c9a007004a40c540300e03a0040c4541c5400080e03c1c003000040e08019101d920101c0001e903490309540341c6401040b648240242c45d01c44040d40c034000b020f4a0107140c0f0111468045602251905102c1d40040803480c0314014030050058121841c08268040c8500b140250340c0000203102a68407441c000c00d180d00284501c400c020203045407000c2d42d41c3c45020310380c8645058480c0c1601c07a8590384080315070b00302c40710760310b03052003d02070010405004255841d0320076180d07800c80c45 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 370689703 1250 370688453 370688467
    0x60c1e0d02030f0928030509120606040b01052104170a03020a091d0a1a0307090b090c0901080f061816090e01120f060b03010903020f07080601050907081911 69
    0x1001e41d81c0001c103080c055405c02e001594084980301040118403482c0030700221450480c0c5000e40f1513208802600b61301002c581c402286040000481074410346090740c0c240800021040103607658010340020050030544441c0c440381314a440310b015507101d0301414902858101045401c0c21a03800f8950090002c2d8000624045a0fa0400e075100014900405204a43e01040c203021004102c02384c952542181c03181c40000c6040e040700504c200f003a50080560318a2582d600c908801007071406182c0d4000d19854001806141c1c0b104151003511206071961541c0d6907451301c03542c0b00c500c40289011350084100e101c40c0451003016030201e1280152896084d440300d005500600103000b15407006040d541c0110052000740c402e0103810010542c008116800b11942e440e01d140a484d01800b4281c0540c44d203071403401415800641c0c001c0034114841a00e440948650f0041e403144c109000e070640080d4100040364542e44602c44031580001d80c00d59072503048411030f0603407003038990f41c0c1c82a5043e0712000c9100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 370690953 1250 370689703 370689721
    0x203030f01050d080304060e01060504020d0b1305010e06060a0309120e01020c0904081c02070605040c0620060606030406020c0111030106030f0e0c190b03010321030b03060c1e0d0203 80
    0xc1d0150400316283c0041c1403640d40c41c02c00500c80100010b04071502e038113907099a00806d42025014100048c4255100c03088440d4010080581385c00c818130400001c604000c4c03801007071003124162200445504800d64840d01401603503484104240c0806541d105a0004526918040c01c940000c0c3d50728080441003c0300020310b4130007a012054400e400e550b06000c0020001001c64604090440501ea5100e07000b1584070028021850040c118500740402c004c100030041da5241c040c3c80190722451108800d00102460302c415103e980d900c15840074011900920344540959405481240098038100c04540020700b540c1d104450304002090102c0140724954060242405084e40404200206250080b0303070b070b94520f0b58010803401200190410001800015404c40140c00469501036895940780b41a2690250461443e1480c044100f20b04074254803a0103202210b5030002c004054544031445240101d80c0840074141803407581d060501e00ca5042c040103441b01000d0802c4c0140c4900c0e2856070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 370692203 1250 370690953 370690981
    0xf0c15020717100e1006090516050a0c030311070f080c0f1603020d11060a0c021c0b16020a12020a030e060f090f061605010504110103151e180e39040615020303 70
    0x10081400ae05000601995a0040c441e05410b6054500420f400b209000c80d11150300c91140e0180401c44904000014880306000404042c240082128020b20104600f00d403555203004811a015803501020805842c0901c516481a0301804184a11021640000d41e995024442c80004030300d600f01c00600754601010072242646a84169002842c01039440642030790f001014040c1c007002c035410500c011442040064001980b1401c2c050301500010400780d80ca400d0400c044000034882c1c0080302140c18414280da592007102c5c5419410034072181c007040ba01103180d80d812500224103100120003180084941c24807240150000559414107090400c01c0030024980a03050500b040300e030414030304a104000085640c2c1c0b0079524501c08028242d0071003018994440c4400300c42891044042d043c19a03c81c00c0d181c2011001c43d070702401c206371425201c1e0003008111104071407091001e411900100c0040d0f0800900410004140c0c0d02d80000840800c03000006400503880801088040c0a41c0b4071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 370693453 1250 370692203 370692241
    0x40b06041814061003020d0e06090f120418200d150801061a0309010f1a0916081603060b1206030618030702010c0f0c15020717100e10060905 62
    0x40414001d02d0708001140005103003d02140406500084011180310787e54003800080c14800b0a030307a207506046d8603050750b60101c450036005e1130080e0703514842900940811541100c034030200c0c0ea0300300048000044000c0800702640402008000311503400902441c004010314000b035000000e07201c1c0980a4031300401503070b40299601e68540311081c840c41d0748003480c0c40c0381410300c44130f407d540e5a5600650b41c007400350390015003c0035003803030015820f0400c40d1054414504060311102c002e079545040b20f03c02120203403559404240c1c01c0740031030300d040f10481000412201f14200800d103039954046005a59000c185040307110b0144074140082072070140070458101c1655801c21400c0c030fa645001d15221f2299a800a05102a60040a041140110409802e290400410312406030740310848112100703a100e59800602901c4008107202d041800104a400c4d00d203402460840c0e48800c61000810064243e0702c2c242c454101744078000c040600402c0040d2905480200c0e040c20039005041602c12a02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 370694703 1250 370693453 370693481
    0x509190813081603060207021534030905090702070317040503010c110303060d150f1a01090f0306020708090d0c1415030f04110d0503070506100320040b060418 70
    0x19144010f18803d41074030800d582d004440142d442030188000f981015002001d0100c1c0080800d512100041300400b02811464240b100e0031003582100d11030020008018005020428512080c0402e050882110394010301c5070044540382074032030300d5852030000700021842e5215400603080c070080c2003e0168451540003030800f1031480040810441d100e0200030403103801407207081001c03000e12a515411a19602d440841001442c3c0d80c2c0c841200985111405480760000f0300d400b550884d40b040449100703c4568601d401e6804c0d06659803170029602820b400e07140e200050003440c040b81d5175100700c51300062017580000700d0649442c03d589070b695207280010b845a20b400040e51801900d00003141d5200c0004140042c5940e114900b8110b400c403040d030b5040d00850007482c1c1c0000c1100000c0100f10b2107002d5000c030342e10b40da501c001044490065010042032680d00c0001540810b42e001203d0200d500020030200d140421403010800d80c0e009a1b201c00c46040c0d6080303102140342c90314400c44910903081 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 370695953 1250 370694703 370694713
    0x6050c0706030b0a09020d020a110c1003020c0309040615260402010e011814030c06041d150306040f0605090a170904020f0c0d140c0d03050919081308 66
    0x8102116212025442094149078803200700b084240e49510350800603010300700045440d28105111038009400c040302940200725130304c1200654420004e00f21400f5900240041000d4109c80da044020b5004010610424801440311400641d610300800b40641200d980020f0041c902c450001c00098400303070284503070703214180780ea100c120241030400d50160b02030034031023031002c4040d004950f1040c445200761400781c00c0c0140850322144d030814440324160101c0449903000060f03000c0080e40e10451140109c101d03080d0003483c41114a001c0d8155009181c031080d25220040900400e0070000126001c03074002d104075495100700aa175118041e000001c0707200505000b0070ba5921708101c1c03050400001c50210002c100039102c0d648980442d0804105082190b8030740000381070259454464005010100d00c01c52100c0c00703541c0030a0161141e80d00000c00400004a00350010fa0003454060401c0189009080803c000e103100d504140303000300d101d0380c011aa102101809141841001e4100c1c000f19041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 370697203 1250 370695953 370695967
    0xa11010206160e33031501030213170a050f161409010501110c0303160302070b030f040816080712081501120507050c0a0b1614310906030c0605 63
    0x400000c80f4942641610441c3c034107040541100d00c648484141d401100034044c4181007160700100c05103006500a0288010074501400103500b40d0040004035201c052000d5010032140e03003071041201d001c1041c40b05541c01c16606c2c2c0c079181d00b06500c0e10312804d002ea0018101c0402aa1640034120052810303c070120700410540c0d001902142042c842e00e810042010484030007414244000380a902c002400c69680304035150249070191128a07040d070242c05a048001070030078101c0f0840e07204000b0300e07110700c41c0c540ea80d540c1c004c680e401c20b841c0d041900074005014000203030390300020100c40d406003408500c003109000008200d07803001400607002e2443c40340001c2075a600540c0000d40050281c10200740e41ea180c810481d501d00a41c2c11042051041100e41c20900c24a80c4140d80550102141012000e070070f40e001b92180d100020034180c07508410003189011014080042440c00030740c114008035903269000300c0381140c4080c0c100c0a4640d5494030100300300070703100038501d0040845003051414159 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 370698453 1250 370697203 370697207
    0x380705010920060a031d010c08041b0e0a0c03020f04061106070e030c060306030a02061317010b061207090b1b010614010806270a0b240a0c030509030a1101020616 71
    0x94135141c500b07041e1142640e80e8a4007007003007200d5014410741d000304200c0d40d80b068003c100e5801a10300382d4980f0304005109018030100c05020060710380442c0c0354220b90b00c2c0c01a00c8001030150b62410403c060b801d2040000a000c0318008200504056541030f800b2000004003509106003c1d100501703214001c0e18078010f0340c9001c12061030413003040b07886503100d40c3c1d650040790030b0044602c2d00a600840000c1c0e00300414801d51071450035643d0105000307881d801110b081e5030803640602145a848a8140b02d64070b40081002c6459070310502d10715042c64016603a400d2003086030007010b00c69005003a40312600c072611000340300701402059415804181e0091440000e40960700c0502518080d0119030406500d441c00e03540112900314111000c0b01d81440c00c442810b00505884100c1c0e440354200b0159280e0621b4882d10002034dd01609a4140c03034412a40b10560b000102c1240c22010f0003028410100340c2d98041c4926060b060041c00040410407500c400217080000040c10f443c0841e201726401040c107a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 370699703 1250 370698453 370698457
    0x7080405101413060209040609020a1b0f170c010e2404020f060c0a05030703032a140309070b220512060f190f1a010938070501092006 59
    0x2030b82103e00d251000c15508010b006031140021050708141802c800150441c95640205210441d40da00c465018240680981c0d03510455040079180c81c40b0034191001203500b0001c44507940000b407002c03500e051441420103080d6001c04290000c070340c00194055800034000d50000424140c180301500d2030745400e070700042d0025007202c02d036402040041001c2229500400039058a2a000300440e03807038001c00d1030020068446818802844803a80740d4003003d801d0b0620031a031090000d1344401008411501220840b90402890b108c0c0911071070034009900c0000030010310b21a401c200b1481c2c980c0010003504503255840d588464041ca40307609201c6001c0130081107880d0405060051240d4030b40392021019151402989103100c001d1030225000100d101c7c5620814508220080b402c485030550001520084094410990780c400e04502c2c009000003120200e0b0400c0041c41e6401403080d210602150320b6401c5180d084807103030354840d030080038000a0040140f80380100c003858042c6109400100b9554 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 370700953 1250 370699703 370699711
    0x10503010902130f030809180402010f030506030712060207120e01020a061808041206140907030632070801140604030f060905030a0e12010b150c070e070804051014 72
    0xd603010402443e5008039a1003403004103d80340c4620034003a01d90901c1011580314102c8188241911303c600389405007102404d6101f250161120315240c00580c400b070b000f40000400035a814061a03401080342c00030440380035a5140070ba0001a103449032894040e01001038131442c1020300100415802c40c60b0390010b071801c000c03980110003054005c4aa145404140f0341403100610110000c503001c10f612003103043c284c000d1405800280103448003040c1900c8991001c1e5640c02c402c1d001400c05201103803681e002920b4030300303000b0310035842c000c41c0c0001005a41308040030001034001e2801800002a401000340b4003600b50001440d880b00c041d140001d1141c81680300061420101d9603142c000d224603940400d0603160414182da82e102030414008000146209034648a00440804031140c28014895100c10754001342c4803410021880c0e44170300a135040303100480c405205811007c40c601110b0802a4080c8480740c03182510f50400380380c801d04045072543d000d900c82d1b2604080c121070241200c130315600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 370702203 1250 370700953 370700969
    0xa0c0b0c100627060f06110606011706060901020304030b0703050108061602030a0305070e12060901060f05090103020f150c0607140a08010b0d15030b1b030f1b04080609160f0501050301 81
    0x2006010f9091800b4044070b5215030031031081984000345490b040080c0c88504580002079800c6a9944801911050420541503d84005510014a0509101e00104500001401200d003403941e44d50700d04030514405c482c000c0019444600408c0001c4040001c26084280c2814011086c0c4a85000039035a014000c94002015200c001241c00a40105c4082c40d030340c04040d200004001030080155901d0b0780a4983c0304283d071800d0000a01a90000c980405032180141140e030180d00e19000c2064072500108802c0d071080e51620340301c9070303481190020058240c40c0800341086140c07120000c0e10032100c040c002c04980a0030445507460750740c0040800e054070300c84000d5507126142c42420200a0a82e910608800e112840b0048148650303001c01c5886401d03a03003880f000d000403071810201c8070302090b42d55441000700741010801c84868401c00d041e1401c1c2d440111401c16a64945d00c0345444c809075003a046070f4001e05c81d014022460007029002508001140e154260f00e0314000920318881441802c0c0703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 370703453 1250 370702203 370702259
    0x11e050306010e120f0d02010b0102070306020a1403040606032003101d030d050117030a020d050d09020d0303020703270611010f020f0a12060f0b07050a0c0b0c1006 72
    0x607540e0160303041c90300c1c404000e4203004007258012161a034500f80f400c2800828482c0c88414040113105000307188400340181d010b0900c0038610355545020390007031405207007800144461030710380c1140007020358411800b554000c100945103007481d41020100520700c526400c02000a070203207450005180760359090802d00028444000b0042c0c04802c9401e14040c1d040d408000f400130b0505030b840c1c2009069594907407041070443d00d6400065601e2164600d40000340e003000d00f41c00d0055000d0030281001e00e02140010031801282c0d0300240c400304100d0070440c0400d41c00301d04801403640c042084000700300a4001460012030220090300300c0d0300c40307100b007508008500702031307624480b020b410054000038203003005e64035041c0a01c007450864002d100c4120014503960765032960180a1302842e02103c00002e075910206082c290b8502c2c0e52381c08a40c05490740d00c20003c50b03500141c038200c2240000c1802031a25502c522040028a0500d000d1441c40c0e4441410702e00148040c000417900b1040d610180c691440f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 370704703 1250 370703453 370703461
    0x304080316090305011802010e03160e0c0f0a0f0f03090203031902011409071d10151806030218030a020307120302070e0906180f060402130f11090f011e0503 69
    0x111101c0b503d41000b0306a500340b0344140f6440c090b69044000191003602d80814048410082c560395540d2007007144000702e020305040241020310341e0001d4004140052551600c40020b00340102e5034040e0545100045000b000030114a0340a40d071400001000d1805100c00882034000903561f0080c801c000820482d81c440f101c170320034004d521011a00f2000c0042e081d61b0700d85030030456115001d911644010034011007040407158400c0c6070a0703105e000403854000c40300b0b05201c009100c3e0000c00c03040509100720000e08098040d58207030704070002c00050358050703a030345000c101100c44075000d02c0400d8021b5105009031001aa008a040720982e4204d4001c080070783c0c540d0030100d16100719035100c00c0c0c900c195542444500c032404290f11348140c0d490144011000114141e496031525041c6420b0003a07044600464010300d09a82c19031100361141c5008503c0c4622400f80340b00725074207800b0000c00d60100098129080c28200300100c060f410909108195020140500c452600c585101d4020408004005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 370705953 1250 370704703 370704707
    0x6050616080c070306110403061b02030307140d090b01230d060c030612060c080f15090601110f070807090c0516150504051e010606090b0d0f0e150901020304080316 72
    0x400080d50020307070611031b8010403070312502c90784e00c24007080c2c501c2c904026034004903610040030a03505525660041d85565030f0b10808840404540d44641c0490300100213803205540103009081e05135004200c1440a94500800c10100443c0d0440054103080f1440c403491844e03031220000d0750000d03004a004104640c41040071070007000f05070031088070403645501c07260620500340c3c44010380a90a48a403403840d1222041c40e4200030303048440c4840b0b1215408a4005810f00c0b0f00e00d50380285040c105001a0344e1003207511030405602d4560450075134000c2070100036946c1d04000c03070400ac0c100d203801009042400304000302a07104100c6820580c0d8a48140c000c02c106085007950881c0300010002c02040c14036140003034940e01d006101d0b2402d0600f160403c928110188070781c40460300c154807109000d03807809a0f4400b80750070800c220041937030b4522204a03190454000c403148547e1000140904004201e44a9013010010300b05140913803052041100061421003125080f400314220321042d0b003200c1d0708c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 370707203 1250 370705953 370705963
    0x120d020c01060801090309030308150a090234030e0907020c101205010e0103030e030607120b030f010c052a06060409020d0501110d060902030615070201230d06050616080c 75
    0x40342c0d43c19864814454241680204400256446540c60500c0c588480941300b00c0d54524004541c0d000d4030800d02005003144650007400c1d000c554a1040c450b901c01c4004c1c5c560380760032903004d4150783e4842c1200c01d010580d0005050b019a00121402c5d081424448802540e41880000e55806401c1421100e00458081c046c03a110041102005001c5583c550040d138245c04400e10040b0302180060120150302e2070041611880f40941e5a2581d0091344c100515401400c100c00d0309607050b00840300030045552003070107180c0c0002415114903a45080c40801c074401651040311081c00c400ca940e1a24400d5480411170720b4210a00f2036012a141c0d00d03500000784a070380401c00080c000d62a050f032803840010b00001802c07030361501c0034080099990310304245003a88000c0340c01c40e41c040086000646405082c5000c1c0c10b2240c0189001880a2150b2001c44e00d0151040c003c02149803010800c3c413543c9070107004180241c40107440380c0d41400720051200f844c00440617001040500702180c0320303180301c2c02040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 370708453 1250 370707203 370707209
    0x6190905070e040c05090108040233031e160513150207030203010b010c0b0c0c0f032205040b010507030309081e0403110a030f110102070b0705010518120d020c0106 72
    0x2404210354102864082c250074400b0000500590a1440d012606030041c0180c80c050b40d03042e100ca034a165956400c0085040e510140941a8210f0300d0b440304e091010b810300c80381c1c8002e00b19a0590740c1d003006610018500d05091810510244841c10058200d200701d4882d00050031608100d0303284e0b09551000d004c0d0b1f4040c1d8114014800d8500c00784000c2c0d035400201d0340102d0b4001c0c2e00800c45160108011a00c3c02ca081350003508084002c00800c10311080303180201441a0600280c403000d141d04c25685045900030b0050380d01202c00c0409011441041c035207584010b0404880800020700d80c0c00018003079014280c0c01070f040c10307920032080b014001904115021031a490a0740070300d40c04017625081e0550402e0000361602c0300001038049450400341c10040640b50402d20b40ca0b41e81c01203584904142c074603040082c3c1140503a040c0001e54444150107130042c0b0b803040001190500e01150024452500e02a81c1a2160f0040140e0100d1151150885103611460400580d8624032035140c0c90150040b68 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 370709703 1250 370708453 370708469
    0x30516060e060f0a020f16080412050d03051f030305090d020a12030801080f120c210702030d091802071e0614011a09010e2e090e0f0619 60
    0x10307009440c18802155991081c804202c1105050b110349046034228050419a5104c44104100c00303988444000409008035204c0c0f02502c0c645611061014040c0440001c210307410307030100c0101c404450301030045640c4904807034003514519140140080c0307554600e02c00a024000c1c00594040591192200a40b2141c2c019100f00c460b16030351460070b50000900202074000800c64800400c0000010a0307c4101c0c0804c2c0c07005040080c6000d540301c1c99640502502c49080c81800c0b07250519041c02c054043e65030000888007521900107005050410321601da002d42004503120041c0070b0380034030690030904019410300068403800d26203000f18028021618807080b00d094440c14404018203904400380c8245c400c40c1540c026613a9401002c0e0241808a414640c000244007800207035101d880c0c03451944000409180e00024131142000c1c10084002401181c01c5069155801c0c00340c200b01d000006203a07164081c04030b0300c0d000c400700746003000c007820289c030410010070840314210034915018007500402c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 370710953 1250 370709703 370709711
    0x1a0721170c04080d020309100807050c060c070201030c0e1818030c0109020418050705090703020f0a0c0501060609050109031b051f020c010801030233070305030603060105060f0703051606 82
    0x120310700322594009200e103508038842c10f001407415a20100a958035004003800c075420702c042a04060700c0d90b42c8000c00a508012040c011184800000c000c098014250380d10500d9440c0e030503000040c15150680311200501218100101c20b0780c650446280e07401c2c01030f900c0301c0075076291034980c180e076426448440000c40c070011590b41584001035112081d00c0d44216820081d45441c18402c0100803100000541150050300d000c001d40d0a016400e1030744030300d003460018074284400080100c907800c0042210000381d007601700b21003001000d20074030307000e041c15088c0850708514140000340800a180030003895401c6424056001e44281340b01c100203010b008080304040340d20106500c040f030424990380ba0051044800b0441154040c40c40e050680c1e801800b066440f14860300c2001450304059240d145030505091b0072000001040c002d801c0a502c01c2c3d41e05607407410020201444d102d41038000c144912020032108031481380e003d0846410961504080e07844400104907801c0d8804c030304030b018160a0070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 370712203 1250 370710953 370710961
    0x40b04020f1b0601030803010e04030c02120c040c080c0f070206040b041205010f14220c0609091401060203090907052502100e01020705011d191a072117 67
    0x280300c041c203420000e0421844a0b50201c07400301d65140428400030740356000410060081c5054034441585c80b42c06400d10801c070940543c0440c0c0f08021520040c1400e821026181810f450240100242c174103035443d11f51078605000791850054407600d81422000d0500180780f1045441c0c1c0011769004120a600d030a4446a8a0309140e2000c490300f00c0445065280290341c01803600288640d0003403814001d4a44007075915840c0c18000c5030b414183c090440000c211079440050161f0070008007900803a9142140c84e4604400d4200b0b03036104c00c490109403001440144021580042945e5a600c0c0403a08001103441c0c40700f09540501c03ea002c46403c8d004001c82c4015000d042800800c00e0130720a640c0c1035602d0619a40c12100c000c903031840d240c01030b0001b400c00c1049610600100900011250100b00045030f00b00010f074640480d040ea10807079205404040000551000c0a206086840030a003407806c112980c1d201119a04042a1066100d00f450b05003440c0340300314440380241c0c014209280403820 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 370713453 1250 370712203 370712227
    0xf021509030c0709110301270e030901171e1f0902040e0702010b012001140405010c0206091606030f0609090302160504060b0f0702121009150c050a0e040b0402 70
    0x2000b0384580066200d02d200014040750b07203101d074080e0f203062240b03482d040d41d00b040c045880080e005403985103001030f0211312413180c84082c4144442d00c83e60100450ba2003548500140c12204100d004a00c0912180d0400071082603503016403e0300d0f01c010380074000c0ca680f04498045041c1c030f01c201c41c580c4414200400320344109a58001c1080c2e80310840f01030465960901b040f03090310340401c0704a001455107541110118408502c4548105107040003181c00003a000901485110403901a11145c0d110700b1a4492245c042c094107030444003a20207440e0030404001c60070840c1c403840c4504010160b442031401e16071451a40528043c0c000a0406c1c0480d181d1810020b5460300c480e03601411001d0400d00004e511b00c0c0030310816044881603070304076060407010481003c0c690003594003aa0800020454500c49034000c1c04a29016824010f0000320320701107061a0124100f07402c00303038039090b150022482a00d904101a600e200c121490070581c00304604011034054000e0380c50b0103070424004220014848 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 370714703 1250 370713453 370713457
    0xd0203030406110c0c04092a0e010609081213030b01170d0e130b150408070f060201140406090201021005190b030a02011710050a030b010e100e070f02150903 69
    0x74000c10040c00140301404003507a4a02c13401c00300507130f164081e210007452403c0c290000c2100c21f00414a02200c28060042c0e1740c2030340003505000142d01c3c1048014004408442c90300c5000d402140b130050903080c106810180d41d840300c100304c1c8101c00c5022480801c0d598581d11640d024544c403218403002540e50704400da440b03040d05040c40005005100104600381d1144003000514440140491442e410301c8041e0701c000c003240200c0360303044080c141403054564040030091006046401c028410b907803030618401d500031081d0300b10310210390400e80f5485981c3c0203058005e0300310f6005400020010410700c0140d00cac0004c40014110402e062000300300000c40a000b01c09100d42c4801000d200211512041548540380300e08000e005c10302c0a040001421020003e80d6409822100e8000c4c4d040d8443c00081c036656415402210541c02d20401070101029161000c0d401034007007600c40c060641040c0130154200300017846030041280c050566240c0d02c0c07007008200100d1002d260940003a007891020b540e129 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 370715953 1250 370714703 370714711
    0x1403100f0918081b1b0906010e03061f080102030705190e0d0206090409060504080a0207050925050705070b190e4504021f0806060304081b060a06050d02030a0609020d050d020303 78
    0x1b403880500054043c2d401829400e4040e0b500038054062340e5540d41d02844076480d00098241c241f6042c030340110361030300248021030203855983c41780c6d9100c07444941d000c1e03102c800c0b000500e000c012140c0c0c00c05500307441c2c2c04a800201a411291141c42d000620003040040100c0080034080e107080c04103000600c275035a40140581c002039400c4e60f003000d480e038040c8103e6010a45410b500817007169a0359a90300725250b0341c2c881c082c03078a180807840c000071a01d69501d00704054000210101d0f00041d244181715421a46085040307860601c05040c8407030303000040c0c0c00101c040c00e01301d0300e82101d200030460125610b08802c6000b030a113030b010980160700144030b1a48400b01c40c01c90282820150460506804460a49040001d039503260419500c3c0d10a000032a04050030440340c01c1000d200200b60404c8184501b00c1c403000e048000c1c1064940301780b060003034645640c070543c0603400580da21b8000d40c4002c41d81003841c80c1c1112000c5403920070361021038070700b40c920800039080303002c3c0310310100005a002c4000d5000b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 370717203 1250 370715953 370715959
    0x1119050c1218030a1a090a0314090d0b0c1201050406140d0c050a0305060604110310150917031810050a05030408090d0c0e0603010b01090509071403100f0918081b1b 72
    0x586e0344110300c00b40d030380c1e02208014011641903030282039441c070660024000303254003a04982d2002c01e117139142c80d4001c40c261404030b0904008030300c0702640a0805080740c01000202d400b4410309107400c040703184c00c0700103090042c00380031b842030b04201740705843c903200c001014054211a901c40e40d03420100e07112502500c00901c50b07410103d928060a900d00c0c01e6a0085058502d9047c8603454062400100f01c0307007107040c2003400012a000210342c008018080b04040c1c550000c5e55465280111410302402c0c8030b01402d2240c02400c080c00c064990000c19120040c045040c0995a9241c82c14640c81601504038199400760034440040c0070008030f00d1304042103031490b45a4a21030348030b1130109401e0314075000035036001a0403000100150b1805c1032181d0340081090401c0c068040301620b148800354411a0101441a070030340c0704000b0644103401210040c83c4580c000c0141503000211030840040100d009000301c000800c41100d8074190390429003c0425000844102c1e034010b0460440f0419034507134040c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 370718453 1250 370717203 370717253
    0x90c090a0504050f01050607050a0b07050a0206060109030b0a0b010332010e040b06010f0318120216080709050402030f1005070e0616080a0509041119050c1218030a 72
    0x14072410a80180341c040c0a00041c040001d07800c04007401081c3e04058070036500c0d031040300c42c10401314002d910b00900403d116a641d80e5200f0808402910b013103000b4207941d0412509020401c0400c4940c0f0310360307812a92025010844904200040b03000d05040300c048542807131418502006121160420300d0385c01000c400c0b15003075a0b03940010048034001240d0203040b0005032800221a58409d00e1040c0b074568085c00d0004804c0c3d003210101546100d501c5081f43d00c2031090f00059007081d01048821040518082c03400116030902a00945450310780c0b19954809407528080780840d9414885503410035501001c5074076030410084200060042a9610008220b1201120805090038000c5809194001e00300140880490341c035500540d000b05000020484180003400030340c2d683e070250313030f641c1c1500841d41d45c0c840c801501030341c0d410107401e10540d0510100300114250030710003184400200184186091315451200d2540c4c4150401054140d81070280040d03100822071680306c442420b0351240326002d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 370719703 1250 370718453 370718459
    0x1d040302160b07020f0d0b090f010f020703020712030e03030a0302130906150f030609020408060603010f0204030b01030f061d031305090907170f0f0f0147090c090a 72
    0xa4039510340c501424200c0c0d10104102c802505014210300c105e400d002d061068840c07400d8403604405841074401c1e0020360005c038540c0203090001d010b05c03c174402c040e000841c9444c0382540d02070360b41c1145205191a0300c078040d000006040c015070b10600480c00140540ea564031640c00020029804010b05c1d0080e40705800c0046104101449040b0688000404501c0594600c03031054804a94891920040503102d2001003450101800600010300080d0010405401c049040600b914001e00245441c20700c103010400c0820140e64460b4116a0021000c00c080640d034140100a0601030041c0c0126680c0c070010075408140c0080109161041c552180f044951540200300509500f1380b508400e0350b1040b0750038484000b0000f001030003940740604440012000f580098141034030b0100c0348500e5000500e054032640e04c00c1c091540c481c40c1d1203114000c617440400328241c200010342c000d80217803c52110384d03540186562644a9920070018000140b62030515070350542c90344002011406100822800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 370720953 1250 370719703 370719733
    0x1a03011b0801060e102f2416080711031201030308100315020d0906060f03170a02030d05061305010b0301051201050603190c0f090203011a16030809071d040302 70
    0xe4998202c00405e4041c01d50611242120452290745201900d0b10b5880c880410981260b052a030792184200d0190407400c00500000007150101d0782101246501c4008124510180500d5024071038081c1c00c02c05000d45034404115541110400303020b12602c400100300722446001d22005040300c3c031175030703650f1341070760768051144c03048001840001c140c02c0c0240d290a8107811a60003400000c00442d40020f28000d8980f0388500380c4006500200d4006c1070080b0a009000c402880fa4105100700341040b49403180d0f84400039900d100301c44400700c9103a41e8070081080c81c0c0c0c41004c11409085000c0703060165507154594903c1d690300070f22982d4841c0c02010541100c41c00d060284900c1044c0c010040c00728962020201d040b4141180710403504c480103e00d02040342002412210701400e1280e8006840750705014840b2030280c4c59890070002814107100c40b20000c0c500c06030642800b64581f400e85000c0d15450200b41c9850000c1d00410f0195450f0018a804951040b00302d5103d030340207508450202d2035103441 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 370722203 1250 370720953 370720967
    0x812011409090d081803161a0603071818020907030507030f091a06120d030b1804020f0d1e052a0310050c0f0a0e1806010e041a03011b080106 62
    0xe00408144900300142c2c0d1483c0800a40c072070b0101520980307103050b01844407c00722100082d02164829441d19540b0f00b40e441498000d0707840307102074004014450401401d5080c96124106407600c02d80c4038500748540085039038500280b59030150000c501401e00e01000341c00b5210445409001030319000070258148000d0085c00882e0783c01c089501e01c02801c59400c000f62040040010b90801004034101c00c2c0154100322480144d0410340d0000b880c40c42480411195410007041e40c94117096900c20710000d6601d06200704000c20003141c81500400c020328108542d402910b4200d5088103c080901040c0403012075240c2c080a40303e441400310303294408290300d129a414071030503007562140d4807149525003140d00003504820900026810b1204151044880c0d500a00c08500069a102d90b4003c0604160103a000781c2068003502d0b42e818a0701e200020b00c1d01e04000c0c1c84610840c0c881c03800b07052801c810b41d000c420651002c1e0091102c20445081041c000000c04105030004480c1000050700030311a441c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 370723453 1250 370722203 370722223
    0x9140a020f04200322030809070f060509010503070e0a0801091a010b16030201090b01030804080114010605031303090504020403060506150c060a091e03021006120c0504020304081201140909 83
    0x144419000450040102003600001c2a81c1c9001090b2844400c9110380d071800170340c1041c03180d603954402c0d20f405d034030301410320f078944d4482206151a89800e1120b5034021064600700031081c41e04545039514804111580d014004d99581c010480c010045240441904004e000501a100e03000e241400650b400301010024414030400ca40c0620061034070380c9504a0800c2c4007400380c80003080c021416241c481600a00782d100300ea60700c0001404000c04a400e02410034000d0710044121200e61604034060701902c40140320307101301e07960100f00384100360064075924082c00300030700210744494891404600a120694905200c0c04403111492105a2203a04940f00580c4100c00b8282e90f48910500c0d00282003100307170443da00b41040720302401401c1014104980300b8041e0340203004160358031035400201d03102c90700600d148640301c3c1c10160100b15080459411182c0c191401a0f8030342c0c0e20f0510302c0c16401a8805840d0400b0540000149002e40c608450615101115542c81d07a44901d480395a40f001846 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 370724703 1250 370723453 370723481
    0x120b0103020d0201090f060e12010203041a0c0c03180a2c130f0f0b220f06020c030a030209011701230a051908010c020a020d1509140a020f04 62
    0x11006000504240403180765441c03060400b40811902c2d0400c00340c4040d4150800c800040007c01106203034945000460400c01d900c600031484c60402e03459034041017409180c245605c0c01c1032400308030030742c01003030888a04014041c16203455100000309090400307400411144200c100100205a41c92040034280c04140155071003030180707051500c00f45130f06030020710070341d20302d04945042001f01d0300c1d98000c0020288140400c03a8034941c245070052500d04050800e4860900445601c40030b400b00300403c22540b41c1040b8030303820b2503100e45001c2020b4401c1c4c04400d04280000315600e030f50341d60541c02800b0003801c241c90340c10f10007952100c0148800350900c21030a00080d2508031a03103030583d10380034001f89040507012180940e103c0e1b000c29007403c0c08101036510560101d604000462080c420280c840c0c22902c05001d843c0c165400040700d00d80510784c040c000304151500d0845003403050707015000322035000e002030f40034a01d800041d68541c40e0242d000da000f0180d200360582c06160504c035443d0b240500d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 370725953 1250 370724703 370724723
    0x21070306061d0f1906050927010513080906041a0304031106070f05070203070e0709030b180a39060201050709151b0b0109151401050406080408090a0e06030712 70
    0x6940011024026a0110b00320940d070382e00046138684480343d81f00c1c03003024005c009000c1c0650074000f03001f0780444400c0e9000142d2614050001e0101031010064000f40c018010036101c403201e10024049101d19400006410200c1924184407072440e40518481d0b8029151b08000d020507402c10394a40030112180030005280d0f054110140d4094000740151500103401c45850740e03210b28400c4038100003030b80d0202c00319005110400410104041041d8040005031071007021200c2c2000f1a41d60f088641002801107019620300b110642d410b0308208824500003540c00b1100b110100380161700d030443c3c043c1c54015400c040005107014004c80b252011940d441c1103695500354050390072150301001d0441c01d12591a90b0b40280c0100341c076418614064001030800090004110100b4183e614590f030120040240031002000700340c3e0460165411660182002c0105603207a241c00100c80c03045441c49a0310058500c00490059000c080e4584203440a500301c510554840804e03040340004070304010014400c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 370727203 1250 370725953 370725961
    0x10b030f01020703200a1a061309020604031103030705030a030c0e010804050a0b07091a0903161202060d0e010f0c03060b0408071e12080c0601090e0c21070306061d0f 73
    0x103040404000c0f80c817034000344c0c0c11800003580c0c0e101d54404011044100c0c0e103c9841408a01c0c5095411b207040c00c450013808000242d01a404241c69010b1031101420200384d000d641e0105031000d00844250343c1e4064142d030360340c0c41c034402c000c0d009214420800d0001880c847d401c00155008810b040d015540103802440c48a40d203075500405c2000040946042004108000440c2e1040c034182808010382511a2a22003250000b491302c0c025840c1a0307203005002c50301007044031000301e60018203074980644580766109190880c50001c0c0c03031020f502413895880c0051400720f40b40c1c241d200c0e40c80c86031130340d41c180300c0540d9582c80e038895400355000c0d180c641e8000d101c04200b032003001201004500d404550422202e90b0b50070200c3c5c2000000c05064407003543c0050070b01700724001484400d0141c8040001000f6054291160720341d00e4200b011414001d0b0b28080b211607240711007803c0e806240c41500101d4606988074a0158080c128511030078444000402c40c03041c0b450440300501e80300f00b00d45100008250b035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 370728453 1250 370727203 370727237
    0x114161211090a06091701021c0902030307080a0302120c040b0a031a150304061116020103050712020408030c06160e09040f02060a080609070f080705070206040503070602010b030f01020703 83
    0x80c0c80072880c0c001031410001520951100710042d00101002d4881d408505d14020031072200341d446464160782d50348104100b4128086004172010548024440081d00d40c3c050b00c040391441c4601d81c0081c040030700204e030000403968076030010400d1440b1500800f80329141e416586400340558041c0b00000c8006200d981411480ac3c0e02c0020f030440c040408120341d9140c40e000c00c962a14408030740b4030250000042005000003401030740c440c1c01c009065189811655031502010042014009040548810100310100c0c442c0001c1c8060b00d000e050215500c644d03603041155030307900c00036000c1c0280c0580740c0000d1000b0b121481c040c8402c202c9845511405059100b0845130340030007401207560891641445000d07840d404090902c5c8410354a840140303051110401c00c8181000b4882010410004c280101c1c050340065081e42120480c03c04980b0f9841c0d92000495500998000940505c104c00001444550540060340b00f50001e0341914940c2d00480c245500380d20405602a0104050b21085e4207000c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 370729703 1250 370728453 370728461
    0x908032b0519110403020607061d1b060703030b190501090504090807020607080706050c0405040608060412120b060c010504030813240902030d030e070503032115060c01141612 77
    0x152200f5420f501e080e85a5000600390340080d070060301c0007903032a81d0b5034500c1c20091140c03003109242c007801414582d80d82e0700c60b010441040a05940110303008121501014040d030016802500020440030400c40842601603105240e4821b550018404c010002800c0c2410b00c02c041c500c9400c1515189000c01e103400b132000c140d110b1007040f00d25100070000f00002c07c0d080e1113900e002e010b010410a5440f480c01c000c200648c0c09a4200e1121798210406110018071011001091601142810032076540000307509401014100107464024000081150780c1d00c1c03041d44001d11640c80ba03114151075440d1150300d4201040c6049c00281494110304166440c07400210180ea01c0d1020f0710004075540840d6408a420702080401030004241c032954603c0c6103410034808d1743d019102c140c00a41c1402c0101217210500c0510ba901d10220101c0640815128030300040d22038422800030f0702841c5c0c2c829402c00c3c164000c0200c02047d1507120310f2a00484e030340d1805150301c80c280200e581d42d10a42e02c240102500020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 370730953 1250 370729703 370729721
    0xb030615040302090f041b0b09090901060f06090312030c020d11011e140f07050405090c071208010810110910030902040f06090f02090108010b0a0908032b0519 70
    0x40c0c2051000200681c0d4a01856128030003102d580e00c060300301490031000c0c040b440e00d40381591541068040c0260607080c070541c3d507030200071070b05d0080c00d8950401d000d004102c59084600314504051012880a400a0000048a10450340b201c03401070a10422030456186850b40801a040707004400c03007075403107562400c10066000000182c50301e40b920540c85000100400c01c0e40311900d8011500014114403145c0b0390114954601900710324200d4002405071246000342d5209050a6021a80e11030300441070b1035402d03034803007200280f0740402180035000400920820f4000d11030514a20038001e0f0710701410000d032000301c6078030b42060702c410f00300401c40c2011302814040503510b00172500940c1c0e50340a42c55602c0400c00d800900c56080606041c281c420210100c0c07681030040007903010301d0760301c40d846e5411101c402c01d0080d142c0c000000103d64042c1d65902c00e10380c6200115801036035260703a00d4508040c0090001d80da03e11110183c41c801a100120b6030346c01d5400f5102800100d0b2031040d0400010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 370732203 1250 370730953 370730989
    0x21306081e030c0106030c1502070f09090c080d02070f0b0702060301030b0a09150606091a1b1603061b0809060105100302090a0914010b040b181c03080a150b0306 71
    0xe054030f101629003101d40680c01544c00c02c0021804004605ca40b6801d01074062a80c400303482024104000380103c10002e104040e861503030b540f40c0606001c03070b400c10040a40703400c00c256140f18022110080d60b81039140140d0480d02c1007070000045607500d0100304c425241e0b0180050b0f065a196440300d02001c5001005500100e880c1d0301801c000582e0104040f0450952010005003142400f100900032000c5801041b000c00e1403a140707081c8401e110040e07a100481414107000ca08488015a03418030700b641c10080000e0f840c0d04008020411150040c0030303070001c0e40c00c4128240482c402c08032407580c07050b5000315090700507000510481c101554815241800d03814003600e400481d0010600c04440b0381c7c440c142859442e115000d00603000941540117000000d6501c0c2068103104c503c10307045c0700700c0158140504500030b44400c5515440d00840b84280e05518000840280b420090200b100c101c9040c040d681c6441300d4250700440c03600002065882a03a000c03400d5030b0300d620a101904e20b1382d0500040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 370733453 1250 370732203 370732207
    0x12080d0e0307050a0507140f090402041404111005030c16080c0a0b061906021203040312050f06101b02011b050115030c060801030f110a05040c0c021306081e03 70
    0x3148081080104072641c4580700038003502042d410700604154441d0030246404200d10002c018903a0380790310b42c40c6508000c45201d000ca440b01c0c070002d0010b103044922100c0310703070b108402c02042c0b108403c0b4000115905841d0703c0e0381d12225140c210380f1072008075200c1c000c0140601401c10004c41044918044911610750289005100c0c0c40c0289080e00343c000071202aa040c40400a003424017112007842d204400080002440c14003c2c0a516003001c685004904100800081e0500d0301c194135070003804140b14020406410311301d98070005c804d02242d01d240101c80311a1907107451441a4003428520041101d1150104010f50044a50151306540b50000c0000705001102240c000e10911190f01c020348120201145940381c0012045007540c07295052094000040000ca45041c41a070b002662101204490905c2031001542110700380d007040350000d00d403072040f406d0103410001c0a4003050080f00c9045607500300b1445003003607a0300c0e40105003c50b0411061080442404481c1c106455215400d42e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 370734703 1250 370733453 370733471
    0x607060e0703170a020f03040e07050a091206020703170907140d0c3b060609040f0609051e100608070c1205040518060a141206040606091512080d 64
    0x41040c001a00e1043d1440030001000301c080c6030100040200f0610001c065424945000a003501c1c2100c020840c005003c00000d000980c0c510540c582806004c0c5090380c5500c0350b43d1030400304000d4200310400c4000c2500380884072040d400c11380c1702c1d80c401d03980c0000921076181462024a40c00c1201c01800b034201802e5408075000643e408102d40113420000c1c40f00140f030132802c242c9405c8a80141503001e4a003103810700e600c200c683e04112950f10010a80d0078079034402190012030000c140f860350490700c4500d05940400c45a000c1e80016000342d40f101c045c40400d004941e400c54803a201901d00391040040c0c08010001c5078000c40d6500e82c402d49908040351081116110000001080c0c021034000030000101404545083c0401c00804440030149086a29280001c03907c2000039000300081e001a00050b804295107003000182c0420440c0f050303424500b09480c00c40c0c09014140a448262401d164041c60b0071f114016060003103c100d0030340282107031290748801e03007607a0007a0f58964105071a58414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 370735953 1250 370734703 370734713
    0x315041503290f0601020c012a03090503030d060611010b13050c0418140f040308040212160b0903011107020d08180607031e091505031e041b050f0607060e0703 70
    0x314869003e0301e1034400985800350009041c0403075481010f06000010a603403440da2040d441ca02120900e07204242c2105d102428240c41503c0f09502c0550b15201c0050644e04d04891502310740202c4250341c9034a03181c40700c02c40c1c40609075552407204981100d207c0c0302202c05041079410a5410202c030f90b042c070b0f02e41512251445409070850740340c85400358035050403039070014401c0c9800e0350240c102e102981007400c190390014910300e4040c001a1048480038440000101c00b070000014003aa0103d6003404243c0e10740f56032029030010f1151902c00d5281031501103020400204547c8959802004109200311550380e48001c7e80201a102c54050303140c042c0c10240b5140c0b2001894514003030740f21101c8840303000e150305000c402d19100b01e008011169100f040b1003810303c0c2e255a5100600e0606035103aa6601040c62010703910402d4034107500b45680b05100078040710606100b9024420749425980a2f124800c1c071405070600d0500582008041045c0c8000c40c00c141c1c00001116058000e0355034017a40e0b9122 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 370737203 1250 370735953 370736033
    0x605090330040305340314010f0501080f06100f052106070c140a0305031902070204050106210b090a1d060a06090c09050907230a02030315041503 64
    0x122142e501c5109103015818004445d503002e0103039032251481c80c04010496040d2001c2a100003000c03802d0640410340750000070b402114440041c40b20401c46582d60303103101a03942240c181030411034050240814010484a0496016502d100c3c03c40e1204c0c41c9841300340510600901d48130440d015402c020726280c1001801510300402043e5220070200081c0e092004600c0b8546a1400c7d4030303801143c1c6840041e400c40c094a910003880c80208501840f0444a900a4464102c00941c070524190000c940c6617048001da00241c14864103101d201d42681c540d217821190740116803507000c00c403000050700e0201c41c0e40202c0740180c04c403071080140d424040d90785c2d4509082030320740348503030f540f559814041064144101002c0790000c1c500142207600c0c0c140400c1070708002514a104110f420800f40c01000c1c07107548500e00303640035140d0b91559182c826400030b4032900199800c9814030707880316164010745003900075504512048028400311034510b950744480c42c0002003400a000c401c070080702001520400b6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 370738453 1250 370737203 370737209
    0x50105160b06280501030b1804080a030f02040b04092909191b0e1909020304020303090603010905060103060f06080f1803070602070b1f032004020c100501060509033004 74
    0x44401c0b920305101c005170641c2e81202109008d54400083c4496010115121582294100d41429610104d80a084020f4005800d006100600000300014440c00e0b103402070045400d0b102080000c01c5034111811188913141e071140c40c5e0f0f4402c0d00201c80700d503e00501066048092030740407201c500c04035a0751009588441d0303085202001c1013245004000c0c3c100d81c6038031b41008201c80d840359071800010702d120010503902400140d560302000140454404004607009008014815600ea60392400f40c01c01410b011189240000d08040700003034403a10344c28040080da0401d84682ca547d41e02c0042100000c44010310b1115104e458482c4445103000c00d03c01441c9080c081c44001d40c1d14195414007404594001c1c1001c41c000032020350680d29003c0680f0b002068a91004900c00003003000d13041c0300c1c40d506c0b104150340d170302c40d100055030000600700043c10207400070794103c04e000c0e80c1c0e42c900040d5840d01a03000c4285d0544c0180d0b1210580d02241211039618179403030500c6801e11130074014071040381c3c0c00a030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 370739703 1250 370738453 370738519
    0x91217120f07121b030b1314010303111506060c2109032803050a0903080a09031e120c4403011a09040b1f09050105160b06 54
    0x2446a602e501c0f01c41e2100c2650400c0041c00f000104046010f01034070010130903002c05030303102d8100b056652420080d0800c1114400280702c031035884000140810740a110441c00700c1c66851010b46030300800310f8100303200000200d55240e66514401480300326880038800d20182e00800103201911820a2440d00d84021840005a1195512400e242c5042c1d00004140c0900b10f2800c200070091041d0440100c0180e030500c0c140d6100ca9040c0c2c02911102442e800040c000f00380843c2000c081a8000706d10780489000d1862030407404051020f420b012610140301800f50144141c444075440d004203c2c0701100b902c101c1c91448012400d02c8102a0a100d1460101600c0307841d518040c6410640c02c90102440e10222a82e0320b5549401e884109a0746410b8401440c0f4001194150040d076490780f1045540320042c0a000346e800d800b41031406c650b8803200007034001c03030440da02c0459a0351103201500c141020b11900324030811110384850041a1008149650000300000301104081080001c1c403c0300c1c240c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 370740953 1250 370739703 370739731
    0x706050c031506130b0903071503051b03060a050603060f0310050601090f0602060109150e130203071d01230d030804110d120f02010b0d0c03020f0109121712 69
    0x202c08058003800c8401a14803941003032108900f107a011000c904e08449452000c02e6a41140b607000c60309001140d4000030031506100380c080e50b040d416410143c070520081521290204541454420502043d40c1c0aa0446642e19081c480703030904c18029074000e10000d150240b00da0300f50000a2424002c10301402c84182c03030f40107001455070484201d4016101d2a0058807070b02e402c0c03c41c000d55401051046001c0540c58032007030b85000032002107140107001135440d0900030340b07424003140802002c1100100c2c02031058030703000602e0050003a809950301000705108107950f460001444c1d940c0401c0c14003901c1c1c44100340400c0b403450366910300c0c0c0c8144512940701c03003205140500344a140111031a04040c05000d8040119001985684480c0881c0d185402c00120000c5100800c07401403495404654111001c05040418058044044000c6034406c880d485900c2c14440c004403a0b404082c40b81c08038408410420f840000e20450090741d0311100140010704020181000740c140210a0302c00000c13042d01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 370742203 1250 370740953 370740961
    0xc2106080708070518040302100902040231080c0d02040207050304150903170f070b0403110d110f0304081e12040b0406020f0f07060f05070c09020310060e03030409020306060706050c03 81
    0xc8817410240081d045951001441c3c140c8029440e620014400003c00e40d46010520031951240e0549000d42a408140801282048000010082d400c3c603a5400b92840080c00034100400085800d070500d4007805000c210321041e8240006034010f00d004840380c2c0030911001c100c02640700031824500714280e441101540c0307141444c0b05d170b00f0220030080b40c80c00b40408c85458055000c504540c200707079010342c01e82c0719a543d9040840700c4e0040102c800d00140680c0700044544e42c1d204080410000010064400401c280c01882c1da60b8440c91086000c42e42200d13407441400f0400401c03011868240302d00f50340c50790010200e01d2403158800c0d00280120000450144481541040035142d00501d000040c050982c4414405079542218840e000070480096001d039010361140301900c9510340d100009007905030716142c4280103500200c0384038510401e00680000c0852244441a8284001802951070b00b800c1c964000040d60000389407a401c043c04102d010001a10b5210301c038130070382c0500c0e001926410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 370743453 1250 370742203 370742209
    0x100902031917120709090903090323010f020310080705180c220311010c210507081b12340f050715050c06150301090b0403030605090601030c21060807080705 69
    0x104980001b00914500900301c000030390015001401c0d29000104284c16111403101c05450b00581d08214140703500f0314400340343e4682541c02440c040c0091121040d08161110b41d41d664615803889040d41c000f45549145400035072000205402000b05002145880400421100b41300c1440311150768461300342608009021812208101e0341c14246004d544140c27943d151400d0710001c4a4440849040003c200c0300e245010f101101c01d07403940030700310a8851090302071101640d60f403a41843d000380201c107681440c4002d030320101d8100340030050801401c90701c502640b41071440211100310040c00001005808981c4900200e00c031188920001e01401d4240404850740e0750308802400306100e0140500003550b1000300d44c0070703441014414034944030b242c0c560029015000c078440180113011514184028183e00d50041001c1d0307101901d44007111745404004604880c440000840090400f01304800812144810440100455040800d040c2d442e18802410800107034000342c01d40e03001c501d0400c80743c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 370744703 1250 370743453 370743467
    0xc071502101118030c1507110405061e15030103151103060a030b091e0303040b0105090c03040f030e12030c07120c050910080d05070201021009020319171207 69
    0x280620414001d2480b0b203121000c1600446010788003040c0e2482003649141c03420440c205055000501241150240c40420802039010742e40a40303440d0841c070000e40350380c00e0a010705402400c014001d2580511034a409018840404401c1e5034403240b40912003452422141c00341d4080d500403150040201c20300306110b01100c0d8001c00c254110401801002003d548644849080380d401c00e8103201290f441c0e4001e107040c14500e00040d010081e600d1554103002c10004040d601c141c5c0300720800d07006a6255002c000c0404801c5540b141000340410000700050194100c40344983c0c8603080c03200400c030f0350000194a040e15000340401d240d00110b8490f5202008019450080c03c1d119103150030410300340c44444074070301e01c0d01030a80a85100e1001ca0382c41c0c0341240e4010024031008066826000008400810301d41c89100c06034018480c0d14401c407070a071101c0c802c207442d0740d900900404446400c150341008440903010260b418186c580300314007400380403200402c241070850341c000a00c5c0c601044054159 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 370745953 1250 370744703 370744723
    0x30b0307030c060f05041203050403031106040f061a030109050c010201060515030109020c120705010609061e0303031a040501290403110906041d07090b042c030c071502 74
    0x358000301007000070400c051102c2e0300b0b0364a24900004900d0002a00b51042e10443d805040320000c507a10800c01c1c143d001c1c000d0026284244d481884440b100280596540420356002e0074008030b03040d20400192a5510103c2c180f50f400112511f1141c6403800242151070000050307810360021003803081150703428807681000e46411101007400003600c0c02000494081402103510b42940000e480000350300800c03d886000f1107000740d8564504e0300e8546540602198440c00324810704009012542a014010030041e480501911502042c80d42d101140a055003220a170100e1074400d06240c0d41c1c5d01d5600030705010382602803c1b84400150410101101407050002c3c95202400b13200c24030000710380202040c181e040c1105c00d407803145c690400240081c82c43c1c0e1600f840c000d55000c20080d500d54045001c108403106140b080000e442040107101c19190000011207a40d154500c05100d0b42c2e113103801c404140c0420074100c03828500c0c4402640c0c81c081c81c0d44c0282c50803080020544803410b504021000712 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 370747203 1250 370745953 370745959
    0x161e0f0b0903040b0904020d0608030d1a0103110d1109040609150806041a10050603070f02010c0219020d2d1104020a080412020127051b0315040501060b0703050307030b 74
    0x50f143c82d240c543c0340a0b01690003058400c40e0005921132a810441d0024800b40082d08280d80d49d4000011800c00201700c140c4a0903c42420589016503940c002e00ca0100a5081c03101c20600d00484041890000e002c016080c9101d09010b11104006486912801c4050069900002841468114600500105a403180c0096802a4100b000007450000740c0700e403d807100900c19140d911845120710041c00b19400c841d4004001000b04844160b110704001c00861041e0001c001c00558083d08a07110300503050140d941020a481020042c20301034045c408607809080010100d440e054031010b40c030803602903c00050003c100f02c6009201c01c20f403400500758400c031411031500c4040c030805400080003c1019282e01c1e460078245210314000c1d0040701c4104107211740f8a4000220380c4055806402d094020395613072103880c4030b8216120044034402510180100107100d5100050441c0c0a013001c0244112101e5480703c10001328800d4003c083d000d124803035103600d81c0340d10344030100038101c810303401031148 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 370748453 1250 370747203 370747207
    0x306040b0627100f152f01020a0302090f10080123030304030501060e011d010603020c01020909070f0f051e03090708010c0c0605090a0f1b0e251103161e0f0b0903 71
    0x10745410449001c400303d001001b8900500881e200e42110300c0c050009481c0650001900b000c80a42c16401068001d5084401c01c1d0701c0038500b4240110000050350f400045a8800018007000443c1e903130030301140c00840600f00d0f4407010382000c60705582003948215001e079110003060204e03008980759180504081da11810941c88014801170030311350188204000d240d400102161500d4007901102c2a0007009000c4010038188144018243e090b102d900c84002485005880b090070710030303c2100c40010719134002603c4007201d06400745807030b4800b4041c05181e114100c0001071241082c01829980d910549440400490b14189079040e21001000758419821118030980015100c450404072940c00107040c040d10301c00004007240b40f021130b4000810462514080240b5846144446480b00e6054440d1081c100707400d150603280042c0c140c400c41d5a40d081440440d0212424014003482540505c1d5040200b41a56101600c4903030160420707690f0015505c828424450008441c40c2c0001140700158 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 370749703 1250 370748453 370748489
    0x316030309060c0f0609030507061802041802030a12090807082d1005070e040905011d06010f06050703020106230103060501110705091923060306040b0627100f 70
    0xb0311300c581c480100078140c1d956200c101c000d140c03041c0283c0384482d80c07140c410004001c80003154100c403048420124031860a00080700541004030008550466024000340a2000255500e80d050341441b201441048500b8400051861041280701c00601c1c8460142802071a1540010801c1c0c4203e8810b6544180d440e0720902800d1700010380683c0503204507800261a16146812036a10b110700780185e03800307030502c81c03d0f409010065214404003c1050803811121882d01182504d5940034407400e6000c22080c401003006900400041c1200f500c280b00004005131224040d50606030701c010b6443c07442c910702103642001c0d60140301d000d01030078007400c1c8940320b01c6034035080540d0785c80f179801298010080040810340b090b4004002048600501001b40015800c10002c610711410380f00e140000010048d0104806050200b0400c1c040c641102d120b0010780ea818043c00380542c50a402031070102c0e100444903004001510525000380405029517043c280303404000c8601c0b003115081101c4014420001c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 370750953 1250 370749703 370749713
    0x40518010c0e01202d0712020d12122c0601080c060901091a070b0c030601080a0b18040305090a0806010b04050409151a12010203060117150316030309060c 68
    0x119101020501c10354003085810f03034249003084a91000d4400c4111010031201140b200c91100705200741303c5000311843c5a0f55514072100c41c1f880007402075000105003403c04041201d0940c0142c51007441c1c202581c00d1f0001074407907000c0f900030a1050000c903580496071588441c808038003d80002d40d4030300501c00c1c1e50400d078880e9180d6407000c026034812440002c1c0c2a8090f40542c081c40001c00c0002c0da6104c41c8a40010040c0b010b82c0001d17001c540310343c0d03407000041e036540c200c0301503074080c0c00180c2d120b85032595010032510041c04142c2c001c0341c1c40313400400005031602500c3c0225101d40c0c469604c113074580c9405028028668626000f40d01903401c00c000520514814209450440705c08850105900c40035003458000e5441e403000001c50070b070a12034914020480301b580310000032819a82c020f21114101c522600700d0205460480c00200003011004c1000185058203400107010f900450600f81003600003032410a9148001100100c840020018507421461400003000c3d6410005442005a0b40d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 370752203 1250 370750953 370750967
    0x60103050610300204051c080301061404080307122c131401120515090309011107050406060e03010516021c030f090f020a050105090f091302040518010c0e01 69
    0x28010042030703c51202075a0440041200d041c05103c15205225050f818902c001e544a80100d07030041584032074400030f0140404800328072641200c840c1e41140d0900104451f81d600844030140703541802d001c08980094240001c1c1000b80c400c0c205c1e402181c21300f03400039100b900012200c0c1c80700c02901c42d841605081501321029066000c49090240c040c03840c90f050010003c090800014400c01c50000ca01902540e40d0855100d001e02c3c200c1c0c0b40030180040d0f441561500b103900025030740003848403084950007032000b4014802e00f481551000f5403620003040844105501c220b000840d042045c1e0414202803160750b410503001e110154914900c7ca1010f50744007404d000819400c24201e1100400c00d111340d00040301c0d07100d041c006001c240518104420050044202a84a4541d00f48000382660240c402c82d458820050f0240c03a2003e0b100040040c1540018003c240204004035404016917451141a1113a050701c100784908495424007207084840b01d00c4102c0134400c46a5604950380c3e00070304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 370753453 1250 370752203 370752229
    0x301140c0406030e12030115082508102301080a0c0c0206030a060e010e1807060e010c0201020a050a03051b070e040605180a05012f04030b041b0b120601030506 70
    0x240820f0802e044d80b039251500b80c10f0a03003001045008000800e8080781000034084d1098156950b8006403904140304255000c24014036080c0e00b545200c40c00403038025070711030b5400810843c001424950700c12000c415126122258110404584032074441c035030b080741503680c000600900030070081401038800340040d0310315440a4403402c0003000041c0450b0840d00f00310080c00104410024a594807400444440000c5e10000d4040c1440c51580c41101e9000071301504441459840a0102d010180151103500391284281c0c1140250310308400440e0f0b041040c807803000c0c8250354456036251003c100ca42400001d00c9030102d142c000d07043c100510354100c00d1241e0007035003064000429480303050107150401a0541d1412680c0101e0f004181800019400f40c1c15a40c1420f0412491070848c2e442d440e8200c44444d07000382c1d2001c0602091000c12220070342150710510651011403003000e120b00d04039041c1d031181d0144101d4400042c003158521080d100060f0005000c2c00c2c00d000c0b13030500900040030340e20500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 370754703 1250 370753453 370753457
    0x80a020f0c0d02061b07060206041202151612020c070609170a0b060a08061e071403010b0703230a031104050d0f03020304051c0b011a0f0307120c0507020301140c0406 73
    0x460b0401c001080001620781c685040f170103d40b0500d945d428040c0d1a030307404850990305500e0003605012480d0021810340703e07001380a1a45075480c1d42c0d503401485600321210850081103482d4018101002d030910052064003400c0e801000a603151000003040703c913458108854600c0c0041d120207000c1c41c0003524000c025485004412981d4841c000f1070503880943d44079842d40e203e41c9080c45400303088072103900b103100304c410340c100e4082c5d40e00d410a4526060000441272500c4040004011105009018014241c400d150040b0310061050910802404120150b0b801240000314040445d4040c810035a90000c3d070030346c00c2d082502c2d00001404d0811140d0014010040b06001ea104040c401d00444024250080000c01103940d1255040c2c8000c10b000303c111100c40d00d5000214124880969410511080c00d03255032901c8004201c0107034540000c0e00d841c062001030034010100340c280d8010060066019913886031500500d00401d03095a440128070300302c0c02001020b10411540352070890701546c420f4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 370755953 1250 370754703 370754707
    0xb120610060f051605150112020918070e0c070204110a2c01030e10020307090807081c05070501090206041d1003080d020c0c0612090f0d020a0f030e0a03080a020f0c0d0206 75
    0x50704000c0d00700007203048002c510512200001c200d114807507002304411070080d140e201c11562829010f07040c40d10716030380b080c5103a404400c007046071155114802e41c4c0a91100312450501e9015400308050b1586c041045161090102c0c00340d29490303021600d0b15106c100d01c2d80003a14000c030400f2100281d8040075a02d0b04041c0c44101c0030350420010040c24411807801c9208641d1f9240032a4005e05045042c020031505018a010016403100005004000c50b80381010315141d0214400040e40d05500001c82101c0654030307501d83c42d0140c0c0da0000540001c0449041c85c6900804005034100b41820040c0851080e0420710028004164500300b5122024020000144d07611400402246441e540140f01782d44000d00180d02c2001c0d142c00e104443c040d4442c0000c4031100380145032566120001c100700400141e1250b038105012070101c1f109640d05a00030f04040c140c8034a1100403403016026600140e500c0f2a0014a4a140d0750b4104405601c6010010183c40a0404540095101d0202c090040e214900c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 370757203 1250 370755953 370755997
    0x14060f01121a01080f0d0302030c0a232802010c1722060b0a080318090402010e0402070311060702070302030601180b03030d090b0a090b04150b120610060f05 69
    0x30007240281c60344800300440f50b940da0300841c0d440c400403940c2c80c0680a02e210303440540d030081c002d480c06840000c0c959410406020800c81c0d106002d0906043d81102418a0301071500c040c500414400e10126000550010122001e1040c1c81e40c01681d0300441e0316081f01040c585520000b50a4210001d9140701029141d0f84500c940c09810003021013010001d00d4021010414283e010188070340c1c0549919a10980e1056130b00d4490140c0060400c050100303c101e00c4462a1840556501034030505040c000c49400c500440c1c100e0f001400c1c01c90110b43d222420001c0c901c0c2c20050580e001d00b41c3d20042c0b1000c0c1c00e650100e52205c00600c581a141c9000700700c00300d45c64006070807080c1540d002500b01ea132502d10120a01340a000d0082e000d60780708041c40c0100300440c3c198083c503c3e11940003070703c240392520b65980b00c0900e8042c0c0484030300915901c40500c6900c3d6200031803145800c959400030a10b07400c20554184406009902c040c1c140b004110301c01512903007000c00d4501000454202c6544008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 370758453 1250 370757203 370757213
    0xf0501020c0f040e010c0203071a06060f0901031104060503100906061b0f12050d0c05041d060d06050a06030b0f0601022a132a0203090409030306050d0c0314060f0112 73
    0x90060f280002d501785004000c18607400009027450b00d001d00045450160b8100400162600c1a622140c000c2d0703040090188855103207000700980032062400090b041c000241303202481c0c1058102c2400680c00000740201030100c2c10070b92018046040040240c0d0f40340c928041e192026040503206d04d03005d1103100100b07202c1c03106540000103801c266080b4105020200043c22030b44240645150140f908402e00749a40c4101c096405a0320340e4044480c40702440101d40a000000400da5548000c48444040002d552405458090396400c81d01203509400e6107049414510001c01380004501030404000007030b070340050f00f001c42c1d4010000088010303081400c0d843c58281203500d40c98000d454500c10b000810340c0b43d0300105c8a90b010065219000e450400c0c11510110301800440040e40184a88040c07482c0640c4400d840c5d0303203c0e0500003038450751070004c94161a6003002c107231680c000da00710800178810040500070b00c1c2e0300560060710741450f214824441039201030190350358048118200c01c08003c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 370759703 1250 370758453 370758461
    0x30312110a0c02031e0606030d02190611090a0b04090b01020118020f03030409050718150909020a110106080d08220303052d01140a23010c0c0608060103060f0501020c0f04 75
    0x10280d440707503440c0b0217101d4040070385e190030036145180644111804080f04030b1000c038034160300c851200304460400616031246000740c50340f0b80100180507020840c001e446e545e03099080b0014814001c941d0784540c134040144033141c0707901c83c0d20360559041c50306414120031000300c14100258103c5816040d0700d06003002c42e141d40941c2d04000489031418080c0240d1130f0300007010517424091070f40c020404940700c06e00c20b50490130329a40100405d14080051080d800c2e9078001d04064441481e1003265260015122820358078250b01044094100c803120507561036104110070392001900310600c9001d0400103d040500740c035914082c00b016920000700d42c017503203500341c00070909103a200c5c0e40c460078100b6030555140820a2042c600c602c00007c98802403410124148402c4801d40c3d0500c1e000c20341e0445221006000c0e03a0b500504100b104424030001820401c5040090a0300d036483d4201880e22a0014040b1112a00010b140751702140c01006107a070300041121a640c42910916400019400898060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 370760953 1250 370759703 370759723
    0xe070515090d14011107110d1b0909120206010605072009011502070e090316020f0904140d05160f1406131b0806010e070507080d0501030312110a0c0203 67
    0x6102e0030251414070500101c0341d41010882402041500c2d61a841c8032024464108010009020000c02100610704203115a203098015800c091000f03036401e13941480d110781038000c41c1000360740312444028080500340ca11500c9006000526146d4103000300908680a1901d00400303102c0d8010254116055200c000101c10750007409444140d6110f5031080c60388074440b0f4100c0010310a141c800150600044a0035026404110255142c401031250503090400c2c01501680c000030900000e03480340d103509400b240b080d4000c0380c0c81005241400c2a072400e21481400250401400f804260149107481403034441e0260311001400c0c111400e4a082c5410085151621040d4001d01003049146407030803034000c140b80d10542942e0307201518110003411002640c0102e440640c0004010b1148001c5601e00036000010b500f0910304280072542c4100050f880f1440d01e080c02c0d911034004104241d0000030141050907125001c1c0314114101c00f81c0341080c080c40700ba9004002074000408190b4074248024880 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 370762203 1250 370760953 370760959
    0x160903080d1812030c020615190b0c0d021c09090c0e0a1503140108060f090f0307030903020a080615041d010204030503031b1804020d02120f0108010f0e07051509 71
    0x209019a04150f2403a800381541e070404a070406075001c07640c1e80301055007071160b12400f61071a1050000303818410719140c1c0900998910704105c00128081c07a04001428054083e980240005800b05000a040200440d1680f5004012a203400500c0f50051803200c1900d400d040000340445401d10125441c000034180d880c0c10500c00c420102d000d140e0b42101c032001c1e086a840610000040c1c2042031000c1509200b205200d030842c03804194401c075210b1000ea00660100203d500d0505445400b40c1903030701c0400c08034040340700c00b00b04004504081512200502400c1c0c0500b52a02d01141058184200300e15043c3c4203950310001350030030f040900a0a210b18400d43c00840d00c0d80d4076450966520792042d540c8030030b0070100112a80301881c41e0700c11500c10070030701c1a21810202040c001d00000e0b4120f0404c1c10905034080c031080d00c01c0c16500050740e1140468220600e42545031800315421180400b01045001e410407203402010b0030009941800c80b02c050340da860510a05200201460142c0405258 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 370763453 1250 370762203 370762241
    0x11d010309210807112a031e030c010c08070f080c16031101050a020403030c0b0a06030f080304030807091a09040e0303090601030c08010c08011211101106160903080d 73
    0x1802c02d80c8000340030b10400e9680ca07a54443e0281c041519550b8941d0013010b84103254098000d000c9004116200c41180c00103811039401d203241108114160900c1c85405400d540042421701006200b4010745010300708600300a8403a0918000040c0741950f815281001c0c80a148040b030162802d403011038000d6a410704e000c100450007450010222003060491280560034100464040070083c421101220341c107444194014000799a0703009607203001800040c04940c0c130400000804c07004240806041c2c03003440c0c615582d1415240107014800702034121020030102d0311042c040b0b541d58429004100b0301030114a0707124025800054058070b44404030030340318000442402000c07040042e40314140c0303115010205a060701d480c1c0480c01c90741d030400d0840c006000500100500c507214456400304900074401014544c601c10007181d6017001410f2100b0008400314100b178151201484580e400c0131290407001c201c4d496000f0003c2c0405018003000d403205800084c2c0c41c0d203200701540040c0110f42d008038100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 370764703 1250 370763453 370763513
    0x628020102130f120b0901180c03020108100b1e070807120f030507020714010216060e130e060402010503090a1a10270b0a1a0d0b011d010309 62
    0x240030390000c001c8400b194510290215001e8800d9440205030349043c0403140b289030303658896500424020303281d1070302da540e1000030050410040b800d00e80054002c501034420280b03140b00040c07820304000d00c0022405070300320060102d44070760002c0f24407128034980d04c1c450648800414244501c945a4000c150440014000041140700b18214121444540f20011b03000d01081017035055500c201da1180051300101e000f070280340a19203d0034044041881124480702da00c80079048400250780052004c54481d2100c0403a03485c0c43d071207403401008046000e202060b07040300e03420354a25003e00002d05001c00440054141e0b001002503c10840e0442c107540d4080f4034605040d801010143d40e40801d40c55640070200d00c402500104800c08144202004203802c889000900105100500198450008a00040c2c0b22080d000003203001c7c0b180c84c5010703680d80b846403d4441180c03154006107051000c4805d4528284480c8543c0380f088001c00e027030218205c45246007200c01c505042072400c1750710b400310001d2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 370765953 1250 370764703 370764707
    0xa03050105220b070f090e0f0a0509071a280804050c0607020916051b0c030c01020a0803220602030c071401180807080906071a01060311090628 63
    0x941c06940c001d4422094124103103950306601c80d0b04100900750034148004150098450396120f440c4018620705121440e07101c40a0100c030440590780300700320051607400d00051030504c0c07080b02d811419101c0100350701e81c5403c00c040d1507884441c03001210000042114180405186a50078200c039030032800d102c04140480c40034105903020303034054595114800d5000103604054040711181c40d001040f8501c240d135001140070885100c046600d08001090007002010081c080068016689240c0540700341d07450311040c14030f0410000c00c100d0465000031a20b002140c00d4204494202c55180c207030003a26001000200d1f118448048014031642c800000c01500702c20341c1d4094010907208402506440014151160a960f902541031002c80340400004001401c0300005000c9144110003082c01c11013074800003546600080380c00d0341d64079500c100c00440a203603031801501502150508206685504d200300740e440c001c4803d030034001c20b8009151a050b10003490100308029050880d0080c0300014040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 370767203 1250 370765953 370765961
    0x3010f0c050c0106050109050a09180b01060201060509090a081207030b0a060c03030b191e0302030f0a17040e07030f0b09041103010b0a050d02271609050d1a0601020c0a030501 77
    0x115955280013000724040d0311500040c81121801800e8126003030418010000420840c41034203080500d60070244002921561141d008064503000000c21b80c6c5400700344003000d0002000c4080f01d400c616500e0000403040e5098070550007141034000c90942c7c0d40c002c01c0d0300400c0a2025164841c10180b0000f030b02c541c2c01070b074081d00d0303510176681440120161012f010308494145402a1180412501403003402c26040c15003c41c180c030080d03103114076560794001c41d01f00302c000000070406400c07118000c018060880c062001c4680306121080c60207181c50242403070b004014084104154545040c581e000e01141c0084420500003441081c03142814a00108225104010180203500744a00c00100b0f103004100d40c400c03906e02411882e140307001d1b07a080203860300001081c0443c400134680d51100000b0301205040c0b0840b6400c1100325928030303050001e06102001d40c4107a200790010456080042c21090444103682d40c0c2000d000d04c20346900d00181e040c800d4201102e608100700b00c20003c140881500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 370768453 1250 370767203 370767217
    0x3090715050a0c02040216080d091a010311090c1207031d03071a0406060b0a05070201020709060b07060c09051002152a0a020a0b07050c0106080303131103010f0c05 72
    0x84000c6411124650599a50082946100114401c00003110240c1000c0c3c00401072141c0f80325505c1624001075071142d0003904400c140c40301203a40c03a1051810801d14100e42912001e19201e1840c181d85151b40700c1c081080b101d91001c0c0541c40c0c0d0000b0405070140b500c20f4800780684072200c225149042800240102031107030700c03640d0707000c00c154200000c40c00120071195040d801000b803030f0345038421844030110300c030001d001111800e0b03039120002064100e00c8050036a01c50b49603906a41c4400c1400020300d400020341091101c0c600d480b4042220138004400c40d0b0003298030032004a000c824592094448d014294841c582101c0045180e51925078041404030300216480c00e0183d081d2225510501462030703400004c00600b80c05d280e03001c4540054800381c1030f0190b0510490b110603109544039142441d098520b02c0100d80301103441e1703890300130030300941d009051128011410740c9481000340d013001d245040090070070110205549916202900000300c000304014041c0104416074000406c2c41e44940 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 370769703 1250 370768453 370768469
    0x504060902011e02030a0c050c060a05180f011e030e010c050901262406070614090f0c06090109170706090602030901020c060d180b1905040209071103040b030907 71
    0x60110340340025940f100e9240340540e5402541058084481550101d00c001420b0701c2a210b80981410695210401454183c1195031015180c1d140300c02d0b181141c4001030110791003026007002c403280b280d0b0b2145040017841038811100040381e160207015802083d031501085200d50030100601d07807040e001801405500c0702070740d0b411245000c1c000701c1071801c103140010b50881520308000c41c1d030ba00340c0305006401c0010050300d05000440d0180005055a0008000310f500c50303101c510b400e203100c0c250320b0f0091780305d08048003400c0081440202903448031011040607105450100d044181c5134440c0011002600c00c40801d40f61808602e4021550741545215240016850050120f503a40c404800e5804402d0107030024901003021004000003a004175945403034250351480510300d1541200214078101d4040c205d00c2c00542011007501c0d141134058400384404c9800d203802c0c84010b0320b030380c00c90b60391001091501314900d1224210290540c844c0d5844960020740c0842844120f00c404500c101c2200d07814 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 370770953 1250 370769703 370769717
    0x3060e0d03052703190201050a0c0e030a02040f020c010905010f1b05190e041a090105040c09091d0f1b0a0302010c0b100f0b030f060406081c050706050406090201 71
    0xe0045040d148210740d19004948100b0b80503040100d03070580c6a001c2d242c44002c0d0b0b81440100044010040e120040d0100141c0d10340c802d01116160070710070300c10380b20300e240381036a0100441404030340d0b40c2d110004000d0050f03503582c00b41d148440c40c80e4103880388410303001c009225601c50740c03d00d14041d01e4100710320701141d480c01c0c0301c59200c184030700b500c0342140700b0030746809043c104100700d41c40c0d00700401e0f034031101402080701190545580d10300c182c0e0a003a60060b0030038100ba4208051101c65281600310360b0180e882d11440d00c6040350130003000001c03100100004a042c924000c0401e454004218889032070f4410118412110400801d5064a0840e200200481c40a11408000c550542840043d0110342c1e40030210010452007601c180c0d20005c41c801810351a550ba281c1008138641c0c5a02c42c080c00040401406810f02c1150106a00040100c405114080c100030500d03469001605c4100d1120500c0e0510307e9105004806440a241e0405401c05c098903060410710043e1881c007500703c0c002517030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 370772203 1250 370770953 370770973
    0xe030405120606010f030903020c12060403140c2808040e04170f1209010b03030c0307030909060503030f0c0c06160302100e0717030405090403230703020a0303022203060e 75
    0x8001542c510801050355407a1000b03150035420303802412841c50039411402060300d0408541c83d100300120352100004010030840c138250400810500c120540310341a80030803c009403801c400055080b0070401030440c071007014030016144040b404040e280050400e000460001154074030089064407030782c09034107208044500103000034000d02c1400c84100c0c800e08113000d0001180c48015600d0342c0b000c401c600003d40e00e00c1d640300291441d009180d841441e9440050381c0b000b05030b40086040b004040544e010700c10070b410500000e4903805032050242d1150b00100304884408010000100700d074601030141569142c16181c5c083e1801504802034001d84030300c00b28000c04180500c9170542000c3c0304005001800d09042459583e5024511301e0341c51b5120030700011a40342d0f20f1a140b50f00451003074950018021112901d0000e0300704141003440b043d1014801c41021940208107166030726071600d401a81c0b00020303080c4440303542c10344040c100d642140c60404401c00c07546612840c4402044c41c22240d0200c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 370773453 1250 370772203 370772239
    0x3020405120304030b04030e12010e0f070512031204081b03280903060203060a08010f0c030513030512060a030501090f0b010f0b0d02030612160f050604081504080d0e030405 76
    0x104a00c4014074001c441e10001b00403a05c80c100f01c60106030300601d440d5900802c0c1201c3c41c01d548141e03101300d10304d0b00590103001c440682000310000810080d10301c40e04012000303401580702e000381c210b9108210b140d8000141007201c034a00b00c0b41d00c0c40482c0c4400108548070a0a80d5480d04107540423040c0b145440c031140b0400c0004503140b1201140c9644144840c0c1c11596518040c1d0405060a6040003141c107001c159144280210b044d19030b450700c00051491100c4000406a40c406400c1e29480248144c1d5000401c0d48002201c440c42283d5081d0308007910740c100411030210480d40003514070b5281c44c0010040014229985201e01d025000da802d203030b43ca421120001030500c2c0b05904400408100106440100c5e8018640c40b0200074058000c0b042c5280c40342d030a013461a1101c690081ca050380601200f404840b040020b404280e40450409050940480e91345812070000c844c4d09409000140c2040350000803110041d038804800e10810718240311240d580d070482e0103420311038402e105214100381 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 370774703 1250 370773453 370773457
    0xa0c0602011413060c05040b1206030d0e010f230d090605010b0a0905010c080f0301030c06032004050d1104240801090b010608180d0801050319170c030415030204051203 74
    0xc0c4440f800100c14200d03a50b504000c22029507041c0034818280000940c0b201340a02900e0f01c8022140c1401c1c591804000301070400d4100c0402c0401d100791020300e030320907992000d00c0e10580f0303181381880c21180c0b240390f0016004540001e261620114002800820540315411000c8e1280c402c0c0c109001d56625541449807500942641500240700b094040010f50310419158094a0042e50401e1800340068014212036000341c2003659614508242041181c0d41841003c01880040c101c94009145650b481c0b50203100b1441800d11078050515454140001700700b00c0d95962000801c00c210701200c140311048018080b1a09840e40740a04000150510060080480e21648a0708403101c0341e081c40400c1d141e410307010302000c0f1901d070100820210407004106001d07025406469503c1c056240408040c9050000000483c20300c2c19403a003540010044003036240400e13401100d1507141e55480d41074501d0b5010b1a800264800724a2001c50002d5170582d0040c001d0b00c2d4140c448038a50350f2101c0321140d40b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 370775953 1250 370774703 370774711
    0x50913021e0a1d03030f0a030615110607030506060f07060b0306160905090405120a120c0c15020c07050907050706140405060603030304080409050c1204120810061e02070302030a0c06020114 83
    0x50b03017003002200d1100110800501000c3d000d402d0010340103440f0154002c0c9100000820300214010644181504104010460b80443c091a0074041c51600303802140703050040040403031280201044010811805407c042d0130b81101600303c45251601400c80b00048102580d54000316100b400007241906240c000a4071803034102004119104451107140c500c3d80c458501c00c41007040703041d1000d03040540f03030103a241c1160b92951001e060442d01d0805060490191146e80c0d0390920410459003800e001060036001c03180c085500000d02d6564440948541c41180002403689203043c440f840e22660303a0501a010700d004008070340e410303030350381050550307a10060350060319181062000304040540c6400496000c1d00d07114490713003000742c4d4012008491703109403404c584000c5000210303000160b0001071306e680080ba504080c0d602c00d14046028001d440803848400c14288400c000c440030a00800074400119800b07003c0300c040d41c080b4241483c0303c0d030413401703003000550070200c50600b5025400402401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 370777203 1250 370775953 370775959
    0x30b040b0d050613020a0b04060309031b1110020717070311031f0c09150210050c0a0504050d020d0506010b030702061f060e030106080706050703090f06050913021e0a1d 74
    0x1516102c00e2030101c2c0390013210481e030009000601043ca42561070180004101d079490106885941d850003030404051b5513000b614540340100058081111680c0d03031207034100d050710034007891040310340101e0501426070000c888050f071461130b104980d07900242d4071044078010380000340b503840c0c044101501e801e4040c044000941c1d000b514400308104650001a00c0311890600c0d0103015620421301c58840700203040c03900540c00030402010361002600407658002c0700078000c80c0c5098a2110090054025030081c2070080300b40c00c0c0c034101107440d500848281c0b580c000b01104c0b11580d5501c08120030358030845618005024102c0400c032860b0088a141d00d41c0c140e00030341070b1586030600c04e0482c0d94845d217042a030b505648458000a880c1010300c60100580165502e190391050981005401125298019620070250203c00c111f1250b1000544003900b0013200e03080d00080c1c1409035200a80150301e11040c841041c44003103910014680024054140c1540395081c401900301c0e00410000440078049030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 370778453 1250 370777203 370777213
    0x20a050f0a0201060509070305070f140414030f031b1504050c06070618140c03070e06010521010603020901080109020310030303021b070305030903071502250510030b040b0d05 77
    0x15211035514050080d0010501c00001c0d80d66a078030002e0f0b48007205440724404a56240244031006a00c0010b001901e012400c00020194000d217000c94184528031a0b2a40100404002c03000d0b80e030140203004400c001c4a04078ac2c3c0381c2541c1c65585e0900318124255154a200d650480c058840904502e180f2503a0400d0140c4001c40500f0184401c580c4603002c11500250b507039120303460708030b0b0744146000110302032005a14030450b110841c130700d00031189268503c294456182040075001c16280140c0c80142880c210751280840c0203030340410380c24801401504029035002051295055015280b011001d0381c84c9445e6982c0d410350361089200c00e0707a00c0140401d0041007030001c24000d40040c04564034010a010301e51401146c9036080c1102508100c0e21034100040c45003841c50100490f0015200c425a0703e6080c0a41130b5000e036a0344102c07103207034140b1032a50440c40e1400400b41e0042d070003000e0142500101c811700100080003084c1d0024144c0c031491130310040070b5041c24600340422080d50b202000b48 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 370779703 1250 370778453 370778467
    0x40b0304060f020309070326030a090c0b040e061f05030411060d021303060f05010f14010302070b28020a0c0f0c08030c060906011409040f050f0f070906050301020a05 73
    0x105459000510645401c1d459030451446400c05200951003254140c019159160443c40c001e0410f414824015512071417405040e255801004110380c0c0041001500203070720055850a00c00001c240d9104602d4010042000a0900901c44526220310b00482d40600941503400d08281c01d46c03108540000010001d200203000074008001c01086641c00919840c2030038410303200c00052b40d100348920114455428810000c10140c2c2c0605050320386e00b150184280c1d030406065152100d101c0c4100c09d4110244544401c0d264000da04071604a5080000511180381c181c003094203140c1951800c0c00c0c81c1c249260403d031128154800e644640143c0e40d6220b14810094903083c00b040c45a40099030030b9000c440780001c00041c00c0005080c2403a408002d0711032403030144113035030401d00160b000d040000d11082d01800c0c01c0d542e4000299005034084803410103402d184c03c3c020316000c0500403c11941c4a1400080400d22000440004a40380401d00340321441d02d8106050907401a46952030208005000034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 370780953 1250 370779703 370779719
    0x301030512030f0a0b01020703020301062904050306071d1309030806180126030310030308010f05100c1434080d210f021b0a020f060307020a21030e06010b04 69
    0x45c0f40500144116900203441e90000790840700c017544107858044195088080145034040034070f501540c5082c20704d0074070f80344c400401d480c0c83e00140381004016101c1c08a507540c0005640c110700300b02c0b0140c15011551000d914100051540420690200c0c0000c2d00050591400102c0c1084138810325152509903440c01e041c013100c3c5e05140f01c3c5000c102c545c00300c0c02d807078803102000a036104121450481210900d18100030b400341c3c8068120004407041000103100c55140d4400c900f080040d0751078803081080c0a410720142218100740c2030031382c1d0b0281d40c4d4619048120120b040705880700445074a61b45c800c0760450500300d40004e00c107111194000309441a8041c1c00396070b5136800001030000180b0607589800b9441c045a4070a01108041ca501040d144c2280000d2030011205c10550f0740140310080442e00090a0984081c048606c900000000200024400d110404419511003590a201c01a01c0031440d00500c08406036000203192038001448c1c4540003404504032030f80000d042d0324044c207040c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 370782203 1250 370780953 370780961
    0x1205090a1103030f0309030405040b0303040605160602090d23012904020403151b0801050d060b0a090903110118020d151d01020705060a150e0a0e0a0302030301030512030f0a 76
    0x31642d4140001d015041c01141d07544025032151203544081e655850400b0304100446014042c07843c0284c1c0140001e10910703030003104031684101140f0a0940e120356526040000c0d104503c1d0b0280c0104000b8201e108010300e41c0c030030080c00201e015140510031081007100e4203da181400035441c0c601c0400101c10720180000300a1070740c0101500141c9040c1d16900c88500c005d6607907800f4011260742e907401c1c0585c0780052300d100c80e4039031191030209050b500d04070005448140e040c002410046d070710149810244e4822002d20010080305205100c007001c0c0781000740c41c1d6410303402d40d042d1075420040c24095110840038800e6416078010600f24a8842d0340d110ae0501069100140c06a0b0f540c90510310014000c00300c610715502c44030800545c3c4da4420303103021030400070081e242e51130b12402c2141c5403895515500503c001e0f105054900c0712071340e8036184214007a008240d10717804203000301c190050034180d0100086046c0e0703001c0d1080b10180040d0201d02100d600c800c464400d441100b000c041341c944075543d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 370783453 1250 370782203 370782233
    0xb3c0706090b180f0601030b150d120306030c05030303060114030705120f07030f0b010813050123011703040b070204020c0124060201062103030c0c0f05010c1205090a 73
    0x240029200001d81e455452100c070a44403014604200382050440b45400c10501083c5070458004e8051549195605841700201030110360180c5010040395616840340c88681d1041031308079402d140010700091003c1c0081c032480c0029224101e5070200844c3d10b00380001160f0184c003040e034440034484244081010b6517040982001d0800000f0011408145458012039000b241c0b03508460342c3e00e050020018088030200c0165102c014100521480c2a82e00700c1d41030796000400700040710b2450042d00d0f01c240103180710114100d8158400e40d880d40c801e07c604801030305881003508000302800e00c1d603015980d42e000324412114161020040c40005080a4015028088024001059440040001200b801004940034a80c149840820414582d090003684000c00c10340c014480d03580d000d100200c1d0792044003c00901232549403601c420080f880382143d02401604902202c4030541c2c680303072280c00384c040c00020800007010004818841da6980c490035000c1c4e490391005121900c0c00342c1c2d40c4c451820b8056 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 370784703 1250 370783453 370783463
    0x11180402042115060b12070c030c020f0325031101080108060105012303040f0b0601091202121501060203120a061d090102040b070605040c06080405070911090402040b3c07 75
    0x4a03c0c1048446900070700014151010040e6210040d01010701091140108440100f08540031101c020039040081d84103d550140c1e4500042c40707200010030b00d40b40369110750f58640118891600500310540c0030a0007a40c1c407030000710300000e589800450301d001e028010306106030004401086507600030781c0003201e086184c00e000f40c03c1d071040d1142217010741c10840c3c0c25502c03068604501e8080050036500a603100c1d02c2400c01d03a1040d4180207100f0010141c41e00020f024842218440c010f0320020011590700141070382280300c00d9030f16160000d4581c1c018001d6641c41c010300c0c0c6c0100342d03000454010340098500003502c60002e40700180009500b544090008501d6560803c80410b140c4001c00080c03d40742c0c02110301144600f014500b088240d84a54048410090400306000000d41d01007002070884403003540214840c1355203680329070184261b100c0140c0c0603200180001d055401500039000400c1c821a03592020030300c1240c620300c1c64008120b0b0600c000c1960951210000500014011880c050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 370785953 1250 370784703 370784723
    0x2310504140708061c0209130203010603150510181a10090f150e010c21110c0102010516031a180105030f0a0203060424111804020421 59
    0x6801280440e07501c4600a001030005030300300802c480d00000c920750004410b4404a010411490b100441200080d20081c801c90350003001c10541c280030310320071036101d4004008104ca10368038034105001103404402c900c130407402d02000230f031116201201c00c07080310381441d181c00708909016454401020b28015501c0409201601c5075440d440e0301240c240c0c043c0d1283c5502c0c40b01d0b81402c0c1c3e00900d0240d540d1202a18070b456007040b000d007030b0344800c41448541003800c00444103003192405482c6c4882210002c1c8481820070310181d45164040f0301c0308942e00003841600c1400410600480c2070314400c0703c0d0710400c1210754502c500d07424425030180440507444000003401c100c181d400181c041103081c4c0418811010a00140400d00d003e100c0f25410f003d980c40180104009030380401c0d110040103002801d003000203003041845d100107444c4078034189a0290708004a5800882c0421140c2160107100c00c6c9102d1400900341a00f8684215001d030341000e0150546135000d6400c10040e4402284110703462490 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 370787203 1250 370785953 370785959
    0x60309030c0706020102040f09020f180d08030403030912170610030b09250801060e0607030302160f03030e0705011d0109080f0105060112050606030402010e01021e150a0231 76
    0x1c00e0159002410b010b40c00566540e01d49801c00760021b0898001c0540d440c8104204203403c0790440480e81208501c0142285042c2c4240020722041e0b0310480c007030940031002040004043e450741c0030240b4188901c1c0030145c440722405c4110b651503d52150b003140300c9121380100f000b80c6050420750304040c8091502081401c150000b140701000c2c01d58140c407076200020440141ca00800074507001c250310030b18200d06298540745004240b402001d581c035006007000030b000c8052512035011220200e028642e410040e20742880d010949109040c000d800003072500640004683e4003060900440d00141c2d64001c03511a2200752481c1c10342050002414459050320004020409020142504039032400000d070514101c1c0c0090000c0200045807045507103040c00f080400d5448800340e0341c10507020b2828000441e41c103c0142d00c0e0000c50020419900404040e2009040000a420101e4648071400a4450b2141040c200a03070080c1a042e01d0030f09150f801500b0106040742282810614421000101c150303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 370788453 1250 370787203 370787227
    0x1302240c070e04170906032a0418050603030f0a08250f03051609030f0614010b070309050f030c190e15010216080c060706021207020f10090f0206030903 67
    0x8039540c07102c804420440100300500589203510780f40412403504007031410a6131800030b0b495100040904485181207001c6150124200c0804071041c44800c01843c0d6958a82d105281217903e62100401d85504100024406083c04020348150380710440b03406050051100e0290f680302001031400d20385500030703107807040d50740d294482a001c4032440d40c990070810512010024240c0d9030080071141d608130035008048900f03034050352550440307800078071251042e00f013481d00b40080e0020140c90800200c80f400003140041a5400801e0b08a01c00d84440b5440c559600912025495a5a15035890f0704000f1590019040c0b11515400e621169895910700303a0712201e440344411010b4540c1a00c6105101c42c1c64203550301000b40c400740d0445003000c40d104c5454102c03d01c1d0b031661012200c5004500c00300c1c4500402c60582c0550300342c0900320304100040d00e000320b070003903682ca9072064440051052000394180628180700b072200d01a0416003032a4048016000e01a02c0c0e0310207003865406120800034a00054 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 370789703 1250 370788453 370788463
    0x60904090c0608040b09010c021c0e0d03120b0f0a0306151203030906050c1303060f09051b0103051f0b0a05071a0105101404050904060e0d03020703081302240c 70
    0x21079500c40c06618113090500d407100d500001e02c03140f4246c2c9444070196208d5000208034100b80390300e4419003010086107200311201c4524200d0590024001454001055003000c000d42c1c00d1b00c0e40303c904002e0001550100031154001c0003125810160130b00041c00400c0075500401000c2c02d05100f61002d195031a00f114036204143e040c01d4001a544041090400a16028040c1c2050518101c4c030704040b010380800d4080e40c2e2074480280a65556001e0404452641c0c0102186035048010b40724040c003050b0b000540340522140183c002803400d80050165a005902d03203a0740c00821800554403801d1014903840c0398020159201409400e000143c005515a806101c80b084c4045010410b54036203001d00ca01c2c0d9141c40944418801c001280703240d240080b0042d01c4c1100c40858030007c80e41c840d4100500140816408462103000b5060050700c030300e4068009241c1248070340c0e2082e42d20b42c1c41514101c000080a80001c0d03008011500d0850101d5001c4000c0301d0401109280e94941040c0030002ca00d41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 370790953 1250 370789703 370789709
    0xb09040b0d050618120703050a030c09080304030803010914010617040f020d12031103090316020a1508071d060301061214070903050105090c1809031c05011502070302030c060904090c 80
    0xa04c22003910061071900b8000600030000f840700840c00c1441c01d5802404074000c2d2901d103c00c150343c801c40b0f00081403103103884800601c9580103a941d565203d003002ca4040c1e009004085201d4282511014141e0505c1d48050407203005e0f03500d0024040350004c051081400180c0305403a0150740404440250369608042d009007481003440c540a41c0c2c407180090b082d1041042e24501410003407041084100020049850380b0005c035800303091814043c03001400b00052500312940c02c240740c080f510125070f0040e10300c6000f20f41a07194064041d100c82703c040c075001d90891901d6001281480100403941c01498014038807400104042201039000c1d41021700c3d09030807903d03500005c1c00808200140700d400e114003074005803008040c003402c10000010503007494044007810510a0500005a980c010900c181e03035500203c10310000c0425600d20030000688400c0c042d42c40d001003181403c6072100d0001410800710303a405005009070118000401140350002c610140d0050388805070180040e520031180405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 370792203 1250 370790953 370790971
    0x10612060c0206370213170c10080a1b0504050411031501080408130e04020120120c0c040603050d09080a03020303040b0601090333060b09040b0d0506 66
    0x14051040c00c10000352030240d0040400e64210b007050103010300518405814920800e01103000c10003a040f410f4207021400103515410ba413020851070701d100100c5a0800c00c8482c900341e01c48141c4041116162941c807442c000650007504c504100c03581500071250182d00c050030307040008800030010b50040030310080540c03000000c0c90000302441645024441d0302c80c4c040720a000141107103041050b00c0d18450110381258107020940740010204100c540840304503480003180000c402c0e0742d07110800c44450090741c00724080b840580241c95004000810000c00200e104010400061040400d0300540e0001d02e072014140151700d44004152190302032500214410070040c5614a0b100724020100c283c2c540081c940c68000c1e40411000c242d0001c25a41c2058100c2000e880b0b54a4020050700d1071226640000e114200208110007080030f007100c100d40e118801912a0003924480c11440d044540d036000359054800184292a401c2c2401d6005550014014200002c0c40501f52503951521030100c985240c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 370793453 1250 370792203 370792229
    0x303130c24080a060503102d0c020105010e0c07030804030e03012a03060305070911120405010c02060a02091c06151215090b0f043216050604030201110c030106 70
    0x944542e0203544254000c00d007100c100001ea05000000e925840840700010400340c48411088c241040380b0b0031030030410714003148102d9065907124058041c05a000300c150140d4038010000031980032940056100700702c100409440c044190b030b400c1d2056580a0401d40400c00c64040301c0050307072024400c0700504925003611000540820042c0c0c00340c1c03461150201c042604005042002690004901c0f05880000001042074132036000000041c0c001d03120b68842c1800750100340003e1000651140c001404c0b203074299451aa1380c61390410580c81040b80381c40d0010300c1c58510849208140c034140c0601072040300003251054a640d00480848007036007140602e5202d0300003043c20031242c80608480c80b40024014080c082043d2034505550038021300c40745141c0c0740140010208413441010410041c204a003a00c941c1070341030380008100c49080707030300c540c28803c08041c00c1304480380000c2c180c110782008100d40e1a090560f0300455050881c3d180d090804c0c401c504640440356428012000a031078542d02c141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 370794703 1250 370793453 370793519
    0x2040f0917120603070806010b0307030227100e03071710020c01060612060806070f030917030a0b1c060c0c0f030806040c05090307051e0301020f0903060c0c0303130c 73
    0x191242d0015020341d1003030340b204404110111000c1042d9046804e18401c66443e0313598004281d02a1090b0031042c500003400c0410030109203c51200c02c0c014070030903202071202100300002960080303c692101645a48403003001c0205400720640c0001065045040d149036400c840360446c1603801c107000e00d10f20359444071810f10559a0099102120914011051021a02d009203081d101c070801343c06841000640800303400100c3c000e0300904080c503445218206040300d00e1541046640050310800041402c1c005000800c2c504482c03034114102000240310080405035a540c401400100584404e00541d03c0791480030800d00703000321100c2402602c0e04000ca1509808000403104e50f00d140d5001d000007030004080701c1d10002031000c1511000d5407620148900c00c200d480300000c0000c03105a1641c00060f000b1a026001d10242c444154203408840050b2241d014905071400b51000088482d801400003030f8052010407400380156003e070542e40042622940d603040318040c075820303681d4510b803c0c4800e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 370795953 1250 370794703 370794727
    0x20702151e031501030504030e030307050610050102070807090b0d08030708150a14150f0f070c08072d09090b190c0c060e071e080c01020a0206040302040f0917 70
    0x2101c1105541900303500d0b614014940e007044010640c5101d0402d50342c2c0000504050003548804503540c4001e040700c0e19103030189403403507550100b21141250072210140c001815400000d4960545200101800915041a05810082548010301350380020325829510115507070000441c0540700c5503441c0301d1546002a07660307040440308014540102d2101d0420008060b00080e088030154040744c1300321117611140c01c142d1842c0142c0d10030000b03105000130318040c040944802040d5681c4150b080100d00c1d50344013505500c469551180140c01c6980103500320095030000701540381d01c840c10f8081800291100307540d4044891600049030740498800602c07040c3c10001703501864001000e24103020314a5540310040c45032921b000020070303d03502ca10020004140501c4604050040c0f98000d0442144084900b82c1e800044d2003060036502516541c2c0c0d92652001c44c442c00c10315000b606c1ca504c0c043ca90b80c2484000c3c0000e0074560280d0380e48a142ca00001e0703984070300144c242d640c00000c40d00d840c00c102403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 370797203 1250 370795953 370795987
    0xf0d15060f090515030a09021206090a0c35071d15151902010603020d080a0f0527030a02090a1a0f15130b070f0c060c15050a02070215 59
    0x1143c0e1140310907800300c2c0060720313101c812650300c00b400200201300029030344007142c9e503c400c01000f01e01d28024201000742060000408400c000d00541c8407204003035540301201760007881d03c4203540c8044c03070040c0126100d040d02e1f2007048800c036140003103540e4250ba07250164465265031600d100140030402c2404140d0301d0b5804c00c09a4540c0854950300c00502100b0246040d100d0300312921240c00d0702c0c140701480301d03000794070110007107401820305007010f0325626025207503034400c42c85600032846411812400c0d030f204005850b009038003202c5550411694500c220f05030007030f4081007903041c407880c2a03603c01610b031259603a004001403040480c1c0f001c4211403501070380c48001701480c0100140704200d4015640d0f4600c8254011403103d034035580c0e0040e610440140007441c0c10802c004c0c1c90000e00d0301c00300050040d01c42c0c98540114200c072100c1d610344e075084465800444000c0e101c0c0d42c0d030810b1280903035a15400309400440c40340e4014901510b42d804190404204640c1c00540a004243c2d40740344c0540e250 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 370798453 1250 370797203 370797209
    0x1201090b01030c0e0907260609181906091b080c06120406050903090d0b06030601060c050d080703060f0603021c05011a09010507020d0809030f0309060f0d15060f09 72
    0x1c0070f100084840300c00a10303011154001c5485441c201c030101e03160fa40520303008082403c9019143c40c021014000658002d10107581580c065100080010040580d075010015240c45001c0a0044152000d4010400707502d101c805031210360f0f84040170400104030250741c1712402c1c1081180d42d40140f070858942e0604200c1c030105801030400b0080e45410111805007580d21640c400300c0001d00e501c408082078650b005601c00180c209103440d040c01d00b440b2086101c0d0b0702c03c0b40c0c1142110000ea032180e078201d420900031751005065910a0010a0406001d060704c10390291003840c00040507540c4194441ca0400640c0c400030100394005000c0302c0e0001104094854101c0401041c442c5500d810b183c0910403d010107919009540030804000ca68426422510526002440c50302003204d542480b000c00d80c003020060b40b191142c00c88880c138440d004010b0343c0702c1441c004c20140c20403a803541d24110703a610040488002d980e41da40c00c100c00004441c0c021000d0891607030754964170381e10350201401440c6550 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 370799703 1250 370798453 370798457
    0x1204110924040e0703020306070504170c011205090c0901120302011b081b0c010618050a05010302011d010e0d0308010314070317090105130801020c1b030d030b151201090b01 76
    0x1000046a521101c55180c1a40410756000540704151684141002c1e40e030740000b98140581c5040c8800c555120340a0402d070742c6812450321070f030b64800c03041607030740d2a80b801c48602040106a0103078841c1981e60090764410500000e0b90510303020310300000c040c0d100136000004282004221401410303824407407090340058080502003448103580b0050310341d400c000c080c0001010103482d019039502001c3c5c180c03010031514030001e101158460440c0310310302070175130701c02c215080c034141c00520207100900505040300d0701a141c64105200c05040b2990140c48416240d0502441104001c41c0352100360300036401134007983d52150b540d41503117018501460442060305d55907000e00000d101141a0301e010b182e00702c418144030b03951782c80e0f80d40c0141c40300c1c000e00b506003001411444000a102c50107400418600541c0c0099035500d400c02050f0616103840108000e805030f11605014031468040d60080e0325043c4002d00000305200b005104107400d9120708003d070b1104004500401c0040214000c0000d058024 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 370800953 1250 370799703 370799731
    0x30a061b0306050307120c09050c04060e0d12050c07050904080d051003030f030213150f02070f0303090e0903040e07020c0a1a1806090402160c05060c100f0212041109 73
    0x110000940e517995a003d074050746c85550501c01c0400145040c604000c200c6030105211514258100498940291095202090b158940c10340c051070020400400c0750760151000c5008005141d0803103458002c140b160038070303100305e41c0089859035230002143e06c1940300d000d00d41c0c0d44e03035600300004d02640d0002d04100021044d0030401d000094200b6000c481c3c5a03482e15006071201008450318020000710340c0555941103101005090166008181c44101846a02183c081d25912070010145e01001d100c050005034073b560041c0724002c02c0150894102c0c0d144030880e401d0a8440842000c001c40a07a212009030717000700c20100752801c04401e0070340100b0080c2502240e85403403404449091040244107102403094030180505d5541d410259030508034040c2c030464503170100003210b0032491052682600d1501d80b0b1840000c7c540b511000322020844120040d20101c2e00c889501000b17020706c4400c9100b003a030240401144160f00040c0c05102d0b500843d2a400c0052102d014800c5031070000c1c01c5010b0200382 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 370802203 1250 370800953 370800959
    0x20c1e1516030302031e07020309010305010f0b040524040b1b01091e02040621060f0b010507081c150512010504050304271406011101020c0c1e030a061b0306 69
    0xe01c02052800c07a03054100543c0e650f40c0c41783c4d40481441415191750302941d21100748145240d0010182500c02c1c002c3c4c804000a980b1205404440e402c0d030303ca0700e42c00c034904101c01d01060a0100080d03485aa40c41440000e000c60116000101d400c181c00540140e4408138040048042000e00440c51b0307184000200300c242140d483c2c44110282da0350402c41c1d600c101228140854403a41d0100004018503044220900225a0813001201984405a075020308002400c00080c00c1c902c11151283e10507103030607181c00d809a8484007940c000c00203490a000c40450282200038550050103900c5170400f5540f601c450902003003051500d502601c24005a1410301004000b5400204640980d03007008240160207888101c0c200b000102001820041c42c1003502c100e1800c00345060260041034241c980b00244d015094005080740500a24000641d029099019650411141c101800c0500ea0100c85403414480c0c08030f03150a0110742c00700e403180e0382d580110002d000d503069801095040e5107000e000081c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 370803453 1250 370802203 370802227
    0xf050303031506070b0106021b030610120314030c04030b090d230c01020c0106051017040b07030207050312012c0c0d02090a03030207180203010b0a0807020c1e15 71
    0x401e06905444080c4980b02150f580005580c82070740e00000c851000d45e15003400948075662469540005440032980012600c0d001c14098441c0748540d0080c860103143c030840010321228103405405010a041007038070a5440000154032840400b030341c0c26a81c41c60751800d0b4540741402050341a0f0340c0c206029400756180c4c40b4a01c10a02c00403c00702c0c3c24060300c00b885090381ca1140c820310074215840011080711451041d0801d10484008962000b6001c21040c42549c01c62040100c4940005108000900264074030a13025001340c41c80c42c1c014140318143c1d41e518070b950303c200700403108420040010401d4000840b4411541828155014641003065042609440020300810300c60440400c85541c584402c0d07040d14080b4500030400e01085540381070181d101e21941c010348114400f0100c0c18082d90000e402103038120348048200f02d107060600c050484203010007030b221100318000c11448112aa4504c0390a0717051131142e01282140c19011000c01104100300c030401103400e0401e01034510070310 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 370804703 1250 370803453 370803457
    0x705090306150616030c02040b060a0f030207051903020a110a05011d0f04090f0c05010f050306010f020f0607030f0b030a0507150509210c030109050c0f041401120c0f050303 76
    0x2404902c03072900074204103000259030340a446200c0164503103114880e0180f40d4031040340c0351401c0c029101004000c440e2414002c151258007000d00201c1c0010362040c0400c0e10950041c07074514014016507a006c110f0840300700d10f05e600104280c005921104004041c404c0c04603d6601c00001140e4400c02a40340c4000a8004800d4012040000c0000051011661150301c11030301d40d0ba00080c010017515850307107041c803201700c501081582c00720108003003c20154040c24000c0307c6c001341900da2904640c0c480340115a6603001c0300d10001103000781441600720b640208030550080b0003a131000300d6003030412510b800c101c48ac3d03000054030950001004002182002c0381d01425108103c7c050484110b0001c0140d4103031040e00e03042500400c2595144514502e85044a0950603100c01a1900070020508140c243c2d14900740180140c0c001d401113090502d411901411340e02005480840c07003016204107002000c4003680400c0304500d03c2c4030500100308d0070110800240214440e902101400c040c04130396a8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 370805953 1250 370804703 370804711
    0xd030501030c1205190524011809020d120302042108040e1b130f1410050c1006081c11060114010509090a0b131424090411090705090306 60
    0x80303180f1020503010b002040c4050941c240b05e80031202c031400180d1170103550311031807111200d16540c89691a00448002c0c001140e040710800c090700c0144201e40092040140f080b91000c81c1d0020152001d20001001e00e080c42480c1c8546450040e1a00d2404a07409600d5a8161080c58070b11464107a0100207003518082d1005d4910710700c501d01c015610760035040342003d82c0780e0406a01d040c0100c0c0c10701c42c58100c2204581a5596401d0392054580e4130740080250300280c0c4616580050360107018640144644041c00601d035900080741c8103980c42e00d00746011180981c208207500d07048241001c200b00040742a031102c40e40d02d07241c681c0707440c8070311032800742c8a11042c01462041e6249001c460a168032900645025000080450302c0c103040202e40301c001000117a8940d80200190307070502c00502503d100c0e241450154040382921a41d824042c0d041c000340c0b1410804010b180b840e00c030303040307a00da148c41c05120303a1007040d1280b000029041000352400004120304100304040104215503100481e01c1504 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 370807203 1250 370805953 370805969
    0xf061508031e0309010914010e010f0c020a1407050a14270106030b0a0e070f08180309060306120a0b04110603061813050d0309020109050f0603130510090b06030d030501030c 76
    0x1213444007110a03025000c0e580015021018010703103001c20a6040d400481e120183d100208440000000c001050720011110500907070082e607640300100c0c003203003200710007885014280e0342c210b1786030000103200c0195600003a11444007516018154106024295204100e0b403913007010550000c1d402608907101401031008050303d034042483c0c0b03a00c607070001201421000c46d10148131302e0480b5005000c4049038507250300280710000806c07095500c1020000079500c0c400043c501c0c0c00d0401081c00030b550f0001c2c1440d908182c0301d003034100c0c80320020f10003100c44c41d100380b81c03600322400d0909000070791440c135a0440b071180004000740507965403665400c0f402c0300154080d40e9a07641d10a0f1800c4522503000380c000e4564003481c40d11a6502d0b51540c072072030429100b41c0f5080d07801610fa0007407002c099121040b507600580200302180307131400304040c05c5030f40c64450012140802009010101918200302c1c00300c4800c07a864090000502c3c080c0162000a1400e1401b00181d614684030029048028461199 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 370808453 1250 370807203 370807207
    0x6270e012108030f09060f0903041e0b070c032901060c2916090308160f14070303030b0303090f0f06040305061608010f0e041e0f061508031e 62
    0x2000e41003800300c410260080b050703640b240b80041a910f40742d0012640c600040c02070600003003686038880002405900403200031410103040118040c02e4007402c03a100c44c14010b43c4140000d8107210a401000054030a140008000d0315520b440c100345a1081c2c0404203024043e25030b03600781501460018111065843d00039518140c1d070408910090306040c6079166007140c0c20800c9059a00584034070b016050008006002e02104142100c0d201070900000700070f0201000076800d0420313400820b10001e8000e4486124034089940c4816202d01c500c060200300d9008030908000b819003500c1b44484441056020b5440c00e00c0c41c80001e81007488011104d4072030541900d0400303c2c2e07210b08003641c010715401002c43d8036a040c1869060b42c4803500c500042c0018041c0ca0002c51180403000040080b02d000850442c083c0e20382d40d0390240384c2c03540d000075000315803d0110400081461134013511642801010000b43d012030b42032124030514000d0708821184e0340208010340000300e140c4090343c092038689155903 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 370809703 1250 370808453 370808489
    0xc1801050708091e09011d01030609030516030e03010515010516060f0204030c090506060705150c19111b0117060409050102120907060f0509040e0f0706270e01 70
    0xc9014000c0c40d41d5180c211034601340b0f500342264901c1c01ea01c0c1d00d0104891070b15482c1ea840c044403034009203600c1c41d10056107074030f40100b0008010303420141c40603109050650030708011201e01c4612400e800e00a40000c0d08a409400341410280302d80f68002c00c4020014a0750200703900042d204e442042401444000042e9006040c888183d1105041c401041c0303042d5a41c4c0c3c0c0c3e0303080c42c00e00c0a9041c00791164403460000480d1f0305150400072201031550003805810002c3c422380b42007078a2080207007040c420078020010b8a80190040051489a81031900c441440702c44000d0b5040c070300003114407481c6903440d103018107070030680c5c00502d40c0100004400100c5600c3c2e46040114010b08034a0721700501d10746c00411014404055003100621034411401164502541e807901140d4008541c115400454420002c0c07811034240394100c40c100c80024011aa0800d40500085140c004154232000014034400c40340e29400724804641a003a14801c00c0344030301503082580700409010184290340704042500410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 370810953 1250 370809703 370809713
    0x80a08090c0613061205150915030601121b0e0a020a030905030a0306051212030c07060b0d080c010c08090705010309052a09070c0f02060901230d050c18010507 70
    0x141c1c0c80040c100d00d0300d50041c0c2d010050080103034082c02010510300c0300620407000c1c45102e482c2c4103001c01090444401800344c01c0c4540110083c06c5400386008891a11a8545040003803d0080c4003070708000400310300901306000d05087c031002400640300810010080072040c02107190300851861300040e070385c42c40c1c810250020212500000d0090002180c0b408005030580c0c040c1c42200d01c1690441815072141c040749840f01000a1040c410201c1480425000020000030f86a440d1103420001045903000000501312651044126108040055400c0c030000302030050226486403414403c43d2030521002d521f0311103c8a0040703504140d9100303500c605019003007014281e84035040704100b00580403920501e0000c491081c01500035800e000214181034452445428519040600200e00328001d5080080a62040c0f0400c4c0c108100e038142c0100406013034012021221186082c5a90b40c0c805910800c00d442d00103100f140c0c209400d02290a0032004581c811140701400d18160f80d56800170314007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 370812203 1250 370810953 370810963
    0x708011e0302040e0102040504050c12041e0203010515100e0a030f0314030f0103060614030d031d0f0c100215161b0f030e030712140708030a05040e13080a0809 70
    0x102943c89410303c2450781e02d05030306500030010b581d42910103001076620158482140e10451981e0701c039000f500000100801e071051803220440f00312103220209581c5540010f401e6440644c2d483d07a4100903840303100c03003a00e0100c0c1c1c46641a0111f041c0410503000c80000580d01034050700c40a0b11a107084001c0c841094072841c2d03841e9800381c454600644a05003452364007072540090000700d95452401d6030104804100300c80c2080c400100800034010001d071004100c01420f03014a00d01c0e0303184c4c1c1c081039a485000c002e001212540f8040401003140000070f00800291900c1824880e0554111030115283c43d20b03000e007019032010f00c850800c82054152101100e542c80729180c480310031100380042408008a0f4101c880710036000b540c510300c81c414100c0405445480c0da01c208080b00c03071111111000140c004400c03510014204c82960700700f03a582c0c0d0955095500000810001a00015040c4800080100d00c0c170f401a0303e01c0640c0c3c0440e940340da01c1444e944202d10100c0d0520907002c0010314103000401c9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 370813453 1250 370812203 370812209
    0x1050a1a090d2111011e0b010306081f0b06031b070807020a030305030103060e06241801030602031006050c030307030e0f0a050303180a0210050304020105040905042105030708011e 79
    0x56034241c540c0810142a0046840003070310030004044582c4e00144c07400500403500088454411800b144601100c41c40051082d0729019060584030b090000d01e10300240642c04000741106c410950780074084400c3e00031a000100400c1c821030081c410302466801d111604c6a0080b001110720355140c038542070582d158024440c0c000d40c00044442c0c003004141e0b10101a50481c0d1052105000f0752218000c2c0544a81c0101c940e541140a90b0000c81c0384094100d842100005000d041118040c80c41401e01050500c00d8100340c036015000020302c89040541d0008100616082c80c1c45c40c1440b020380410380e140d1102425000070152540040385540b0b205000c00403141c41c80400311940b2040034030704551281c2040b40e00c605040c82c0444200040c403404035074488415801040d816040405143c1601c0541000c8d20982c1007110910000c1001c80c500d102e034500950060710844400c04009040800d404c15440c01101000310620900c041c46030400201415030b0006180c200d819941000e04400d0003a540e8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 370814703 1250 370813453 370813463
    0x907180e030904021c020c100c020a030c02090c120f1f0806190b06071a0709060c0b0709230a0b0909180f12090306060603040c030314040b0d02030f01050a1a090d 71
    0x14024410f0307d00291548009850010600c200b8803249000c1c0c1c5c0300c4c0340e070510140105440c1890344c401443c0070702c289a40103524048850a007600c0c400b1001c21224200e40c810030b00c1010300b0900c106211001c402101c01e10040c00081c580d5410702000c1a205c44c1e0182016903203c040c032081212030440c60b003006001e80b002614403034603104a424143c6141c1039810342c44e2769490407100451221b6205400304c030240c0d10540c90f0980b20100c4c80d55220f0b0403031001008001001040000405e21004038492a41c900e05031100d20050381050104002480c00c195000c0c1c0440c401c20400381da82500d41c03100899001c00000c0d10411412552954182084601c07a040304940c05030740030103203042c52840041c00403000e050b021203505654008c01d1044610040e6006807841543c0301c4200006441032042c1d00d4503610407040d090625a1310360342641c450b00100301c0402125004410800e110086d007014a0052400319414a1218035080f01a4024a07139030709965058800090891401d403503694100c03d0540e07002d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 370815953 1250 370814703 370814707
    0x1b090c1c0b120312010902040f0308030405030c0607050d0609150b34060501050405070206160311030115020c040c0516030e19181a1c06050907180e030904021c02 71
    0xa5843e54041001031414812640002c10741d6120751081da001c2c0c4000384005da1407541181c071181207540004008030f0b0b191100300010211000c060000c0382c007640b42d41d1640d946420405412900341c8a00d5005030740b01c90b24015880ba240c8444202410496005001480c0d44060110010002ca008072903508500141180c03892800c0d460b400700c48280a003d0300d801c01076a40c03203004200647d038042d1030361401a84441c1c0440c000e004242d0b04a03480c071305035040c002000c40c010f0011810580003640101c501c1944448603044030f0b0340600072469400c400710f40401060b22409070150050107600f6881c1e4128941b80d1156040500503c02e4140c070250040142080030651642c4006070f2016003e074011008010b04a2113031480707580154501149020100405004410140010703010040c0020450701000d100b1000400d585214047c0220400d50252480600b4404894952000d042c0c0300c440c0c1c01d01c0d103208101d106001000b616500e440894015a43d0f40d900014035000c9034071450260146840 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 370817203 1250 370815953 370815979
    0x322141b01020f0c090103030516060912030501081606050a030f0e01020711190b0306130f0e010c05070c21140a050c010504050303030a1119021b090c1c0b 68
    0x3805005504030401d078221244070312900019525641070a0415800a400c070005000181c00354020b801e161404841d54a007030643e40c5c58000c10f4404458066a50f2246c4941d041581641409000e014142e00300c02004801040c035164084c80809114540c02c2200110740082400d1198103d0244000b2607601480703080c180c0c80401b4001d502c584401c036409101422010101d0409d42d180113603070400030014401240c50101d22441035403001f08071540c01281a1044180c1c0c1a06100e0451a1010100006484140d81000c00c1c210fa0316a0080750503c02c06100001c0003925000000041d41d450b1441d032064400341c130760b001c580d803164208000e044003d4440c0200c0c0f00b060005081c01400e02801c110741c0525220300c015500c2e0f104500400340c16400400008462003c6a00007aa440b074480a2107840d0a20710340c3c0714082e41c8030945070400141c01090241c0901c45101141d200314203c00c90751040356041103041d0b20300f80d200383c0c184200034402e4940002e10500441d072094190741006804164000b40e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 370818453 1250 370817203 370817233
    0x1a1b010608010608101a060d0e150a0f0525030f09080703081605030c09060a1206090c03060e070915020309130f0e0a080a0e0a05060a030501060212032214 68
    0x10900010b0000038500011010042d005402c940c1a429000d000b0905e414000390303019003d0700300321162700450700c501c4205080315030226001d039102d0554003000040320b115050001054441c00781100340c550316028000c82c4000300c260881840100705040c005618070b81650008003418000001801c49070021816805040e0010070b118803d024428100100e13180356282664940401d4660303160004061151440c5410b0050003880300c2096401c0070700761117403244006001c0d10402c0e04803251490311030034040c0301960540102000380c001400c24801c1c2e8501140020035076500da1040d045094010603603016500d00074001c8800340f01c0080d151401007802c504404020b44070740c6006a41051401401100503003010407150b000950207104d0710300d009c003042070455100191801c2c099111010380d03400036080c0d81c3e00c0f00407c90459280c5000c1001d40c5000006418200c2c04800d50802920400411210171900d14410448480e00d0800610400c10341c2420180d59045c2d08030703401c19220b0341101c19a009 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 370819703 1250 370818453 370818463
    0x503030d1508100c02070602070b0f0703030f060b0409061d160c0f0c060f020a051b0301271a10030210030905030304031d180612012003010e011a1b010608010608 71
    0x9080d50200d83d8070a1f550350301203075206600c0c4640e90304604180242600401008024200107019180100b500340244542c3c40855805a20080140300005001c00c1034200714010180249042d908940415118003860055008000e08402d505c00702d030889825001d000e035060f5034245401c10140600107010340341004400e81d031400740d100400e03a50700460021600c00543d002480ba4400094401c0c1c503c00e050040340b00020500c07959165480b000306600307070300364950071900b022000407201e00750590030f0900013403104c1000600c40d00a400c001c100941d11080b5807075001281d6042e208040401422041100203010855000300f00d8000001444140341c1c0c41041154000c42c4800d401c0c107031400c11000c1140310084030b10004101c1036a000052540d03e003103440100961107080000c0713016004007614886000b0501242d03c000c000101c018404d440c0040b040f2409029001d0441c50b484d04007031032401c500e015402280080704281030056072180300a4001c035008110300002032200c01d444180198490b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 370820953 1250 370819703 370819721
    0xf12040c0b030702031804230103140708072c0f07030f05150909030403141b0105040b090405060a08060a0c0305100302010c0b130b0a0209010f02070503030d150810 72
    0x265261408a041c10741c030802c070383c011000764009620349000c6402c003d00e000203160940354855941d01c0b2802c1803002a000101c0070174400e80c14080c580d030440c03814007140802c0c07e030f10301519401180c081c44203d40000d0043c06a50010048000808820012035520040d1141c86c8200751044d8040c010948552810f0074003030703403281c1c40c00c3c41901c1c10044031034101d403411164031048403480d038102c1c004e504000140300e403c14226015a4501616501c8841d84420703014041216944440c03042c070314090b169032207180403020918005161074500086d0580340e00800340d00b14850303581c440109805656012000c0001d20405007680c0841c94890221002058110341c01c0340804d040800080c2d0b0149217141000a881c0d0584403450103203040e440d818110352004010340328503004042c242000c201d600c0010352095050072400341c1d80b0207074a400101203994000080003503510060ac02e009903074020042c0c803c1144184000900c1080c11640e03a10b01a607582c0c0040940e000d00b030804004480290441d40f80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 370822203 1250 370820953 370820963
    0x60b07031d240a03020d050c07021f05190519030f060b13030f0f05061312020a05070b090604050a030c06091d13080c1b0901060e030601030f03050f1204 67
    0x90070522505110704075009100d241100d101c4803071400d441c885003001400140506240040c00c100d04000c0c10000c442083d904103100d90300101d451380071843c00030001200780903850015134000d44002c1d000780c0035024208503641090505034070005001d20800030307504e524032418400c2071513542c3c114015000303010041c0d00981c3c0c181405070108540c0011400c642400c04500808486c15155032101410400c030000202d134440c03102c0d100750010542c1008070b1802103440695841800401d4588448841165003c10007550030070351000011a00c0072035280216075404100580d17603c21400000d002c2c0c8203681019502100441020090000034000c60003550b0710f0391103514000e0f0b29070704842444520640000d8004204c180082d040c02403140100b403505109602c00b5003400c505040042c208000b001c10102160415001040c051500c170319401d0040001d4100110840080008031751074440c140130240c0241c81d507140075410544503034100c840428032104134588502a100a81ca600d18050707400740c41d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 370823453 1250 370822203 370822247
    0x403020705100e310b10030515091012060f0f0e07031214030103030e090a020315010c0c0f080307030207060521040204140726012106060b0703 63
    0x15650a1010440c28410665203c41c0c410100c500100b1036000c3c2c840348045248103590700b403c1603440307000200540001300c211021400c0e414410a20500405001c000020503080c5824003096003074150601d8500201514030b00001c0d43c5070004641503611640c40050075040c0e084600082c09800c0c0d0040412020035201480401e1045d0044425920f4100d209100d40d0050401000080c004c10084a2501d40c01d00300711000103009251076003107030800d80c010b4020aa401451046070b00e86038440540c800613244e021821400c0c40f905010302c00580c1c000385414085424042024005000c00702001000c90700441c0d000d0548865115840340c110035070880140c400e41c200400c2d101d0280041d103500e080700301d06001d48001c5001c4400c100450250060740c02c035030f485160400003e282100240b00f0802c9407100d50844c0c038a0190094a2400d60041d00b0720082100010b22000314cd4078900752074400410364082ca000c01505040b0028401e59110701000140003400720101a000710b92200300601c41c24030382c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 370824703 1250 370823453 370823459
    0x12061814010624051c0b03010603080a02010c0c080f1b010c1808030a0210180b090313050a03110d08130e071119031b0507030f050606061c18120804030207 68
    0x42400600707043c48010a10602160b4900c00780fa40d51040300603502c60340821000d4407640468219051030b00140c681e10800101004242e0702401000b44040c80c0e441e2140b84203050b030302d80040c140600c2c10301c0c0808640000da4240800010b401d4181e2080821008004400584102801ca40000012051481238000c2d00083d061404010b4810f4001d50b03030040c00396440300454242c01000d034074094610482450141c040400c000e11106882020520002d69660440e5450480c40750752a07403160f0b2041520ba001440000c20401c1000c1031004161151007020301c5c0b80ca403c5403140909d6520459100740302c04006241407501c10607501079400c6441f50101c0301a000d00e0543c5555407012001540003c504503140003038402e50408a034a4109554a0403106041d5210b5080042c0395005540d02c0c0601c02601090000c24000c0300c1e00000b08440340307407a003a1588a0048030007520340c607818807941e40b03a0b030030b4810301d01044110107200d41c440109440860204005040d0000559051300103101c1c130030000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 370825953 1250 370824703 370824749
    0xf01030618050709050c21070e0303210a1404060207060c0314040f02030f03040b2127070509071d01030b0310020d0b0d0c0303080901020301120618140106 68
    0x40108142c028003c0c181050601d110040500710180a00310156400c010020101503600d200144052070564440e45905010100410300d50503900190300c0781d00104418090015070560301d01d40c200c040b40012049688003000075000304000411030304800300d8682040304200c01c40d4020b01e11144125020401c1c001600002c60445180841c0f4141c0000028042008641c803001031040c00c51000301110008502c1d0304580e815900035600210b40040007140324030241b5100b21040b02c001c4800701745100146040c00b454030640d40718013554000300c119580070341070303480d428460f98003d0721018091044a06241c0e6008140c185800e140794500c0580d404030040702e601c24010141c20f107030003c0003042c491003c441d480e0025031000d103403a02d0035035483c081c6040a8940006401600303026031004210b240c65400e0103840d81c640204040c21a074810001840b131095460b02a031041b9070800e10010b030440000300305070014110054090403240100c4041550703c1c1054001a0903a81144e00482c84d0300455112 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 370827203 1250 370825953 370825991
    0x1f03080c210301050d0213150f0503210d0f051e0a0504170a0216060c121716050c060f01050307080309030a030c2301020d05070507020a0509060402070602030f010306 73
    0xc0705400c0d102040104014a0954018141203000070181000c43c0744c800d030b080c0212007103071009540c0c4598200e070801026801e441140004c0c41c041e4042d00c00302148020382800d000c01c00780114040700000c40c182c40700001e05d0313200010b060780c603035400c024038105125540d07484102c034418103480802c070000080c003a04940c0229802154041284c04002e6514100c46509822a920880852182c903000c61101c43d46c4007a15801011291208094800d07030303040440f40e003070014081000344038000440d6891241002011036000302c01500c030130305108200c4011aa01d20880314075081c0380c0320b03200612614491610705981228002c40448140c2965240015200d000d4511690341c0b50308480104000f19004124103c0e02503c210901c503030b4151901800c0500c0c00380c0c11000f50f1141e40c0418004440390700c0d44100d039007154150428508024070741e400502200818081c00b40601202030214010751601d805484503160300c10429500c901c0c081d44041b041c0402440305035200c0d03003482000f042e00422000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 370828453 1250 370827203 370827253
    0x30e0f030d0c0605130507090e0c01020a0f030507060f1a03071203020304030b0a15060c030818061603020c07080a15020301050d170d0f09020316060c03081f03080c 72
    0x6640d450b020b80303521082c00a0200400442200d0005c0c9400d00002d0018400000030782449580001c414070500102450440030448090555001c04203800114554905060340c135949841c010365030707800c146020005820082900d900d280d0900c1c0354110351074410540c0780e40c5e0344004c0e41104e15850b901d00c3c00003200d40d00044040c01507003042205002003001d42c1201ca910080144020840b1804103105029201d126440500000d551200b80001c060344035103150340001c1858a03143c85803540a958640ba81d1014000800034001031501c500e505000360151144501d0380411f64662542ea042441d40344e00400d10b0440346038212200350340e400d5800b8800c1d40c1c1030302d0f0007500300b000760b18103070f9a00400307000c104007006102107007401541600d0300340740244240b11290321000710f1f001d001031051514214855940c031581e21200c031000c0c092503501c01207101d102d50709840c4c0284152289410100c484070824000340301c541456a0110a0000c10701c0200b203e10908812503480d60716405940310500002c031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 370829703 1250 370828453 370828457
    0x12020c030105070e150702030601030308150f01051b0f1c11012c010b030a06060e07020a2001030e06071e0504050a06030c051b0606040e030f040e10030609030e0f030d 73
    0x89410078440c20300036000007400c000c2c1c1740742c10b1500e03203640c00003403814100761320490000d003900041058516070103480b641c0c001810384590701910040e20000c0c1c828010000c102140030481048a0007d00e01080340385240c070003c009807002c800440c12541d0b103501524031020041070503400c084865800520030184040b656104d001d0a802c3d9075104003407040c003620f80d010b440c2c0d034980c40c08000c00d580600082c002107100701030000d031880c5401c144810a2100404d84019034016806160105500e40c5000c1e1580758201040b40b410310f04040180c00900315000c00140380d1250004012510ba040749100c0783c0808015603840940300c0909e01240c60340700300d01410740c011110034010008140030381c00c0085000041c1c00c09506101d40c082851804c40c04042031241250b000000f8884142050300c24003070407507038500107545000c0e000c4030290783e0392080c1c0c4140704800c010070000640300c00000d9032010103980c2c0058180040b40c0d007410000e018400c082021380c46680f010350210620328000813030303080d120b0103a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 370830953 1250 370829703 370829717
    0x1a01110a02010809030d0609050601120516031503060603050a030e0d05031e0412050109120306050f0f0a08030708070b130b070f03020c0307030809070e010506030103080a02010b060712020c03010507 87
    0x40c1d401150480d03005000326100e48014809003202e82014040c0c40064019568002003034a031141c00109229548001d0507007051410301486445816500c0911905109040205a501c0340003580c3c8144a019400681058030389500031040200c04154034040c2c81c000e541d64198038110008114142c002000020b0040d4802c001450080295044d030b00e0098034510703407590405a42c0e5152095418421000700d03000d96540200070100961001d5035030b00d0070030514003041041e041ca00400e410400482a4a20a081100700c0d91220307034419184c440500044007d682d10350303d681c40d0480307960704580c0e02102c500b0301ca04001041c0c0350b401590a003125400003507409990700c581800303542d86442c4200c21070405400704008100e01c1420001000e0491180d5140381c4945007090140303050103203d8210302d42c101000401044956a0350040d02c0c11740350404101a941e4905c600103034018500615403a0b0411b501080c07103000d1105120000b901c3e034040b6025146d84000030b1080508890301110220082030780 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 370832203 1250 370830953 370830973
    0xf0a110f120607030e0a060e0d030c020606012a120810140609040203092805010b0415060809010b13061d04031d1c0501020912070b07110f0d0302011a0111 68
    0x11135049042030070350303170000d0701c0c0300e61403589600c8280c4001c3e02d010314040e07008541423200345030b0610501040114034400341129080941c002407040c5841021202c118100720741b00c80b41c1054010003008810b60220030002440a9000b0141540c2000c854000103464904030001e00604111290f800e4103100428941c076103100d480400000b5080170704800042e01c03413985031600d03000485607400e90306801da81c1c00400400d01403521509403005124028091410100214020401101410140e8129040006180e556140c800b8010859009100e6100c0800e40e4000c40100003a4090402e03030314440704041c0f454840006c10440d000050750001c00040c10f0080c143c00444003482d1100340c0c1d4070000c049040c04160038001c100b28403600e04c800d54142e58006649101c0d8a040401031614941400140c0703911458101501118050a240034003021200d1409904030350b02e110280e9100140202034151540d070742d0034000d00801c0101c051819449031498054020340c000c01404043e606010010450584 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 370833453 1250 370832203 370832207
    0x15021203091e0a0507030503030a1a090406200f13050f220e03030405060a0518060f060105070204020c0a03080703020408100218090a0911010c0809040e0f0a110f120607 74
    0xb1a01002480350069203044400200144800b80003107004000950321707402c0034136060084592820f4200c40c8403000d80b504070314a46070380d11030980c03040c1c01207000181c03d2004110a001d0800c035500c2d16507089000a130340b0040003104006050081d0081c80d5001c0d03403548500a0010b51008040340d19480300b520702556000c02ca40c0079410000700ca4911001ca450040158814a9504180c0702120b0b01d4000c4420840f00c4c035010f01c00e007a486500941309a40e4501000e00c0f01c2d44440020b841c1c00c49041000340003034481c0c0d01407011540119800f8000710354402004507682d40300c103c084001c8000401c0e0b0740100368024800c0c0291020f0b11076030780140c0b80308900301010400940c840c182500c02e481d60500d8180711036852a00c0280305000d0408003007600d850034a0104040d072107801d2007030305105500d0021004280c00d441607807400b0500b03071800211031200280341c52030f0003484d0031294528403407454100300b0003507980c0b50a18150420744007041c204055504002006e00022200f0185600000c0040c040328 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 370834703 1250 370833453 370833493
    0x6121116022101020403060905010c050319020c070f0803071202010c0905040e07051918180b0955080307030204030c061715150706020409061502120309 67
    0x241c034040c2c18408030081c0e0b0b2241c00d90700306a101340c0719260744040c4002071050a0080031005641c48c9000b43c41c526040c0114843c803100a5546000c0960100e90003940a000f081030174090044803100c0200c00c0d540d2100076660b6484900116509007010900c40b00450050151784500e102a4840404890030442800300800342280c00759801c2c030680be00011107864201d84010040401c8a48688007414060405040604024100c401c1841c00584985059801000c00301044c0e06c46070701c0103075840c2e03030001628190203488402c401403200160280e1442c100b4031150003001d03020044005c01141c1001089008203c240c001103806180d5070b822000641030300c000c540c005505c1c100103092036201d44485c0400c3c6ea030754000d04042092440344083e0445c488004a80c4403200700c1c094580d070010075011079003420341104038448014021401d001004115010b0301c02900d4940420054107984002c1051080445004a030140c001d141004020313410700022a0700c2080c003503009040104011050420907 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 370835953 1250 370834703 370834729
    0x3030203091002010b1e092d130b0a06062d30090c210204050705161a010b0315091504090c0f05061314010302130612111602 55
    0x155070751101e00d07849994410340200c000485604441e204240c110a010369901d01501e8028045550116503103404026510208a40c0c00110a082381e516010b03d08c43c10364204e4a001090a0048410840920b246921101c100ea00d150b4510300c8282000200e05c1e99440c403002d030402c01c0140c0c0060310104030700070b0409030950298800185040c226408800f202001c11342201c508140c2c65000b1b0030180020391440b01c0181040d0007038820310f000400c4005045d6004698001d00464a0f40c00082c24140180300381d611940340501080c134030a1491600300d2040d8a01250040704940085c0080307001e40700345080c3ca206000c0c0030403040404029008004145100429498003004a5051118942c0f51801030006480c840c04540c00024102a1910030403415034005a014074424003402d66000c1440400904a642030800181c03008100c0c401200a803050300c0c81e10f40000c0e03092000091541e0b104515105440d4045420880c0b1031003044001c2043c030500e0040866140070000c480090315040c0e0104002e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 370837203 1250 370835953 370835957
    0x3181d0a0902180403030f14070507150b210607020a050709091b090b0a08030903030a0311070203010e0303070e01050301060e0105030a20180d0804060c0f0213091209030302030910 79
    0x50000300c201d110450b02c1c003284d040300081d44841c0300400c0559640074510503954140182c686a103090100200107001d0404080c0807280c8100c0c240c3e1010440e42e01200e080d0300050100d01c500401c035116000340c03020749840f20b41103114000029094502c04261003031102d40c45006880d0362450031020502a0030050010789480607041100082060b103005140001c02c0d071002e000c81e101c00c0010420402c1c7c0d5603039111380b203250002c0086281c0d81e0380200440d80c10229a08001554418031046d400f80d600a265000390950318090707250340142400030195200d08110390b1405900100d66004480ca40802e10802c000300d11400344125066002d280619400421243c1c002240040040180c1d0800003440c07014040e424001254007005134040c200b90b007078100581c0c41129000c919541d84ca600c0c0724030721803181000707c0001a04100708400c5903040d8155002415015644911040c103c0104880e9108413042c584039038003001d505002d000200308890701600610b042c00c50010600072800c041840e0a01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 370838453 1250 370837203 370837219
    0xc12091c05010f0219030b10140d0f020a03060807091416110106060e010f020105010311040203090709090602120a0b0a0e18011812021906020f040801050403181d0a0902 74
    0x81c81d60b8007031001d0030031001744c91401e190384031014001800321030500164500404428a84901c1d950700f1440030a101c1d682d52014a580300c411301100c40c02807504400c0041505d0000816000032a45a00b14034292208003040d503080700d640b1444d075400c0320315192000c0c4104a52400080f01d004a800c0d24085041060500006e0004200b81e800c0c00c403a496040a00454818901d80445507031020903140c80050390300080059504503122902480f4070384060521540e00080010b42c4020148184c03001403548140500c5640403500d810806500440802d441c0e4924942c0007400d44c4111303025402703a144000e01468503a509050b00444075140041c801034246000c54140518898240304a5a10002c0c6045c6002501424038020b2000c4c140c2c0d2812801b15401000014200110111400d5040f94000401641c404c6400c510000500440d0b12a44484d40780c0b000300b00a05030414440f0101e04094900101a1915420465038600ca01c0000c0600c8400303071000191101030907441900040e0000b003c1007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 370839703 1250 370838453 370838471
    0x3060c0903140f12120a09030509060307050a020d030605100c11100c020301230f070c0803130c050102061005090c04050a0312020114060612040303060801060801020c12091c0501 78
    0x1a00d90040300009581580c01554080e90500c03041c400740410760603141d4150314003005c1e0f0b01d01c08444070700500002c044555a41e800c000300340c010b90031240d0b2031401030400742d12860000000343c101d8001800d00c1e0098001d0040030820603129116217000d6035802041e103c0d080400c60402c44001c0100c001c01c44080d580c6000410069849100b440b110414542c1c03242c0200e00248181400d407001c038840d0440c3e01c007003130741d00102030b1051a1343c02d50300000c1c401c0c40b401d403030303544100488621508250103407840070000706000b400440310f0b0303130009201d0080000088482d50340004903600c00040ba10b007600c41111380828019440c00b0034880760080d9400d0001824aa1240001019142070354011190003c4da0741044400c143c082c001c6040180495040c10214038082010607a6442403411030007a10001e04002400c040c029401035000d8591007008001303c0c0d0b11420458003d40c8007814082241c460010b0108005d80003104440d201c0c4c402500400c410031102494090409001d82d044840f5501c54a402c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 370840953 1250 370839703 370839713
    0x20d1715040e0309130504020306061e0618010f020d080105010e01020a02040e0c121b040b04020d110a1206140103091a040c05100c02010e01081503070306200a0903060c0903 76
    0x801d144542d84005076035681c0c040010442615501c540d0b40303048504010403c00036990101d800d80c4c0c81101504d607014120710101240d541c400704105c0944e4402d07404280300814050500200726800c07400c1c1c950005200c61040166030329600320808200180c0080014401c5501c1840701282e02c4006004540c10301c1410790000d0146c8d00111255030890f84481940c184614100b100c030625154248054194090080203284408005401060060361103800e054503e44540e0f04807007840c03c0e070351002c014800310100030a43c6a44252801d50000303c21400204045160344100802c880c1c42c4032070100b4100d241070064016055601064650030026881d1034a400c0d0650460340c4914031680c0c0032003485042c0010825440d80142545041048060360100140d030001801d2044100900b80582969108001d041080b1602059503425024183d800800c22880ba000000400e03842d5980315514581c4c0b83c02e090040c0100c01c08140010917440f010030101c0e80f1a4405d8010700601e1501d510b100f9120303225 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 370842203 1250 370840953 370840961
    0x201181a0a03050711100506011205070e030105060f09180f0f24010e06010c0219120209071b1b09111b01020f041418040f0b0106020d171504 62
    0x11000c086030024064802690601c149a484421410203501c0007018482c4d0340e984a012640d02c0001550310004520aa030191800d26005071132a01c0900c482c1c0f41400006240340c0007055418000c0d800d000c040b40c1503113000f2100302c038902c0001c1d2a6540996488141120600250f505115140500c803544145100140031020415400c5401803d01003650b4107a141d429101a000083c0300811000603c00000b590079207036086842403804010004190000945044462400105904850600266101d064540c0e0385115008550a00059540c900700b580c2d0340c0c0901c2d54a1441503072904414000502c058030244154004040c51156162a002444111109e11441c0c120020012031010b003448a011000301041140384025400e10402c040310324964081c40c0184034800648401c20310031070b1603070401c0114055903402c0311500c506080c20141c8800440701010765202000750004240b003030001614a245c0078841c2e85080243c0014208484036480c06000902c00103503152100d00c0e00d03a07035400b07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 370843453 1250 370842203 370842239
    0x70b090601030c05040c08070c031806090e010503150402010c11030d050309011d07090b040b0306040f0b0f0906240d030207060e09090703030f0203120f011503051003020118 76
    0x3403845505508041081000551061344141d007008004a04140d0000d562600f1090768103109000e5400c0389030076078031601114603048091030f10070000100f944d4003494103011200a40100c3c40c0c1642c9030028076846801c0d074030010040c3c0784050007007401548681c050183d00b50013200c4001c0e00103034034000070381040c0e01940f6040006001100380100c203042803041150003c0b440e200860b0020a6031500364071043e05108607606030780e88a0b000d4401d03840d03e0300070300030070b2000809664080c0b8040c60b010203481c0c4800c10540d07401030501c000450b18149a510680190030703c0d80140031555405003140065207038078015500c0203a00c120046055114025030070010781c030a402a0280c2800c00a00a283c8ac2e40d2076a41d502c00c0c02c2d414140520b02002294000c10340b501894074441540000d1801c0c0e01d1481024009c201d0b0951910810121810b03000030141602c9019000240040e419001182940c1080c4d07440d00800700401e41c200010b601409169080e8070030700c1c110300e00780c0d60b440c040b03400d60000d441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 370844703 1250 370843453 370843471
    0x2012001020315010816081501020109150219170a05060607021003050f07030603080405210304121b0b1617070305070c05030f030f03150a1d060a140d08070b 69
    0x100e00c3c60140e40e0802c081c168081c4001d000001440b1080c1d100910301c0c0000744c2581d01c6aa0343d21040300080c0d00c00e400030002107400403600a4207420700c0800100941c40081e00080040c4208281501c040c482e80c40340190210032200344c08a80c40b2400060003c1030301801c1c3c0d95012504016880042c0c650103030304078a15080c0d840010f0a460b100150000030755008000c0802c08d89030040c2807001072020b105136410340d03106035070070300030140c0550284614031a00c0c1c40000203480046000941000c003000c1303440502d885210200341d0200c9203c01c1c1018041e00b4000c03104042c80920003a00ba101405c0c40d80030105002d1880e012003074224506800c41d0303901580c410340000300002119805d11014184200c0180030a400400c0c0d10b08070414031649034050300034903078941100040481c1014102d19002644010020031100c14030f40d4170710303034881113090704241d920050300c81d0000240507180041b0107904844804c45001407000c0410104100055008012102603c0c02e003c1c490100f9401d550252240a0700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 370845953 1250 370844703 370844731
    0x901060e0f0601030b0402040b07080f040515030915071409030a0b011706060a030f080307140a0302030901140103110d02180f060306090a110126270c060403020120010203 75
    0x120b0001010350300c650030840d010340e00412007041890708e10004c96070025002008035480e03a502d04c0805000c0d129070b40c480c03588080b004c030444407070104880003540110354910855507103a0082185402e411f80c1128a4004100001e643c140034080000060103a0f0000406880c4000c0310381d0341e10002e816082e040350901c003040f10000c104182d410440d040d04120f0856405070154030b165102800f5030f411420080005001102141e000303401500010a000c1840d45500d0b104c00b104000200290000c980c3c4e03100c60b60070040490600c2e01c01c0c100d158181d941001c0110948141f0703406220f10036041c1c030b4003260000014114103940b10051a0302a005098031200590607050100030036285c0307840503205d088160446419980040c18140004940000030b00b0700c05c0c0c0040006403249286103041a00c22102c480c0041009012800a440c0215400c0380f5115144040728808000b50766110f14101190040c608000c140090f600881311903116400c124200d0100b0080d03005070a003a6041075940700360b01221 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 370847203 1250 370845953 370845961
    0x302120304030201024b090f031e01141503101a06041d0603061014040b060705252d180207030905010327140a050705100c12080901060e0f 61
    0x4680000060a040f00003405d075100724441c10400303284a0001441c0c41076000708d0707440c00d603034409005451592034820018003100040c0d0b0001e50207420041a080002500840010156003100b0910b11541c0c00180043c91146e4074806500000e041ea524252035032040088510101e65601c0010005803084085000c4400840c600f500813070729010302154860340041e41001407080c00c82e21208100c40c401500302884499000110740144504400640c000c140010204280400061084205000080050400243d141d4104008003681c001c203404000c120401455440800ba01c81030305040f0710030706840450303035081d581c418402c114654142c095000b207440301c10316400c6291940148400c0c02c0074800ca9100050240501601030880d8100e1183c0e01d0f010001d0140c0718131944000207502e001c82e1101c007503500701541c0c0da26280c07040324070500040c820100203c1c0b0808072914441d51110150300345e4104e8840a444c500d0f0010b0005600f50340e2610009034110300030a10a000e440008603410740303410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 370848453 1250 370847203 370847287
    0x50715050d0c050f031506120c0c0c0103060b0a0315171606050405010c060e010b060418050c0a020304030f031103030c0315010201060b0327030c060117060103030212030403020102 79
    0x20b100460002807040c20710500074482c0004084030783c4503202d646500140c0442c40c2c00500d01380190040e000040c2c040104120b02004180001c00208134500105c0c0c2c0442c941e42c004500743d980c01e014641400e0002e11100d80c0c414020b8010050b07160076012400c83c42919203c03200e0714411800c0e02c07102c06a0101c48031550300d1034056034020240c2010f24245107070505010002c0c2c882190f0050003001d4a9030b45000c000e04c58820b50101c80c003110020f2100380d407540d5961007200c02d50701c028200100300f4a090082600ca801400480d29080455000303142000e1864544903c2c4081000c0250305200740d840f00d02000344c2090009510902d1950f406a8503400c1851811518000302085181960b2408005010a901d4081583d03070140d001c1190120000d40102c65514030442100340032458031021410321081840496001d042c0caa00c501c2081d0000c0020303140300c0c2d0360700c020712000c2c0c05a0402c10b4461909005e002c011588940039000141c07501c038030142c2c40c1036580342d0207400c0412102ca03140d031000403903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 370849703 1250 370848453 370848461
    0xa050c0907030507020a080d0b041a04270f02180a02040f1220040e0f0105040203330a0b030a030206040320060114121002090913050c010309050715050d 67
    0x245410819450803004c003030b507030740b0107482d01404131580815400c8100800d900312401c04c0c04060703c02c0c00300d24408200b8003010300d00388110350720a60801c07200780c0110b00c08070007038105091a40118a505003660302c88220a0003055802d0b60840b0b1446d50030102c950400c20903a0246042c80001a540c80c60f21544042114440c0c001005074661455030f400494100d1600f41941404a5441c4142ea6a10000207000f041c42608582e0b0a005113446c03076004200640c04144254026000c0d00c4460010790301d00e49400410325105d1000b03c2034a081200b038a100f110900340e02030045d590010b10800b014002a00e02075040c1021030069012400f0041003691084121400070b4041c1c000615114419a2054445105001d5113500c1540c12440542990b01c198400c491442c60f07509403288075503080b011101070b600a0403514001c083c0341020036000e0705401d07040360a290308900684081310039070004501070700c1c0e107800030354040c42080004194511000590703210034590b1740302c1580d1421082019000d50b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 370850953 1250 370849703 370849711
    0xf090106050406151d03071706100b0706020309100501151409010c02010e060f0408030c0c010203040509011e031211010b06031b030709030b070917070609170106080a050c09 76
    0x50b604145003003054944801545111490b41d003443c80d039224a9840c6036041442014a443d858403443c0b80009404819292110004504205640b8265540305020501c60460303c102034050300104000c401246c12036020b10b130486511070641d030060145405407000c0e21001c1e0001d8904402e03035062000141d800c000d1001000c02c01940c000d04202c10800080d0000e04c200b40301074103010420711840401c0d6600170840e11411a00b40443e516a078903103404070703070740d400101429115110780300c81c581082d800081030b202140c0009110780c5e2940c1c20061580005503818501c002c0780c50340301201100103412454254860b281640d644100e8500e50000f26023981c0c03000c48064060740080051000820741c001404003502000c1e00095900c5c1c0701c1c1e490846640d0381d20fa0015095070007a505109495a001c1448400c444103d0942c5940c0c50b21250950b441c0c0006108031070214210000030040d843d06020508020949da90001600c1640c4690319800c15001d4402151150098100c0500902e0011616900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 370852203 1250 370850953 370850959
    0x251211060105060919091b091a07030f1101140718030209010b03072115050103050f010e09010b06030a0b042a0804150c020604020901090c0504210b0f09010605 70
    0x581d45000c012441c0c0c4d2050303000f058010203800c02030403649080344590000030000c4c440c0400c42007d15402801c3d56035845102500011691030300005c821b0311380703854034600042d0304c0c03426880c0104c5540e040e5000440a4609818446441807035040c0040c01e00c41c009070701044034141e040500d0100c40003004451483e00030000d54042150500c09a102e0021440c107541c5603a5030990340c0c2e113503508151b0700481c04a1090040c1506450305554099194006542c0c82d080e0a28a454031a225070055083c0c2d603040b40c04070054010f032001000101c01c240407086c0c00c81c0540c000050035092030703c081000b030380c012920019082d0b100d0762070516034101032142e000202c8915101400740314955003441c1c8800300c01e098020030020b824001c54188180c85440d80c0034601c20781c0007044003243d000b0300030391504804c95046c4e12510300200001882401c40c01060b070380040c0d0741c0c2c0c1c482c50305040c03415082d0038001c09225048114405586400000c00c3d5030010b90140000c49095080e0b031500400550039a9107681110340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 370853453 1250 370852203 370852213
    0x60902040b0409200d0920030309040b010e04090303050906010603090203122a010b041116020d17030903030108071e231f0e030a08030408251211 64
    0x20020841e4030039141602d440c004081104400c084807510881000d040388031048800094404162045512661303009200c0e130309006486512640d0f100100c5440c1742a503426400c01c22090b18149000ea1288110b220141011170090641101040c00c407486a5400c45c0404e6989083c8003280300f04011040c01498249803c2c4181601680802e17203401c12444ea54840c0e00001ca00035290310a482d041c1503445c0078802070000c84e00302001c00c0c24044e1084d5405607004618110345d101c0510070f000b08072082c4c0a0311941c25126241c2c0d41e801d21642d0210944255040d6460401c0895262500d000070b5000300680d800035912541808a004d007403500340c0d40159180c51440c510311100600c003802c08000c5401e52403500740c1e2400e10200b20044411a100b071650320850b00e40310024500c80e0100520070032500365448200501d04501410764074103410402600120003440080d001602004c000e0200c2c2880d000c440102a0b440c1200c043d004035510011150700c02c0306050901803e0788004150190b040c0300340144 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 370854703 1250 370853453 370853459
    0x81009060b09010825030203011e14090d0c05011d0d1205090c040509010b03010504050102030709120503091507170a112a0a03020d060203150109180207031713050106090204 76
    0x9036110744003441c40d480c112404d14488a41307003c1c04d841038002c6d6000350007030200550420116400c0441d0704282034041c3c0c90604000d680c800c50302451403064141c1801000d408001c400141c4440d200140c0480781903403181074034111100740c004549075202e6000c2c014035000d8091000507089030790f0200410700c01440d00040003030105c0c00156103d00310005540c0019151035030700141d40500500f200003070705036007440c0910080010541c01140b007004079540e0051940d032196040d100e406440d000151065100740308090440c603103441c41c1c0390198900c5550b5031030601a039a42800017022148011030101010031070400d0240c000103105c807507280403000392030107000740c0300a41411540f8941c5400901080002402d071078aa07800354074043e640081184402012a00d010000b80d4001c0700e410203408074900c0002c8032540220840c6090b120741180e50407828a0651418009400c2400c081d0200042c0da8015200140e6507807400e4001c030340300e018940a4107040d082c51401d54880d5400980359620400c010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 370855953 1250 370854703 370854719
    0xe01060807020c010e011b050601090506040c0507060513330603050a0b06190e010518040201051b01020904051806060108090712151515030c0e10020106081009060b0901 74
    0xf0680d0807809080c0079206000100c012901c100b00c4600746110f40103609074070401d00900190090480d081888241315590f68103051100391404000c83d040030035414030034100024070381d403c541d074481d00214151140c200146c403507403003009010042405129882c884d40c0c10904102c000306400d901d1290041c407901e807441d599103079140640781001c2c0400000d0004a1060354640c5071200340c81e540b1010295035540c51741c4040e025a0403e125651082d502c1186c4001019100100e1a118640503166141400c030401c6802400391070140030400295030070801c0c9c1c11981d486125541c029048400c60641c1a110102145e00d0b2440180030907062086d00010024003132000a501000e44000e1034105154214500c0c0000302944480d8035011030504040d824413180b4031030000c0008541c2003501c601484250500c0aa0846020b52800700c00542e40c0c003025032840c02c0c0703010420708a140301d100006649a440403850b0a056041804050840c0c89000030303018010640180b84410300704540c0c0da02070354907080b65 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 370857203 1250 370855953 370855963
    0x121503080403121e031a03011407141315030509061005010318061805120408120a0509090a0b030c0303030f040f031710060809061009110f07050102040e0106080702 72
    0x100403d0382c1d000380c0001c03100e184600043c81c650040d90102c1c1013180c90001000d0041c0c1403c00d04001c1010310342074640020701c0d050042c9030100402e110005000d4460180843d402e04540c04e68801000c8200400c0e4040d400c107414820041000e0886094190f0100c0d42c02000d90740c1c00b9040310700a80c030000500c44001c1d034151042e01100c1007400c0c0002c4042584810b038851000d07e481c0a400d6601d1b00980c1c80680e0f2003000c81071603041c07286e425255420000d2645900347d00036405003503d250301c0b002d10181c110392503100034540b03003810f400c150342002e2401000829500044550007600c680f145580e681c0360800b001594902a021400395003545800380781d031160f1200003400900702004490b184424180919400800140300400314950b618000d01d01243d00e0710309100d510001a41803000403400740000c5007081c021503496940103507891400008202030100a00158103d080400800030518040c000401d602ca200d24005030700c076450f240d49030101400590100c01406282810055110b40c0820 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 370858453 1250 370857203 370857209
    0x12080a230c0a030b030a060207030f0206070c080307032403060b010302070b390c0c04110d0504080912070e01081501090e01060302060a0c1106040b040614191215030804 74
    0x5103511a41400403c0f409800c0c507803800e5426004011205080c40071640050003214041d0b00c400c0c00300c20309918126545c20381100e60900080000403c2c40005030b4030801550400c0342450041019501d042c41554103c0800c400b10038404550141001001a54050000d08400c01d0804500300703c015222202c450300d004140d074046e803c000d202001000c0183c1a12080e415804040b6003000d0b461100100c520b5004e03180d184c800f845100703180d542030302c0d00e40140594410b21a0500307040402040441e8090900030b030044605150600000c050b507110141c0340d825201e0313100c005116052a007410000d0300c2c041a0041d42d41504007090038000c6940d04034110b030442c0c065000010b000c1e0440c1900318010b02150304001d611036400180b4608895105141601c443e00070b01000e40110026802c02c407043c031030f40c0b10b0040720038400e200403c8854050502e070128003014481a41c5040254030400e07426000000074803012584001e03208011100074881c0c0c2111000b0940b50000d074504517250203801d80510300c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 370859703 1250 370858453 370858471
    0x4090914061e100803070506190203010b040303031a040e0c010305160c0213021e190903050d12061707030b090703021e03010b0a0306050a0f111902070312080a23 71
    0x1901061011060100c1c4000030801d40c805e0743c4e10741080d468429100e007001d4651418113101024641c018101a1085034105c034030614200340782a165540a60140c2010003000320300d101406190705098895004044114800d90042c0800701132020002d8100c8101801e1040d24003c0c4165450348107422400114409404030754031944604902210f9001c1c0c4660244882010b01d80303c6554102603c4201403c0042000d503514074450b01702e01c9044072811480d120241c0681c0c00381c0c5002506a001d4100c00302c05039820a0007091190711202c44106680c84004a849603034405c800400500119100213038001d000e0f84d000e808054950f0300040c1040508007071001c800740d0346e001c0e04001c6070f90035800a82c803168083e190743c5040e60b49003041c0000f0071040f20000c070b0940c2042060600400300f40f203800052100811f1050801c0400380b500c0454a1408101006600c1002d0000c0080381b1400b088070050000d03903644240351301d401d04040c01541d03d010744201c455880a614403064800f9031014036800316440f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 370860953 1250 370859703 370859761
    0x61806060a1a0705010f05040201201b032a09010f0e191b0f02280b0601090e04110114040501051c0609060807030b06090103050a0f0503070204020409091406 69
    0x600c4910b0094411030100a02179883e15141e001104203070781186e4844c500036281d145440c5141a01450041c82400f035904103508101082d01a001c40740034079452a10300175049407407090003911540181c44070380304544921111101c2d101c81504d00700203014003405400141481081c07610816016800d0098140510358881050124400040d94441c403600b0001c9119a4a009088400505140070500c0d031800180555074064500c2031000b40034424400300103010001c4203080b6240c140c2e1440c00542028100400040d0024600e45c100002038003550242c007028900c41d0313200740090b005824034200074006603400d000400c116a003140984100400f03030350400190000d041951402849a5004000d526182040c04160041d00144520075644250395202c0c1e2600e230302e02004038202091200900550148030380d00001500303949080b0051b44610112800d25100360b00050a076040f03034005a80c056038070131681082c00341d484d440603c2d90100c0e8001e40007505003241194030040c100e0301010307804a00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 370862203 1250 370860953 370860989
    0xb0d02030604091a070306060305060f01051b0706120e010b060f0304170d0f0e0105090c0d06060f0b03160e06031803070818090c0c06061e12061806060a 67
    0x4035002034032000e50101c449a84c58161240c08400e840040e0b8000e40007914010020400302e000f40f281a0061400606440b090481c03d00115101e0780a85d036a8031400001610230250810304110840c01340c000c1d41c035110700d020b201c540361808503841a000380e440f5a061a0a180d0a51a043d0480d4141140040364580e40d595504201c4699501520300d00041d00c40020b03a100c100d692584080c41c082c008640902c020040c1d0807074142a1001520140348641203103400c10a54500f0081100031a4817808010804540e00d82c1c02c6022103416620500d4088400400c0149000184c500c142090300e05091004a004032500410158000248080344c45500120141030601301007041d42e004590051040740d0b1094015244100030b0030136044c480c01514044c000c14032114500081d61002e10011008007455600c0c00108144580e034840880d0601d40042002d40503900d50300518100300c00041d000b050035080c02800f0303d84038080c01040071031a0300320005004090b42c1d1800000c0031946201081409688 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 370863309 1106 370862203 370862209
    0x14161112120403021015050108090102280219080405031c050a05031009020a020f28080f190201060f0f14120c04062702040b0d020306 59
    0x180250962107155000040d4014041e10449900b0801c0b900000e0895040040c9001d030448600030501055820100039500030420b20b00840c030305841c84e40c03c8840c004c0061030402050b00140d40c030641c0c55100300301022070b00034204a841c011814525142d802540284203060183c0181d03007585c1da96130008a0038036101903e98841900d019a80e0004885e030b40d00060004800070007140012518584d6032000d0300511256400130118000c050a44514000c40c102c0c4a442c4202c5510b11880c013960080c0041824a5001000680341e0046508019007401042c00080f410b034080b08609080550540084040b500c0e18181d00d080d00780c803044c2201c800b41c6d5500034001130049950f09000507041013074140c450003034018107880c0c54510030320015040e0b407030315803000f0101e000340d07404010142c132440b030b1400402002d540114a0140360010381c2c000c6003d01c0101c03600403030380800007506a031 = true := by decide +kernel

theorem cover : BRFrame.Cov 370683453 370863309 := by
  have h0 := BRFrame.cov_init 370683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 370683453 ≤ n) (h2 : n < 370863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
