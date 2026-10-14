-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3054
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:31:17.120505+00:00
-- url     : https://prove2.me/submissions/d7f9170c-4fd0-420d-9e51-d827f068ca89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 549100719 ≤ n < 549280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 549101969 1250 549100719 549100733
    0x18070504081204050a1a1c021308011509060b0a0c02041b02061e04080a180801061409010e0705071e0f030507021e0609010c060605030610290708030402030a 69
    0x81104818a1070b800a0188040d0a00c0f00d4004040c10605890301800d080428108880d480341c0b020030000c1040c180c0140215070855012207603440008105401c4464454070304034002d03d0b00598041e81c0c1d0020120000e03551000b400380c0f004580100014501300910402c0a44520a443e1130407640960780e1b41c00211100c419242c101600e00c102d500420042c50803c5492503984001e81c454455071120b0810000002d040104461034a00d1516080311000341002d00ca4410300c880382c05c80015542080404103503408403c0b29480840b01c111003900032642d0326038460b000001c0c00e8600380c002030390070800d001c080b83c0b2a4883c6001e401c5c0c4201960454200d6841c2d010b00d02c005000104e00050000a4400a5161100a821030404001e1560540200d9200056140d101e24040c69040c026007100d10b00501038140d010030b0080602030f0a4542c035180020604051a2841c01802c8441c0030030000e81291808184002100101c0319100a140c2040c42e1543c940c2e82ccc200070710403649031040c064450001200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 549103219 1250 549101969 549101983
    0xa0909050c0702100c08040909031803141204030b0c1b06010605070201081f140307031a100806011401032d0f0c0c050a060906061a090a060c021807050408 68
    0x44202816142e402610412240703481891807601000300c02540040400c2220f4210350481e400c25000050030760441c9426603070003528010301c110901c400700d4000184210b1940008552001d107043c3c3c1c03103c08881c00c25604a00950101800000000b00050100d0341c1c00303c01055207031940c402e5450b115441ca01d04a15282d000d0300050005200419030038110750b08024031580280d141c8003110b042600c428207064070182244602d00d40380d0b509120300c0445840c103100e59005150812000032003560060207030340c003510f01035803001c400c40b1b000c45001071408000b0800905075094011300300703880e001003130046000d030505000680c0d10442001207901040038141904007601c239503001c00300701d40000040f00c170100c483d1003807580184000c500403000000c401003081c055080e840000041c0300c00440c1801c10040005800821704106880f00700034113092110701034252103000303c40081d90141ca03548202c80309404500000d4120614181709484c001700c18500035401100e500d0101e00300f6070745058440c0f91400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 549104469 1250 549103219 549103231
    0x13050f2409030f1309060b3a0e010b15040b0d0b1504060f110304050a0e0c120405060a0c090b0a0c020d050706030911040e03160609020904140c0d0201020309060a090905 74
    0x704d6100200701c01055400386070700030006150054240400301421070f0310008044000d290285101c0b000c070411840440501085240518041018840b942d10050090441e13031a0140b290440034030359801c246120b000c407000c0e501468030880c00c04008801d5070f009028410742c156806038603c10f50000c081840c1000d0002800c2c180c0d1240408420380c48060010390100d51002c0c00c0e90001c01060110740ca40f1640b24040b075145d0207202400e556026490052401082403c40361048040188000e101d000184c4074055071a182082043c60f54400080d00c80c0e11507031049404005090040c2d884141c01a07480400d51800940081a6060706590b62407c1078555003110020940c7c0311030700e03400d0111103000080224015102088001d48821000d684e90051580c64200c40c04801d540c20100101908030b0603000d5405000c8420604040c0f400d1200c80701c0354501003006100300c54407200c06107000a80311209a03010707005540390242c03903400e0000d00c0c0e015914400c10710900660004800180d44035480c8682 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 549105719 1250 549104469 549104497
    0x160f111f0c031b080118090506010602011b0c030f0507081218070b120105120a0c03030e04180201080402010f030b0a08030703030608150604180b13050f2409030f 71
    0x740e003000107400c40b4410080510074050150403040a00d8000340010b055451141042d01041d02804110015100000008165014103c000105150150094001c00355100c03a1800d414419001c02c4420800d42000500014506500c0036955400f52000b0042c0a0103202e0b00c1c0d1804a0f09059004101d40aa070300d404c6c1c214014095464600040c00300ea0b01420f020000c0601d4043e9420344010000380c10300a21340308401a000c40e0245240402c4400303c200d61188440411681d80d08001d010b003001c14652a000390708040890361000c074001040c42440750705171200d15950312a41c00459559101c83d07070182c02e0590390041d112251f5030700314011009100805c0219a520141d1400909031126540081000c3d031181c90b0100055088480e8298008010b94002403901500300d800b9054101e0440042c12403d138410511600205080d401000503000d00111000c0c90a01f0308000d582d040c07140d503d05555a54221b0b003480910750700140c01d81211000c4100e9003001e01d001c08988a075407000004040384 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 549106969 1250 549105719 549105731
    0x60120061909050c060a0203130605071509030f080601020c041e110a020a151803030f05060609010c0b040c150804030306080d0c080309100f060905160f111f 69
    0x10301520881103003501020207060040071410343d0b605603207080495165100710f102246500e003640c0308105540c0b0028003806051b04140e40c6103000ba02680c000c041c00c0c1c80c82920f154202881305031a00030b440c0c40d181d00d80c0d42c410035a807040c5c1048600e2900a41918114010300c6003204443c3e41b0343c06098510010303000140010580b90304002d0480e8010b50303017291600420f10500000b40c0d00810f12a0030503401c60070040b150301c20406800700401c4800000764001140350001c1c8241a8554031020603480742c49810029038031020104041801140300302800220b0401c49540041c5800e03010302d1308207105810041c0c0b25038890360390f4405880f0709080d010005943c2420007003410307494000c50004002507070150a001d181e800000f0300c0c3c0c4083d800041c00f0800d000020580e0f118040001d011002d00d40c0000f044401101c03010b00b8090801885480b0a1a0030940801c11b40c206003010700200e8050b0307032070311043c40f0704c54041511016002401080540541145880c0840a91420102d6001b28020018031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 549108219 1250 549106969 549106981
    0x100f1d1801060902280e1908030a090311041b050904020702090f1f06050316020309090c180301050f16090306020c070f0611060408030910110702091f03060506012006 73
    0xf8505803420550017080c2d0401030510442d030017096501c0d0044040d50b00890312175030000c200d0f0315490303681c1c00307240c0d10b20001502c085034031741c083d078000240c81c0b01301703500450020100300f044140e60040d0034225003a40810700502e860350141d070082a50040c00362025051500341c2d0006000c50342c088591081c4200c030304042240c40c119580082c440d03240381c440400c0c10a801d0400090450100420581440d8101054a06402e0007001034030030100004180407401e161005610080b42c00c0407030340043c0c194058841c8145440c06000b29441607105c40c60500d0343cbe82d07803800500e01a80040c0c00c58824420050004400324049000405803404114010942c0d1440d040d041520103134591b0151040220140910152660100300039070000d13008000f454498031910710b29801c0240c2c808011030f0031403910081c200c031884e24402a000650003140c80c00100da42c2d40c8241d0329070b18010601d00f00304018404003480080c1299116940281d810b1501704443d50311080c0d0341b0340e8014648900d04e00c0381d00040411074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 549109469 1250 549108219 549108247
    0x50f06010e120a0c17150601031104030b090d09090209010203030621030d06050f0423072f0613050307030309030905130e2109010e030c09010e100f1d1801060902 71
    0x5c800948000100906180580080c000340b90161000d410561541040761508600e4000d43d03014581001c540c210604004803000e07a9907880240003030114400c00e1000030420464070039140e00ca0010703000b551645e99850104010442c40c50701b80e540d0201c102e0b0611040000402c040c185448000314002889401c00381004402900b600c80302d0302c140e04010140c0c00010900c00700007450a58403115542036200d8403415210241c902ca4004580d00d1780e064071040c4007001131303003031030704210802e0039941203845400002d01030400030200900981d104118101c0080c0c482c0e8001810341e8028503100305410b49031030025003a2070803018501d003130700d8581801040c03444062141c00a9801c81c98241c0c000005542c45900b514099510050705000d05020040c009490900030030305405001040c8050035a11103c2e5129003240a444030742010504200208081d0024241d21095030400b400c1c540345080114001c2400441c009c0081d0404101c1d41680c0600181c240034000140c0021130000d42c03145c8010400f14 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 549110719 1250 549109469 549109499
    0x703150506031801050c041d06060f03062e170606090d05070806041406150112092303070b0c04062f0a0b0a180c0608070c051903080901050f06010e120a0c 68
    0x36485412000030700125950b0f00d03088804070f101d0600705d4ce0b1030780d4400c00050840c02d0f0601c82212080c44070b0424007100e0301c141001c01e01502d004d80b81c070b17075820300c0d000c031181c6448400311807682e0007101c1002944054039011404002c1c541c410002c41c2e00301603c3c0c000e01400c148064030112080c08101c8014a403055003440074550007684e8040c1104240754020000f4007242c1c40e000388107182a07980340b071501405415038402d810811901203e5106258070b2007050395950242009442c40320080b00850002c86042e002c03681241c5645d950f4454000c2a180c00c0b901081503421070b8500d4890380e0070030704111842400307029112400b50311103041515140c4015419103182e000130700c64440202392600002002540d03000300f551410303d4210110750b180c200a5030190040740002c1d10382e1242c1807141a00000142d83da002d050b01ca0358036103940383c4903494410f00ba540192800320307030000c0c0b01d80011855403080554014201c001002c030062908140104d81c02c252802409440348400d0f024188502d00c01d4130740388 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 549111969 1250 549110719 549110759
    0x9041802100e130c020d080a05060d020f0103110f040305070e0106050d150332030f071b030803090313090219030903091e14010504180b21010509060703150506031801050c04 76
    0x28001c9180000001d03241580d2f004009200c1d070303149800d40210f40d129601041849038120a0305944101c1025103c030240c0040c0f104461510801c10049803103890244064126259a12840e05280c0003240582c09007052104d05c406451035030344004086551500213410011140c903000318000282006840030500b07074000c50352641d00401040c1c040350000c804846009401c040200a004620f000390355a41c1503a0b840505195004010b22401c5800030008108403d01d8000342d0340629601d4040c3c80903801140c01400007460711200150620f8020b801c02900c0071310a1a00e0120356450741c18080715000505500900380c6581c602c148009049035239002001102400c01d01e046c180b501d2010700a2002922211104a8642c205812291202d5610005502948170020780f0301070400500c600805088030000c0b10b0703100350000b0400c514080d01c42d49400d04504000340c080b96080c8030502800740d00160040004895610f4000d0300003200f1700c0f0303040c080c815110000b5070b56032526407150082e000350210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 549113219 1250 549111969 549111971
    0xa17010510020a0f140d02100c0305010b030402040f1d0a021908070612020c10140a0608061803070b100312050408150606070c03060209041802100e130c020d080a 71
    0x94400072980008850080d55400ba07140202d07151140b410044010f58142441d569104100441081c02e801154030101601708a20030404804003400c00c07030503a4428450811a82d00410104025003065009121405504030b07000c40e0441c130030708042a40d410003210400a54004200040c00c61620f0071801e801d0310004407080c01c0e05824004441e480c2d00d118800c5030207001c440200c440c45d025164040d80c42099014081d51244000d80d80c00d00050420094094444e081100c00a9003501441c4034140586107408020685a030b1800c1450032090070b10400080340f40f105001c00300014107801c414034450003c1030200c144130707403651038203105940d20303030f8061818808103106c14440900001980ca9050b60661024007103911741101080e140d125034000604500032009001c024458603800410000d40192010845d2a4040040c0080003540c190002d40c42224031841d082c0040c4070f4000200206801068021b0140c1614401000c0f42c0c8107242440140e04032454009900c2d070400c0703480b5804854200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 549114469 1250 549113219 549113239
    0x1701020405030d0509011809060303030b01052701090f082b08070e120109121d15130510030506030d0f0c02010c06020f1201082803030b150a170105 65
    0xa0300c03243ca60640c00104840802e000c02d031030303200b28040c80a030840c60074000703607268a4400c800041c1a4900041d804607040045507840c551250007207907401c01804424647c440000c0d030b44401d05a9250035150b04000c1c80d00d102107600c080d05040e00d00200300c01001480c071807a400717118001000411880b0341c090001180081e585580085620b80d00004c2460400580000c0d440083c0c0e07114801003409249600e8116400704201c5416603e582c0c00c845525400a4911268120541081041020358210a00b2101080c2c0002e01a01810005000c50340c40140940c440c000703e01441520015130001a40752024000c2d682818441102e0324501c0c0d24180718070b404400400380401349485402810860440e11180074011070341d040d00c0440f070385014040d83c1c412a421004003202e90078001c00341c3c0ea0140c24024405450f60385188028035000c030304408007403a8544c4081d4020000e14445903000341400c00c1e058611011074004145a02c01c9490b85610071038134030108460850140c105c280034980c620 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 549115719 1250 549114469 549114479
    0x30d15060c021c061404050102090316061205100909030903150207080901050703120510030209060909061b070611031905100b0a020f0114070f050f1e1207050417010204 74
    0x2c54000700f400c4041c6010401d40524600100104084a40d0001c80b0060700240b0040040640003444140380c120201c4000d001c8154034400032002c0c500c920b2010960b001d180070071103011a005240e010891090449200d640c40c00c41a09840c10100101d0000c0d840700410701c1044488074100302e440b03501c00001c5003001210b6841d102148207200302203061203401718040040500c41c0510010b5440c0c03403032003401642400d0315451a2080a03000c100d04c0b521080e800600a0f08110300b036207118580c0c0303c0041001c1e4503050034903948104070043c0c0e0180040c080001c3c0713000c00c401d40036481c4006820394116580f46802d031004410380705038880f001001da062109004c103440c0707452a90b4040d5981110080d035030700d0389c0350000e80c81c00303c0d40081d242c1c40e5420801000e400f9a061030b00319220f21925140e035039410140a5045820b07100e41ca0310340002c0c0030140251440007420500c80c4900d4503c080e03a5500d4051a50160314180104481d204c000900000d82030142c15010403403044260903c0c00290b003424100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 549116969 1250 549115719 549115729
    0x1030b0f0108011a28030501061404020c0705010e030f011401090f090b0408030604060e1005100f020703170706020d0605030f0a050304090b060f0301030f0204180b1314030d15060c02 80
    0x40c8844500c25100302c10307410b460030b107407005c0c1080c81490030010303007021942c07031800c907001e4001d42c8558086001440741000c4141000d00840d2110303103034800a070010350b00b86001904c48503107004e07e6603058841c5d042151441c41c0e0920410309841041c000300300240d031410303a40ca42524080e0b401480000e04107420417000036079503d0016005a80501030948992341e00004c0f030001c02c00d13030f4040303100c080040b01071104102440740030600340e072810303550804d00c01119007003070325145000800303040182d1102c03804202281c40c1c047c00044c40c0f1005900c581c0f9211581d01c0f40c4c400c1e60032030648150360681d10001040b0f58503003000550280f1030940d0207400088002e0301c03419164003480c0700350301220752a9001d9071900e0780ca10040301c5160120080c6d03c1e850b543c403801c15146420000704200e00403071030803a400040500030800403048581c00f00355140c003035980040040e40a000b040e0100d661000102120000c01000e01c0680b1003004e0000340020301e003445880310703c11803240e83d12000510800c0b0740310380096128 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 549118219 1250 549116969 549117011
    0x1e1207050d120e01140a05011703030f0402010c080315031c170402040209030604030f11010203040c06110a021f18050f120705090a020705060f071b0f0b01030b0f010801 74
    0x1281494a0b5050b00a9601c0d0003611032000184101d500e44604d04040d442102c00e44c1e8014462800b04005603a00e50b403041d201079808040040d101d03071007800003413000c2000c0c0d120340383d00030310600d41003a08041d41d40d10b200b526003003500c0f898040703c40021505e60310309040015a60700c8440c91141e01d01b802280b000505000b0501a0000b07094030b03c0700001d01035407203e0301107031590a0090102c80312440c007414014100d01b0390b9221680019200029246520380c14000c0d00c1c000c079000f00300300c000d4070300d8140c05070307001503441c5009201030140d50313029800b580d2030019a4003040c1c1c034019101c4942e209a100180604110454443c013600101c9040c071054864083d00c550f090410350b18442d45262819074140380c000b0a0340950344c0840d4407000c1043c1640135030040c1c88198030480c2110b0043d1203407901440c0000c01100c00900040c000306150400b91584480510011f008842000300b40b40070381c6030400c100109030800d0312512940300c144540c1007108051240180503240c020005048250f1444480d240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 549119469 1250 549118219 549118243
    0xd03090e04111e03010b090601200c0d0c08061005030303010509062d120105010e040f020604031410180302150a1404230a150c0e0d06060e15010522081e120705 70
    0x582c030ad041d2545c1030030030003510100c4000241110000c7e03000c0d00e408400782c841c6014104182c040c8402040d00c050f441c0400406541004015505580c207003824002580402041290300010003400e10401c0840b6201d800d090070750070014004000002414401c5401080d80c0d039028580c909001001030b400101d4806811036070041160031000c000d0300024030366010343d410140c00040c42c0490350307154003000184a5003280f40020103221890715406200301d01c9146c26800303005a041038054601021600d4001e40c0d100c03523504400592a134682c3c4200610b480100c4045a20312040441d611620502c2021145140588001021601ca8656800040700c0740d00345000000c0c2c1c0c80c0c40c420b140d014003070603030b49112450141c5483c0795601d0310306004010700101d10482e0b00190b20750b00840d130740030b02c0d45100151802d0107031110342ca050002c0c1420018408004200200e6201849000c143d0340030038041d210306500c1240420f01191a142d080900740002e01452070030303a9004000789000190017080304008a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 549120719 1250 549119469 549119507
    0x120d032d0b0f09010806010302011b0b1f0b0a02071701060803071101020a0f0f02120304060504140d0c030c0e09011b11011b09060207050d03090e04111e03010b090601 73
    0x101e141070118040200c801d1207030758880e03000800422061000514035048074000d0340c90481094804500032810020b07400b0181140c1034003c0001ca048070b0003683c4010710b090122105480d00e03583c08810382290098060040160040030041002002c5200361080d4000064000c01c152450029907650b82d02c18414003d0646007410305c4407400e83e00074000c1280c0d680d005100300000755190314003c10381042d80c6004038414000940c400004403070010907242a25501d4907403e01e02420021001c1e44903031502c01c140d5019660100071070000e55a034401c0e100451107a000c1000c02c1c2e0900c20fa8520310540285081c82980c50301e00340070a802c1340440052110700d028244201c00a6485810385c0c00341c0501400000b0072507030000c0c00300c0d0190340111a0300c1111016030036188000d45075002c1080c41003c90358003600048079401c080c81401a040781c1143c2141c4100504410034541202046010902c1103a4009144030b800500586040a000c1c403046680103c0e00e415407460043c0001c0c19009000486030410307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 549121969 1250 549120719 549120731
    0x100e100603150e19020408031c0e070e06150d2a0804120309080702030105180c010206100314031b0c0906100918091b0302010905090c0a081005120d032d 67
    0x201c4051341206c0180000d20241c030760311217804c0c102d982d03e2440c0c200c2221000d071400c03614403031102d0f010612030300b5a000d00c1c1004107940c60380ca040201c40040e0711350514203d0001c1080c42c58403102441070440362180440c114581002001350450600701310800c09040c006c5c1c90007008005011300c0c0c00e64044486500380000c543c0c0aa06040c000c078050b4040003034141d843c200c20712000324100178130300f02c83c1c00c800004c440d01d0f0314903600126102d20b4180c62040c80780c000c4600510000f524000c031204440c141108407030030059001080e0498403284081620390b0340124210b612281808007141d03a0040060381c0800304207025050040c003c9200d449000e1948000d5101c0000b2811140c004d60f0807540c00642d01c2d80082c1d408416a805400f045c072089001c00c0391407400040300e0610107441c1c1d01c5490210f00b03490a0200c007450640e48460005c14103854140c4280000c503542d5507407086d21600b03900b19802410079000700300001c3c0441c0c1c502e03544001000752412014218012814992030420910840440d007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 549123219 1250 549121969 549122011
    0x705030711011a0f060a080a0b03240a0c09050d02010f110a06020310090b030a06091a0703050714031009020f0904060b0703020c0114070209100e100603150e 69
    0xd03900d0101110715424442c0b0b5441400407050080702d203000841d1818075040300c0c10104030503071203802c82c80300209020200160440216520012481d107020b410360700b6100c582180540441c42d60f0030300c4404210081c0500021b50000e01c42c0344164400741c244511032a08000000c2c0340e0702c050040090400800d0590950007030301c02e1902060200d10300301160340611280c917002020350000c42c0c1c1d0602612145100143d004c5240c0140c4118a1014000e08003e501603154140540340701d0400b030307a60b060400480154000616000b40c41001c880d5800541c6043c1868018207603900d070702c030641c2001e005005010010056680324001c03140300d200016602e940400c80902136004600c8010390061030854000748a0b401d100080201902c66825620b03034204842c01540c070311218480c004020f88050061030014140b000090f9000140d10040c500a2136480b01c44580d2110201c0360840312601004003044841c0d0503002e2a60710022004204450034104408503080d00310092500388908041607800c14 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 549124469 1250 549123219 549123227
    0xf01051c02041d030702041401060f0c050a08030106030b0f0d020109231e13091703090307020316081501050312090a0906080102030402151303020111120d0605010e120607050307 78
    0x14500c0000c07404841455a50303102c00782c482e0000300b400c6c0d006034104a1000b25400c01c4961160580b481502c403901000100c60003207401001d501d20407510340c8640101113001c10b4002014500800080c1d030b01140d922280b00a20060096035400f95000e040a444444010707a0030055001c02d3b2400340d50007a0038060181c81144011815041483e000401c5052100300030b02005e034842c01424080d0b508010981c1a04071a10441d0011031340500290a07501d0001d01038880b10009541151441e01242d0401616400284c00d161304510036126000d040f120800c4510010f114000207003990b074030403050343e624000c00710381c851140c822020000308000802c851507984a0303e85130081d1110701c2d010800a5164900300b8000e40c81920140d102d00c01c2030182190446142d0212440300f8031043e0041911031541d40152031010504020320304034000c1c580d00d00628150400a41f070f1120b004000401d080d03282c0800544146440340c402400780d480d1546454100800092090f088406860075540d281d580c0c0034112 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 549125719 1250 549124469 549124481
    0x140906090d0812070807090b09040902031006150f0206041b03050a05071e0b0910020322090f0c051e1605010b040608010e07050603040206071b0e0f01051c0204 70
    0x2944111260034075030030711080e2000b5100c000d1004002c50041c0c0c486000556034994225070444c0090b480348014400786e0603440103031807160405000480d244005a00090030100b800003451030f0035688401c02c1110401c170694006a0798113509150340d0012504900035283d54004102903c3e50b1074070114040301e820440c8021008540001c00e0301e110342c81038642a91900c409205140d030a4000901da20a2540b480401e44c089491014000d4502660001442030709201411000290700040c80301c41a6520b0305444040783e02004555000301c80d0400302c1c406c0c00c4442035452040c9092418803c2c10744284c004044903a040046010317400703002c40b0101440d68603c28030160342207034031a651038502000015000000480c204030b405000c0c490300d6802c1c45003280d8400d8058906a4090310081059040c03000041d9046400a00000e00d02001900c40e01c81c5492800d410140400700d5400c20080c66400e8117003140c110103070160708409175150500103603142200c05e500f00d02e0011001c0107401190744643c811 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 549126969 1250 549125719 549125737
    0x321040e18033001121b0f1e2117040302030a030509040e0a051c020c100c0213050613020a12050109061d0f13080c060f0a0b04090201140906 62
    0x495036034844100126124024030300b4045a0aa400109054000303403c003441c0c1aa5040700100d00c856110351a21920f0244280d03018030380c4200c03e000440c440106a0a040140c007800c10f1034001a21424107041c100300307450340034101707100f080084601282103401501301180d07009890400b00c1d00507006050b000b0711440e400207505120390401201003541020181000f01d0f001c480800c100e41c050509a525900a10030042c003540000f040d9001c0c541c030341910b0041f018001d10484007240d940d60003095100600e080c0f040045440d0007034a5003185415841c80f1407002848109120b24100034008c039031140c0000051054494000c03490303081c41440742c1494862540d4042040c025940d580309004020072243c05040242d20b80990b8509a040c3c0400039140102c04000301c0349003a54428202031040b12490104643c90309041007090f150010400566024a0080714810b81e2803d103040442d084a4030040103030700580c202000c00b00540c1c0c010042104654917001d05903540d9100000060680c0b10300269 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 549128219 1250 549126969 549126973
    0x305070512030a050a06210201050a0e0a0305060f071107050105180d0b070915050405040506030307120504080705011b030c0320060604110306090106050f070c0b03060321040e18 78
    0xb00104900d154000700d001c5c804c00d030310400000303498040040545020040359654418516089001035101e00300400c3c1c3e9551510700890900b500000045080c55550b0080d20180e01c89800d024442c61607540064100c0f2a82c1082e201c0804681c1e22103407580c00c1442001d0500c64086060f9003040200741c280e03130107a20b000344001090720640c5800c00c4600310035260b51000a00240c000b08030303d04180041c04c646685d544500e030610b8688030800001d450020040d91f090301051002d900082d00c0c0511604288146032603640d20b42d400e107840a0b180c09400d0780000d04220104c178856184800005016005179050701e00940c500c4a80d060a4400801084900140e403200820b03100320904003050040c001e00d41240c0a001528403482d803407150703000c01ea03021503110400c0c1d001084007900420040691a0601000604210303407901ca101003500e460380031078480840082000741c00d19090081968001c02005030001254414044003410302841c012030f100d10840a0101c0c2082442a91588003660101c007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 549129469 1250 549128219 549128221
    0x610030504031b120801050a050f19092c071214011b023421120305060f180a0c050c030a0c020112061805071b140f010e0307030507051203 61
    0x9003c0410781c4e0703010001c1c400281013a0002c0703100d1401d0b11801048034402030014004000704400c1120a5151055041e81d1403401ca400141d404914004c0030500c0301c02c00e2904d5542e02031b101504070321000401c0c000e01540c20400e010310007084486900c2e40f516030482c140d00c04074881200280d00400b8080035a08100d845a84051440ca070f00280310050408016a82c1d030b000c5540800698a50004290088070340c2119803040c421203804046068800221015000001070b00c0d8540c00071a42140340d40f100029120710412981c0e0900003100f081140059070b00c2c6000c003480c001c03070340c07a0144003410655543d500c4100500c1c40c1882241601c0000b0104815247c4c0c40d24812005000401070000c1240070a10024440c9c0c1c0d030041c0340c400c0c0b0003207800e0117a040014940c94040400145030040000c410310010500300d60108a045001e00502031007109000e0030502d9500c0803a01d03100c1580b080c0300e44c0fa0f040010465107800040140c0d2107496160420342d445070340e0351404508003020500000d0840700c1c048 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 549130719 1250 549129469 549129473
    0x405010813020d2406080c060a080c070b010807050913031d011206090b100c030203030a0203060406030b0a0c1d011706210d18030302150a0615020309040b0301050610030504031b 78
    0x318800c0d0180c1c01c4031030805c601c6a44111aa840700138104c4090392003c804d008400400d4010040070398019480a011440c04509036685401901c0a8110416550020b14280040d08088070140d0300700c1305042001030326100c59a40141040803100c1000440c0281001038101d99001d4040308114061280c0148041c5032160784880040c40540c02092040302ca00c0300748000207001d80d807014807160709540610b196035603444189010754405040e4a8206684403000008126a916403900602c0442d40c041501c5207140070060414200348141e820440c030621001c40c0d0382c3c0c3c0007100040541c4400c103068800e5039800b40016200c000e6031007203c04001103d80003003002c541c08a80054850b560b9102c0303030380030803184950050b00602e9001c002c2c00750b0700040300c08006401c95807a0700d91203440a500841d5103038681192202030003d0602d000096070000c10440344070324044c082d42c240f00000368001c1100d03190103400a50020181d507410000d2658940100d01414070860310300001c0d005070060082c02510314 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 549131969 1250 549130719 549130763
    0x333030312090607050705060408090d0c120b010e09030706050411060a09082e09060f020c01020904050105060a140d02070c0b0702090907060509060f0d090320030405010813020d 78
    0x71202d0030b006015150000e00305500600680f10f10390b4201c1c1c01000a81d07038903640c812107a40500c8003d60f015203514103410000b40d480000704080c0150018010b5000205d1a02402d51501038100464008030401044034101c0000141e880580c0c02000c041140d8071142006040c003500003610b65005840056040030198200303008408903141312080b5013a0b0325a030114098660001039020041c2001d4480d5403680340310030303040f880080b03026010024060001e288908101d038081d40c1c1102c2107035004a60b0882e070345804d100e2540100000c2d5a440c2c980103241310000d06030b0795800c08114180d1008035054460202540c195a26075600c8200c3c02d0031192a00003100d10350300300b440202c2c8500b5140c03000031800d000c0442c00808440841c1c960344d042c5650001044010b411000044c010303a041031045213140005401002400d40c000d4a42400503040040084011703008003401218a071700070003003004282d0307001007080d9010340107114500c05003400d40b000030801c07000a08090555072000c0c100c00018259 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 549133219 1250 549131969 549131971
    0xe060d0f09320c04050c160c0f080705030a062d06260c060a140f0403050705090f0a11121602240c030403111902090703020333030312 59
    0x1800c01a01d08a4802c10b6082e500155807105a24503005034250680500305600041e0b003008001660038280500500220642e80015038140c8008402800400050031140700c810003a0021602500b111410718011175507801c0f00c0480200110ba071180c0003100d1801503c4a441043c584203807090751220181b4403034016004a006076010003582d585c541d01d13100b41503404c0314184175128018103442c0e2501c80403c80107801940ca03c03420b1021b0003140b08960004003001740301040c90303900031b0b648690a509241d45005420b800c69030159203400248064174100d440c0d6213900c44440000410700e81c0c0141074110333031401601d1400303840002440c2401600c0087d1850300d11030440d6a42110400500c101c40700c0000c00803040348000138620000820400a800700003076a1050090030842128602201228500289840d00101140c40008800d04600c2c207025030582052240c50f065055060603518650400b01009502c40219907c4240341181510b500850f20108001000e0340d480301406512150074100c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 549134469 1250 549133219 549133253
    0x308010303140405030c24040905180d0215060105192d27032306100e01090207050a06050114122b0318060207051504030e060d0f09 58
    0x41c1001d0b00c082000c0c03000d040e50110741008004004459849051160450040200000b008400400340c034080e800c0c60000c00003810010743c00900e61802490213080420b8000342402c0940110500d00b030b10540c0020001c03031055038a00c0051051302c8180c01030f03030360384502108998100c0c0400c1035011000d800901c00d0100c01280c4900400c001c10700580440204510440e545c00701e610364509112180c1107061100010a17046681d150f25901e079162106103000e24190054030041601040340100750034000290011900b81c0204001401c0c4040d110301c0400c1401580d0f101c0e07074046816030500c5020001c1c014110b402101c2000503584894115410700c0c1c0f4420228090705051900792041003000855803800b4800308811900c2c91001310005030382d5a00104040209a1181c0c0882d4107403004151401d0254801d0500603030b1004a0f04c3c0440c107060314990341e0400109154200310105c0d800010000301c0c00320403504165603075580745600009003209242e4070b01c21890310080004200c00d00380d4801e02c1c1c079 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 549135719 1250 549134469 549134477
    0x20405040c090b0109150507110303031812191209120302031006110304030305030405100c080403080106080f271204170304030c0510350117060c0306030f0a0308010303 74
    0x110341600544021410b4070a42d00706d640c28244aa010300c1c841c1000d844064401e16400e01007030481d80c0080d103513800c140c640c0306e16a441501106002e54040009a452842e10395001e41400e00d40f65561404007d030300e4003001030284035100c001c4001c02c00d03801281100d50140ca551074076510544014000c1d0001c542e010524581d100001c684c40703004210840101500038011480d16003140e504075810b800180c000c03075075807181ca4ac6000c0c0d801c410713004200401d02c1541e214031075480d060034018040c86040c2d12440c284800f40c002d00c001c548480660035880781c2a14880c01c00c0700e000b4000d4480403c55a0302d518041d010342d00e80b0b01c4814100f200104222030662030941030102e440089140c880c4103504c801411074500b164100400c1c100584525542c00c80c905285080c4080054038a01400003e2440d803443c4114000a00340480c1400c02c0e030303016042000b00840903100850036140e486030040c0100f800c5001c007000149540e0340400030038003003903a100165240c840c000d24010300724200a000440c041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 549136969 1250 549135719 549135731
    0x20a0215040f090f0209030f0a150506030c09070e040e0a140706020d03090203010204090204031b060f0c080702041d061b07030f0e01090b030907050103050a0509070302120a020405040c09 82
    0x100d003200681d000d0711260145682424030b0300c02c64000a0080d00300c2283e219800348407a01c19a501400514180d030300080240ca1310480b9841c00303409460104101d450360750714140901c0202e840024058220a505a44104654490700800e440503003c081080c0e50042c103041460360b24400100b100d220b02c43c0700d501100c0e500600e1080241d1680c4250140c0c030010f9005400e0001820b01c00d8012044050002c1c00040c50503807100b0b0102d06980c0640c0094400d00340c41c00134181c980d0705410700c000c010070a501d00301c0151003060030002c2000d00540c00242400c6000b0a0407402d558484d800650110200c0e40b03225035a428a0307a6464039000212040b42d00c10108103001b140080000084810042e030540c0c4150343d640701804141c8040400424081c100001c50030041a282195001507016032800c40c0240a202d241000041c107032a002003400748032605000500c00000000160f1900307030790341140c80c6081c4100e0108554600324040070041d5100c0d08040c144802d01440480210641384010001c1c010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 549138219 1250 549136969 549136999
    0xf150d08040b0a090b1827040b0414010609021b060c1b0c0d0f1e020303040603052502011b02070e040b04080d1a09061206011404020c030c0f010c2a02010c060c020a02 73
    0x1f403076a209031071943c0024100040001d00122240f80d442407144600d034540302c2c80c904a890071030300d070707a081402010303400503440c00c2c0810003403021440040303600010100d503d0420103001050044040070441450300300503140c2d459406001c1211840c0d00902101c0c01c0c411036080240c0404900102550f044140c8110540030105104000360610340140041d440c20b40341c10411401010010312038503010039034442301c0610015030580c0b030070758421036030002c9201000d128502846071403500800040d90301240d010002825600300707031540316402180e590060784d22030070b2030b0050384508981d00030107520380210218484400c6c0011440d0550035240ed03407642c0c1d03412040c8801d00e6800e62110300641d021000400074590b501c8450300c1c04890180c400340c1024146080640355800003143c0014a400c0114003c106400900c60700e003820342d043c0b07000c42c8281442b800c400b00f001e070000c0e4005804100c8841c07a4095901505c001c07445c065006d0810841244601c0e4003e450302e0170714104900c114111250004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 549139469 1250 549138219 549138259
    0x73b011107051f031410060c061b02070e0709120f0302010e030a0c0b01150509040e0106052d090402150d1103040602121612091403030f150d08040b0a090b18 69
    0x2c41b401c3d05c0146e01d80980c1c00d108054070300b1040c02c80d00f25802c0740c5481040b03486400986090b0603548407070300180300c105d003444041c8854200c024000b01c10001c86500c00c20080f600e403e22151050303008070408d01c0070f1520313050407805001604219203462000140d46084c0341d502c40c440c103c8007400f4041c2c0f01a141d0721403403981a1074805c01d07441c41c001402031000ca4840e00c1c09a004d03c18144400d07000140007607a0320042100e00d0444c40103202d8050403010103207844000d100c601507402c0d50848880d4100d00e41307030340050080711640c606803010031008107103000c0e0b08000d94170904980b840c2a81103600e0745002d1511034080e5005581c030020141000d0081404441a408241c5540415072101d200d0184191100d100a10400500350740440301d6881c10006884280300650003007444458250951500b102443e01074945403204500500c0060110030208844c10165015154804031880c4d8848100d20b04031190681d640045d0440381d00000d8402031804417448410040724159240c01841c6042c8221035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 549140719 1250 549139469 549139471
    0xa02160905010b0f0c160b250515071b0c050102010b04060308030c070c1a03060a0f0305030f220e190204230d05010203073b011107051f0314 62
    0x1001c0b1400340105065080d020000d0110b502501c1d00300c1d0740500d000d5055600d040041e9103c561f641c0000220140350030745440440c648500350701580381c00300a10341d4a0580d01c980421114003003900b41c40200704002d00c10f44c0240700040c50800c4056510060342000d03030360080303a441080e015600e04180550303035003464025141240d400050f45170031a82c4070380010307541e43e01024048414108404010405240d407600100030301241c070040c00e44a00d041f106010f07809955070024002880048420400124000121802840705040d02c40e05c4109103000039aa20b01884840070505a540c00c02140320400240740354071860030708a041d804008044280c9040b8400d07401018401c0c94420240c0000c0345903280c008103c40e074054500f40503c0c400c0c0e264a0b08980090f0b640c40c0c00100340130941072840000f0207003e088100c880c040c0300340c040c0d100e08401102c494080100d0307041c4460440c0d0707890700784403e015240003000090810001e00344440b10500441d41801070100103745031800e48131083c0041400c0f1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 549141969 1250 549140719 549140729
    0xf090105071e0905151306020708060604090309030b04031d0d1509020609131b030b1003110c0a060212161b020d022e032706020705030a0216090501 65
    0x480546690362030100c00110707510b0365418007008180010301ea072195441020442c251940301500ca8965941858907449142e100314115807010000b40031a0802292440d001a41207500080390398551500b80c4001c040ca920140c40760400a04200605411010581d600344024030a0b909c206520020041e1101c039190002d402000c1101c51041058851b40c001c8603981e0004040300e00702511000050141640c5110408a070b940701e4254a0a43e002c0352038001e1004490f05040c8034045510b004150700c2443e4842442c100341d1140003103045070300702400701c1d0000074050050781c01c210300b28140480a580041460411408907100150310751000c3c0e00718210035403469407014100001501d01000d210440c107016680400321944c0540145d0716102c01c03001c0c40d04c8191402d03d1500e03440341856070040b230003100a8113260070f2800c0800301070440d00042028118021045e035500400e03040101c001d00075508000c3c810b11001914007505900010104015100184840141c03502c55070308000f503540138414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 549143219 1250 549141969 549141977
    0x15031011030906010f35030c1006060309020d0206090d060c030b19080718150608150405090712030c0818030708030f0a110f0111030a1406090c0304031701030b0f09010507 75
    0x10032418102c124a030b168100d0300c00540f0301c040c0a0024a6095501010110102d135019080c1c0444040c154095800248a2f0f800c0030868080503402082e910244100001d221f07410004840f4902d40d40d060301d0ba0034036508107404010304142900c0160051a582c0c2d0928441d500f07002007100e0801d410145d103800c0e03400800140c021a807030000c001144c00041c82da001245912803403802500c1c8154800038004083c55981c0c0c03445401c2180101d0130a21142e2001c60080703081c803040003072040b07000034103004568283c40e01c00c4920b101c2d81801c8507096203042c0f0050004100041c5060704820116242422000840a8403041a901d40900d80e8030700c12208179407048101070040301c00c41030041e040c5880483c000d41c02d84001c00004002542114807071003030000c4c18070340802840319240c480c0c818001c034908a441000300c28205138001036100180201034040c042c00010000301003512652410420042d82c00c55000705503168a840e114114003110381c000c09100c0040010171905050090b24003d0500e0b860b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 549144469 1250 549143219 549143249
    0x1b0e131e0b1c06020409112803110714011d0a0209100503010c08090f070e0613140906070e0f011d061c090c09020307020615031011030906010f 63
    0x4010010348842115142c0c000d081c1000c00d54901c2e03420180c003181622400006a41e1420104010101d50070385402c0030040001740300441c07100790041c0c4082d25269010403049100d00d42d1a0084010b49461844903c1d401d9011990705d0400142c0004103242451045c02884580452444440c420950700c0084015034041214403000d410f081d890742d41c1103004c3d1006158201d40380c0021a00703680f11144030600003580b01c0104418140f05004506600c02c03180040c11049181c0484509001c1d00504182c1c450303000006000e01c4441030350710440b0b0000c00c882104619241c40d41001d40c441c941150b592010401c102240100c43c5850100d02c0f4481c8416110350503002d011084007482c1c010841e0489411003001c00c00c000d140c00c407440040098180313005010803107844510f4900c0c0318440310b03440544883c0c014418030907403580215201d6445008420300700080000900080c1c0f60080300508118501d00e0201902d80c0582a031004520031086002185e0070303a42c0e1007a103c80c0c442041d10a824003c00441d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 549145719 1250 549144469 549144521
    0x190b070204180b040b060a060f0e041808030f0a02070807030c0219080d110105010608010501080a150905010e061206071103120f0708010f0b030703090203011b0e13 72
    0x1002402445002500015400118800b180c100050602083e203249006030104400c001590001a500c14029038111048603e00040034010300c1c58601440244101c0d400c2c0c00c100d5848950004081c1d04031819443d250b8901420220030692056030002240010500021180301d90390080340c40341a84100c42c0c1e0718003215a1021194075403640320813039002d0302c00440d041070101c800720400f0281c108000075195001c40104081d1618072407103010130090f41014010040306801c150034504481080c00d0540c3c0036a80d058410b4001d1101c60382e030000c061501c03080498130380d000d41e00150590b050703103410b441c984d280d1000b00030b01126500640001c0d030b03000c030000401c041d11079420560f03500d4018045904140300c0711448a41d02100b2100b0016110201f8104403070980e003e41d40c5401456800850300c001d904101c01c80c00341d0301c030051000040c1038032200d15034119142584000d905a00300411445040f91040000303141301100c4400e07030b00c1030412003e082e1016081d4441c100c100704105030510030041d002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 549146969 1250 549145719 549145739
    0x10501120b01030221010603060504150303031808070b070305070e1f05070b04080c0c10140f041710060501020c030601180212070302030601021b01020c010804171b070519 75
    0xa080c1c041c1055024030172001001039000389103490b00c114003440040381d8148007000702114196401103103c0c6003081c090100b051144c44102d02541d030146004110380301c507181d5505500780b03444d06c01010340c0c8002554000f8000118181c0e0b010b001540d038107200d55150100b04a4a003110498a50b5010b4815019030f250100710741c44407031400c40d00d414014140141515262000241120181c2e411440043c0c400329030101401850380c100e0044a042000d2078400100800d0100303141d01000084c41c00140881d900c03009081a1401055644100c2200100c0b62031059151400d80c03e1340b042c81e504003040070071a0360000c251080484000341c01010a40c0c60012007110300c903800a10a03190395030030000080300406440041d03100d4480c5890150b640d042c50400245001c2c0c0f4011b1503826402c2c6030b6100070a51b80e000c0385c0b214030b924003481e04e011982c50b28140604059505801e85d0380d0110000b0b2058500c081682402d0f510701558420f0b200a699600144924081603191010414640c42424848601c5d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 549148219 1250 549146969 549146981
    0x6021801260712021314010c080a0f050702330c03121009090308040b060d080304080307110105071206091a12150414060a06030503030606160503210106030501050112 73
    0x92070f080b03040c0030380504400e00f282e100f1a4440703600d408400051001c810b00d43e108148401c828070300060281640c0e2690f400784d0241c403506508008880300c02004551103001a14401a0010071400c91503c411110031204013504c41c90b4071001e207003840b03048582402c0310241d401c44032818001e0b616180c52100341005100c0d0007422642030340040e040205501e20144503500003c0e201e6100d0400034103140c101008840001400e440c45100807200070f41c001a200000d5903002030f8071089054480c2c9600d0401d4440c8044558a1801586480208210580d011080c10350340c11000404200694442c3d900e1000d4401564003e40c500d02001001c00305814580080d010720b81c103420645150a44028014161620036242542c0c0c200b554003a800c0001401c1c42900d030010314245e03080152034550b940d031a03101e0000500c518468400402c4210070700a40c0e48090400301da11105407a500c1510124020401c039402000c04140154000003088090207440781c1d0381a154161645040b1001d20b03600480502a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 549149469 1250 549148219 549148231
    0xd0504090e030408010e0d080c0406020709050a0f1e0b0402030f060d0503070c080c0109083702090a0e21030a0f06050918010b0a18020f04030f0602180126 68
    0x4003c010000c1e070010284a244000c04180d4080d2500e0b0f01c203103000509429020b801c80b43c1d02d5500304001c00880d600000d43c1e078200d03142042e011650303644a981e440000c14125200b99881401c1040c03070214100a100c002f1160110003008111804526040c8022030004540b00844e042e0000702051062070281151100305200c3e070122483c0200503612808941c3c080e13400801107a020090658456800120500c090041d1200074442040c1c60500309a001c0850440b8000140e0080c8011841c1c400c400103200e00c164001d03041c000c031030800700700d40c1e0001c104422001c101e5000b0400700019441e070918010080d00300c8501c1ba01d01355180c91100c02c0042070440e059401d59503903640b00240c15111400701e42e03c00e14030640703141c41401c0140d528500392404241220300c83c4c030410400340000080c02860a2000303179003960050300c82e68110034090051180b9000500318198201010b0b0401c202500188610841c0314105800c0c01403031401920105207a06500e41c0c840741800555654901fa2004260302c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 549150719 1250 549149469 549149473
    0xc0c0904021203071b0b07150b06042c011a07120e1f030e0105100306020702040930050412080d0605281403070506030408120c030a0e0d0504090e 64
    0x2502c1d201c100d610310381c84044111185041000321501c48070082d01c162008020701600720b4645211070741d4800f10b140c0403600a80b191641c582104d107068a1342001e07940a01424500e590307904003c4c1b54000ca880a0040c06103403144603010011803c1104c0340442401a614842800e08013003195079400e1990b114480800c08001c44c00140078403c2da0713080303c07804a400394118032482e46400803a00030213681400500784038aa0410303003442100e130a04030304442102d810400040c0c982d00c1c03d10008014001991000d0103134440880d10f800e040d0b0340300c0060009084ca60811051300a85150261042c0c06544601185984042191b00118400c040102f008107801d800002d501601c2d80001070300051100744685900b4082580c401543c100d03250030201401061420300c48000024000a07500d03419801528050000440814200001e00d81a504000c0780000d010300f25103002c0280d001960411554501031609014400700000d002040c0c108500c811503558920b054186240b0002500320222914014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 549151969 1250 549150719 549150739
    0x1501090606050924070f050d0201091e03140408011527050402040e01050408030a1d0d050a14032d0411041d031b0114190f110a17010b0c0c090402 64
    0x82c011310001418224810214007a00c500341d818250b2500310428000e40640e89050702a41c0801c07000065403090002e2000c41104040580c03070204c5001540b400c40600c0000e010901040c40c00040d003080f05400069040705410681d030300c034146201070740c5400451186030103141180c04002030350400717a80140060702c042000f80b00101554219203080b1403d9881c010007001380501c1000301c1c01110a0303140c1e01c0301e0201942050a0202c2c0c0c0b07134290ba0302010f00f400300004064060501070a00042c1042d00d0001c41ca86a14242c240036043c00000a9105506060796240000c003820780d01505015070340055a220403c550b450601004100d10341e450348a0314455a00b606041d1002c00040c0b040e242004c4040c40c6901c000c8407800d0a450000d40342c504100c1ca4241080342d96441c0045901c4d074003050420201c0c40100c5000780d900181190303561240350190000c1c1c0c85080b5038111048d401981c00101040b91103070b81e145a01d00450094800307509040d00001100d03812762410610013038010340000e24a0f80d107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 549153219 1250 549151969 549152029
    0xa0f080c07120e0103180206041214120d14011401032004090902181e04020d08190905100e010e06090d0f0308070302030403360815010906060509 64
    0x10510508010000160010041804550b03040c003510443c2ca07001d00a080101013140d0008234075009074095a417a5091813140360041c492584500000c06030707010180c0300800200b1586140039072004441030100c1d401d00c0011510008001c2c0180e040340d80d81c0c40441603100c2c403040118040d10003000400d42c1d00303c99910b001c1c4901c803420020130040c84903880c0064101040d206204180181280a44070a00c13000c042140305d10202d403510319100504050103080c1c2e0303510310000e44145002c0c08081d04c03048020a6040803e0450a4002400343c60b640b600c0e0700441d82c6604100c00c2c0034041c0002c20000d0210200d031082035028861008007148010203035402c1ca01c11078040340c1d102c844410300341c0c0ca078400e00030786506268100200c5a000140c07458158614606518050094141c1080c40201c1540ca44071881c200d02c0300e0fa2034a03013007a440c000d0314a00d05035102c101c02e0380ea100e036030303858417508003c2000018890202d128003402c03951aa100c042c204462803080021b00138220724406018641ca94001c00303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 549154469 1250 549153219 549153233
    0xa12051b0d020a060e030403080304030507050106081c0e0916050703200102071203020f04030f0f1a06010216030507090e0f1212073e0303040b0402090601050a0f080c07 74
    0x4076450301e03900500100c529410540103681310382d4010300303a94000304411310200740301000302d07030740550941020b41d0f46645526241e0300400c0c1680c801001401141d40d0240c00e007032010420f046d000e034170744d5600e560002444100845640150f41c0c40382050680040249000e0060300030788030300c7d4001e0030b1110480e14106017450445600220f8011182d40c00502c02003009283d40c1d4900f450070062a00b1424101d000d1800d600622590001400c0d03040c0c00b00310081041440340900340001c0e400901c00840e030000104801d011314080e103010f0f0140c05072100140c4c1081d810201c800c2269004802095124076000c0b03090014a201d680c448090b004181080b094500c08205049241c8100c2c1402940c9988a1846a00c1208060080e00410814070810b00012005407017607500100b561168441481080b658901c062030030344a0340c4003500002c4104002d211041000d58829070094404c50660f03510080119120f124020b5160007140002144d601c400e03100d20621903000c130000a0751860440c90b501c0d10b01d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 549155719 1250 549154469 549154483
    0x21e07050d0b18160b090a08031210060f0806040504030c23010c0306080a0624030515010e0709031121010e0709060501090b03060f090c030a0e0a12051b 67
    0x2a40c80300c015000c1c010b000e42400811642c0044440192041c8448a90000e80d20504c600c01d4030380c02c00300443c450485943c0c0100f600c0003440c0b078208a079598070044042454001c01114000c40e03814032008001000f0b0300800520025007000c0e624040c055a52108020050901410540801032240220400141c0e180349010041c0c0758501c01050750500a1419804d69002c0d00700c034800c05007400d40800c0503001c000345011903664014004100d1444141c0d50056215a4000c500001c01d015400001400000704503c040c1400d0310b51014910303030f00c0e240070a103260010f030398003400607181240c00c001060101c1c0d18020039002c010302240452100c01102c50249985004d5800f0302e9540318031280c002c2d0810490b05000b403c1c2080140059854100060b140b00002e10414001040009c0000c078965616507414201c010010b0142c0e0603030404c99a903088540013144d01550325480c261983c6031301d4400240e0403609a07070081c80b411401e040b41074100c0f41c41d000401c071040f52110611124280c3d0105000c1a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 549156969 1250 549155719 549155723
    0x32523060f010515030103020409140303070c0201110a0f080304080d020f030108010516020d0e040b040219090b04030b0112050c03300c0705061c0e0601090e030901021e07050d 77
    0x140001d04016015611844040c0d100c64480c0318010300c0d40300350050603410707613044a8046074006010445070400004004200300018068000081000000c0d034001c46841d9149000f1784e03a0700507901c22040515990aa450006040c2c617001c20318101c0096030207001540d020780302d606014244070010305410242d80007c04001c440c0100400144290402442030035481100c90240028060943d01d020f52640110040b00302003118000342031560b84c64613005052a244081d0003156108002c0015009003e4426080c01c0050107040001440c0300c0c0c03d50964050700e410844640c0d46134a060b20b8141d8680000301c0440e01405459960341d00303039a0038821b026403c0002d00002d0400c01d0740c4041d00f62991010040c0c110a11018081a8030115000480ca41596010b1303600716600c003600290501c40040c04401540030b1030400d404140d0403480842c0f03042c100c03150003400f0f1141c42840e60400343c90b8043c0400250050b80b00c201000407440401d40345800145007541940e08082d1104041803a01a084c502 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 549158219 1250 549156969 549156973
    0x1050c09040b040207351c06060c08190c1b0f0b07030206150105090909030a020106061e030506040f0f0e0f0f0a080309030d020c0a02030c03032523 65
    0x1820301428507008001c1842c004541c21490190141e480401c03803512882d03260b140701000382c810000c105950104a042035179485501d615800002002000900d911010001d5141411b1001400f2805415482c100c0c581c007046050a0002e070405060080078061014401c10201030b8640001c0340039090058416403c103180c50340150709282c83d060700c03c05160b102c0881e6640410504c80413a901164544e000303104494505401d03000c420049610340500c0103110b611030108020305c5031120000004240389413041d0000d00c20b16a5410094410294011440035111091440708079003038800e5000d5070b4003042c02400002c2555009010300125841501c80003481691101c03180340c000e5080100310592102000109480038841c582c10340c48590305034005208031008408503100031000e0044c8e8100c0325a1440864848810080450b5124180e00b0140c2c001e0045000000ea60700380802100c4401202030410710441c9140c450b04400c4c441e282e1030640b40e03c009024608180000f1580c0d0444480c20080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 549159469 1250 549158219 549158227
    0x62706021905090607140a06020f12011406030a0e1002040b0a12150b1615051e01060912050109052d010e07060509010c020d03080a1a03070909020a0801050c 69
    0x903100a0401c4280707490341c01d00ca018807000c18142d941804640c0c000f6441500f170401407a01492241c81c10b001484020315113400807410030a1074004a001d0310b003034891138440103400d0743e80b00c000012040310000035070742002003080003038040321940d04800900140d4070100e544492540f85401c0807031f00107401001100c0700c0000c50742e0240da030002164110242141f4200044105800f03400c504070303514424030104203808103000d0040210703400255901504402520006072011042c00300400040701c0c140000b27847c0c0741c113854041d1b902e030420364140e600c0780d15503d51036030030b054010144503040002101c41b503480d4074020300003840c20b00c5a844841090400c407c403405802900c40b00640d49000d80e0b0849a14090403504c0700b0710005006401ca40142c1440390b034444003640100c4804125110203500321251841d01402c042d48903c02a00c41c41e8011b00410003805502d410003070700c01c8a495a603603d9440000700788103902c8684d01c079581e058070091400d440d45598a0340d19082d54003c075405603501201007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 549160719 1250 549159469 549159487
    0x30a180c06030606110606030304090507020717100e010507080402090c071a070206010515041a0904020c1b0f0a0b280804031806050d0e0708121911030706270602 71
    0x4040d0961645c00702a0101d413030a8404240c0c1d9020714454600c2c01038683c008280440d0090000301c014152500c0b000e841500c40c0030300503540c0d1000d421495903171898a410081400c07418803403107005d05231aa0303c07400240c640b9001c120700c40c040505001080d00d0100a0700340090520032041c0c1c40f4194507003a60140b45065100a418030005a2081c4e0080010310030700b050400c102003c441c1a03840703001c218401d251155004c10b40303034020700c0e01c4103400070301c00100b03034040880c0000d8075108000420290880001060207008240c0c16101030b09030000390011040c0031090554000c3c004009848580614245081c1c850300d4044403405404804a40c002d42440103165000300c10ba0608412109040b03050381c0340143c001c00502c0743d0030300080003a5170b40500c41c4c0514428000000241000c0c02141c08800001504660320740c40460700d1400d001110051200090140c81e4622281e1940380c00796003005a592034a038080d1548400c0d1052500d084100c48104c070840c1a58114202d02540e00107803111a41 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 549161969 1250 549160719 549160727
    0x609010c0f0504090c030b181b0c0c09090109020901061805010801210302010b0a1412070308030402010c050705100f08150a06030b01050706020328060803030a180c06030606 76
    0x42003800041220046920075901d820004540c1100e916400c0043d94002e420411801040605a0507510100c0d07400c42008842c0d640402d0b901a4a03184960481000030324070140440c40f41d4510101c00ea000300480e41c001d454400c19042c2c3c04001d650000c110b0002f00d900280e248d89007600404007040f9075441c0d0b0500d01440c0d0030742e400a0142800c00d03a0750355041070003a60b040741c3c50705041d42d100e4258090620400d17201f0342114082e244041c141810003600d80d501c0a001100447e000c1d8040d1091915050020384006100b0003244e0700075a1891851f10796030011160503e5440c419622071150420010b500c3d1281101f43c049a02a540c441c14525901a4024441000500401c40307131604500051b425075100000388007140d0700e60400254024920006076110f004084028182174030100801503042000c45e4858107060640021011405400c09068101c07006802403580590060000400d86012035126841460948082c0d10390318045541c2e0743c010954a800070400203403075150411200307400c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 549163219 1250 549161969 549161981
    0xf050604051507020316030203070c08031b0106030b0105042007030e151206060901140f04030c08060f040305090a05040e0f010605040903051c110703111005151306050301020a02060901 81
    0x1016685040c0b50918070310083d070300e0040041a0101c1c40b11a8040c208050003042181d4000754480705d000542c80d034900c8010b499803c98401108a482c20030440e1000010600c90349040d2507101c9101c0c2d420b64240801c0c4002000c2d8507580315040050441803440c40c0610001421810740702c1e80d19401805606018011030740c2c0500c8103400e1000051121200841502d048075070b01074001e440c4a51104e20420040390701010085009201c24000110b5440c0c030000302d401881a240590065920369603103061181e078401d4100c034060300c030424242c041000a44240001d08103000024a242c1c00542c0b07840c00201201c001d4418110f0b55480044503140c0c0300303406e005a00c01003170201c40030440360340207481c05003040c4140c040241001d03118541004814219505c5114020419203045881d0081407902604110303502c00b440c149841004802c249251140c05514451060750345c10700080c400e0340040c042c0302c201c0c031000c600358182c40d10b42c0461545c0382440901030280890307005200c0c505200380c00e2401c54072 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 549164469 1250 549163219 549163243
    0xc120309180609040f170d0b090105060c060f06040b10021005090615060d0204030c150809070612020901030609181e020f0123040b0a0e09062206030f05060405 70
    0x80700401501d40e46081c001c55000350020100c0300e00d1142468001c09090060040030601c11001c500000c1601c072079032050030104000d89943e6080d036242c000304034090050b01341e509000d0344450001500e0081c40e030026504044040c2c408540e5003d0300c40082e2050024035803000060b8003c1e60b05070203034601801516000600c08014107642d082582d010f4000c0302d1038030401070041c07600103a640c5010102da03040b90006c1d500001c0704050743e501d1f0041780c110070702c00c0c0c0b030004002141040455404600818440c08a811540301e04880d07075140b00300d4030060f4101144850506039620000208030340710340a400d03441c84515518482c44003440c90320f05804078041410003c083d0012402c4001038590311a41d031045c800c2403c004203003070300a101100748860050780c06000101c0100780020a4801c0001402c8488032644901083c04e0200040c800d483c0d0084800b00e90202c0c1403c006100c08040c402c8040719003e5040d804079041e500da454481024469010840b00c0f45d000718100424001c0c00d01c04281044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 549165719 1250 549164469 549164509
    0x30506150405160203220509040f02120c010e1c0b0f07090603021804090519050a0209061f0f0302162616021302041805010f0501020a081206030c120309 67
    0x3c04074881c020340c0ca01030700e407038030419250000740b00080040395090f4a00400004160039940c0c6018a002204980000c40490013810820300c400109200070541990001d03040e59154114000c460030001100204804103240b40c454168610208844a6803170b4840c83d140c0428841900703014800401c40700040d8080c0c400c04d44103000201501d4040c0710300032600e400489000c00d850005090035401c215400a00c02503030800000304500b0001b0104800d000180200e400d0401950b9610078003011070b08000c0c20f120440d07000d9002c81c40203806140c241c2c6000e00b05280050411104000f15001a000c20005544c1480c01c040030402076505240d411810140e01c0d0b220606095541034244034410304541c1c001d01c1079510070604a1404c100e5030644006000c00520039001642da01c4c0640001c0c8828020400400d0a000004c942c0394000a41c100c841680300844a242405030240f440c65004081c14459150090100e810040d9445400f420b13411404000a195511950400c00203681c100315000c02c015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 549166969 1250 549165719 549165751
    0xc06130311070f09050a020c07080d0305060d0b040201030c05190905030d140d09081614070503011a280b04060906020109080f0a090509150406090b0f0d0804030506150405 75
    0x8010000c1c0f10301140d1000d40089510b841d08828040a0b026034000200e051187c3c0c03070002070f6600001800300014040d9103040003d622128180280d1001c02c4038060701000e150740124006501c82d512400e102c440710304c0c295040110200308201010b1500d04407000013041582c0038401440c0611582c8280131381030601c0b03200f54ac07401e041c10199015030090000d00135500d105840c00d0010500484010f00700c034070300d055207a40c06031500c1002d1a8904120494500c20320101061a00341403090030882582e01c0c103600740c600c00313803c10451941c604002042d0b541c0310518038007814041c1c1318855006071040f11820b648483c00d002000b01140d0069000f00116030401c2900004620320398215000043c14400d6240d45228101c1c043c3c1e01e10360203a1056401010840400150b007540001070340b08120111014001a41d540203c44140c510600c1d4003544444120101c510318903000c40c2c2850141d100303080b0a414a0381e65110f080c10504110745290642d0078050b044141441c1c20b202e80c0743e11071140301d12401d0f0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 549168219 1250 549166969 549166979
    0x31515030e01090b27060f0414071430010912170a020c010213091a01081b0304051207080a091e0b0912100b01140304051b01050c0613031107 62
    0xd1400070b0900b121140088205c407130b1076078455400307000010b028022600c040c1021168107084020460342901d04034016501c03000701c00c4001c10b01104803605600025404c3d40404100300d0381e404074003800032405640000180117030920440300c0070005107031400001c05452034103008100c1503403148100c00301321240d0345e082001c0c030700100c407980c02103040c1c1401600d5141d80303042180248501c0c940d0102000720403070009000c503080d030440b00d13003a2140407480c0703890b6140e1401504e40f10710549410102c5c0742000300d4107040003c6030000e1540a1700034011202510744e40184460560b00c214400d8840340c100141d0000507541110310740000300001c4070005010304011209071740560361801403c1d85150009120301456588031080071187c80341c1c130162001341c1100c51507140100f1404a5083c0410442c00326541003220000c01d1300d10558200c8060108805034240403400b01042100341c0741803007001d00244a00f640100005032188920a010881c0486603040103003a034204a9248041f5500c15802802 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 549169469 1250 549168219 549168233
    0x10e0111030a053d0e04210e010212070512040b21010321110d03050121020a06050706090c03050606090a021603141e03010905060406050d030c03031515030e0109 71
    0xa1050b4070000c404101c00316032400981c1184c03030f5010302503059840040c04140550910a501c528032000c0840903a1404c00005036150095201c0c2c0602580107100c0181e00d960041c0024183c86215030103507840d440c16000b00031080d0308250001641c003500801d0503110000700310603030000c0c0140303114007003600d40c50350380c8801030f02c602040c001c0110181c0000c60b61426004801014499500303000355200f49907a000001c005240c24440d01c000d0955518881c541c07180c840c14040040c41c3c000d880d080b801c604140d01680c00b903110403400c4410540c2c4400f0803010401d0131400380702542c4244040c00c030fa130600c2001c1040030000944031040c110720410000c5141d842112041da450f03030385070420364050a0071003040001c0303010741c180c2c0c2c038209100051000c240305050002141600c0c0c40c100d08028a407104002c0c80101c0b0004d0088a812442000c8218080303400750185620003882441c01180c410411002e9070002911684220150010b8540400066801d80105220341180a00030808807006440d401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 549170719 1250 549169469 549169531
    0x4170f0c09060d140d170a0507090e09121603030f0606120e1903082a0304200a29090d02150d0203041109161d0102010e0111030a05 58
    0x740c824680400e1003020012840f99141031041d4410503140b0b400101039001c0c10344910503121007040038130751b00006d002249038490540500002c3e5a41700079141412213034110298081c2916185200c0d130b01d84c0d140b40c800740100504c1421140000860380c1364041c9006001d0794940a83d03001d2041c1030130300070701200f0790001000d525000f107100c007c24841c2803c05e90508148445000c411802e4003c65103000740340d000b6101c14021000d1074203080c04829802c440a1031001d200c0c840d80c0c54480d0410220340420219010701002c4070660740300d0b0403804001030005611180d694030000704400c1d6001c8041040400c15a0700314861480030355079140484400028541e9050f1840c002d2007000344e155080000d41c0c6090650300709140c210801c654904003424a0f03d840400a001d0034425840040010320031011106203042d10302890312110003046034225408410444c5d03030030703135030466507603041c600403402c006d006e02079155145c0c07110340d0f550303082040000d802d030341300141104180003241038410420b00c0904914 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 549171969 1250 549170719 549170731
    0x4180b0f060901050d051305060c07080a0f0e031903140c030d0e03040519080706050a0516050f0a061a120d05091302072a1a0702120304170f0c09 64
    0x201d0b40c0d5101c24001a255805228062902685810b00700b191480c00a2081360809016204850940d660102058298421030304020884103040c01685844c1d801155089401e0000d81080e030943e8204002003880c2c286986042c1b4071440d1003a50070001d16410001e607152004444500915001c10000d44507528400c036240c290406580700e040f0250070000340305032006450b00401305584150348a9000d2a00300050007076003d103018001c1d001640a00403402c0761200180d586841d42806074040d03582c1c45840b202c074000d68003809442c8681c11050424411010000d22030320f00000c58000121600e8103d4040d550680d000320502e00070740e00260700000e03450f1001c034154034007075070745444000106420540354400a4121400891200100b0180214000d41c800c410801d0b0664400d01d1025220362600700d01c03c00c0c200401c0e04400809076229100100103075400a09500300150b8240362481c0386600c29803051010003040340c805901e05030f060120840c084181d00003403d01c45149000241d50400c00303422 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 549173219 1250 549171969 549171979
    0x30b061204080d060b0d0b0607020901030b0a09050609330c0c0f0a0f0521030c0a0c05160807150e01080717040507050103060b040e06120f1204180b0f 66
    0x360400407884120b82842c80001c80138055a40c2d222103001c4c1c69007207105480c030002d00f0005d8082c0c2c01d007092401d0b607081513001090300034140d00e1515100c0d002d80d00a4440c4100907101d01004000c1541008454015000c01c1d00800c80b0000010412411450041c0e05080c0d601d41180ca4603c061060404580c000641c0c0074225074503540ca14106150800340c901400c09400784480240620030324003d00c05d44c2d1801902541c2003050000305c0c000c0e80180c00070030070304203400620108040c5803004020b049480c1003030400e42c1c48480c03d602da03289400c118074102c65200b002d00c601403100340c01c01e11103880200001001c400020b400183c0150046090041c01c5041004600024400a02c42d5040d9215486c030b4006140f040d081c541003068544480c0e005050201e400c1c03920009000d100c601c01c4504070303501802c0c900403d41390001044000500304091030090f1041c608481800f020610820180c1100b00f10f0060351a0f04d4821501d90000050300c40819180c83c1c028401d0180c1c442480c1c0070000141122 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 549174469 1250 549173219 549173221
    0x1809050d0305180a03080f060303090a14010e090405010b04061a09010f0e10030516050c03040306020306240304030206250c02130e0f0111040510050d02040914100501030b0612 77
    0x1400300c50b84042402d03482804d214080810042c143c1100c8210b000c0c010240e00ca81c85a0341e000141640c078442d040d00c15401107400e400812210000303054004e0300500500d458501c041c01c81c0002200c0c01e105403010781c2c05075540c0e180400365140c10300c11030f8020001c2030070144420f401a11004540d014440342c05051008480c010065180304021a0703455680040c941016a0031298008000741030880300c0c4003000003040420003110340900c043d150b03214170600c01545803d085681c0e44010350400b604498121001030b848070a0800d00c80968134070319521240c0103449242506009140c0000509001c07030726080041c0fa003101204045500e00b42d6111418450701c44000351010070000c8400c030044404041c5054518035100c2c2010641c543c100064034000c1c072204940c1040b0390f40d80d1086104080e804420311a98040180c01807028101c020441d10006003801e50f109030040980f0401c40500010075145410881e4441e44240604041d00d0281b804018441d136090100d40075204011240024500b90b0b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 549175719 1250 549174469 549174481
    0x405071b14060a0c1d0114190809120a0e040213060c0611030c0d050402030a060c02070302010e04050c1e040816062709020f0918060306010e0709090c032003011809050d0305 76
    0x1100c24031f0400e010388007903504c14080c00e48458009181c100f0800003904000414a08003000844100380301d07201c62654540b101c81301054915a0306c003c1e01507002a0240922441e89192401c984001c103299203964583c0d040526240003218000180429108030610601c0098052a42620881e40551000103642e1701e85000092924814442c02001c250821100c0e102d0340b0340c0880e040301101e10070380360301544124460805c41070740c1f01203954012184080c00401007450101240f9607000e20382101091401351110041810075807148200b201c592080078080104561020b580d4800351300d01c5400c03e50001644120009840061041f0480d1b5a000b0541801c07540200c022140080c000911440510407400c0143d004103c084506622902405d000000c001481d00d11a501c0392015030b40e0702caa0142003c028000410b40174460000701603549001c22401511450200100c0c1210452103450750301d009100d401440b64044c01d0840e40d41402d000340c0015100141c0c56408458a0030086202d42c0c0d46 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 549176969 1250 549175719 549175727
    0xf0316031101090b040615060305040803040201080705070b1e070309120513051f170106020d0c03091805040606050607030509060d02070203060a0213060801050f0405071b14060a0c1d01 81
    0x50f0303005081070a101c010b2004104243d400340e090910700d010398007a034030ba945070144c0484808546c080c1000404000040041d8861144a540030150342000d80c18651651902c1c9000142100c84039070301c40c094000e81c4d034800e2540c80c0d99a80b042c0036250a0080c2c0c2d403259a22094405554210f50034018041076010501c00451001c00c040c3c81c020300140216092600c0908a00c1d1501c085800031a002410ba02d0700c000000c0b0714141a0742d20f03074004025089135200d0072a08040000000d40801201c2400883c1041c26034880d1210000d40040204050078036081c1a001c441c40d6070b200728400e450410803040000e801c201981d000c0e510889401ea08c0d02c4c14024a00c01921807098000d40c18056001002083c1e89a0750140c05030400014012000f1621124141d8036603400380521030b40f10702e01c9408074419103407a4204030380c003c20516014590f01342e400854080140c0e0130300b04445112800507010a018810416181d0108140e041805215402500034250790394000203941407482207506080d60741d000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 549178219 1250 549176969 549176981
    0x1713121e05031b28120e1e0714040e0c1909050a090c090b0f03011109270610050c100506031515010c050c061b0f0316031101 55
    0x10350340a400016404000105254011610300f05280c0d00d01506400361088001a90054030b41c0310b20b141019009594603034412046090007000700700580d054032862240354041c64803a103c081000b092406080005500c40d0720b40c50710302054643c410700b401c001c0c19082e01da0240d09071000765000140c0c130340e550810a0500907240b045c0c54000305040503084503211101e058004131402070b00e00f00040c5c8c0b0f40003903180a0b501100c401900700514160188000d48055005000c0814010311340c41c40c100703440e00030a0a680c18281500b03511203010501d503900c2d060030107091050024440001c0c2c0c0c0b01001c2d4910b40c003055409850035005044c4d0034400085903000c0e03421501d01c04024002c443d444c41c2c035545031201074401100c1850103070080c40300729041007a1740040b080c0030340c488140b0482d0945004004445521701803034291164072036007200a42c030743c440350002c10f821540640d01d02c180c0704000c1202850416000001c1b12994420040264a0204105005460b680c107150480c182c40131001c01c2c0c1c0c05061 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 549179469 1250 549178219 549178247
    0x1501120c0f030b10080d1403182a040e07140102030403080f03011802092101020f0d020a020c18191116030201050a450c06171312 57
    0x400350400300c140060f400009200c2d06840303451980c41500c8100741e82e12074030807070b19500204881c2c204001e4540313a0b1402440d4084510b846520880d8a4a01d0340ca1501c2e4410400c100c00b880e003020070000e650b04107910090707800301c2070b42c040c0030100b00201015a60000f40c0b007444c2184544420300340c00b5038824401c440c0115046044240c8400c11468801c406034802e224040b0341c0341c032220001174846e5003402652400c8500500f074010002d1803440121242d14403c0904415540c204050b8816114117809048140320701180141c84104a8034041c3c988211700707d186216030308081941c01c2030000c08010690004e00c03004030180240d0407104020140105804840316105d001c41c1c030707603031411079148aa0a0607010398020710054562100c401d04480300b88140314414980650000400d12110209031084000e91341421050b403220381c0e00c20410004181c04580d0842c1c0c3c01c6040201907071000200302207401d038244001c0075007020407880c088071690640003885412803840d004011406600f04400002c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 549180719 1250 549179469 549179489
    0x1e010b0a03030215100323030f04090203010e01050906061801020a060624050a020304060c1a181c0c0b1503100903030f050402010e06030a0b0a0909060e1501120c 71
    0xc1d12803030040d4454a5082d03035070860040d59000191800c121800500499411204141680401c46c810300b40d14049110307890303c07a100401a45c0103840036400140010b11544800580b694109503038552f5912040e80003501c0303200070409110f0ba42d541c51044030003a0724451540d820324400301c1c2c01070341815405030010f4101c1d0f240c60000901c0b00135901e18011010007024240426059808045c0e44900640340c08400690081c8000d010382809054000700c1d03103000302c601030307071030100410118094442240c8007940320103800300726446010104801804101400c00b505200240028020441c2c1e0400d10054243c841001c08290b04948042c03071000d0440015081d039218004d45140d03c5e014081324102180000c3c90000c11400301c020030f2264500640e4141d59145400d0b00c140100442600b000d40345a04003540c40004071140d1ba22004d140d4001d002c0d40e107001c200b41020381050780c2224003003614202260021f0403144400024a000305040d14809410b0000303030001414240c0c404075040d00170392251 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 549181969 1250 549180719 549180739
    0x2012010b0d1b08010305100e0c0607020103020c12071203020f0a030218030726061303030903050d1802090108030901210603052d03040320121c12020702031e010b 71
    0x30a62040ca080c0c10b032801907085a403004c21041e521f000702e0716800d0f00e00801c0e8000c241880210319040d0000c180759401490050b003070045414040e400e1082954903c201d400c0c00180704c1c800c0000c4501d641942406d01e0804505016030880040402c0c4030b4221001d0030164000b980e115017104000b4181e914100c090101c50445444842841c116801c1c5012100009610000c0203110840002c00c18030840380081c0406a000031550240c01804900501310144641400300c00c0100041313104224898804900500aa10071801480201703c0182c101040c940c104010b09502d50340c003c0800303d210701174076010710f044141041d074030402008690001086401400c0d5050800b2070f903000940500da07010300c03480a00c0c40c0b0f9442076950301e120b1440001c01c01d4101c00f00240d52030000d600352a00d9071201030060501401700321503007802c00d00792055081c0440401000d0803034203948034011180f400d003110011031415140d40c0000c1d644241142c0090411626040481d1140c0829045401d649002404000d54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 549183219 1250 549181969 549182021
    0xf05090f04091b14270a06031a0105041a0d1203150306140c0a1b050c06030a020a020c0f062205040504050f10050408090f031507032012010b0d 63
    0x280c1d42c040d00c60940d04219102c5801c09500d007550001c98100c800d68030511600c0c220340c24000d6131741002441225210360b641d8000021503041400250441c0c1e8000c0813074081e604000c01c20084802e059481c0c66948101c03090303042e0540700c0c0d513500502c0e00d4110245000c2c00390403200032001b410500c441c1c1c5125810412002040101503003164400000d4840114010b40d16962040014056007440400084007000389800c005038601e40c0d924014054070594195450000100e801075006651070b40c1d01d10307030000e0840c032095814080952200c8044411051005000002074454041d2a4070840c500c044c4000180d0120561000b0070020301016200303010501e4103050650b20b6060f5020848403d0003412500d403400246403040a108a0703102ca0b1050034038103d8010310200c481001042030b0544100c000d601200c041c1c01b000c041c0301e12a542e801065008030840a040b0314644002041030341c00e02440b40c1d81c03404400304401d5040d130783e420221945441415410b07602801c510341c0126078030003c010102d40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 549184469 1250 549183219 549183263
    0x5250e0a090c0207080c04050603030a1d060403110102060a0c050406050d0204080a031116050607080c01090f0c14060301030b01090209030304150306061416080307140313120f05090f0409 82
    0x2084a5012007611b2084000d101480242c500894000c0d515801c200444242c01c0c0c01109a404100c41e85040f50616038118008542680d105400c1a140c4d240040414245503904000741e56103d01e1450090100b040240030240035401203015510600501280c201e1941e80c20740d054034024901c040c11100c0030041800d01624a10f20301e0604515405030078090011002c24103d09811288003502c9140b60010944079005103401c0001945502d5480d00e2140380402c0d010a652a4600d0041181e044400d1404803400c41d80c40c4a560b80700c0c0900028401000460340962007203045551905000d42e4919016001904611460b00541c8104d0300c68146030300c80b00c1c4d1550100c4152480c030b40ba00e90540c030142e00b0010160041c080f02c051400482865140021b001c000a560084180d041100246402d150700e004660011a46211a284401107070811b000050b08415040641c40c1041c0341e1440901030024843c0c46404413160050401808100d001d4403103522030503040c0d4022001031010204079016070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 549185719 1250 549184469 549184483
    0xc1201031505280207020d05100506030d030908121506030a02040618080316110604030809041109010c060c12020c0c19210c0b1306020105250e0a090c02 67
    0x201c11a840c1c0000111402c1540c20304505450b0700d041d0405410095203404030103580b0010b0104c0e0041d03031202981300041c5003000044600031207844081038030b142c00c106140c0343c900000d94035801c143c14000503201040e40e10007101c24202c090240c40340d0315580c0100f0040b42c059105817150700003000004010111866030301800960721907548035000449204440a10341604d0302940825030000c000345000341c00c884294022080c4200c0b40c40c0a100400000a01d40381c00c130fa4002d9034002d0000a055440d803500e0320400d0099440080c0b00f60500c2d02000000b85244403000009208a0f0740d941c644180c82d00030103c1941404a40409640e640741e094039a41d02e54908a07103c0b405100030b4200c1000300f1486006100943d4182c00080b00203605000850040e0f441007082510804005c000c08524000750000421003440e101c0007083c15240b40440c02800c45030b0061881c200c1c41c0b51152070b550290408224034540c40003615200541c0308160707001802c1e0140070380c010362071103180c0502180c0440d000300e90b50b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 549186969 1250 549185719 549185753
    0x301090b0108160905010f0504021b030a050a02161d0403020703020409080415080c18150708030f0c070c06110c120601080c09041a100e0a150b07020a09050c120103 72
    0x43d04080d0b51034201c4002e95000380104001105464014821414286d020303040109000080c000f08c01000c0d00f0a41c02d580c030040306000001c00000b8211030031034041203410403a0340c59010569100d841c0c4180408082e114810b030090200001e00450f003498400c10060026503001041002074600c1440c00c00915032007440380c442c5203440c8804100b0010f0240c0719007441882000803403450140000c010b501100d0164071402c4c2e001c501b009100c07440011100c054400d507849031701c20740d603a4188500381e00c8050303030020310340701a05000700504030005011501c11000c807903140c01d003503400513107440c4220b0070b100000b4143e50b00054a044000340180300050828100d806a00c10303927540e09070741d40c144403203250200c0c0c000c2d00034035020540100480350b05045591017450f11604088103600c0d25082c0c0c0240c4001d031788540c5c0e211788170008600d02c4000410540000c0c91011252407a001495003ca904545c09200b5504001c0d13540c400209540c1c804002c5030f621003c0c11104441941c1c4a02d86165030024003214 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 549188219 1250 549186969 549187003
    0x10e060c0a210f09170307080718081f050606070503070312090807060507081e011716060306060801060f0c0f020103060512010218180112020102150a2906180301090b0108 75
    0xc05c1818801d03003213034061200c5950b101001d948424098820031074884415854401e00900020700700310034880e4031911000202d1440b908400e08d5089000d40d14040d1903d8030031541000070700b00180001040f60800760303040c00d121034140503045100000f00000d040140117100c00041c0e00341000101d501041c03240d06251100c88823611a0013104501c00840c8927a8540f14408800500ca0480b50a03614200b442e030311710880d101c04411104442c02c49045611144c01b01f512040213001094000e5121800740c01c182c5132621403c101030000611034100c604010380036042d017070340705020b46e4400c0d080300024210103040e10b046003000005d054000c7d8000f2007682c810800d400b903400c01c0e51501080c000402c482502c01410b0990803da42d03401d540c14030b050308906500ca003c00407041c802c0c18042043c0306444a03400002c80700e00240c007150512110085924800300041600d22440d681c0d0415078504074609055055034080a8000c6030042c01c1840001e0124a82e4800000d40c41c0c13400102c0109076080654 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 549189469 1250 549188219 549188243
    0x1522140607080c27030d17090303060d0618050d0903020901091a0909031303030903030f030c0504090f06050a030f021e0306281d010e060c0a210f09 65
    0x36080310898003c0e502d025450b04200000040d0880d1001030a480360049401c01c450001d00900080c170705001c0305c507624082036001304901c507c0d0380d1115070280c1c4105080041d500c2c43c0f5000c0c3c00150159207881004104a680701c0040890b21405d400e2615100e61200071a001e4507800c80025140003950f200491223a42d00c60000714181029000b4156880184949009881d1102c402c12618060080515080344000e00c0f15004c10010a664000114066101c1c124198150306000740401841c1f03003031809041c1400c001507a00c540c81401c84081751070080300060105003001522005c0d1a043c0c0c000d41d84035035101408000c1c003840c7c80d40103841d18800c07503015540802024101030b8090035420704507819044000020145013016481d0885150341c45091081110701034001000c4807c540000a1038641451012100340401d1080548400780314000307101038038000c0c0300d08205110350882402004103400f0310f0040508000081003040324502c006016402e260416200140301013807060340c000030301035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 549190719 1250 549189469 549189481
    0x210f0a0606151b0803061c0b0610030203132d05010b0118060509060a0e1f0206070309050a080f040b04090516031803141e0d0f0e15221406 61
    0x8000c403032080405030308010f142a85840340e10a03078000610640e0007000a00303032038400307601c2c1c1c001c004450f510585074050750303040201c1881000340c0c4a038800400d146c0304200380b00e490340c080035100680980c400500e180d070401494100c185100d00c001d09000380886490803000b04071040d08104074007074003a80c6103420107242c2c1d01701316182c4041d881500040346040000c00082c1c2440340c020408000107040210092030014041303035000003044195000d070448243c00d01c3d01682e0600950340c110103640343c140324181d4075484040d114443c2c1c100042c5030340030004480c01c1000c030b01303410b450080400c4040203448176035400c80000a000c045440d00080071802c07071800d401c2c50003807084904100248001d9210b030040da03501600c52440840841082542c244202521401c54900034036a00040388000c903202c0d081102c4100c00e41d0403501a2034061400d00020440a4000290109201009050b451255160500406a51896031001c1150071405c803a08000344800301000f212407001e0101210b406aa0b40c0c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 549191969 1250 549190719 549190727
    0x100c020c031204060c0b0601020a080417010b04020f090105030910090302070e0f040b0106051e190e0a06020607210911100807120906020d02130f09020306210f0a060615 74
    0x380140000303d58108508004259404030f41c61f40a04180101c0b060301c142030b21101d0840e00142e209612103400c949032100074000a00580b440c10005480543c00c1000c4a290a40203004610f900c030704010020000514018041008100004211000f0403070020390b41002034962920780200a080402c0c0c8020030201c448840119100d1038018481150716400c04004039503e0307214906400781c1e680c030082c064030b41c44810030080030400c90b2401c2c0310f202260140b001030421406c090945108070900c0000704486038000c2500ca5100c881d51030041007030f03181c45034056580c030031041b8030891051502d040582040b114180171000e0004c100d031006061100d403032003141d21101c110f0302c0740c1c0091030a00218200e090f150304403550325440703150058100302001340e062089810802c024039040591050410072580e915104002400340c005040d451440d000d80482c0c61110740040c2c03e04030100c0c40d040c9441c5d5038014450025050910001e680502c8503c1c10448003426003402504100031004100802d41401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 549193219 1250 549191969 549191977
    0xf130608040b04290c0433030902150f1e090307031205070510050403031d06010605071415090712030c1b1509140a12020d0302100c020c0312 62
    0xb020582a042d0343d42c540c0e410091804840c203019030018298a42d0800341e5a000801c0d00c1885106071254983d0b1409150f0a2110840304810406080b018442c6100030000c410030007440629060219002e17840b80b011405d03141140400c600f401f0720204203401030f101d5810085c0200f504243c44100c02442c03140003044144034940506500d540a41020000210144803103810b800b0242007641c20411356803030341c900304600c9074541d1601a03070b14410017003010382511a24188403103011448d071000d03850302001562500107008200c203009010480e1410401110b840e1160f84840c130007a0781d10300d280b00d07001c140c00750f8082c5d5248585000d00d040208190b50004032030301e080c54060340c981844034501d84608803c01408108610704191401001c00d000485860740703108103881d55904c01d0400e140c0203001d07006400058186200b050544002c002d40e4a000580051440e01101c0801d650764191400b079251541101280880c20f080c100360484013a00810480303919a000c3c0c040d1840d00418085006243c41 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 549194469 1250 549193219 549193223
    0x9040501061704030f021014010513060812181c03090b09130b0d020a030f03021212070f0207030501060f090b0a0e0c21010923060f0103110f0f13060804 67
    0x15030b04000401281c818810040300400ba80140c0780d01401c94403d08041e1200b200345040740700710100041249082400c040b11608511440400550341030516154841041d000a03a440311004511060f401d01e043d0314480d2820b030000c1c00010380c404c031225005d03484070341500d00b500865030640c00056003203c110116260424020240c0054154541800c4001c03c80b102c0019080300b80a000080161101aa2040034500035054200c204a01b40f500a1400304214035030320b600802030103c42c5102c0700d4101c545400043c0ca05000c2b040401060003240340c450a640060010b41c20124006401c0086040300800e84440b40701c00c0c0284d030a204140704800c1c040b80b0031a0140b184500c0000c207542140f2024103003c00c1c082c5c050b0310f0900c00120303068884000a0300045003095686038490600251684140c1440303a0804822078149414400550a41c07051b00110f0f0500d0b45968000d00c2c6680c900049030441100d003110640c4940b981c4018a0b0160815131055600036152400821024050100144120303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 549195719 1250 549194469 549194507
    0x40f0f091d0705040f0e0105270304050a0302010e010201020d0606050417010203100e1017010c080a090203071a0f0301260307170d060b0d1a0d1a090c0a0b0904050106 73
    0x30f49410140310041200d19040d0a40f1030707a55000880d449401e015042c042c00010b64090345111440308008414030140e034140302c0581c4104010012902d45000030b4044030340908191301213136000300040c1e0180c41200c07403c0a0907842e00c400800d8094029001e04143d0304403400341030902901aa10508034441940d0313005022584030000c0100720f1007204061350110720401c000001c983d44040800003035240d08860f41c2607944845030a075a05034420f00141d07004a50950500003c1d0035600442d032140176502504880d00320442d2821881c0808004450201d003880340c24917030f40e42c0e6600c00f0600d588043d1504000c44402d45141081e2a0000815100e546070012580c8100c400362207030703502456221a5031030100503103550001a0307005c20800644035848500c0c102280c0701d00031040c03000a00d0041c031840c0d0300c0340d544459850301140c0380c079101d0b804403003440800200036200c0a881d03070f2400707441d0002103034070450f42ca07800300b82e80c00c0c150054904a80709480501150b600c4000556840e4141d08401c8100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 549196969 1250 549195719 549195733
    0x711060c1c0c0302060112111306031109041e081e0403051002030622140a0905060f1902030405151807080102070314030601030f020f1209030a090303080c040f0f091d 73
    0xd000000d0349030b01600c114144241002c0323007804a41d8401007020301040c526625901041032210250003400b036144200d505c401c0900c2d10703544400c83c401c228508041c520107a84209410044401e0031900d0061070366000310301c06c4422104031110b6600c00e010444507800ba44262211040c280e0083d0303401840006c05182c05500400710406605880500c0344420685464110b201c02016002e1203010301d14884000c900403d0f603040441c90b1a02c00f070002540a44400204451070784074018090301348003445009a42d82c0c8032810300742c0c50020315010310001c4200100c24400e10420412405141301084400c0c3c1d03030f140ea507840350b0b20300701d0084500141c0880e0b5240c442e00301e40b551100087d58403d505044c0040d003c42802c142030100d030002d00c04105803501c00034100310130044901c00305502900d002c0055103070060002e401800c021241c4401020300c4a05000b041c6c2040030501a80d028000d4801c040c40c2d410303510100c108100005100b100c403514030700611983e2401d110184102c012854400414003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 549198219 1250 549196969 549196979
    0xb0c010915060e060d06021c020c1b01020714130606020c010801080c0303030403050a111209010216031e0212060c18030319050a02011112010501090e1b0711060c1c0c03020601 77
    0x214000c000d411201640d08200e0102304d002e0114074440384082c0c00c00011307100e03442800385a2030001082045403a030844815084180d071390000d0880140da4030210380079030101d2140c2c0403452041e0400c0d11921224202140440c4460b40050701c0001c0328000daa0760341190766103c0713480e910f5617008060542c15400400004020034024070080030b10b102103140441c03090078020502414143c031400099000f05000460380320b1580e0401a401500395140321000c0035078510740e035201400360301071121280c0214103a105011355860039100001240303210251112440e103642c038101d5580c4503130f0550031286083c503540c41a9081c004107032020f051103091042074503c04050192607035001000d8200c210340d00c8d18034501c1400c44039030250003000380e02018003095504101c0050004400368000303481180c074080801071421040b40c0e143c0e05c510364010b0443c2c2d65a8a90409405084410b501290040c0002880c3c502c42c400018510040400411926100c4c03c800e032021142e400400b031001d00141c4c4802c0c01404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 549199469 1250 549198219 549198229
    0x10030809040b0a05040518070609060c0f29041703010b1210080a05280f060b01090f0e2413052a04060318020d0b100b0c010915060e06 59
    0x140000340146801070f00355a401c0010150785041341c0d20715070100f4461109030286001c102c000003500350350a00156050070b107900140171000b166405071211140041540c00d020903401e0000c0c10b02000310000d0596a0800301c0380312041415a012644c0008030540600207600b0740c4203903810f07107020507940c0f0320306100f05080b5592102d0207040c00e0b00710801907400054243c0204440318240b8840e80140c28030100456a071060800e00d514441009640c01100c100000c1c900c0d680038220551040000400d00d0480340101e81c0c0e2010f80d045064800c024030004074034941900440f900c82d600490910407025120240d407070051120b28000383d046401c140341494641d0080d004140d000d00c500440c04086401e08038040b4507161242d101d408182e1300001e0900040340e250140c140c16503e102070b040c101400341ea0209100000c2004041c1102c840003001c06c045107a862176120051001f40c80203600c0d221000034040c020b1040141c121001c400e503000b0410880c3d6240100012a01104450a21651a482480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 549200719 1250 549199469 549199481
    0x80f071b05010e011d03030d14060409020d02060c0106090c17070e131a19080d08041205030a0b0a0f0f1a04092004030309060e030a050606040b01180902070b1003080904 74
    0x120a0907003200045e4881d4600300094041002d500c0c0340031030ba1f01c10802c0621844440900018040e42c00c0120f01380150311880444a4596810f40340d0701d6481c844070554500501e21500310703102e40350605044c0c108141d07100c41101910999940300c2400b549844009072044510542c10940045452001000c03a103103952204502000c0d2000780d01c0f00d005598009000301c0358446160800070f490340018024048204038a2241109505100800707042603201c1049400c201034070038023007143c004001514501960040f46880c0d101500880310a600c036590380c8407246003402441d44143c00c500d03000071044d0f040da080258200781c156040f880d041c100303512100070f8003251841c0d154a46500b010300b4086d5038008002c0001310700a070b85803038642e802c103000105104020b8104c50300c42d40c401050100810310104469800810031103000809618000041c2c2d4140710340c555503280d2407244c00b00007981ca800c50b0010103596103d40384100c4156a401d0456031082e005000c064001d080038041c400c850b080c55840781d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 549201969 1250 549200719 549200747
    0x10506130902070804080708070e0f13050a0b0109050c040609090905011d151320030f0d03021b010c0206040605040f0f1110030203072307080f071b05010e01 69
    0xc0d0314261215030341002d0341e01c040402c6520301000142042240020b0100d10082c000d0040a003000c0c914000c00401160006400ea00c4180d050f0004182d400c1e20105041401e5988001601c840e5000385c01e11060b852001d12651044c0b03418040002c480b104010100e03801c0d1983c070b4031f0726065181811070060042803a40e0084174550760350703002000700d0020242c1c4055a81c01200052506060026100c02c4409000d01a945034140803422100001e8031025170000d80c0d910030700000d010001c0f42c0c0c0003a00c0c1009908825010b8054240c50035005070b4140c0081580d6681554001042a01c5c0e6010500720740c0402405401a00300c10301040015607180c0150360018050f8408000740c5116403500c0d00718020401c02202d05502503c00c250007800c254a280c841e008950504600f1880c20690192090346205070482c201318405815248403000041500e0b07646403c039010b2520751b940501111426071000c5001d86005018403201c803402c01809a40c0000d58006a542010045040d4015a1400c08001c09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 549203219 1250 549201969 549201997
    0x120506160e0a030f06270309091a0d020103110316090f12150924050a09150207030324030b0a0905030406080402010c0203010509010f0e0c030a0215160804030204060b0909010506 78
    0x3c29a2001b00480c0c0d8000c0901507a4114038010b914500035010003241c2c0d2003408800d013070030318030506001c0c02603170500410382c140c0e02d6203884a05480102c004060b1a03600f0b8590200c04010f1044007440311129001000312600e407038260301e0b100e440b0054140d09601ca000c00d40b00f4400c00c0e120004141c130010340ea1500132004e02080c0521175035514410444240c0080c2421550203031b1003c07040982e40a0180c105141200800034007403252613841d40c103460790080040031600018114105440380e8030014001c011551942020b0325448580c2c80c00c9105880190303070160003540450b01c0d440082c80b5000c1c007075920030000d40c54985407190550380440c00800076030501c4403240914016880038000c02e803095001c00000104410321030400c404951005824100c0307640320750000502602c000610030785294044805d981044010100c0b001c0b5841060f424036160307a02c8400010802a0f00000390080e240700712002d01071681c4494004010b40103080c03040d80d020415400402c0181003500c01400711480d02c40c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 549204469 1250 549203219 549203231
    0x70206160c0e091f05070f0305190e0607140c0a0f0212100e0708070605040302090c04081e0c0d050c0114040f08030414090915090106120506160e0a030f06 68
    0x2c40640e07a9482161500d0700b0743c21084070b001904c44803d1035132000c2c040d855030801880c24083c0008160315007840741c0405042d82d603404690355000b9000340004c14080c26406020480400c0c1845440303020a4401401007005640020f440308600c3d402d0300c1d69080000c000f880c0700089030f1114609140382d00c030240d800041030032101d100340c8424000c0a40c20038802101044900c0e880c9042860301026a0118516030000e0009001140d4440b0484042300d40407284d03001182c943c919a0062071045510100c850311a000110000c104801e6180015220f40070940e05030248101c01d00041c1038036000c00070081d8008051403065580212650303c1d0300c0320070340b40d0182045d03100d05801c0c41c40301d6242c01800c4c481d4808181003151035003100e103609000500381c6100301c0d542000212036030345051b00384030720754046a074400041c02c2070001d41c130080060000600314003001d5240d082c22501c0710303405c0e50700c1100d074440050000101c60203401200480d4101420310783c80c1600c0c41d22814090784540e0070856010351505 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 549205719 1250 549204469 549204479
    0xf01051006140d0f020c0604030e122e09120e0406030213020304030c021c020a15090612020d020406050a11070303052a151e010806060d110306010b0409060803070206160c 75
    0xf1006d0041060904001e044500302802d011708007101420347d980c841d818007400001c4a05020504035094003041e40c500030348044100c3c410160420f0075100034412468520400c05110000c00b1540b01a0003e40310031324101c0301c42c420b02c4241d56040c08040d401801c01180700d0000c800c258000c541c498000d1805910b030740d040303500284181c07040c90f8070001412600700405003903240180c070759070081200030b2165000900c042c5014214944500c10101481a502c0c1651507804064048510f2280c00c001d0440d0345a454000c0540305812a110a200095403103806000c101d600240100969402da110380c0d003804400c10301c48944000c0d00c0304e03d11005035085c044c070103020403c0105511040101000c01d0721031030044040781400141c02c44e0034029001d00d1004000640000c0381e0f49400050955a0291108882c185841e44c407204800140c0c0520401c000010a43d415001503c10703a40e5411007804075079035541034141e40e0f01410002a43c000c00401807601c88248031000807042ca03105001a1404503520 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 549206969 1250 549205719 549205721
    0x6030a090c151706190810060602032a070801060603020307083702040504110d110304260c151b07020901050f0a0f0803030a0c080403020309151603020f01051006140d0f 74
    0x16032010020b90302002580c40c082c847c901400024066910045040c02c1c6116422031304c00e0050340c25620003001c091030a160441081c030410024102c640300174000b159607200001e0003075000301ea40400040060b4040707080074441c030341c11980300b0301ca1004805841d46003680c40300e90382d8a150420b003140d43d0700f0007000556840d240180c00418034100f02c142e4864040b120028241c40141361200141801001040009031a0a2100d5045851030030311940e200d1803003100c030845205071200c4240c54030500d94414001c000c56024144528042c030703c684209020090fa00426000e001c0000303610100380c0005000c6424050f030605c1242800070050855165180002100c02d590361300010515000001088081d640e2801070103210040d03450080203e20303058400945034006d041c0b40c24802c00e00203c01018800100082d030710b820026000d510015402494040c1d41c440c0e4000d0300c1c0001d54280320024101021941c00d450840e841c980702c2c03002180701d0b040175810980c4010f0740f01c0f1400c0c1e0341e400322038107103090703 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 549208219 1250 549206969 549207019
    0xf06400605042d05040b13030e0402280f120f0609060f0303110619020a0e09100806090c0109060c08040911090f040e030f0d090206030a090c151706 65
    0x1040322412845200700f45032840c00303a0240c110001036040100740400100100180d542c8085032030407010307080d01589003c0700c10001103000e403544240046880d108207250080d000004184280740a52584034024090b02c003809081007840104240840c140c003034020a82181d001c500701c507180024150f0715200e804046032104c0d0803020f0a05000f82c6d040c020940c00c48038100c40261900000c14a51500d05000d8912001c55002c5104480e004541d007003281e405441d59081c0f082006104c8a51850400d11a0017064800d208410481c4148000300300711490100382d4802500041e0f56550380a0304004095400c1d4082d950100c2e181d840c1000000b4100c1c10b58400c000003e0100d461959484c0e240700d041125422807481600e21545c40e00a222840d980000100c9804900020440740c039208a21781500003084421006034101c1d8000080025001e40341c0d01035409039200300c65111400d0b0b01c5c2c400380a0b2a00c5684400c3c0e000c54000920f400c3c21605101c0c4c4a035105070001d101500e000540100e810950b05 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 549209469 1250 549208219 549208241
    0xb0a180506040b0601080c040b030118021b1b01180308090619090f06030c020606090a09020603040602030402190305070b0d020f0c07090507020c06030c1b060f0640060504 75
    0xf102010b121aa6a1141105400503001c81281c2d041505190310f40005120602c50401c21495814035582d090b24560103071405180310000000300043c0d0040c0990322009001160003680010300c02488066010324003848618039590400440301d42141c0e911601644074403403081e4049024000344030861107205281c0d42408142d0f40d0800440d01e414100c500026080d00700c607090608000c80c05d1500c41c0d000469a9100d003007210400700760b403640b80402c0300a007420a070103034000c03000004010510025400950045100b551120200c0d4040030304240441420700009126810882c0e0803c80780c42500040c03c007561180704014505050a0904641d9500a00a0500941042908106401848c8900390380201c0728000740c030300e040c084800118144401820810800804180745a80840341c10742882944810300481c0c807507041034080c400403418112051417040c3c032024a0101207269035201c882c0c58401484288408400c800c1c0362219500005014200d400c0d911200080e07107503103601886c1c01e10740c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 549210719 1250 549209469 549209483
    0xb0907060c050a02121903030b09010b190c0204060506070f1a040317060310061502060c0319020c010f06030f05010614010f0806010c0507090e060a0207030f08040309270b04090b0a18050604 83
    0xf01d271000e0104040c4140d01c0000101010700c86c0485800500e808901537039490300d0800700f10891032000600503c11138000b00c2d001880859501f08020600f280301042c207028201d05442e03192441c0520545120844000b0001410a844031444920003640c554001c00000c041c0c0e40b00c1440600c4020844034258000860025079420000761250113000c296007041a1604c460303d103240c21015504801301d1080d01040c0d40760700054600070f129013940f20818048026100340580d035170721300308503d544803141800e4803075501e40240003070000180080c040f81320406031598075100292641c01e4a4400300113208c18184102c0628000015200740500b4000c0d004040c1c00140d60703141801020700d0014020180d00e6900d104003c180e0100303401050f401c500258514100744a50b03200e1a003210100e1442e404441400d50f1046118919034188a4210400714200720400030889203800b004280c0754a0700e006030004400102013010f110494025040c484660340c031403900d24029070b07602c5d8640001118152110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 549211969 1250 549210719 549210731
    0x30712140706091a070e0f0d14060415060501080a091e030815010207050f220f0606030c02030913021803030d060305070b0a21090f0b0907060c050a0212190303 70
    0x10802e610981c3e2090a229074614142c40c11400190119103a4403840c0c7c490546c0e2140c0d018242c0c2e41484030191581d11080e030362074501401ca1070390350f142000d46049030964401c1c03415400005191046004440c41650340365003544690203000004c202880050342c2c031030110000710914200c20b4054001c1148261f42d100700515203040704000e01c86109164a045410920040145548243c030048103080111811801e40c82140f131100b40d514409847c3c0382d5600c0c1071403e0858104019030240c02140c0311074030180600c444480b0708a80ba031146041840d809000080d4200c100c100d5076028100e21500e442041d01281d030b0040000e031441d00036101d22442e01e07484160900400009000340001803100d0b404840c00e2000b0881c024050311240d411074090040140301c50b10b54000c050300442e40c101d800c030051001c41203860800082e920401c86214480f0700c039002000900c1889490144502c0760000e000d0144002581d003003101c03001a071168203009100354040d00312900e003928002310f009071085c1c0307001500c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 549213219 1250 549211969 549211973
    0x120f02010806030a030e090915090a060c110d121e02090f0102030a0f0f0216090507020d0206060d02040b030a020406081005011413050402031203160207080f03071214070609 76
    0x1074003802010103000340c0010142200194008103402c04200342114646c001783e4421000500d04051222000700f100c00900c10701a104c0c1000c1444107089006007406e0003081103107881078800000c0c14841402d55408540d185a0461045100190280013202c000c2898810030021968806220120b2107203d40c8c0052054001c0c07400b030501040420082c005141040000400a400c500100000300b00740400074400c11030441c1b0a01001060f010060500e0754820f8481c1440002041e00300c80042c0584541c407481d00c00140002403042c4200700c01002e1803002a401e80c00d10020b03100740c140554041c41080e03c141c0c0140d03100d010701800307040d60000801051060f05807040c113454042c0c1c400220200b504851507101c0d1164142d00444500c9c40c440410396885910100b8507012a10610050780710b40031043c0101e42080b0003044040c0c0403190300b21140243c6074401284c88403641182d1403100d61081040400040000d4800b6941c05170070304110034441d2144c0c4000c0d03010351090004440c1140d550f00a413003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 549214469 1250 549213219 549213227
    0x13006050a0e010b0a0f0b0309030408030f12181e16092306010512040305161b080303010810051f0905070813020a09050c07050f0a0c08150c030c04120f0201 69
    0x400904c085910750001c07031030f00805042100250156043c90b64000000071445901042124024140401160341e00c910641d90721040f5041841071440d03c0b2003580c04103400400700b1040c8252980306e40003400c4038034201101c1c036100214020b508002c5000e100d100f069003501c4000389000800f902a808105c0046030f07100c9180000720720082000b44c14210040c05940e0340e10400b56500c811071a028208a5140d0b41411f039841e000314007140e9284210802c9030010805c011540c5141d103010341b10441e541903140c5020540b80c0c0024010a251076002401007101240150840b54218002246860004108142440d01b034503898122480310341c0c0b10f0b020b000180c0c0e4443d0300b5550100420b40840b0000ca080d0380096041c440c50f10414400c20389800c041080031901001f200c2000750b00c0780484070581032000c01d960b190040018142d400004420340011410300c041004180c403003500711160b00641d2a0252008a608003400045610b0750038400400d122807048880d444181c041c0100c0300e421417803440010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 549215719 1250 549214469 549214481
    0x60312131d0105040e1501060518063f0a0504020f09040f05120a0e04360507050402070b072303010311150414060f070501150e0a05013006050a0e01 65
    0x403034107a0113000560314a41b0500642030548141d8600b15980300600d5540a00321102c18803015070001000803444403103454202010145540301600301c508007064402c1d580e00c090003070104000c2000080001e0020b0505601030342d401440180040e400000e483e0218150780e2044400b11040c01000f0090f1007840001c10425402d400d07180a0301c2e190480c0884002d040c0d0400d000070b107004503218400c1c1c80e1a410301b013404980f54981f42e4a0102110f1407074440740301000b1011002d480700d0142090200d610b00f414002c0740d8a06400152004117034a403031100b20340e66042218a148409108580341c1076400c000c0e0011802140280e1000c41000310120800c60085140300e800c10f800c01080000b0132004a00c11103845280b4030840c0c0c1c03140c60300300c1d074010024140f0980d10020819407800011580700b441c1c0418023016120f010440c041d60746c1d64103ca03181143c2d400c0c0601401c56090240120700031203070422200d200c01455035100202c008540e1981f0039228242d404030989911070502241d940800d00c142 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 549216969 1250 549215719 549215741
    0x7080c0316110a140112110c03040302010311070f02091e040f1a01230301230106021612020609010314090714030a080f0310030507030606030218060312131d010504 72
    0x11115041c600540c02e011010701e4001306044c40744901c841c1e900c544840d44605140000e100c0601d54a0b00d04440443d141d0380180403c0f0301191400d000c607030032032400e03c1c1a03403030646e400389001c00100416020070542250040c111503643c4a055201d49400b000380e810b0f980030b0fa20403500305000351401d290408000a030444022019510040100a243c502c80c11484400307903140e902e0454445107802090141079098082080c1303020f000100c903c049030292106048680c16401e42c1c0d240c220040b0140c00c407650505c92010513400801c1040003500c2c0100052802407814180004e116502d90901166081e00301c0d01c4100907040300d1410004840320318521071440c00210050210640750796180a024045e008024410714004400070f4084036124014401450f004011162619036a24001010300030034002240074002402e41203401c5042da00503203002d0013005025104802000d004110300382c008c0358010308044424000095024000041c0c0d004c031603d0040d1400c402c1d8180300601003a83c0040c995 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 549218219 1250 549216969 549216979
    0x41407032f030a051f0e0a0b1509090d050d02071b0f08010b0603010e061503090105070e0d0b06010c0303180605090d02031306180906060309051e0706030207080c031611 74
    0xf000006900400c1e15080b009071745502001903280a0103030002040c80917891100c9214900c20350081c01107150880d0b12800080740c48000040d60b0105010182c46c058402e007080b40c0c00420720304c0c1100c0c02000584140e0b5058400141041c000b500c54550380e40490307860301d0445010140501240640c1d01480c0080c1c44060001e1004c408040701068140c03005100380b01c50f400e03901011038042d0f0394460035000140b4a41800769200c2c01c2540c0c0a0b0b00030841503403000c0204000c0d608145842c1448401034100701d030042d0400c2819592580103690422080c0c404904059480150422290780014604400c501911340002e40385040c81c01d1030700c1c1030020020403066510030700c0140b004921904051040d200c02d450f02c1d18002c40c81d0135480d0790b5010550002901e260a100f00410f40070b50503400704103560300650844904c01a00300782c0c16007131007107000da40d0b80c107070002e039018003c15000390000c10440784036a403000e203403548480a0604640207041c00c0d04031000f41d1a001814801d200b2010400590100e407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 549219469 1250 549218219 549218233
    0x807050d140d021308031201090c02191103011e0c0201180503040b0f071226040305090d050f070f0608090102160b04020d020405011401090605090603041407032f03 72
    0x302480c02402480b0b11802c00c1a00024070015024600c10030000604005c0300b180e8685c031a5071050400c00c2d2007401003451b014030303005419001910019800b903200b811550340c0800480300d500c50003030310401d9a60f241e400d036481300190f600052411422803c0071140c0c050004841000c09002400e50b0065880c0c0d0305510801d480b140f0204902100b00c0d003c840d00803450035a0340ba04a8a00d03443c40c014514054104100c2401440718a034002010303e510071075455850107030852405031103550344c505980181c00617105000107808e88c1080320600d070741e0902a004a5070001401c038001d52802607950000441a80403040410800c1e4005407525004036400c8001d500f041c00c1d030700d6005c030001c002c2480038201010b4600401c05644a121082c20642c4c1c000c0c000340481d46e15030a0a0328442c00000b4824001400c0c010002001403091095070078058004140c0c030300d991607903111000c00841d0340c201120b540c01004000800182c0c04a11100200442003c0008544904100341e4905060701c524a0103508501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 549220719 1250 549219469 549219497
    0x1090c020604051507021e010c091d160c0c140102010b0d1a070e090f040b0a1808090301140709050f0a080d080c04120506150d0201020304060f0e09040807050d 70
    0x482c8403e440a07446101030036981d05d0400c102e203400d001c00f108015624403c03501d01661081900a42802001a280d00f4a00c43d034a80da40c0c003641900c2c010086103110700001242c0f900310703c20010403460701c02d86003180c100100c0e5114000d0340c1c00260b04c152002d00c42d9601074455540c0a005031004150304441030600b42181ea150203412890118824424002c9000020030781c038001c040c010350040004d00100d8561625203030031062000144c070180c52420000d4002251b11006000390f01c2009111410007800e803203a542c1e1b28400e038018404595255484801c0041d2040302c840c0a14464100355480b9840c05280105100720301c11100038841c0502c1019a00b4000341c0307000201c10030094090b107010601542ea509503040c00d4002c58110034024040e100701e000c144900014401d02038008041220f111000e400100134407514240c50080c050382091208000942c0102c211458942150910840910f00c000000b071103201c04a5007110148000304501062050801c004030b910b402500306520b01003022 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 549221969 1250 549220719 549220723
    0x200322020619091502010e01061a070609020d0602190f050f04051c02120313092a020102210106080f06030303011406070b01140319120305042901090c02060405 70
    0x2c02040c2d404103815801001c2401c0c890000c900081c00e0010b0380584640780c0410080c003a1a10b004114420740c2040c0020803c2da81e0b00c01e030303000e6a0035180041351600155554100c050482e61605a034003051004820000c5061800100940c04415042d200d41028150000d4503c8900360030020400c0814000d11400d0100f07903088606a460440ba4020300c820b4845001c1103008500c0e10083d00301c142c1c03880c3e5554505001020703006540c4019000201140c60301e00c480d0403a00c020040704c101c000300c464040d403100240c401d11903800d400f0744009840e00c18030300e040e02c81c007801852810013001d42540c01042095800301042d50454081030060f03c180c1000400281e40740018090390710685000607200c1aa036840d2401c54108950240006c601c56a40301c1c4001c400c0b28061510074003a000340b18072140500c24031003400c500c180e8000c55100d040500b800080300100390040044a0145018011540d62480b4455084c90354444180440c0c0660500303444409403994801d40c903043d5841441404001000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 549223219 1250 549221969 549221977
    0x8040305210301230414060f0d0503070308070908030c03040626010e091614041d120313052b030e06010e0c120702030702040b0904030c11042003220206 67
    0x104014084c00342d410180c4a1400c0301d500c00d0300d241e200703244c14580c04050a061082e940300700b10440d02440088100400d001613040c0c0d50800805070342003002030030000390080c0181da40284d4030740b8007e19040e40b076845080c03669101500c2c4260340d510119082040540c0400342c00c40b9071600c2c1c01c05036411450440807110391401130103601d031503c2d40c00000508000d01002105445100b2182c0302031310694810348040003c07d880c42d403d00035401e0800c0c1c04400c855100c60f400c001c004030710040400411903c010a015003015090034900350284d589940428000c015044250040351800254400002c400805c4101005031000625007040320900d00f0312808514941160720303070500341c01c00d170f902c0203a0209148140741140103807165944c184a035450b8008040d2075501d209450810401458400b04410141e04407801400a1000000600010300b91038400d0405540980081440c00b2008501c1d06d50702c10140400b80ca0842c0882048400f10b4166804403820f405160030303648085403070700030800710f1007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 549224469 1250 549223219 549223229
    0x1b040803280908031602190915051f031a1206060405090105070c030c02030102041e1a030c070318030506010603091b150518090a0203090115050f1002070b040308040305210301 77
    0x1d24117101c907096403609000d001000c3d514131403212100c1d1700e40c01074000074005850b40c811118110340340031071030342131420081c803113650781e4001079940010000e4101c016140c10b030481c8500018130040300f80d250300e4800380c4508540c080d40151a49281543c1440100c8200420000041c1c1c1800c0030300001ca42c0104010100c00d03010700c0c1c410245541070021a0191080d5401500d0429107008103100041030b9680700425500c5426004282840301c914102c030500041c3c9030640315076820400800005e00030601700503810940c45030b148441c2e950340c55041c2040000d902c01c0d400b2a45620100b0b040041010100c15a00c2081c1e0701d8240301d42c01d00714500311440c00c0302030f60f00c10b00c00009450300c400c6205400301407044000600d00030041c5031800383d0307002940080c0d6640d0440d42c06e02020008004180f01c001d400d0b01c80c090400302008008500304100c8142854002c000c0d40224030000c11110104030040016500404403a03554500d14078207685410742581c45051a541014100c1d843d400c0000c0032641128 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 549225719 1250 549224469 549224497
    0x306070c1502180901080304030b090106150e031e100c0507320d0e0a09141f050306040c0303020d050310090b010e1206070e010f081b04080328090803 66
    0x3940554031a1000c3c003503029150344c0a40b0380000000c2c0f0f03000000080c401d803440f03240c01010725252040a507080c0e80d45030240080030341c492407114a04a11039802224045c9004044400410614440301005850a00240344907002040c507440c1e41c42d068018555414080c0c40d1091804c00c242d03c43d4000105810310762519030034403010b40a6000d04c02e0010702258030509040c0c071401c49068401034081c400c1803c060707005141d280d6002800102c54810211740c09041d0094070324982e990661001181202e50f038880700c00c0c402d00b201050300c1e241000b181d4450f074864404103c6003421418007a10380089002d1030400c0050410402070200811001c2c4011500c06410101d00c0800010042e50f02011014043d50800c03031820000340030080010714280140d10540b100b8013092180c038011a0009030184050340820b402c603021901141c05c3c1c84140019080042080d4101501c4d002d05904640c4400c0b0307940c0516002080c201000340380704143d00c4018031941400b1420902e0716007825180d00500da44c01da844 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 549226969 1250 549225719 549225727
    0x110601051513080303060906040e0307060b0301061512150515070510020d0f050c16080318061602010f06030c050423010f0f1e051005040504021201050306070c1502 72
    0x32001c007000c0e141d0a02e004456440125214404260360380c1040398030318803c59407000414800e0900e031080c2610702d80081e01551821780551101c1000e040c982c5003080d015136070380c07400148a00e40c0261a10032000b466aa1801e1600c186152606441c1c0c501020301d00f042200d58100b0642d80e488446510800c172008107070b5210046e608015062805c00a4140c01141c000a40400300f00c486502002c000b20a14000b00150344900c08400998095041001c0803070410b9003d95002c00e81020146600a80c1f04808440072201e00303810508004058681c50212a0040060000d40c0e03028090300700c041c3d285030010402c941c03450307c0d11400e0018a10601d405260744207182801040c4881c44129010542c4a44008a50391420030018850091103050a80009100d01090044070100002d81820154110581c2a8188010400000d102095940070b01c4010031001405886034000b03404142e005000994484d03242400341401c101d0010400401c000c28807080f0000100710b82160100311805460050f02d03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 549228219 1250 549226969 549226999
    0xc010c03140d1802040c03330b0d2306011707020c100905010e040908030c091f030c09050306040510110c2a06030c04031e0605040302010c08060111060105 68
    0x440c0c0700e010160400d6030709040b21000744140000083c807070207100381c800700b000301401103048048941d4051804080d66036003988030100000c01d0341c041200103100d20400d541640d500e0b0b160b02c1592007041a1101c4640f92000341e56090000c4006c0c01990b4502c1c41d00f004d491400c000020400300d60600c0c080b001f074540c4404200c1141c0300b08038844106c00040c01c0080080980798010300920501e11070b482c00540c0b001c40711909818a8040c104110364030400a9096031542c4228044e1074005026058000380c40e40848a55622060aa401e001921f914000ba4410700c52200801a41c490380007a400790f84031b0350034403000510000307219101c0401d03860b00080d036250707601084841d4841d0b190f0118252107494403803003401031709110307510300100441e0a0b0300d4250444011300549000446e0070000302c3d0007d000800201c2e513100403414000d910b032401107900c003026903101c1084410541d81540140c0d9514164440142c00c050b280342c0000090900140300ea4203150360741e5442c5014001d09008555038000411 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 549229469 1250 549228219 549228257
    0x1b06050906130e190c0e0d110625021804050303151906021546090b0402100201181e050708030c0c0609060a08041110030605030c030c010c03 62
    0x250804042482e50f9041051108080c9541072052842c10352800040788102805200c0800e003504002c2c00007200520745848017814a41d00f603031500d8102c881009400c1881d03070180c80d5012401030f02da20300b80c01040280103000c6400b034100c01440319481c2c82418170000c03410000c2a2a031214203400c0700b81c1e10715882d9002c1120000300a0501d00b8102e20b651010450a4000c640c40d0240140700300d6800c0e003a51280c0d000320703902e101c220500446950099140e0b954010800c02c68140c40b1542001d4119003c05400c0710003124003a8a0a6501c807484e00c081c0b204505c3c0201c1842c012012510092000f1174800c0111000b00c0401c00780103041c1c00644c0200031040315089110100c060b000f400fa00c00d050707522078105d6100d030f000c0b0740a01c0c1540a84400c9407190f2030010165110010042c1174582044150b180c140d03565903018005456100300e154144045a0710980200c20707080f200d83c0d01290040c035040c281840d080c0d40f034954510a0700043c0b014421640c0c4031a003440380b00e4140c85d040030f8141c041d4031a88 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 549230719 1250 549229469 549229507
    0x804020f0411040602100f0c08071227030f0201050601080c0a120e01140c0f0307120b0409050c13050606090d15360b15060c03030906041b06050906 65
    0xb0a04103000c140001c8440d004500441040b40303401c4c080c440045645d4407e01282c50140151012070302c90710100b816644501001c009540150034009200184003061340c01306007409040c03417001e02c2800a80e40406520003881c1c85072050707a000a01c940d00340800040c114000c02000d41d610890080f5400282610860452406407100e0008100c813404a00c00c0c0340c0a4050010183c514039040400b191900781c502c000c5a091040c022111030541e15522011503440d1161602d2001a94842c002034419540341c0c07280881d0144500000c040c1140da49040c0300f007503503001420788071080ca03100400c82140c59174800c594641034110b80d4404503213224603111481d12426000340392214600408289103201700102c4009200600260821401000070080309203c0b6200740106040754000c04038500014207c0d4031b0b490b400c1c1c010300d02401e2002114a161079900704480c454800d9100b4000d04c001d20068000342c5611106401040d030701c03942060000307800c911841c02d80c5402500c0019030f406022824003411 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 549231969 1250 549230719 549230741
    0x1060e181905070f0f0516081605010b01030608100917212d1503030a02030310050a05090f10050d0b0702120a020d050c03070b0f0106140301060804020f04 68
    0x34650070700d8210040a007800300100d04070103150030003141d5100c0c082c0c403106000d894103503901d0768044083c48041318543c00c0010f812604017411035128001600000142c50a5050300d440c0782200341407420040e00f580c0700214168145482d140c0300340207601c404104451100041c0783c01040d40d140524012042046181651480000c04503400c00a2900840041e03441122807030f1101c01c1743c0307a6544801c001c02942c03000506252613540309460309907210084561003402c0c0360500382d59650840120741903522004011006030000420001c02c0081c1101d078034050b000c142c1e61210002c0c1000003041004da4040d04100e040a1075000061041d1804c561a0000d01006020300008580d50305d883e111442068a1020141c01040e50001c0c40406080030340d041400c2d80e034000d000c40d241244c003d0781e071584088135109441c002000b601c000b103081003401600820481c0c0701000d143d03150007402800044109030160050714100010440145e00181443c6c1050b01150350409402c0d07100d00240003402da508030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 549233219 1250 549231969 549232009
    0x50d1b06050a020705040b090f1b0f0a08011502031c0908070f02010320090103020708120f01080f01051e1e16170105060d0203040203032710030507020601060e 70
    0x21805581c014081d060b082070340e4003103d88540d1502c04010039140d80e1001d1581142e10303500000c03115a502a000740d00310710000c0002207180107500408040c0d51081c011044030b01030000c1d002c45056401080c490040403003014181e113000485000030740700d01c0340c4d41004422220030440246000b0b0241d126015095100d02159a54101468400358950701c0342402d078040b9140070b2940c00011144c0b9400e26542c0e65100b461441d201041d00150000e400418080d00d03128024411864004880c0c0d031038601607094103040440035858400b42c00d00c1e0559130000321426904150610501c01c100d00c011680804825845142c1c55880e0550030301040e48203543c81c240c00744090b09200702c6400c0d8030107054840e50f15542c1d000d64403982040e4181d56070801e22800da00300d0300411880d0b054602d83d501454000384000d05481c9000341c2e0800d0f4110380c81040c4078400d80c4013000d10704808513141c011940031005529082c2408a85060000652134000510a003000d000415010841a9403244181da40701c10f04982 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 549234469 1250 549233219 549233273
    0x52203060606170615031005090f0a05090d020a02040c0527030c03010e152203091d070c0210120f02030105130204030b1816031b1e050d 60
    0x6185000d42542c0c460725002c10300d400c00e50782610068440c058854500503258085088042d24418510b80c4000d1411510014040700440d00b9070318800d001c3d025090030030320544541044aa5913045a4018000454942c48008144612500070580019164040720b002580144d0984251410710030003d00f00080700235054025100716919140315841c000075070890f405034507024141822540e240e184c180ca45d074401029030010350b94401c1000d50211104414015041c40340b12009120501e5040c1100411052101800601204117500c2d00700c4c20300004400c2c0604150b08082d0000044070b50203400f90340c582702d443e0a807501a03c0e00c14a180b060380400c000344132000c0c04000094000780070f2503100d000410f504100c144010300913201070342d40000d8066559281c0d6003e00c0002001c4030482c00140c0640e2201495103581d461a44000b103000e41001c8022001490400240c888941c00c440300300302580c00040c0d040207000f1000700c16148145c2d40f22172484640d0901c2d100f1201101c5040b44801e401203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 549235719 1250 549234469 549234473
    0x20909090a030f050a090308030903040b0c060103110108040f060f0e33010609120311011503111207090b0301200903060c0f071106071b080c0102030c0d052203 70
    0x74030aa0703880c001e548103515203620710780455241c82009404000681012000e0011411030380c02150802c4100381182d1401c0d40d10030306810390350009450072140750840070040050250015440400002c01d281c0999030740307003a550f2980e12a420185c040d25066545040300903403100f6500981e01c20b4010011183c0442240d03a1905000742d0b442083c2c400fa00400c11110701711042201d401e4181c03a8251140c0500364103000c9002c21560103036406408200315030342c820407d154288100c000403101c08480506060450400400025072500380d14081d401035103c04803200301c085901c2d0282d0f148100c011030101c0400c400680500039817008580104801c01c072440e10214401c00404646206505868040d40c424596030b03424000c26041590130801004000002900f1310381c5440540030003840310f27040040701d460b0201400c03441c0b80c1584441c00e25900034003902008200020308120300744000c0d0300d45680c8618654a9480d000802400d110340400c1041d041515417070300e100c002c01c5c1c8205010070b141c3c0d64 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 549236969 1250 549235719 549235723
    0x60501080d020c01030504021f170708060109240f110609030307030c09031121061504060515090f0d12020d0e09010303020d120209040905070e010f0f030b060402090909 74
    0x5819008090312400f001c00f40154000c0c010750344199002000850b03c220040a40c0d40021003080d404810002d125042e281204188504980100c031103544943d8240b40400000d04202000d0b006580f581c190140c08a8025081030b00ca988000050719000c01e06444911003604c0143c40100c4504440c05040308210944000201440c801e540d1654248113111005c0070a44030026180030141030703100038203a141e2960401c40d15801c3c0250540e40281c90030102104400d06010f0180c074146250b10007515504038614190160f08080d1104407683c800c020300010703640181d07116407441c09000303003d1000c21001c150360795600300340030746e800080791040c3c100307049002034803244d0302c0d0540404650020a2202c1c503062012030141038a82c1a0020183c58150820660340010000d034104070464081040100701d84480c003a4a0516200f000109102410903280098008051b00000307107040340c1010410078102d0308440300040b00c1e08018601515225000494082c0c130901d90270541220318003050000203200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 549238219 1250 549236969 549236983
    0x207060f02030c0706111b0d020c030111090f130203070f180501090501030f3b0c10120905120c0c18270a030302040807090213031e06050108 62
    0x104480421089954a045100324001555041d00084080c03080340c00080300c0350301907204030400c01c0c801800c00803d0007181c8010102e03000340001c29081150401251a010480882c400750201c0083c4180d0201d0341895801e4056201018401c00d1451a003014070b442c0c52584441c0c0e00080d50055540f071400030b102811843c240c03140707400000d41048201800410301800d00c07096510581d120745010b460440114094030102e00b40c401003e40c0c94007120382000b001c6092404200c40d890002c1c45005407400c40352400b109051880c2000d80100c21081000e64494030700c0039100e10700741020070320948001440d500800389071000810a00c036980b40e400440f0040d40160034030740e04580459401480c014180401d03442000c8003010526041004501c600c161160841c070104a0b141000108012104820b4a0100b0b00003041c0c0c08a540041c0a1104071400d200500207001020070a40c94200f6a940010a4811038800a00001e5005441200b04040d02004411894104900b48401e507151403c403512010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 549239469 1250 549238219 549238223
    0x605010e010f0302030a0210031401090605120715230d1a0d0c03110d08120609071103070b04030504150306060e030705010903080a020f0d05070302061506030a0b0a0906090207 77
    0x3a5a4000040011490400c0420790780d016003d07000e007040c82e07402d000030200355819400c2415280c05683d140c101080d02d4042c002e21800e480410841d2510b002c2c00140d50101501c00b001c3d8000c24400d11031002c2203104181c0e00450340c58001c80040c440098004901c6110542d4003c04400241c40d140d4270440740c1003081c0401c0340c0030411851445d00000c02c51035040d1803400820307080c59000100041000610041e011001c0646203610b441d105030344641c46580030307007904911280c0c0351040c05901c1c240240070681c400c14038103080400c0c01d400340b003659a0b8040c503440240344c000d01c0c0c00010300309440b82c1c00342c0c0e00915540c0401341203030f600c10760090081c10950040b4800105040e68440c02c40c030b40000d0711811a0b0040e181c40322080d04503154002264002c801c1c0b0419440313444e040000f20b000c20403080c180115156a242d48411645c5802414941d01800d0601c54090740389450009994400480f9004100300d000010034507180c90100317817100d109601080c01c1d14500309000a07202c0b103540082c40390034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 549240719 1250 549239469 549239489
    0xc13090804091b030218010c112709032104020d060615020f01060612151a180d120c0512030a1505030106081f0207150f0b010201050402030d0309080d09060501 70
    0x2803c50707504400300c0c000c5420310069010b0403840301100c1d5001714102c3d0740103800740c0c43c5180e00e140e0508c00303e1350145400000440c060b800501d121400c520009245400441c018007646c6006940c00384982c140300c079501c840054081007000f0408568030001c00009039540032070103000603a80c604152110401c0002c1c85000b50203101042e50100f50107104001c1600c040d07495000039424210a07050003400c000b86200c900740500c4801141020000904004044042460b10f0740c0352401c041003072568103120741513401005c01500001c00a0151500a00142082c0c43d04001d0090141400c510706070309203035186942c440c00020300c280181c80c1e0300700c00080712103040303011500da988030107240c204e0f0400d04c0303950300d01d400c26805d03080c0e223040d050b405409000b05e905016040c80c8460311004031010341c00101e0050a581c0d006403150700b0105005400c2200c5090008121500d0140c000c42c0c0c444005005c0d03181095964426202000b1684040c0c03903082209000400000340365162400c0103140a0150080007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 549241969 1250 549240719 549240761
    0x1d0a17060f10060c0201050d060f05030f0102030c0f220305100e0c06030601080c040f0b0d0501120201120513050f01020309060f090703080f0d020c1005070306080c1309080409 77
    0x1c0d0541e401c1d05402004401d0410341c881e40f610000321484a0408000c90402000704800c03039040c180ca000c0e05029141d0a0300400c08246841b0400d803421804244d40d8055900500411552031000400e0b40e0919078803601503a0303110580720721454070100103641203084010f4010044180440007039200c51482c9640c1e400c02c0f501c0c085ca40310540d21002c05e005541d000c1404c10001d003155100d94040c9400c0300c1c124140e0ba0400c0d841d014200c0e00b4085035040010503100100c5c034458503c240f4040e031401803000b8400520004034540000f814480030140c3c0541141e10342011540c0201c00c690780c0028079400400b40c034014100750084602070f50050310103100c2441000042500c074002d014901d809240310100411509241d6a50200791380c20801608049003030520900fa011455400140303020a20100034100f2056829645421100043d102c41c04040c83c04805200d031010014141e64000400c880b0948801c40346030b20306010300320107031005280d0340010030001901807050700300b8922188600b10394000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 549243219 1250 549241969 549241981
    0xe01090602030d2c0a20030709090303180302060601083103090f0f0305010501060503130b0907180510090c0c020111101d060a020313142d0111090d031d0a1706 70
    0x1b007002602c07441985500050810000102103511458090348a800c2c0458450910782d84408482e5080400703030056000042002507660340081d1061341701c1c5101e01d41400d0f55200d00321020b48a075410303c0b802080e1070940c1003801454029800c1c01c00410b90000f121100d80e4458030801800a0144811500c66080900114641d400381040c5c03449844a00c0004058140300d8132840d81c101400342c915010760180c41000f060061450180000c1c0345500280428181000d02c000c00188005910142900c0e181404031000c41e82d01c448824a4150246440d10756000c0d1515994180240001c00311111440d020110100385040d010400c15861001e0585d141039840703121083c1648001c07241008246120f012020000300341c4504204042d680004840540344401c0e10300701d503406c0c0d2070040b25100c140000340451186017401a04071145212500c58140591b44001c079444a81d5400d00a042c062146088101814508001c600001c001012910403030740e254040341e40c13148860031540303250051000040c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 549244469 1250 549243219 549243263
    0xe370c360614060f03060603040f080a05120717060607150f1d0d0c0803070c050d0302090406140a06030c1806080a0b04090f020405090a020402030a0c0e01090602030d2c0a 75
    0x1e0760300a0040da43c3c5141e1b00e0004010301e03640020422201101848030110104a501780505030b08111034603170070f40d51034490440500c00a4010844000c00060b01e0080320b03013505c020403441d08540305940d000c0c3c0360440c80c60004200981c010b4440345032840d0126031640020b45070803125010709040740c0c00104071001311400c2d0301c0385c50385084100451107020000002030844401981d00007072518040707568640980d51141880c0080208400181d004645000300d4a05446400b0092595905d251002c3d2145070126803028954441e41080c150364a03002d4801034000c0415525002c04e213440c0b61a40e41e100c0101614455040e181004600e02e040c490350002c0c01c041c40761641454100c41c001110b81d20135070820010b440e009045c04224055038000c94010389546c0090340c000e01030400302103004e42500e18000c2500d8108400103040140044081000310340200880360303000a81000880e4901543c40d200001c030070700c044585559004840e42484810010428440b101d101350054110308c0c00c1c103800d80f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 549245719 1250 549244469 549244477
    0xe09040506040c0f0e060105180622050315180c0a031b06080408070605091e03031605090a0e0405070302060a050a0206070f0905040f0e370c36061406 66
    0x14140600d00c0c5c01107002503004e00c019015620031450140308900c990004070740140c00c00c020b10110603c0c6000481034075140500c90502800c2c0607002401468a06d03c51a06001c0b009080c116060352101000d0300c09400520488001d60800303050068583d0380c0349803020401c121001b015030204800314010901910404045003e203411040d60380c11719106807102402014040c02c140000e101c1c07003000e400c4c15440d140400d40604880f0010319180d01d001840c0c3c1d007203050100d81e40e008001c01084a041f180ea40c4079890004d42d41351345115400381d5524505186041030640010358044000b00d076071009903502c0783c010701d01d5110941c02c2d40d46a1700c038900241c51314002d00600c180400c105003410f000c1030a0a034080c44c2c10b10084403011807001081201642000d1810b400d03600c2e0305008100c81400303a03c0c2e1008060b2001d06114801c40340c240780342c0300c0041d00200390107054140d10201645405401343c204401c01c0034880d041018580c00c62a0881500034075480c42800040e1003901544482c42c076000c4161 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 549246969 1250 549245719 549245729
    0x6080708061003061a0a020c03060c03043306170f0d0f050405130204051008010b0a0f1e020c03070e100b0c0f060a0c1101090c0b0a0e09040506040c0f 66
    0x962003501c48404004956480340400d8041566962000841049255100c2d0742c01c03840600d5940d6a1412402c000d00b401102851603003e0b6110034103008031320440008407503220342c110124400020000c1104680c0d00c04071494003940c40e04400da140c20f400811b6100c00100e072012520b0700144030b01d07414041d8980075400d071990389a40114000c1030740140500440e10200da00d5140080c9040c0c1c03208001805c1032010303190501a654042001e000700c0c00c004011003401412400c152051f90306d84109a1018400c8065503010001e805040c01c4055000c1d04080b0f00d264449040201442401d1038025503501c0c0031038405201e03107c2d0300070000e101100c04018900554058100c07400340b1741080e0a2035119844900408a2403003110746440b140c0c00306000c3f4602074081c90700c01060744900b0940041074410b282c2ca41c4800c07039140070404070020326603551500448035030401c02e5440b100000780946010025151480e003100300c0d0702c10032013040740c00304021b84182d2262410300c5812703442e00021030380c2e10780f24040d13 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 549248219 1250 549246969 549246977
    0x70611090a080a03020a1509140f0c0901030c03260c06090601090209010c12021f050702061605030411060c19141501170106090e1b0609030a061802030303090a060501060807 76
    0x181c007c1104da0b4064a5403180442e404a95502d01e541e400d194055100c00c401180e802903a180b68501c1c2e030500000c0034000f012120300c0341c59419521498080da08501c001080c0d60060089442004c42c000600d8500d40148d041e0781d41c0394261100e2868550704c040b22405618003a0000216492900d44250340c0c2000d0103075109400603d00340c0d00d4826154400307181900f9481100e001c40704101040784980f40440ca08400441c5600300410040d2400c60050200030300b0826915058072503d80c8201035036441178001100c51001c0d4150004a0414400e40b64007031900d0103510040401d84180c001211343e0284202006100444603044807034070f42d2810b504802e1059401e0b0010024240b1030382d128440c121201000140007581c8140c000c1c100c1e08103c00380a401c0d04a49a51614101d0108141e810108180ca1962400303031407900080e202e46208200900c910383e01c2c441c1c2450f050100207076848840d03002d07048959900780b420299075903191411044a1050074600080303a06480356a00c64014205511 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 549249469 1250 549248219 549248233
    0x1718090a0e0f0313090f060e0405030a090e040321090c06051809100b030411040204170c040603120c080702040905010207150b010212250308060a080f060c090303070611090a080a0302 80
    0x320321741c050607032803a0308401191101c40220fa82c100d1040707150b028900c6030000310b072381e40c1030920041c1c4181d03010740c44403c48521803410800400e40000040201032136803802c141382da1229a40f550000c0650141c05410003070701000c0440e966030000010481c05804200c0100303500b0000d0100400f41c0421034140c4944008088101319030008100030350f40091140d00640241c60301312000c10100c2e08564810450014244240c0c3e4103000b060104c440709086c156018405542151510b0081c0b07484202001c0c20800b40143cad8605200c1c501c0c05992000da03005200303200b40d26407802c01034041d400122040e501100b20b0700c90045a40c80500c00c1c0300b15900180c001c0e1940e40062520400541c00000148400f81404ad13601100b0100c00141c0040542c82602d42421a05003e401d020200c8203642040f403207940803801c0c21050485c0007071490ba02c0500d456040d65201d000102003070850103590f034020f06031410322003440018203580024200702c5209482c02054150796141241d91070a0040c1d010b030240e04010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 549250719 1250 549249469 549249479
    0x70b070204020307051c15080a020f1207030c09060602070503030a0c060b0d05010c2a021c02011e02010b011706090708150a060c1e1718090a0e0f0313 66
    0x600036541c01200c0f8200710f41800d112070041043e040e808450003a6a954030b211f03503d51504c8014031302c8090b04404008002c10505c3d0b0b8080780010310039412451140001500407a4035002c01c129480140d540048114015075884107440089c183c28003c00c00503009080780440c603810700005644002c4119a652004403200c1c0d12094003c02d03450900d20f40000141d05580003003542400b0301814805180d54480805994480c3d401802551400116984c0745403004072025995501014401c0f044d609070900ba07000441c401030725090038164020210b0019910011745a507010740c880c544d1317800d081c4c0f00d52070314150070505c600081c00200e62a83e81b224011001c50101c0d17115260035944000076200c550284919480046e50540d0030b584000001060302188030308000140803000908001041888208412644c0b80741c044040700380700c0c046034040401d0500a01c00c105100d8999110090144286401d1086102c0c0240c101000200010702c1280c100c82c0c0744940001c103c803103062408001201150900c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 549251969 1250 549250719 549250721
    0x12130906061407080906071a100f0803040b031509040515060901030b01120302010605041e0e0a0804031515060519020c0a182715020418022101030320070b070204 71
    0x43c00005820446c24000300b0001000b9004420000009080c01078803031800c00e0707000415480c5c0744c000040d20501800d040140100000a8405581840352001e88a07030300c0c681e070710201b0b60005198170340c44035000d001e01c0140007010607440c1d120090302662405980d507030000e00c48103003000e10004091900200040003603c01d0148550344003480b0344004281d142d0b54900040a035101c03101000342d0040c1d060324100c417001c003038440c985082a42030b01900120704030703807114880b034002d92001400c0c2d00b039991b60360b07a02e05110b80d228002442e03406007000004d81d00c41500034005c0e000304450a5071403c0c1c0c0c080d007002c0c02d07000040362110b040e00148140203060810440c044640058040c3e805038907100c000000c51401c0c5083e4035458100e65083c5150f03808a2818403488603100c103102601d00c0340c03042005101d0051403085650005181c0706000d42d0310710748080360840f61100b61403400003140c1c2c5000080100b580c04044081100151540c00807101c00c0002820384a10444c410307011404800c0001400500706 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 549253219 1250 549251969 549251977
    0x20303070e0d03050705060f270d0804240902041406091501171501090e1012080405100c05010b01090f0306050705091201020d15061b02031213090606140708 69
    0x20038605217007016415a1045e15000d0161100c1e10980482c200b04040a0310842c4103082269941309210307100d0b82608203054450030b00c3d402c1d05007000f14000024091010040555500210074000c69000c2e40e0141c040f0070042035006d004a01c258108028012280700014260740569002810305803103490b00a00c14600c40c6200d1034107410720840318110802c45a1580ca024840c68544003401003045244000400351a00e5070021145603540c1d2081c448501044e00080c810340d800c0c4910b5840801080c20311860030302071548944d502c902110040f02c10307030b42d210082000f140e1062009029642c42680151002081e5004180c203804210a04202141c030035080f0139008502070502034030705200d8602060310201d42c240102d0b00c82c1e4002600b82c8440d4240d1007100b0880c004005079041e15400d05000420301e0142c803105409800c14400b48074190b60f8140900320744040840c0c400c40e9548160341c00c845042249202d00140540f40201c00104140213990700100c141c4412005403810405035030310681604 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 549254469 1250 549253219 549253223
    0x3050a1103070e0f181612020a08030301181a060c010c1103090f0112020409060f03050708010c1d01030b0310061a04080c100201270b061002030d0b01020a1a16020303070e0d 76
    0x21a40b80d12007808041d44a41b50f01903c0c102d0301b4522421090300501180140b5036110301030585c001c00c010810340c0350a582c01c0055801c0504042030b882c10389205416800441c1d24002d034030000001e01d10088200c1584080c2c41d101a80d01c1d086201010303045407641740d0248007a020740082101446440d03562185100364644072003490014280398880000c070044170b134150488444503450345020720034003404011500c0201540c8009004110300d50304000c180c14554940084c01100c4000b041e00e81384c0c060b8028a01320039000d0100c0341c0010700d445441c00540744901c04c90441209454100907200340d02d000700c6054440b0b0400070700040311000103100d94007200900e84d00443d56903c035102c80e00c2c51140e140d1040307140340b0000380701c841c041400e05001007103014240e54400c101c3d02ca07802031650b40100c10346014003c00840002d41a01c5040140d007040e5a07040020b00b520b248401c059240d0341c420000c54042e00c0c02c0040503c4c081c1200d50b09036902c2c841a90b66001040c40882c0c0c0085031310b400da1440d02494 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 549255719 1250 549254469 549254473
    0x380f060a0f090f0609020c010501030b0a020406140a021f0c1d030a02061303080a0203190305060109031202120f040905010b07030e0d0f0f050f010509031201180603050a1103070e0f18 80
    0xc2e81e17840700c80040360054011500355075154401003090100c0c41c120f1a4004100c030504503d41880e01c00b000c4e1584a00700c01c40525201d0218100140a000b800301030321990f020041005508c81d030303036420401401103c0784200403420b8406680e00030300141c0c042c40c2181d00003a004018a40b115000c204c4982c009101d111a241c0c0c070228044000340401c00900030040598000759182c038010b075051010407024075400301c10146854100300c656070b40501c02e50103c03a00903a4040c6150400c0000701e040880ca0705c001d01000600164010168ac1403100902c1107403541c0c40c00f0011641c0342d1800e00c2003440790940c003034002103e00b01138440070720300f03142009030582c4501c4680c49940e4132543d892034000700e842419280c54100d040300f480700310030030b00031f035503014904e503019614000d61030120003882c0006000700c811005520140b02055411075200101440d0000100e0b6050398040c0741c02d2100c4505e440505000f8000d0b400001500078048004034051640d03c0002d40300c0b651001c600403180d540400000141f4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 549256969 1250 549255719 549255731
    0x60403080703090501090b0a050901030504140712140d0c15140109140c04080a0308090f060108070320060901030b0d06020d1409120304380f060a0f090f 67
    0x514100007020704a110f9250340000078a000300240100c00310340d03c5441242010000030700080e42c080104c03078486000b401e00040f5902c480c24201e0002f0401e5204403114880e900c00401c0600f0004001d203500361040300c10044007080c04440b541c49100303240792803000c60261103401000500024010300180081d08000807074824030b100c0c0f004d03404403c1e448000e5150b5540480308544440d00c0103280d00104402c0e03030b113150130700c0c284080740e035110a00030281c200030700d060110b0644641840030b4406070700310300d040312000d5031071700700d800c0d1200b015201c1116161550030845060703c200e540c5003500e1250052042d801c00e2105001940070f0b1400381d241d01e0317000201c40ea101000614074405031908500e4003038005000715020000c503480a9001e000c6403000da222a0641c040b80011404076980301e030303100f07512740c3d20100c80f0b030302c1050a41c2c5180707455200407444081000c0c2c0760000c1c00700b00d0b01c580707007140010082e40c4966051242040a40c0141d0108503c84102402450102d4000d0360304510103560010f05 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 549258219 1250 549256969 549256973
    0xf121513051209010e1509060c010e0105090606031b0913080c0f24040f08090102030d050a090b01140901090c020703210807081e0612010203040f05070f08100506060403 74
    0x800c0c00301c070420b049a62020945240350350744443c10591101c81516055000e00025100350b5080c014802210b100e10000100040c62a0003904245903c00d40480240800c0c240030610940390041100c00314080d00c16110840103420b44110700c0300c41c4201c046c1c88140c0b0350310388110344030176100032a20035261203804014005c064102007006a03501424903024281071102c207203011840000345542459000309460900010036001c600561010360f0111801d661380b204800182c0c194090180a29007891402d010012800c5041c1c02024030307948600b4040c40303660f8a5280d0004030041c00540b07142c001582200501c0154402d07400300501e43c80500458a5248d50390307860b032218240220014218120210100d0091600080816048085403e2601d030f60304e01600c03601c80401c0340c0507401111000070070100f40d258560890540894490780020365691130130f410500074142003101c045580f031150000001d5400ea9040d840010b40d5003050180c02007040d0311540c0000f0300b00c09070000b580030504110000c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 549259469 1250 549258219 549258223
    0x6180306041202010c050c03040b070611040b091009120210030e0d031e0b0102031801030f05040807050d1107050d11040608280b130609060c030b0f12151305 69
    0x12207144140d80c0030444a40704000242990403010304001071003000e00403454201c0010055070265814505026154040e80c14100040c2146d80c40207000703c140000c0100f009241000240303060b4006403a05115a480c142048512503071a02c14210400c858113550001481c0503035461f44003400030310300441c3c5400c008445506001e1031510140c0481e540d0380c010b56036103010a609442d0148000300c02c011b564901b0001035203e20950301031381d4000c1c21103849440c0360f1b80241c0c401c20142103006001c20182c0b0f4145448080c03984440301c10760b000c0c8a85218000074a01c105c1d141c408444440000d028502d2508050003c2680e03001e40480d420713008203012548640f40c5200b488000d064200040c040070f108120703003d03415165a11407404504002d0202d50110701c0a00304d5540010051190010f140c0440c20722200034060004001c2041d03091110080b90a60700d42c1010395041000c0300c6d18403910401400704030303101c3c4c0d040091070481e41240b40151011011040c680c0d610110050b9000380f80c0c03020341d8843d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 549260719 1250 549259469 549259471
    0x10b030609010f06090e03191806092d1203030902090703090b0702120703140d0906060501170f01030f240641060c010f0c1704030c0206180306 63
    0x2005a992003c21280040302c82c0100ca000b40584c880c100806210310411507224840c070300c40313401622403514030000300380e100b1104120000343c1c191440e0600c585403840200f01d520070344100b15100152004504100700070707100e801d1100c0003221041900b00d103003243c00210075071502415003c0c582d84000070001b50b02d400035560311601c02550002181891464004140e000c0a00450110740c04038080140143d1070008072a40203070181001850605031003006061840340b0175141101c0717030608035003c1c200003054200c94181d90702600d485804140c1300801303a0320f01c4011140d1101420102c0010008564034040a40d02d40d805480b454400c000c460031070040c0c04044544840354203903144000c102541c009698107101d00b040400340e0b00960044030030070012554002d0040300855542c04810810380e04c100480341410881802880100d15800ea550b000704500d1030048003140000504c803d04000082590b442a40d00d23845150507000349800744089500104089484402c2610300300e48660341c100401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 549261969 1250 549260719 549260731
    0x9031103150f0a0518030909130f0501060807081b0d03020a080310060306090b030d030c050c0109060b040506010203090108160302040306050c071104050702071403030d111e04030807020909010b0306 87
    0x90b40e4242400390340c031402c542009000481e5500c42140741003540c0b42c00f000300c5210580807070300d211154803203403c45400711306a114018504600701c28990104501908070504841254042c0c60030b4683d15480f0907102e03c100607685480c0d402c031400d9080a40f6110400c200c07030900034070444040035100c0e50781006651040d550481c400d4a0f41108001c6039a0500400010b042216010b0040d020941c022035642c03c4080700c1342d800e058403120040e500900c00d500703030f0b102d501d0320350002e00144003030341800001024200311190156041c40005006540004101c4080400603510040d140d03030341080c82c1060020510143c020160200000070114035a401081c0c0200c1071001782c01d81e55440d52500e44201c80c46001d400b40070350f080000300407500c0d4011030020308130359410400034921151480003c0c1103101d4141664101854407152002d13400803040a00003c45c1402c3c400500c900a11181e6461405540b000a003100b004001c80401805c0482002c0c5c2c1200c0c5030320021850000190001c1e04100c02281c203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 549263219 1250 549261969 549261991
    0x10c0b0c04080a0f051c090b0903100c0e3f190804060e0a032d06140907090e10020d0b09151302030c07030806031e0c090a0c0903110315 60
    0x107013005111007070200101482900e610f103d80f2000042010b00b90014610501d051040041049541500e00384030340300d28142d070101c040051050040024041c14461440d05002c0d500301c0400003440700800e4262103070003070307414800240313228000041c070242d0102e422821658040c20119041441d800024070000c1446105030649a604106d07000700070890502601e80301d00d960220400100c7e1066551600ba071640d0320000c5400310581c5541c20510320742070f400170800e501c1d00b440010035002141b0b2280c0a28002c02c00d46400a640f801c0c448c058484048010496400c0380042c4804080340c1c2c1c2c001c0c40d034144120780100d109401840040c00540c404c40f000c1c111078841c00b02d15515898442e01d040040c2454540031400e5080844110900380100c2c900182481011030100d100f50342d0800c02c01102d800c14071070244130300c0303007582500b910398275042403003801500c030600400c41d001090300880d040e0900980d039075808645140c0f45c11107006541468150075024001420181d1580c040b070082c0320f540c481132 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 549264469 1250 549263219 549263243
    0x12050304030809160303050901030914072615100510020606120a081608070c090e060a09051506060f04060305061504080a14030d0c0305100f05010c0b0c04080a 70
    0x1005001050024080041d0750800c840c8201e00b410800300b01c6007071703e0305440c040b51504400701c010b800410b010f0b1030141c503009a05000014a03c40003e41e5415039a8420700792003110f141807141000510810000e000e81e0304441007280340c82110340340240d0b2007401d02c182038030f025564402246654100409110040c3c0000c4100b008a08101483c441044a0f1400030400144d0035101d41d0b4050040c5003640d00c005540c0846042408000001c2d03403c600d402c555000e0049603141c60b2403009004080307010700c940c0141c40000740607848a01c5200e055941010180501d03402c0d8034502d02c400040144400d074000001e01046201c420850040e10142c50f507038400182d1401e01604105414280800d1106408001c22040c80762a401150000c1c0055200141e0031580c51041811421405010200322820340383c00d508801e01a4541c01941c000c0c0f00c10200700041c60f0702c82003080324101090003001e0114100c484080d001030721480f100e0b540042d070784594074102501c2d80010380c1041404841038482420b00130f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 549265719 1250 549264469 549264473
    0x3020f010e030316080603010f020c0d090506090906040f0e070611120a05090112020c03031003030809060609060126130c0803030112030c0303090b0106081905060f041812050304 78
    0x44214201c0c011030380c00035800c514241004a15004040c10313108200000d0601081c99a02c09400c0600f684120013015521110340100a03617a516004d0390380c1c000100c012400050070b0400004031094680058048030080d90b410050201800701004910307a2940d5a903103040240c0c40034858003005e0091030350b4908000721072102c07203850500c0d20010504001f104010426510780c101f021070703003400b1703007824000101100020710302c009004054070381045010010801a004800d00300000c1502e10130346400301140c031740000050303607900111242c81c0c1188030100480e03910745c0550180d03041d00400b142002804111001f070070b11044402d982002070312120602d40c60400c101e11142c00003074480349006504540c90701c2c509500f88400c3d9a00a001c1c02210006007003814441e400c020041a0021034021555a50f110001c051f03400840d2a1a08405041049040600b1a00a086c080c3c403006091a01d030698200400000300a4049120403803950120048009076240154610940c3e143c1c541e03e840703151074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 549266969 1250 549265719 549265721
    0x37230a02130902130306050705041e0609060c0314090d0c140111190b04020a1d15060412060203060d1a0f130b071110060b0409140403080c070201031803020f01 70
    0x1c0d8101e401c80c5030061083c600c08000c1e404c085800c50b60490070100c2c0e10b4807824010f4071385100b42d8000c2e00012400511004405d14440050b100b1500f0307036a23404000d9030351021b08882c54076500500500289480003d030408404950181600c40c1c0d0007000c03540b04846a5807038915544041d4090329001d8a06c042000e4250303001000d401034042003c0180070603541d540107001d4059480ea00c001c201c0f41e140d00124003952075509c2b800b0091312610b000168400e012061850b15100c0860790000a03075480b800000e09801c01740103580840f01680040d03401103100c3d03650305001e500010082d907048145050140c010608110380c20001074441c11240c080b07414420300b41182400000c10420b03e84181134a0740002407808405070b41c0c014a180b5011942142e0041840e042010300350440030654100138020a9030320030381c4002d0040b130307003844001c00142051141480d44c002045030040c000c51060000503a6450f034071401040214814500007900f120000700300b81c800c8047d80c000ba4016400052035000000007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 549268219 1250 549266969 549267007
    0xa060c050d151d040213110909070305100801060f0608060d06021303060506060937080705010215070c0311150f16020601080d0327030837230a02 64
    0x600000f00518945a0040703180c08002c5031005c1d0200d81c0e144030030000c503140d000540ba6031442c024841d0340c0c1c078100108024054042a1201e4500d2042000c0c0001c199805100d64000c580ca088055403c040c6405004d42d5a040000c00168220b880c02c0076450010345548007c0250820803e4108409400c500708401100c10040c081406503c08000410903951024022a603a14030080b01b010f001d0350130400c40303803030784603a80108042d0082400089512540440c0600640c0d0003a801c80d0181c07c00f01a010201000c103940f00f80104d581c1840210110303204150760201c0301584c400b142c1b189003110aa0401da01001c80702254040481d506014210420b102160101005413000340400d50508545648a202c00145503003810b5480c409186070068813a5070720000c80e1240300182c991a450304001d007800100711203440590081243c11b6100746a442c1e00d4030080b26280722046020407259040307500070828486603042500c1a6902c0880342c22240300640d10880c0d0482000d61996500340f1030f0075100d51 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 549269469 1250 549268219 549268259
    0x91704030614011d0112060906050106030506130209090115170f06150c060c1b0303010308070201030b0a060806210a03020d08100e060d08040e040803011409090a060c050d15 76
    0x2107039000740450030501e04141e41501d244201b0324a490401d441c144000f0b20f10110001e0185052400008109030550300c29489040c00f507904500d0f54210040707840c100d2140f4901a6880f01c4000018020403a559500300c400c8440d41c1000074105014105410044408032140003105441e0f20800c4082c0c18041c20345e550054652510303505021035076011a0f103c90008004007126440850100c03020018408100f003682d001b2000e5070754a58490420343c1840e030048600780d01003400c0102e0042c0b2030801940e005d0807620300740d9400c005900c58000708244000d0340c4400014003166010050400b00080c450b120141e44260010418000d0118010b406020b00418041014903900410405102c5410b0510ba0081c8101da1100202c2c1042c07030481e001e4055038106c010000410b1040000b00542c01c40114180c0d600104288070690900c0c04006142100700d880d08400c2c0c002e41112800210660002152160f80c3d0510500f44488401c030b1008441030980f920440b46800102005900395240200388444 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 549270719 1250 549269469 549269489
    0xc0f0a031704261309021b0c1302030705130b0903210a0c0c03050d050d0e010207020d062d060e15010c021504030f080702010219050c0409170403061401 67
    0x216083d1121039050a41401800708500003040701d08140201d44102c404003e08071601c01141c0d07441d0301c080c600941041903a0f20741840385800050504d100004c01c0c58910200800c1c030005e0f050305645900194002901300001d001e024800c0c60349808180141502034444401106d0301c444c9081e003010b1800c0031101560aa140052812080b00d00b901340444810890a04003c5500034142c5000c060022142d803000e081402048907402e1043e92241c01407030034a0044005011080342c0c4c1035072600301c0c420428000d61200d00040001c00107295030b0042452040a201c0f40203611003898080d8244844079018160742d265124014404070b10601a1a500941a8158544414680d50001e0541c00da90000a07114000500f000c0c01e07800c40c24402c80e0061a0312224004403680c40f40340904a50b00142012405402414981502c01c2d10380f5101003a5a42c000c00103000b0034161800b48001040c10303100992300c0c0380100f2110161200719800078001148103100c000b40684140ca03880f4515071041e04000703911 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 549271969 1250 549270719 549270721
    0x90709030c0b0c031e0720010504090b030c1f0f021209150c030715051608010e09010605121006060f050a0e1c030309021306080715050c0f0a0317 64
    0x100d503200c01800103403041601c05039030700c401c40c2011501d9800741104452801d042417140052003c5102e01400300b103403151403861510403410704c01c5002d20fa840c03005a0300248061008001181030b5800100312080c002e0103035484c0701d1041c40030407407045c25200300652a0044040748110140e12000f05200610148060000c0114500340a10507101d54801e081c4a400f41c0516010005c07100001c54075035540305004c490340d8000324640814207803141c40c09040b84503d800000340b903071408806801400700142d61509016824404c42806074080070704000460f6603a4000440c46480c0d484000040f600b107140288040b200003c907400c184c85254002208001501c080d501000740c000082c1d070380d081c8590030301014098124021546440c2e07082d512030342640034840d00005043d01a4405000c2900039500c1003182844440640305480c103602c5400003030707070000c1810000c40c81204071030240400940303416803514820442e010b280c652020343c2000e00740c0007401142c04042e00b00101d00e02807010b8064406c06 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 549273219 1250 549271969 549271973
    0x1204030c030e1801030b090304120f1703060f12100c030209030f07080307260403080a0e0108100e150d0b01061b0804090507090506030c130f0312050d11030f0609070903 74
    0x10880f040c400241044110008694036107418010b5602501c20b07500c98a00b000110b0805540e00314144400361201003181e900f4486004000c030489224560150941e11002402c1d81070201500202c10385849a008880108500c881c1c140030300c00075001284d4001d600c1d1600b0004150a000c0380b0240c60543c0e42c8418801c01403d50040300ba94030301c94105c1d413501c80b4100000d8010900103001004007410701310001d00402040310100103070041c19010369640b003075020302100642e031211040d139008a84500075a000c101b8800143c00c40790348071802d85e01104540a0034030208a0f80d00300220f084a40100710300062201550140c003031801c0c050710076400201d4003d030f070322085071a20890049400c01074480002400d45030140261342c0040c900235201564a20344001032843c03d40101a0540e040006040c1c0028038824960841c8242d94100a03075202c9544003040070f84d0f89600c1481d40c91001900e41020603100031980c0702941c80342c1c4440c88100407a00d094010003c00500c014001410722072a500c003440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 549274469 1250 549273219 549273259
    0xd090911070309030b0a0608120d0c08072f070b1e0a0e0d021c200102030f0f03060d1208040b0a0e070302010e0402160c0e07210507051204030c030e 65
    0x21203030014248501d5441b00070125002c0c198581190070144a900060102000264020041007170503000821942404401c02c5400385002e64540780050b0240c03010354043c0c0090b0a80c0100120b01230504003c00c2240007000d81130584030751001200f43d1010503020081c40140c0040700d1180c030a4502c00f85000303c0072801605c00050b04074241d0140c440d1a200c0e00031511122507a84d03020b141c2c400f0000c0c0160740780c500b9203103151f00006000c2026200d8000703240e8075400001030700e0411000d40c40d02810112402211280c0340c10041500d5440490303107880c03101240303a140d0b50420041042d90b03689000d180600b4034101b4060041c009060306490704118005480c40440c42c60706030380d42440d10b07201c000881302c0050040c1c00b45c0752461450400006040c805c00426048120440b220b0043d90007507940c51101c143c5000308096801d01110040c039000d030994000e150701c080c1d8080118104541401703021001d10200010442d0210081201c1c854242d0a041d04000218030f810b0382283c03040d03210841084016 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 549275719 1250 549274469 549274487
    0xd080c0703050a260412030b1e03070b03010b1206011d04092402040312052802070905041104060504060b040b030a06080610060e06130e0601030e0d0909110703 70
    0x9020050041181500c4a10501030541348441c0380c2c88504803900c4500c03a541d41a40280e0301180e40f0b50702c2c0e00d0740d451050700a00416200800040940b01c01070020b03440c1c03400d1690300d010b1141c0c0c9400390340f102140c3c060444020710302a2984d610300726165203c07642881407420010301400d041c82002d003040d022020701e010119070820710940d00400c62202d503142240b08422900030259100052080d404c54040c032a501400440f405800320070440888500140d0341c500c11f41e0304110650341c0c0e0394407413200e84400e10110350b025246441203c0f8090760382d107101000c80d402aa41102c1d881d040c1c900b1002c50746010300030321010740780494080081c1e81c540380f03d5101e24465441407400f50b180200008401514640c400001820484240c420b2860000b18502000000d802100c0c00300e68020a40d000604020702a9030a4003181c000c1d4030812414016040c4400c0c80043c082810107449021103c810542807200541d40c254684030300d044a810641e03c42c040e680340c403c034400718441c20b10407030b400700f58440501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 549276969 1250 549275719 549275723
    0x180f01060308030105210d0f0905180f04080f030a06090b0a06080a0e2104060807300e0d260408030a11040e01030c1a031501050a030b1504080d080c07 66
    0x51003035100c00d001070500f01050048489011f01604c8811082c240d0400c0100d100d0505950b5013124654841041003480002e602d00d003881c0701c20b0040055030040c240d81c2d4207900503014225990402d5252031030140640d0044503007424440e1180c1c01007103492042d01031707242c80c25030071a4482441403c0450041644070010070340544946c860b0441c491000c01800119208100d51203202c0c038103406c09011010a0b4014030941d400565400700142030b2030302c2034403524034801e04114540d641c46031804112071100c00d41100a090103039a00520003164008122004c0c2006003030322030406418006001100141c00e041c41809145403207801c000006280c0d0b030803a41d00050041c000540341c202e100303100d000d5006640020054070a500000b0050108000d240c0080340c000611f01011141c000144090500041c0d4081d1501000b1074203200b11903028502401070400d070b80c40e00042100106e4001008050284c40f0018107590000e03050040c60300c01d0010351403010590500741c8030307403c0c0804c80005a00c244180 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 549278219 1250 549276969 549276979
    0x6090f0c080c1818090c030303010f030303150b13050102010b010f0c020423010b03010e15060313030e040f1a03160608040c1502010506040e0105060a06030221180f01060308030105 79
    0x708110000c00114642c0d00c0d40b00c05444003540c2c50712484d40c0d5011100070b60302900f052203412a04a1940750000842c0e060721202101c0c00e0781c140c41e43da000d4001d411803190f0521810041e40300482e00d0041039000c1c060450f40100a125518509000a82140c0c0710050703250412011004002e00d44e90071640b00c503441541642d00013038a210011a51000e40e130b22410b000740b039001400000684010706006103041c0c0e00070506c44800390301c1e00e01d00310140e424441c46d400d800030014030000d81005a5120002d0146009007000e065010011001404540c2802d0141d80e03070300c0d581c4010781245825100c0c2807c1820342507008207161400760500b40702c030b500b9920801c1c0070440300394002001c00c01c40001e100c00500c000314985039801c65810b0040d01800088920703c0c015407901d450700d032117001c0500034075020342000380a1034400c40c10000210302070740c0049210f09000300f054446c4140b10050b0301041d03118144a109003d50502c040c15505c5c200a204200740d446030b0b04050051002c15100d60442e811100100c0c1c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 549279469 1250 549278219 549278227
    0x1e070f0215041a07230304081c0804081303210914030c10030b04050a06030308061e0d02010207030f030503040c0e041a090f0a0809010212040e040305090a1806090f0c080c 75
    0x20b8601c1c1c030040000e01d17405004044a01c21607030f040c0e0010203802aa805c1c0c0b8140c41044144624a0030540050121a00003400313400205010a030807038002d140c0c4103150422040c0450b100d480c0e04202900d495468581d81c810181200d0b186684004048081c14501d01e0043c3c0107116040029a07500a9501a43c840d062400c0e207112200d0103039008040c2e4040c0580140310601c1e1103520b030710080450384004d0b404aa40354000038000d20344400508010fa102022041da28240704e4103201c2001d45400040741544541c01012001ca481161120011072090756040d941c1c0c030f4545401d0301503c00307544c03040e05200010428003000485010b07ca008401100d022411142c0d03550150300d02e00801c11001c5c0500780100d24844c0c081c85510402052002c4c420703003c071134202120010440d0030348100d110703d1194916600100300001c2c455002801d00803801001c285800d40c454400114109000307080302e50590b5900070410030413000b800b811b105001c40310000c1000320800800940100c00c0140060700612000be = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 549280575 1106 549279469 549279473
    0x1d060d0c03030f140706020a02160312030902010e090702010605100c02030c090a060f09050109060e151201110c030d0506091009021e070f0215041a07 66
    0x4140380951a6840c1101d048055a103080108615040d132582c07035400c420090107074140035240c01665615155006032038020048a620981014a20300f040030821103500c1004044050a001c01c00000c1b510049400c0c40d1141404c60344402035005218003154154400800d0724416240e07075a0090403100160b07500055040005c0d450760000000780f8180c10040b04858000c2d155200118103640c4420742074404060380c0d00000220365031080100700002d81401010010000e0084a45960511402d1030405445900800380200c8d80840444401c010035401080e910f600c1130342160300c07050200e030099102d901999841c0192400c2c0000b00e0a0307440c000c10424000c95150b034030003400351b140c4a00c2c00040c1d00a040e84064203c5100341d8451902407000c014101244100e2003d244004148100014200d20f8000c00d064040f052206021075043d015801906035116044603131666400c1c = true := by decide +kernel

theorem cover : BRFrame.Cov 549100719 549280575 := by
  have h0 := BRFrame.cov_init 549100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 549100719 ≤ n) (h2 : n < 549280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
