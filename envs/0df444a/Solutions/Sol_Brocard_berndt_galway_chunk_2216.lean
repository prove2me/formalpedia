-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2216
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:00:53.364201+00:00
-- url     : https://prove2.me/submissions/57e7ad45-8e46-463e-b27e-ebb0b1119629

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 398381294 ≤ n < 398561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 398382544 1250 398381294 398381309
    0x40b0313021824030f060906011502011803051614030a0f110703030810030501051003110604150e0402070b0a0e0f0d0c23070312021b3102120a0b0901 66
    0x140400090b038400c0500d1000c6080a13050310345007400c40c54541d00f048412a070000c06603000400410540c480c0341c0200352076481700d10003000f20039003070f0503040410802030002500b00b00b0040b58030b0301c031100b0b2810006403140e445600042d01c054109142d036101d4014000707a0006c41c413420140d001c881e0086400d0008100c180c40542002070841d83c0958060130b000d01154426041c0c2c0c0e50100000d00c003445210300071069211420700d014594502000302d880c03030514081c020310f02070102300034030200d04100002038a81418114403403400319000c0341c0280a0f000c800b0b4001d000c0303a0240180c2100036400304000c91041002e6401400070754035116500c2c3e04a08404000071b003207942c2c0c10045650482202c4140c5401c405900b02d01510002c078610f4400990001e83d5000d40c1c2c102164013050301044102c0e006c010804500c0003c0f140040010180350058034064900a1030018120107070380d032103503420000801c9074011502c0703000c5521743c41c01c42d900c22148880e03501e15101a101c041d2a0030b07594903040700d504 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 398383794 1250 398382544 398382571
    0xf030203060403080a020c031303050c01030c090b03040305120109051f060f0513050d03170a110405060c0a02090109090215070206161b2309220305040b03130218 71
    0x30b40c0e40031102040010f20b442802d540c00c1c40010b08400c003c0c80103103652007000880384095410750904c9410401c20b410000d060614281801c038040750401e009504460680c00300640700d03921814144d5040c8a200700f480504040100085640e4510b40d00445c083c200d0b40c8042c03040001a4a01c600010b0f2060040901045510400c00c0310944034000501d40914890440700c1c2c40ba03510008141c50f00d51c941012408070302c600c110501c03000f2012601c140d20080b4600c0500c9140c03001c0305010312921460051a002d90000201d41a6048003000b220542550140030410316681d684440300050000ca4800ca00c64030312002c0c0507102c1c0300c2d008203072072600790010b000c00d00d80101c0b001000314000c4401d904580d1011980340c081c010f2032110403014010a28403070740780c180e11a45401c2c549a00c0031000d20903c60400350090003510b040c6841a0001a046160b170b180290380d603410141e496028540c0580025103001080010310705540340340d081d62510030b5485d9014540c1d0010891182007040b104070441c0300c04d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 398385044 1250 398383794 398383801
    0x3121b0210110c07030c0501020f070302150f1b0c04060e040c12050f0d03020307080109090b070818030c010c09080307031409010e120c010206060609010203041a090a03030e09010f03020306 83
    0x2103a41c821490348008480039072904064142c51030138106958000e65110803610340c01c020b01d50b010b005422208a00002910a290850b03002510050001004191101011800482990400044800e00c1d00c92400080c031401e01c08036415960055217403428000c44c10101c0024441004280642c000c80e800045d803505542004840250019400400d59151082c000072501025007807201c0a21101070b0b94000d0b960386080800501000010307441500111300d00701d42a4041440d5850154000040d440e0844464950140791980d60801c01c155070b1281c0400034003403080310015030001da41d980854444840351591030b0015510ba0041010140c0840c02a400501208481d40010b00141c401414042c0507500088081500c0320b1850f927080c429684081110300391913804001c001d500c904210390a528080b000300000703489003e80d1141c0300e0144410314401c082552403d00fa220945405840160707025540e0a00810b0100c09007880ea010700c01070000400d60180d20404c420580e500039004114585 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 398386294 1250 398385044 398385073
    0x603090302060609220b0124020607110304090e0c130c200106090c08090c030d1704170a090f06140f0a030b091003020a0519061d060703121b02 63
    0x1500070301d08031845c446a282d40500721010340f08074031914003070401c1310107642c10010405842c00e010084010005414680400c806600050301ca82c01415441c080c1815050001144d1840c0a0394100c582c2c0780d41009000066002c2c0040e40c1c030020002111006c01030701002d00100101c5041d20760010005920051403406c12000410004504690700000101e06540301c2203482103490903d02c00c0700040d16041480b0603150f00f00845210100120003030484031002290140c507034a80400504050300f15400020248040c1c032503030ba22590300822510396186060380000b0605030b59401041e0394645020000b050440c400c80c03140c0780004007034508a1901e0b41480c0c482500ea0040c3c0c420310100364072043c1c072007045e868040e03c1034010380c80c1c40803505015003107104220410400740c01140c0159211303045a08512103150860046074a6800e0216102ca1808a80d54002c80440811a00920001001010964400480d44000060340700801c01040c90294000840850301c0240006a118074525403021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 398387544 1250 398386294 398386309
    0xf1002061305030d1a2d0111011b260405060408250c08010b04050f04061e0908030105120c0a17010612050604120801270b030f070303020706030903020606 68
    0x11406803044038103029420003804d0a03107281c00c2051004040c0082c514049050211620b60429902c100103403204400e02d080f10290141245818100110b82045500050382903114815400400f620141d8040841602400724000c8441d5a50441c0c0002860b02c10020f81c440102d02599001014140a48a540f64208590420106a903118a240d20700c1d5550700000d08654001900c200c1114242c90324004145085482c1d580c22940540d05100410118000040c1c401e54099031141e40000d074a242c80d10382e40a0740c40c2c00c540022005290040100c28007860102850403640129003408203890b036045500d80300c2c20245d20043e000380e0005030600122503005901e800500907103000081c000d94650007201e03c0403109005440c0c0341c1240003440107000b207070b07d0920301801c40ca0030441c4481d450410000c81345203001d95220020120784031404000041900140e203145001012600340d07003948603100c2c0d20b401c1240f10807405489102c0000800c41e000b40100c400d4290560007a0029079207490602000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 398388794 1250 398387544 398387581
    0x11106010f0b0304140d0f08090f1c0509150c01050109090312051b1201090605030a0c030305072f0f10051e160b0703060801110720031b0f100206 64
    0x29490500050241748010412009040c280344d54000300300c20810070240400002900f50101e0390040801c0f5010310200107040c0d6181801d0003480252040c1100381200c59004100420342c2c012107030744404100d011100082d00361010120020401a641e50782400119640390780c0007404070301c081101600e01104c1c3c0d446076922081131080300d0207410700c80128088642c400f1200040b41e500303030001404806524455100585000c1d03009100404c1f4640f86e00c00704191900c401020007000042c0101009400c0102e1040006a80b170400341c540c9401d00303042c51220042c05100d004a440344904c070018a0001c0038121607240640b100f520f0282c66040c203407090307202c0d400b011010310350411103a02c10003004819403440d203004800090082c00c0685004055502c40d40c45122160706001340c0207980600305040364120790740300d1100e1008044841c1c0480503031404030070203641409401c0c1505010b82080d195826a04005c50708113428403401000c00c0071000b9460721700340c01644543e0000b8060140080c40700c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 398390044 1250 398388794 398388803
    0x10c17011404060e2403070812030705040510090519030209061002032820071809060e1605040e030711120307030e0906011716030204170c011106010f0b0304 69
    0x42144d201c1d0381c01c1158a1080d204c42400614040128502003001d45085042d003030214040d07e601460310007250390ba038160230714501c2d41d01b0000006c140c08500032030403203008041c0904440040e80e01144041d000d4041881198052100d100122140440960402c000e0740d038001c01aa80c4c075101d110901c003400e54465404400c0d0b1004010441c0d1035180840d1903200e030504010344010300b5030341c0f04000b00b416030010810034040c1d9003081031a841c20000703d08070341a140581000d036908074008400c200035082d1480c001d040300c0d15240d80d41721a441c021621480589090600d41c15a940e504107110455444039046030300d64005002040008240c011841150341c8020034a10000d0342c075602140c1036500038107045020170b05403101600c035170a02c480642d80c080c6007401d000070075002c51010b800141d60002c00780000d502110300b1000300740f4042e80c143c602410010f816900000084004140d9030383c3d00b14580c501080040c040d8a801c580300046840c1a242c5402c0f0404039903140c00341c86001070704003600465 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 398391294 1250 398390044 398390051
    0x131404080f120423060903030a0218130603110105070213180b0a05070e100c14031e0430081c05090d031401060e01080a060f120302010c17011404 64
    0x58010482c8550350380141d0081c1c902907609034802103052416488800c400c040764202d001001014100482030300ea00401d80701c80503944540a120a40c48a4000e02c1000e5100406000b0510b40c03031001e40c4030409407071003003100309aa900ba000040d40c0780c1c050340f180203500070744008810000c80020703041080030045d000d07840f4821040c541e403194801d0004a0b5804130780b59440081040300b0707074081c07072210075080180d480d880558140d1900030300c0c81102070b1020340320044505041100c4c0301c00b002124040c101c1c000d000d01440b04c0112212405500c40d128024089006003140b1100146082c000b8800014140742e0b040a00b80c00da40b071140d5900408450f40b01001300c09085420008a405503521510600c80509444140e000d00502140c42c20070841c111a6880030040c001d06400c42c000c2c1c4140030003402d000c102560344100b0750000d480140c000c85080242080c00180c060400006404a54442e40090007400c10030301003158512995032001980d560b840f8010041c008520b03000904280d0040d0010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 398392544 1250 398391294 398391307
    0x6100302070c09021c060905101403120307020d0201060e06010818070f0308030415110a052203050f060702030a21180503030a1113090e100e0a02131404080f 69
    0x500301d801041c07000d049103010116034106038511b40701d500094a08120104940c0c14003e003d4543d00d10300b4041e6407407980441001c001c05030303000c000752464076003844041c03692480c010754025117604031003035200090340c00d28a0100300c0348006590780b8810941a951b03620250307144a04500c01c0322961142e4500c1d401000004a90040030104180146000700340030b40c0c3c2c9090034607100820581442c108a0904d207420144010f8403844011980d0310111484c005440b0b4110110855421000d00008450340c0740e0910008100100455000d0400c1000800c1d50100e990307140040c0d0b120b02ca01c8402000182c1d4421461846160030036030b0100c12007007408001800080c44075400031a8058803010f8070694004001c20110180c10f0055070200060703c0390050400020b207000303042d5900750313010302404140c4805061056170402c000c00654075050700c00a008510540c03e07540e07214810200c00360700070320461200c1c0461414034001e200011551540d03111003655280c80302c40d002d40005940f0540340c031040040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 398393794 1250 398392544 398392559
    0xd0816080c010c0f020303070207140114040f030309060807080a1e0203240a08060402092d0f0705040303022d12130e070203041206090204110a021506100302070c 71
    0x741000e41071140000512105044003d003a00355044400800c40d407042080128165010480c0d804654200101000425200c03005844104103003d008501541c0458000307210b0350b56103075650440703001e51500f01600380c071140308503a04070003118404081040702010490f01401076005604000c07642042c8030b143e50113503100341e00340e901c00c6d1401c840851145c2005501da2410b00e0600d401c554003201c0c03032902103140680e069200d0a00400191007201c1a00c009030300705c0030080101c41c0503001c0032914407030074150b40c0d2024110f450560700142403e418500240c20039000b40212019282c01d07400829400644198494003090020220072010300607400f0300c000340d0f5003044140c80500803503041c580c50300800246000140c40307070b0303010022940091090010994001c001c560580e00340440805016007282031032000381c00380207002504a4a440006412407140001a1003140501e0b42035620000042c0b8211684900694030594007050410406007098001d500a00066126400311244240d071480c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 398395044 1250 398393794 398393797
    0x221090718020901020d050c10050c300c040f030b041703130b060a030b0c0a210203180d020c010e180103050606180f0c070228051c020d081608 63
    0x2803107503401285681541da0140041081c1c0c00c400c6c60030314207000c5007001c52980c4502c41c0503100c1d0816a5078001c40d9101d04041c0441d0342003442c100700383c050003540740e80403001160801040c014001c608000b05040c80d02040c1100c0c201e6041c10500304103182983c5821440000160045440d0741002e10990202b40c61132002c0c41c421045042008180d4031036003040001d1040c018165845010b1240090002440c0020740f61340000104e50690380365401c2c00c0c000c1d030340701c1d000303100b0391880c0c0c3d03402103400c0f1003960300b50000d502c522801c000c5411319004008055544040d0805030002580003045100010b51084800000c1417038020024081044010702403520004207070001d66140e00b100e800c0040606001d041c10b44605490321041800d46803120707c24400c940040d24405a5180011b42d0390705660318001d80c14451070031070f001d020b00709803140328602001019200b694001c08560f40044440c95144803c1c46055801510400c2044640d43d901c065aa00c004406601c070000d950040c03010070360080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 398396294 1250 398395044 398395079
    0x90b010e041406010e0303070c14011407110a050111070b1e030901050a050c03040b01060804060204031e03020c062502031504030806090f010518041e1a0a02210907 72
    0x400c0080d0404600042071a110710000b1402503004101c000e002400a15010f4100c40c0300c03003010005541c65000484850640933100b081c0c4c480c002c5034039000e01a061740080384030001140d0016031150780314015102c4120342407403e0342c150026101008981d00c503100402c02000c0400700c800741c2046004071180750384c2007510040c2c0c25079500ca00700300404025220b51504907191384038813429840d05940ba100140c005024601c100202e04010500b08052a01540c02940e40a907644c00c031003a6042d0700901440441206030014402e201c084105400d00c030048515450b000c05a80c600785406158661490f01c0c002022030f051b105691200c81950000007000c6e000324801c0d07480303030480d0400341e08112001c1d0f0b016042030a8000341000411003943c036102480410300c2d880560000d15512420103006c00700c12030381c025108203800401c441c108011000a005c0f00003000d0f005000c1910340d074010305d0807400b9106c0c0d18007541440820b0f2003100c00070381c03007035a070b01410f88002ca80c0c0254a070760b9008a0700d0b5000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 398397544 1250 398396294 398396321
    0x60a0302040f060c020d030c1a070f230d0504140a08041a0319181410110a050313050a02030313051806011b06090b100f0801090c090b010e04 62
    0x4a0140310940035402040010083ea10346001440c03c0c2d5000a001c0c0d00d00b0060007024001c2d5203800508000200e41c04039050045070006080034546043d0103800104500b070300708000341d03200f00320b009608020b4201103a05d9009454203401c01001104002c028a006081610004001100845142d00402440f41001c2c8a520f142c0e84607454103044240c02182ea0720301c44003210043c810002c03100303e142c3d43e03c80314045508020400858a0040c0401411321080240c01c04600600c040d403e940005000b6070200b40e601c0041003904017110b281a010f020300800040000c1c02000400d0a40a2620000c0b802601500c143c1300715408a3340024135640c801d0103450002140034000304071a00d8600c0c40c20000c05a00300e00050741d4600030380000c01c580c009900203490101c160084409001c41c070f1b40288840c5900c0100c400280c00d01d0240c101005c0c1541c071614903902c0d69001d01203406241030040a034540e41c009549200c1c54107005e0301d00b02810b070341401c2c98100f19524040b10165a542d010f20f90307540514 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 398398794 1250 398397544 398397547
    0x60d05040615081b010c0305160b160206011211180130030806130b040e030909160212280c020901050a1a030a0b12010b030d0801081b010509060a0302 66
    0xc1802c989840e0442e6449458140c02c80180404240e542403800c0c10b01e143d09180041d2105464a025175140c0903101070b012a50700145450400c10041c03a000302e000d50141e4a00d0303a491240c00b42d040b40e91b82400d009080c80140ca50160034000b450094503580701c450000c3c03184e034043d44d100ca112a8446000da001d40302040403a0050040b0003040110a400e2141e60b03035040d107443d050380d1009041c2d11805002c0b14024003d49107403001c15501c0b0f40c000340415100500c240202c0390000c6005541e50000c10410b4403e02c1d042c0040740003d100c1c00301401c1c00b400c054002e4038012104100d400b02a0704048480150542c1103002451030f001408031451030010b258682d2503c00700c43e401480012081604204e003c1c010405d424401200700c2c80354010403120751465155650303120303850030000d80585042241c010100c078011a500c0c85040d0400d00c10090181c0456900b060540c408540e6000f007881403907242d8104103c10700c6060b94441080c0e01c1c44506040c01c1e8500f5a291000c03c031203621403564040060390 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 398400044 1250 398398794 398398811
    0x10b060307031b0f05191115060a0f03020d1101050d060b070b0711030f090a030533040210080603070f060314011502030a050d0b2106071d01030902060d050406 70
    0x100c0c2000e0402e508071803902c484d8510400e040178100d8483d90360204107040052620101d50f0384151141d0f6a07000310542900c103c54031190000c0713045241640c03200d10136100d002010904005004001c4100da4004001c04004080c2d40c403041140c0c01c40940c2c50b030402804009400030103015002e0303540140a04964984d581403503007080031a40c1809007500d000c00442c1d5080d0000305c440003088d5020a80c1d1402110340d07035441c8000054032079015030701c020f00c1c0740206d10504100c1c007100011240041079021344903040c9082d60143d483e40708800c0350000e500000740005280d0540c440c20482c0c1e0311880c003504580016450f01300010300c01c80f00d45c0c448400251a45a40e0400c001030000740c43c01080e03440d88064007800b810502075102d0040d500020200100468401151961600540c17900040686040d162414030019514841c2c491003e1485c24403d140c046800544034103858403460b110514175465200f0b00000440c050901c0540070f990052040c4000302d2402c40300d00c078181c0600c0c41070390300003610003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 398401294 1250 398400044 398400071
    0x14030112060b1008150a080f0718050601020303070c0501091703090c0a0b0702040c090b0d0b010306080c0f100311120403090509010303230f07060b0f040e03090f0102010b06030703 79
    0x20b10350384040d405034500440301220241c010340300b16000350304005080342d5035000c1408a641c0c1c0701561300142d43c070b1040f42030110029001003041420b9a629466203116502800201c000340c40b000da81c002e0059008000180480e44200e0301005405d00c04d800204001e01c180d12035841d60000001103502146000051100010302084680b0750079009440c211040d0f8030302820754505019103a0040c0c0a00c3d00c59000c8000f503442100400d018011501d00036484181406c0c3c000010050701e9020780c0400c0c83e10b10301240010f0009031064030010b000302034006019003401800000d11030003150509054562100210200a64026241d0746c07099280e513004608d000d00b001000c80e0820fa1010f40100345843c018008030384c0c85582800075180c00b8212101e11410200c80c12481d02c16043c500000e8007000c50344030200803158120b2031030548101c2d00240100d03410402c0004840e00319076807544561007007003036840d0780c140303085039014542c4140000141100e0040102e5030a80c022542c1a0000303607121a01c80060 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 398402544 1250 398401294 398401301
    0x904081b010f0e0c0a0b030603010207050706090603050109050f1602010b0418020301061a19180303020a050d090609030201030509010b120a05010c03141f0f080304080f0a0b010b0a1403011206 84
    0x1030f0201c0014858910941c1c085920340340b29009411350480300200081050b2000d4045540090788401181c9a16684080c0102080003d015a5002a0400c000012102c41c10701495010782403103a61a259034403540403640140001e2010001036540341d00c00981990b03143d2041d200003070003035000340003001d14600c101070840e005908007100000340305005144240540c17056400d1410710810301e14a1107902c91054400e1005490424030211160101000b055404034025504611440450b0b2030107a40880503038043c6991700071071000440126080016620940025400090b040c0001451140101c046a1010300300c007042d103c5940300c1400740c42040401d100c0c09507001000d10741000440304000908a1034140034000941c11482d003da41c0201c614842003460040404c2c4415521080e503e00c0b049841e0380040c4103e0301c05004010b042c1603a1000070071000340d80b40e0b001c0f05181c842d0f800d11440204e1504100400001c100d01c1d0415040d800d81d0000086020b414038595450301c125240c540001503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 398403794 1250 398402544 398402561
    0x72307090e0a050c01051b1207030e0102010e0327030f0c10050403080306150d0906060f051909051003080d061a0903070918020603010f0e240904081b010f 68
    0x2580e00c000300b8500403c070702191035020003c2c01d1910a5603200d50240c40e8810200492070a44a402405001c0c0b0300c03140080000d00340280709494120741c2220040059080303542002c008203458004000c198070700d1080396100c0c10b006606200740e000c1c141e44200400e203000d00c060409501640013480070540b43c9001e030600032107240e60b85021443e003410341d511692a40805030050f40901790f501c43e82e01004600c0c00541e01d884110410410400000d070400101501c283d01c107484000e1124500441c29040c03010786e0b080321080c2d80c80b16440351490428204003d0000511421145103c141d02000045256004040800c00807001048043c2800750200c00c13040c0c030001d00d41c108030007040070201c00c0d100401ca000845145100003ea84001041120f60a80003180c2c025405280003001080240104400740c06444040a512500ba50b1f40d05503406d030140c002500101840c0809451141488c0812400350b01520540b030171400e03c00c48406811441c4200101074429944030101c020041d43d1070f100300b003c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 398405044 1250 398403794 398403821
    0x120f01090b1f06090302130906180209010504020405061c11040b04090507050412030c03022404050c010206090304090510030f050c011e1202220b1b0a120507230709 72
    0xc40b5180080c0034081c81e60301d100090246801c18880b291491441c1d101e40007207038002e882404002001100d241c40310215280407845681440c00200382030070030b4407c0d501910070140809140403280c0c10000c0c1c1c1083c5124403040c01d10b0f240c01c0503c664000500251006182014180c2e44441c00c0ca180034041c0c0d98010900410400148030402044501c4480c00c00301c990181051043c075010750130102d00f056416011303640c4400441851032460f100702070ba0b0610850081080e606032803504401283c40e0601912a035100303510510050180750907550146820000c8458424000c50341c3c2c0d41d40700c00c121801d52007540c2c9500704124005043d60002c2030088204210000d07218602c01d2480c0c058002e000d0a620190600d030b02050383e2502041d480c1c07850300c0c00441903403003030030403a030b11100c031810369021404191074070707232820240054500006001001c0c10b92041c406400040003010440c0c00b6013101d20242c813564441c99012a007103030340a115841000b0504040e0006608040ba410700760b40c01c00100f0306 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 398406294 1250 398405044 398405101
    0x605030a030512100f0611010e0d0e120a0506040606030b370905010204030507080d0305010803030402010e03150106020106060e03031309020306061e04050111030a0806120f01090b 79
    0x34002940502100c4034840d21000883c06a25400c2c600b403c04103c070b42007138858090103074010921540010022802c00c1007034009100489865015640b60820842c030b62000c80c0c010714001c8043d00c0d118a9042624402c50115069000680c540c1803a0203425107064580703a0b5078900c103000340542c64000340d030322040210700d603080d4070070f0700c00e071609000c544100f00c003120200c1703117084426004990003080009801400a54885499003422516044d081c418104213100e107825200300e01d40240180c904031154540698210b9803560015107075003417544040c1d54076003da48074204c0c282a40203003140c0606600da000050450903c800134102c1c5695182d524400d0b4401e110250324860860030030302c2544c485141c0540c03680c9600c404101c00340a0301c1d032801c00b2403180c1c1900911140300c0340090002c80304266030f0701140d550120480c0d600c03803080c2c40c0e91400082c11103000a02508000b44010f041002d40802c882504a00c42031113030846541705401c032420100795085c01115140c160201c00810030000058 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 398407544 1250 398406294 398406313
    0xf0402090a0e1015050d0803150108070c0f0807080c010e0f030c0a110f060c0c03010506060415080613020c010b1003141915060c1a15040b040912080a060503 69
    0x641d0341c0140240400c0070302d8070384e01582110260b100c0310400a00c4040d024200007221890010010303013089402c1121403030501004500d0b9032142110034000d2f1403036110144e0541c0c1c0f94660001100c0914000d0b902c2500402c1003600040c0010024817440c1c0e0b600c000081c0c00104084c409013002c9020720041d80942c0140001240d5100c04140004401d40c01034900c140c50807140040b51080c44840355040d171201c0c0115814008440109103541030f02400c4000700100da507203204020580c055805000190323540801040c2c0e0082c0108002030300100000c09000300101c9001c8008141c2c0e002c0501d448199440701d075011110f0a0001202e03041a413035080902880130400f01551891000070808076180d1070500405020702d8090f44035155018030427604030700c0f039038503641d01030f00e04520401c0c116400e118400010109030252407603d0300800503a4100300c0004441400c00003e80b100d08045035019a4480c2c18000003001c0028003481d212803030b02e803400b081c5005150017048030070365442140a9000500315 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 398408794 1250 398407544 398407571
    0x90f060601030b0a330807260406020a030b03010f14060a1208250b06090915070507050f010606080f09010c02060a180501090302061006090e06060c030c03030f0402090a 74
    0x520554000b146460031090325581221051030004190f0b404504810041918041e4405100c1e40b207031f00c95881d41484078000a80d010324850080c0045052011203d002c00c0019169030028015211507290100f688034800d000a0b0841d090b410300f4140d0b0700d0703681c050211080b1106040e1030740001c0c1110000701040c5000800c811380401c8a0300280901c1c1d000030440c00500040e03a0800c10001c0e140c1e6200b04040003403910750615581950711910800c4040001a840c101c0000c00f010300310701c1001001c0795030f15010810b03a01e0ba04404400c440c17034000c0030340c80940301100340f090070014070459855880a0034070b88052059850050402d0502e0303410141061686034000660f550484106000040c09942600388800f9000c00340c070300200607508051402041c9640050b00380e01480c041e03000d81400940d07682d4266400840c9100e0000f261580e00001016882e001000d07042010103442a41e18002400d1580740c256881191200d00718a010400d01c019428110801c90384451010010004541c03080c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 398410044 1250 398408794 398408809
    0x10020d030c050339030c090f031605010807140c1c05160201050304061116050c0d03080103080c1e03040306110f0909040c0909060227010f03050406060e090f060601030b 74
    0x43c00710882d0001e03035039074100c489518480c01c0b01310142807201c0d00c0f81041116003040d6844945498814009803042d00051302e0003080c4a40c5151001c40c0041c980f500c0c10303005444148005000100303201e0480d9000c0e80e035590302001840c0380b05000e00076080482c40c000307101c100810102209020010f00b4807140342d10303a1340c03174200b00e02054090030302546a60726450400040d20f4034010000d10b43d038000c124048450041182c4503002417062042e58070078082d000900c00c81c1012240081e0001e8050350040001c00c3c0302400a0443d21400703400d603400800d80704500000c000c40144000103644c40040c0401c00e1040502ca040041c0702c01e0f0b2509070ad84000440b28449501807800c50350303c2141003c000c80c0070000b551101c180241405203080c4000c080e035040201c002e4004695030203060940d101030001048440513000c0f2188016122118107083d40c100450003400018001c48515903a0701021a280ca0702d0729680d441546002c0041400508903490070382084009061581850300703200030149213940e08030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 398411294 1250 398410044 398410081
    0x23040c0602061e0a0209040905031806090d030e0301020d06030f0c050604060504090f09020312070b090d05070f0c0806040f022403010605070c0923160503150f10020d030c0503 77
    0xb041c2c000070f511000741d03020091040d4101b450b0f0280c07801460b101007010103c040d1a4020f61000004c4640d064981030010b1071003441943c2c1d81c00030f04611a000064050f00141040d09030180005040070415030303800044a1a41d042074924104035400c0000b0491040c00c0900580b00c140e03a482e04003840d003400a4894080c6000702c4040544840c000208801c2c0e40c2e001c454181e4000f01203a8526810310400103d0f580b10580035582c08c10b4140c00075020090016034124210001e80d40c40e8608912a2074100801e00402070840c2c0b040303208400010f41100c10808140103d0040b19145907490103441002609903e10704529080800e55401c7d524840d4101e0680341120700074200b0b540c1d600340914104a1207400340e001020802c0c075040e5001c150700a041c01424030900701504412454403000307400d00e90100080d1002e00090010400100305554801c82045c0454000d00080c0d03050906030002092881c3d1140c010300184c1c00406024004c039850300400098511030309016186042081c480501d081c0c0c501c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 398412544 1250 398411294 398411341
    0x601060e030c040501090c02070605040e1b040902040905060111210901031d0309040605060c06010302010516050105040506101406041502120715060f050f09070323040c060206 77
    0x11550100c03540c03800d2040d650000c4009000300429a1500c41c540003e14015130f100740188a41c02000c035a15005070111400c1d14000305d03601c40e0b10b680e10084084050310911002180540500c40050f10b600140058405445c0c183c1c0c0229031850607000051071070f004c0000c1c0c000603034070200d241000c882c19640300e17903a082c4003842925541e005100041c1c5c09456541090654107581c070f212401d41d510044054200c04004580c14050345603070304200f0443d03000308035201041d500940010001580660f0051601030220005403602d040c1035114103085641c11103007a205e5800c208108490b2401f00e490040141100e40c09403030001102c1e01c04100302d80558042c401412219101440e592070081040e140c1c2d61408401c615524141072030043c0d008a804035002c500a0708001c004154028240e5015040d140042c203078408614511003008000070000c2d2400c01072642c0e501d8100401740313000d00c4100000001c035030840480e040034513145060000c81d070f028004541048052000c2e080100007030064000b400c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 398413794 1250 398412544 398412557
    0xd03050c100b130b0f06040305060105090903120a020304031205130b0603070b12061306080a17040e04030e010e0433031101050a1b0b07080906040302031b160b03160c05060106 77
    0x803a0108170200700302615184d1180e40481e00000700840041c0d95810380f10161540180364445603040d82e80d034040d80e0104840001840000b44104540b5030103558000c0c001e140a00e0240d602c07c0b07005080320010342d00c03801c0d10b0140703000010511166200c086c2c0c0044e402e5004084062a00040b03201c2c40c0104043d42040162010100c0c0c0c80d541d80d0512110b400c01c0c54001005425500e0b40d002e940c414602c0003c440c1c0100143c4041c2c45003a4042c01c4d90300302c0b0103c1c041200340e80c0c1c40b80e41c04c440e0f40102e40142414440c080030000300700c0d01d4911030310b170170307404018801c1800e842c0440290729140910b041c042da9040311428240001210301110018014003801c00607100d00e07080109442d10350705a1050340e5180c074003a1282080c0491412094058038203070321404c1c1a510343c0380d030301525080211806000f581c420030441c1a44181c02c3e0001c03152500010139183c0846030841030f1104000c540c0e01090325400c0c04000c0c090261011504850320049030700748080c079402d0740c0e81d034a0f03102d000500c990014080c1e03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 398415044 1250 398413794 398413811
    0x41a15300c0307091109031b01020f0a050613030309120503070e040b030a020616050f0d030501080f0d0f210906050106090311040c0c0807030314100b0315060403020d03050c100b13 79
    0x288181601c0d0101e1b0014203071800d141d903c1180c0e0945205001d13030700b80144905547c00070b5149000c40c1d480280c94019000d41042e595020408400e00112001141016560300311036000c03500c8140040d86803c3c1599407695242400701009240d00384103125903114a2801d44003181680e40001c84901082c2c2c191149a2600325000d00000c100c3c0c00e0040203400c500501e141c00031030803008550f00b03038603505a480821990740c030f07021312640c0c6009103140c205031030340409a0384801902549000039500ca41d071600c0e105d40d000700b1003000e142144a0740d0b069a090344402d011410803801e40103040c09080315103070100c205031031500c40d1079204880040140c0110b13030b60384050902c24460136200080075044841240d44044500d0000c004203034250080101a4016010510711002e1450745011031300c1c0340300c10b2411500e1705080c642d00c001524410590019080000000603110070103a0400709029031903440d107902c21a071010342441100d44000302c0c0755160171010039803551000f5000f484012206000284101d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 398416294 1250 398415044 398415071
    0x1202043203100b0117060f01030e0102090d05061006030e0604290c130f150e0d05160911040b1210090e010e070905041a15300c030709 59
    0x120a50002078140c06a64090503000280e5086110500300a0783c1d0045c140c80e03110810034526006894581c4d01c9421280740c0306007903101c0d80003a840d0210b40c2e000149011240300c0020000002002d040380d4681100b002c0247c51098400c000c8020641414140030451045140b207403180c4000b0401030442c80305000020702c07004456281c130201452038480b0300c4213007458001103100390888800014100392148000ca901ca102d200c10a003200c40b0707a4010050480c22000c29110101c4245c01c0d99080010301d860364012403810000d820215a000106203009800c105814041d01d00400c40c0b503082402c2080108082e01c448800c450303001d031881c0001000360b1500240d003150700e440d943c408403103d414040030868812044d40321210441c2c4c04421154030701d0f620504141580c1003124060701d03400002c0340114200000e103101551200f51010840d44480004000840c580b0152584405414041c6000d03050300c007010400d1480d0b12800c40040282181c440c00113965050349010307440c20142c4032002d40c103103503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 398417544 1250 398416294 398416379
    0x90601030c0501081e251418121b0102070602150103150e01050412090609031106070507080102120a11090306042a0e0717191a1807120204 61
    0x1101c9010324170380c5410300321000e151580d4a4600114408415403210b403260380140c00149042d003064902c3d508012000088420341e80ea660005034110310110102e460703900302403084505845015401528903040900020314080003a0090010b56210129044411090000f01030440380d000a4102c0130b0742c2403400c40e102a1100d2826181d10350f080005200400020b09401c009086160f83ea0120741603a4610460717008080d03101c007406602c5d0001c0b00740700300d0031b0010041100b82d0062040f2180c2c1545c0740f81030303800c907445107030b0251a941411007070003000e41550065008512001c404941040f00040000c0c0d00c3d130324040c00052800e400080302c0091140002d044c006091031060702a0312069640c00c2620507850116a03020014000000d00f42c10400d60940e558090500501c3c2003203400700f5080c1440003456951003a00c124a110541d401460b0f071200d65180c0502410780800c41070381032031a809082e5000742d907150b40c3c903580144020300016554840e500034128007504128189909505500350300d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 398418794 1250 398417544 398417581
    0xe01030f0f06291018090906090215070213020c0319140406050408010b01110a0303090503040306020708131502190206040503030a050c060a0b01210f0c0215090601030c050108 77
    0x460146000707242d14040108101d2801e0304040d90300c196a404480011901c1785441a003d041e0014050341c1400340002c130b0703071010708031130f105200c00a1015116000203840e401da1900b03008412500140d084114206040580415952040306600381130b002640e0988901440402d1800c1d208a000340d85110792182c0d885c030b01c2d1440c80c1140300351f8464a41000500b83d034014000c0300c549600700a204500303940700380203412807000c0542c0a0b04482c82556401c41c0076010307442094819204c10312000c004502e0620007000154440e6007055524524080344450a1000354022103d804004140c2d070b54054010070310112803080980b00c408136900324400034040380190303004a074043c40040760b8000c3d0342e50000c5c02004d0f4445040100c8400d5602c903c0b588080e80d45600ca494000740740c1c3c020800600e6050280e480441c12503040200c0e4081c20b2081150440e10580185030042e0b010181c07500d03583e030a00700040c0d0481c1108000d0302c0355604688403609504a144030b00c60412084800061660340c441a07503c86 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 398420044 1250 398418794 398418821
    0x30e030f092404083007030c0809100e010809010c052b0203130c120c09020a120908091e060301030f021201050702071d07020d1103040314160e01030f0f06 68
    0x3143c50300c0e1a007095403100b821138804281052505a02850780413400080749200b000700d0580c0c5800d1040c1e4080f6070302003007000200c0e020481441000040d0707a880701201c602da0600d559110200000e14001844143c0190110302180d141104804400b580b10040307810011980f007903200c6000880300501c00200030398901d4150140b01000340300d030041e08140c0b2450b50358056070740c00341c5054640035054000803100790020807400c0d064504026400282e0060500b00240f0300741204004c0400c48040152418103100f151519000100c8810525060814000c5031060314444000e0b11022000310b19148010300010704100d81e201070980031036680b40707081500e42d0041c00080c4080e051500703000c2d550b603032523019420020420000c0c1d8085034205a910364401c40d0140c1c0181180308406074151114442152096100c1c0800c000c040b011812021800981000c0d0303000400c00000080861001c3d980d698000001c080c1d6880b0040012403082e6106152075a0442a283d520b50560700e44031000b8000c40d2125070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 398421294 1250 398420044 398420047
    0x702040203040f060605090f0a0b04090209070f020d0f441005040c080609041b17100603030c110a05040603062306031203090a17030403030e030f0924 66
    0xc108400c0c007203060000f52090b04240402611041003003010081140c11000b003813002d0001076102100782d080a1607080001d40009048101600030401d140e030200c406030041a10040704410240d410420542040c7c1d90f40b510f85c02c1481c0c01400109406508100e085400c4151a00724540002c45500080404d0041c40c5000030042081c20395040c8400403240e9554170a004074000840d414540102e903003212581e40c480c201c1d5504c400c1081442c15000d481601e82e040150031001e0700020620b142d00c040d00040000c00e07040c883c00d018403483d0190801081c0e40b500d09002e02000000c0e04021240600c90380708403404007034000040403942090940e88056805420b203e000018480154400d50701c080c0c9102401154200250304103142071015100c01307070540c4c4442d101c070303c00d162000c01454000d0894000d40390b40345090b0701c8090079820841d03480a4841c1c2c0000522040642500c07402d1040a11040650305140c103c1607290385a0180307030b0b0301c0740c0603040c1d80002d803885802e507078600d040c10710035001802e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 398422544 1250 398421294 398421301
    0xf120d11010204051908060106030501050d02100e12100e071a0a0302090a0603050603010b04110406051806041e060201060b0a05161b091104030c0510020a0c080604060c0503090d0f050702040203 85
    0x170185c124865280c03580143c800203c2c5140c420702409050f20300c0902079402d41310080d0b01380310074010321800c91b50800c10a400748404a50f280b20000011041030002403100314000c2c0002c0d01101d6040c0c20101040d408100304100302e11a14203818108148444820f071070700d03003007071080d80603110701e050303469200e01c4121020070304541540c0010300401c030a40080050400d80028042192403151400040040622080206510840080a0f1509910312030004081f4450109903590010f421004440300e000000420380e1462416410050046100900080d445c0c20f04107101c1388501103280b42013250000d039081d052144401d10200060f40b100b001c4910030084208645e0304c41d05406000e42550601c0d0583c0101d61402044c1c4040d070b500030b11500c4010346468104040fa03c11250004158060b20f018400402d43c2800a50001c1090002412152500785000c10032206411000b2040c08406e0050262000000421402214181c01d0801c201c4602030001c0d28580a2120020742c024000000c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 398423794 1250 398422544 398422579
    0x4050a080a140409020318211804110403030e10080601030510080a050c1302040302010504140a0302100903050c060a0e0f240405031b01020604062403060b0f120d1101020405 76
    0x443c1f0800c04101119202a035682c2907079241c1d041440520342c01307001d105140e43d02030040310043c203d030803801100e0010f55041da80424240c0351000801c45240310046010014550002505101385408075070400603510410800f4201000243c4005e040564560000301c1c4640401c03002006440f0203800c450a9210900c0d00c2c6a0311008040300303500480040e03801c0e2a410125000b9201540d905840711800e081c100400c115042c0c140c0e04d02d05e940103110761800405600e072981d655105040c143e85036030542d401d6003485868548c2e5a00d2803401220708108a403a404ea0242150361030090440d0400000008030300000c4008014001d0a030880040c902c00d801c0c0c4000b448010b20403280d0940c182c482c00c803022080206403d03107020850f030250308002c00107000260321368040c4e03008589601c10342c41d00040c20144404040c040e600121a00c0da40c40304541000d1800982c1d000c1c50f1081260784100d28160f41c4c0249841c0d84029101000340700d4564003031a8400d80030740699015000207449051550404442c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 398425044 1250 398423794 398423797
    0x705040909022b0507060e030304170118030f0306120b040206030a09060c0905150427180b0105040506040e0715091d0103020909030a09030f0203030d05180c060304050a080a14040902 80
    0x1c3c101c1d140d11403d0300001d000b5020f4040250300302c500901650030b281c40d240c14507000c410000380c200083c1d5030b900040070300d42c4081240403040344d02035a282c0261003281c0d20301030708880650b00060358178070203540404001494041c03016409035060f100c1607140d8840f00302d202d02403c1c44040003810141041a40301070301d40d00c42184011580c04462403020f100c96401040d00380d2080d4015003074a5030584181c4030010580450800d8450314445001511840760b50015010443c00d035001c4400280c1c41c00100319901d41809031030f41140c0308030340400200400e1100f240c1c0d00e0b081072050b40404d00c2003170a070500c100d00911004008043c58048802120f000c0b8140000ca10424001248106034260115051090010a03250900483e841d5a8145400c2d43c40d030007911000098102da040c40100701d00f050360240340c080c00b80990300c0d00c110b0540303031815042d009003010384d0b460059005074814820040400e8000030030070045500968403d41d0342900020494002c1c0424a020000102c00200000e491782d5503030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 398426294 1250 398425044 398425129
    0xa02090c09030d08040b04030f021204091407052701110102070b09010510060c020906150a030516030c05030105060313050a08031f0806060910120507090c08070504090902 75
    0x9040c0e41c10f06001260a58080b0800e4401600320b1013041d00180001e8000c0c0c0107071000f001c02e401100c55801c0f40c1080d504c0964000d40000100c01e07142e02d01010280c081081140d0000401d041086c205007404035030000104003100d580080203010302d43e560742a40646c04180b8010501030081d035440c007a5042c800e00043c41650380308440e41c64900000c0c01400c241b950f01e015101c0ba0303559103034040c2c983d808200c0170f960007420a0383c0c44000c5540340d41900c7d03c07810080c201c0c0060340c0c80c0890b8500c3c000d90140080c0440004000505060004400f0400c0d4020222030654008231303140c40d103d80741c0143c1004a100e5549000301580300d2508000e0501c444940558400e0302081c40340070810401041150000b035003440798102c030354402c801040c41071901e201c0c22a131081110542d0b4200c00d03580d01002d0300d200c00041c016a0260895807040c001208140192040c1c001300c0d05214000d42003c100042507440783d4460310301e06944d10700d83c40d03007155154000f41c3c802000c11160408641050000c9190402442 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 398427544 1250 398426294 398426299
    0x120304020f0a05180c0909010e25050f0c0a060c02070f0f151b051207140105010608190f060303080f090c090610200102030403021902030307020103020c0a02090c09 72
    0x30040802603150410b401801c0d5a0302803c0d81c0d8650054810f84000f0780300c0a08588482401884040f02e0354546a6245000340304a00701214035040410756682d20005080003180d0b483c40d2600392042498125048926030302e0070503011607958642240070b50070411130381c5009080d541003c0192807215070009039081960440400801c0442e540c034032560804050b881a0b8003c000c02d200c1040a40d0b006200da110103108681d42007110010b16500c460a091082c100901d8540020483e071040c0800d0080408944130440000c00c260b50609401402552004118840c0c210301d075007a0082912080d00003444943c506002401401d45a00d005406c0090031515944e078541c01d500020009440012249e02d04d0314003901810301502c2e52428090342c8030f44003120a0620210191005400c1380300080032001a111800050f1039013840d15000f030608020800130000c03840d080004202598010084500315a030900740180e4899019906904003240c20030080e40c042101381c02c01c14850b0b103090050a284008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 398428794 1250 398427544 398427559
    0x10603050c0a1205101d010e0d030e0106030b0609040212010f06060314060d03030b030a0803010b1206090705030a0f0b09100302030616091202040207080a05070b07110307061d12030402 81
    0x3900600c1d00d01d400d05a101811940c404101c0d42c0340f0f074a640d40004007000110186c40391a81318032829038203440300d110140c62503a00100807600c2c0310341d041c0b090400c1e014101d002070140e1487c68444c50707100075018103020300c541e06040224086566007071890a051900000a10284042070005002802580310b2040413038105150603161100d01001d292054500801400480405d038a040b4014040c50000035014404d10f21903901081401000d0760007002e0000030a0740d1181501003607a00c1540c003a01081c010610042405445500700c0241d075401112034500217450702072002e940340034150107000e29030032500000600c00c1c2c0303000c0d615003032095034006c0e01182c2c103544800d00307441103449004009100149900e041800000040c0301c00070a900d00041001d4240299034807207250300d0b84000d1482e00402e0000410300200310f44916103550040c82401d00244901402001c0f40c0c0364840d0b040700801e09599001c0f028241801198241d2100c0740c880d0441b2201d0010038003c0d182540309440c141d00c101f40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 398430044 1250 398428794 398428799
    0x100309120e010e090108150705091206010f090903020a1401021306020606040e07050d14010609060b13140607020d1b0b0c0f01022104170304080a0f0c200a08010603050c0a 75
    0xc02040e5039040706e991500506803103d03521040901c9406c0500741500704142040b0f240c05982d00d40303002d040d500310007c020780b0ba254500089810b0001860340100132450400350620082500412405801074020103ca69034140c078005030380c024460f41c043d00030020a10000030449070350019100e881048141d9082190101c0080705a59488481c400c0365030217480c0700c640c400010090350807000f255a00500200d908c036100c0d808001a00c0d82c80e08030b00d4130141c2c00b16812404d00c1c0740701d0310382e4003c00b850500318414240c6100070503401d108400010380030743c003000b400138104100e124038001e680c68001d0324a60340a8540d00c0c400700300da21044d040030b42403040405e80315852170184201c0d1101b5004c41d00745880d44684116803410158014400d031001200380302c192108600000c001c41c440c070f00c2410410380e2000c91001c064568800c1da07484c5001c0244600c40b0300e00080c00c42c100d80c00341070304224000b0020815180002c8040b40d55802c034140c4d41d42080000020000c001510b8644500111900b41d005034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 398431294 1250 398430044 398430049
    0x71707120b0a150c0203010e060a0e07060c050c010503060f030f0c0a14090a09080f04060c1509170f0c0f06010503010e031306050d020724050106090e06100309120e010e 74
    0x3142e01600320304403d640506101503024044c1d0024007440030300089509101b00d914642800c4045441d4083c9540b10002c00300d240d0014840355015000c00d050002e1080c0d007940707819989114a04100741404000004114180da50a0f42c180341c941c4000c04582c1b07950311300050076845014500c403141c01140425808640601d44040300005104084c004004c41d1350f451201070301920b401f080a550f00c82e002c00024010940342001807000c1c12803900c0740d0440d0b024034540b52100c5040b80c2c2c580b4240038030f0140540d0000da064103030500d08054505a00d41c490302d64465050151144000881c03c034422480c00d200c5103800422558121038048008010750600980820b403030703210701c403a200071100c0705103414072003640100080e16603007805400c014140b00d0386d07686525144010065201010800c1c50420603828114007503e8054046843c103130b0b03502464108040020b41001d00100e101c1e41007040428401440b030342c405100d1540015944410600d10000500811760720f00106000600e40c1c0d806400c81e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 398432544 1250 398431294 398431309
    0x20703020c0913051c09120c0302090709231224130308070309170d020d1d0706230f0c010608030313120c080c0d0e1008060603071707120b 61
    0x613500030002c0c1610404e002444031035049000303820300600045460110f07009401d02100c2e51154816456404c03014150300420828481c0104044200044050140000f940420031084030221061924492042c1c604c00942e240801c0700b5103240c01d02c200382051911080320700d080141c07a50f01c48054416030710b649450040408405101401143c0e005020607992071013640035140482c007800e00c5024880d100056000203601060000e03224a8001c60300051103110f501c19884041109150300c003070b544240b8030f0745d900d404440c49108284406841c0c07820220140820a00e5118800c202e0142c1c0c8030a00185440c4980040070301d101c2640c6010310120304140004101ca0060b070920b4480b030128800c2d90380d407009000e114603d10b020840440c0c03041002403c0a4003500c21a141c0d10040d00903942a01c03001402c40c800c4100d0584902c00403c00c900b000c54001c1e003900d030807507401d0759000d940c1e64910070107581d0310b01e03003201c60802c1649640070002d400d60b020b40b50400000c011082071040030b900d0010007542 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 398433794 1250 398432544 398432581
    0x6060906030804051203070c0e07022a0d03030b0a0303030e150f0c0a03020702100306090e12190915080601090b0315040b15030f06150c0601120c0504020703020c09 72
    0xb2400800080c0060300e005595403001540c12030840c0e152400d9030f42e0f020800c1e411030348030310190300e803c0d400d00840e60380600c0511007844030003d0292007244842c011904042d120f42e1841d008240c1042aa010b1610a41051060280251880f1304265072403500034001c203c10707210441c2600900c0390b20a0114881f04400d40101c800c0450036130140c4501c40419015800300e600c100c10305030b003004280016101c0301d0001a000c600342d200002c45a1400302c401c8243d03140642801c0140d00a80090555043d1309810745542d090000307070012800d00010000c3d2218031054012030500c03004100203210640d40508107502ca880c1c20707a24000215070700c035400d68190009941c41c0c0c020740408045100d01c0c1c28241c3c04a0122a00180000c2000389491140300c03941e842551640c01d0300b03010300c04020380c5081c405e10030102c2146046d0301928080103000701c1a15954103000c0c42419440c40300284090210000415000d4100240119600c04951a02940e5030703c42128090084400d40d0026151b112a00b41220301c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 398435044 1250 398433794 398433803
    0x909160b0c031c02040e10030501051506160501150306020301140a080a030309051e03040801060519091107020406091b021216150617010f0207170705120a0c0606090603 74
    0xc1040300c1e81e055084460f0210a160069030911001800d24078030341c811801030380340e84008030346281182421401e5030402030405462054180d010320bc80d842c1c10080f0b44510144814001c420034003441c025024103406c01c5c0ba420b822168000220510403035900440c12958110140da206600c041c0902c81000c04078131a0b468690042c4510350301103802908a0400c3c640300d0402d48179441d0300800342d102e1000300b4850304c101e15403010030103102c035120922031140904022207403040002300c028100c001d580550b009140e40aa00c4079041c00503903c00c00c3c1500d0700154020014050141c80d403035000e00902e144080010203861a00d81d100d01240041004000d4038030080d41c0614144030040ca903040010050b004440c0e903d1400442c00407114644161005440b01d100d4518804c030035401c8003400d40d106800c0e92010f06104100c500c1c0024a02000304c4984a409030740c2586078212804c1117814540a20340503c140e03080002c0c6c0340380700340c3d225441e000c280e0301c81c0307400f0061651120104012101c05010050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 398436294 1250 398435044 398435047
    0xe090d0f201204080a02040f05060616080418020d0b1504090c0903080f030403140309060a111c150609030b01120f05071203110d0f14090909160b0c03 66
    0x300100801940c032808507840110742c91007140b080345034210390150340034168030340000740c0e0101145858001d406030112003038070902a0b070411100040c1140b0822511017654031a0900c00010490003000380c0340104981d5000f098490f1040c440d140295101c034821103092403a000407540e15280141c08e40c030b0300300810310a0501b09801d0001000003811444c80c80424041501d4000000520a80041c02c0404a52070b8540d00c9040c585000341001d0007138403810030789000074020801803030400200c0302da2184000401003078051003d040011030340728290041d0f01c07070003008e12a040e44507070b550801500d00d07420b048030000440d44d41e80211842442800014000000c6000420a600c070032000c20b6003c43c0a20702e10502c8248654605d40b4103100780d84220382a00c1c070010745805054105d14081704034140c01000d0035010f02d0250004108030090051301041c05071514074102800c04041c10b60b020b05001800f080d61909080074850b075165000e880c00d0310b1100040724007103100584001580d034900c01e400c0085 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 398437544 1250 398436294 398436317
    0x905090c0313031b020607050d0e03030406050703080601090905090105060310110d0506361003020306072d02030405130608060c0306010201150b13050405070c060b1201060e090d0f 79
    0x1200c0740d0b0b10800115018200740141c0b0b04c096914030000b04201c43c8608010800014003c130082c2030101410501071003504180400c00031550014112264158545031501d040d0b5100e100682d0358400c644c004510603803a000810492a070150300c806e015100c12030440e040c0b800e403152110b0960301c08030800410303102c0c00d0000c03190042c016004260842070040111743e040f0095050000c041c0c012424070524203c86640120a03002d1400c403580e04424002071781e81d00c80d070035500170980da514098040802c010040440c0e604029402c2b51540500740c021444403285034030403000940d00e40150240e00d12a100010380b08101c9141e5118010440758034801070840d5540300d03d250103a035003005001034159505c5403020310781100700e010ba4202508118002a0301e842600c0101d1500301000d03080315015920303103401c0c0441706803c08031043c03000d03900c0800804c2c04a8082c000c104011800151410190b09042005c142a00e240e041e00344140141030403240f003001c03402c1007201c450f100c00064202041d00082003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 398438794 1250 398437544 398437547
    0x11180a0503062701110c210f040303050d09080a0c11040203060f0d0615092a0815190602010228050301060804030c05070e18070b09040225030905090c031303 69
    0x800090f4491800000d00c4245401e05143d2650004040f5070098015040854510140c40f00b000c00c1c24a60900550811606009402d503d1045000207014004003013022294604103811131001f640d071000040d900e03025154000f5080c1d01402030200ca40c6d03041c82a00b00c1043c00c0038426241f00d0f50300203008610207040981032018884003181c09440c85038850b03c1248a00808a0740da8005021a40d0000365020000214480001c1c4000e0b4624180700c001c480d182180c3d90005409402901d4007801801c1d0603924000103035501c115141400080d558050009903054065000d402032100b4000c4810305142d030b42541403116070801080d1000301d882400140311407449101c140358000d1203414403070203403542501c802d4501885544a4203011042d4020440d02034880c011004440d85c0e1a001854114104184800c2a0003441c0600380660707804034480c01d10101e5844a011002054a05099041d0403030500034070381000360080c2d0b0f01542280003c02e034104414801c580c8070b81c001c50b5012480c05201d640 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 398440044 1250 398438794 398438851
    0x90f0a090f0605190b070812090a06060905040201121d0a14011d03120a0209090a0903030e01061a09010201060f08010c02072709230102130501080112140111180a050306 74
    0x701f99105a8280451200480100c0903a0b004140c0700300140510a02d5241203000e95486800114100b4104030a020041c3d802010580d41c0010a20001c10714100707244071500380300b40d03141e00d0201d244254000c90007449444000e0820b081c8506000380b0100c010005d02b0070100741080150401584104002e10b448c0314148030380c603000142d00d4005441e008c001c40000310441d02c141d611010243d9124041020181c051040e0b1420040d040000d101a600d01086161885013240216004220005904e3b920b40c0c0700f9032046015240842c0350918403500d8050ba54000c000713030381c60800544580744000c240c000410002c005c86055084100c03481c40b01d5402000058421101c1c203d510f411040b601e8001400c400c8101c1546045000005032640c1407101e4007100d2403e07e51082e414420341e034005100e240b03142e0203c20140e0381c102031140c000340d40c1041080d005200c10298805000360124800804030b483c100015040401110819611600c1d20304058460702c00f0b544040f10180300c00b004940781c010780329 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 398441294 1250 398440044 398440057
    0x60907150e0f0409121d1c1e0b0106080604021905090102340f050f090421050405100f0912080403020d03031d07031205090f0a090f0605190b 62
    0x420b034103041010030010509403528804210b9207000d542c0b044003030341640301c2d034118507201c841c0c00d900b40600041408100c003603c1c40440c0306c2207103816070001d009109503400170741000c04107a15080003002c828148080c03603c8080c01980001159503001c20380502e454000e0342d03054a03080c80b0030110a5028502a50740b0703070115000505601907101280100b4402c1500350170b1841100e088010340340080c0300385004201d6940c1140300f00e01401c54050069880340f0024905440c000c0c1c40021b500e46039814020960402c013681c055440c1188015040300d2680440540f0840320103030340441640100d40390544e030900c0300090001c001031f04100100b0840c0580900144020f0081c5085490300e0740300d0700072451000c0e45100640110351201c2019003402030ad101c01d0480b541460010700202070559540d0341c41d1182400b100003c0041c0800c1a0085588001101440c94401041b0071046555207d000010300a00c0200050140c6001000074490800013003088403403020034040268607051002d4101203070003c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 398442544 1250 398441294 398441299
    0x7110c1c0506010602010204080d021917041707091406030a110109030c0b0a110d0c02060904020906030421020d021c03020903030406020f060604140a1d0a14060907150e 74
    0x200a52000701d942882141c1c0a41019800540e55900b000c2d0700b6842c11008140a10855208891215003004980580d0412507403004c8514002060a80c0d000c0b404d00460700541e41110015041200201c1c0004122080701c0c2c1d840700510084a4603400001e4028003110b03110742640003511b41d0400504401d0480202481c14101401c240303407251201d103468032464001212610b8001240181281c100401042c000345400003440c02e41d05c85a4003c115030342644009005413404104a41700c0e5495406541a03110050202501d0386858180b407035444104401c2041c0070320356080001200d52000c140305c02c40c0c111540003012a034200e150b07510400030a1601c00020540d0038050754100e90340a00c000c02c0201081e50080000941c141440381c203200c000351481d44607a01d403a04408221980d20003050313102c012404c00040801d00c0c00b01d078031070003540e40082007001d00656840004010340c030b180340d03802113003090101c55180d5a0412000c0e80d41443e402840c002050801c0c0c4203001c58401d03840040f209001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 398443794 1250 398442544 398442589
    0x501030f0b062d0a03230705040b0904090b0a0903030e01061d0a0204050907020d021506130903020a05070f031a06060304021c23010c09180c020a080f1207110c 70
    0x18400c0c00f02c07580114a0f01000292100144000100c0d180250442440345400e411850306002402400502c507600c503103840c050340410700b00415543c543c0800100e60300020b0a45003450b221082c0402002c5031401240428030740640c4d07407904101441800280c80ca0740c0c1d610000c6e040429030003242114003c16034800a5020040070519884012416002c0c0e103103500245401c1c0b0310f2007001307410480681145042c60710080104406545d17410201c0b1a041c00c00c030390004140155041c12402c10b08001c402510394414490005805103c810300740703045034090710000ca41c46640450003040c1c1c3c8001d8501d035a0080007403000ca00035151640c00085000344440042c0031222890b81e90034000408414494420b03001c40c20200180582030181042001d0b05241400081742001c04090003c61104a410541941c1d052202c000a008020103d501900005265194088008500025071040350720b164440e0202021500c2603002d544240387c011001c202400d02005040203100e00d905142e52000c007a07192 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 398445044 1250 398443794 398443867
    0x60d0f06020a080601020d03022d12010b0301090c020c0a270603030e0405010501020c010906050322060b011e140a200f070b0f040b0f0c03130501030f0b06 68
    0x110310080c85044100d484051051070300e9800039003450360b007c064205160041041460060043c0c0c00c0d00044540d40ca0852054036a07005100c006000300b011560709141000001b1400750307509005181201c244440030701c000d00c00b1440803038a50000719100d0b5000740b1030316801c0c004402c8401807189030203980420342c040550500010001d80f01c20340e000340c01040852030103006030305060007807e002d4102030008104a0030000002051010135100e05010006c010000c104c1100c03c1c40e00051301000702d01d0661219100d2411711000074881003101c1ca010403207042c40201c100345100131441d1031105030345503001e6480707a49032a0700081c6d101c07a90100c01c0004032811040800746a44503880c0c200c2c2e4a00013060a5202150781d5441d03c0c2c8139402410306c2010903c42031040b02e03c00310459090301c1038600091307221080040111304d90302031a0000340260101081012004440e2030171042100c03001d0782c003030203811801e80188080f240000101034111104018808152810170302d0020034003695890aa007848 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 398446294 1250 398445044 398445053
    0x5041805041110080118050c0a110c0a061106090118080f21060a0e06031f060f1d06060405130c02070e271902010c030e06120601120c0503060d0f 64
    0x1c1046950004901130b00b005000400c0000820702207030b03081240070031440c01e01442400e00350041c0d40c6260100020b03525140401241071118444008010b0121340d181c40d03c803800a0003504003032a45904a11030500000c1206405004070b0505149000603000060f202e0340343c003e240c1d4000216918100020000200582401c07001604c407052a404000300508104003000700503074469114080040d00c03041031000e40c0d0b90209000d1a8910580505403120450b21032050180680d80d00401200781c80d8000020f80300c0c4800c190368040320f4007005844d01580c0b404100120760140e0300030680c2061004041c40024105da0f4800141ca099500450300407640d190311964108004568508481803070421100109940c01607003905806001c0c054503a04c3c0000c1c804201400d040d84020741045820700c0c4890516015503103004d4001c030050841c0303a841f0a15401524460820740351617000a85202810342030345014441d40340c41c0f031400d5030b911340b03182c54440800584111341001641c5400c1d101c4802d00005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 398447544 1250 398446294 398446309
    0x2010c021027061d0114250b060102060f0f060d1a09070612060518100305010e150705070b070818011b090501080103050604030f03020c060a0912050418050411 70
    0x4081020820b200c02d400c001008000303078440f0f048850580c0d01051a06020317a00001c0481d98a001031709115101d82140c0707500301401408010310840b458003201c0400038080f45205440c4910000c3e02115500c0d140d02e03241402e000d4046420801072450350001c10702c1880c058008420302c9000c4d1100b4641440141541403c071a426140413101d80c0c040e0404215807608204005400c854420040060b0f61509001c24034103902141030b021040114400600c1c40c002032440c1c14040c5811800811110303030140101999039590058100c1c01207503420000340c03100d106400b214081c584c40802e50f0402e0300d070700405845032000a03005107d1a03080c0c50403424042ca0922030740d072500f844543c0c100a00f882c1c445000e046c02401d9046941084642401800403c4c000101c058005506141910030b1482800d8200c0080c0101529400c40d0302540081c0300c800252600040c0406011f00d06d0514030504850301503480d03120354451034581550b00f0102c840825907a40c4010341c802e0260806607000388240c00041ca20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 398448794 1250 398447544 398447597
    0x90c12050f100812030105060f0408030708040f05060304030f0e0f1009090c030b0a0b030606090a030f030e03011b031d030a05131d060d03030b040204090906050c030402010c0210 78
    0x5440c881c60401034440d0760111904002c2442801a003c200e140c010301d41e005200c140113185c0590000a044d40d440007558080ba4000c14008041e0380d04d4044070310f00503041d03078031922480e000c4c800c0380180410316182041c101c0c0d00640e40b6841d01348140301d01103030a843e42102110740c030758007a01c01d010b0072006884040008404180c01d503100c1c2d13070745070600850b0011585104400303000c05180070345560b0b05440da940f0280650307500032441912603441d1070004110384030b5408900c1c0c20050000000040094508502c0030341072003a2948035152807078806041c00c036681e2400205150001c1601030107001e009601458401c0100c40c0a180980c2d0b40041e9146503922030301070440060400141c01030700344180c40c4c41d00050001e02c0c480700300d01074901c0104654810003070300d05446030303020034617403000c0502981c40100c04060240c025502d4560702e0454000070420700100383c6809003040d000404404800e41200e10031a416190f400892203140c00340310000100040c4402442181220180c1d940440701c0320004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 398450044 1250 398448794 398448811
    0x3150a020a0201050a050108031e04080a030c0b07020c0f150405040504030903030f0807020a030503090a05101a120303010b03060316091a04020c070603230c0d060e040c090c1205 78
    0x96854041e54000d00311003000b000100030b18034002c0140003c11021048594440458920322010018240c15003098840d07036001c40ca242c442c00800d00c0805401013103c154450141500f2103130395468aa0603621481c00040495009103004020740c100d141c00220541d07402c0704081c915007059152030100d811110b050700e0a80100e41c48442c01c00c00c0542c013803080a400c0d0710340c0c58101d00c50b04100601940e00c850b900c200800744040440002d0140108000c0306100d260071000300c80d20001c3c0f2070525402414240c9444094684d00c0140759a0b5003455079821003542d28401c001c601d581c1ca0649080c44130703000644000c2c2d1500903161043d03c429400c1d03100e103000e821090b0001a00000450340046074001c00c8038650300550050049034052035000c50340d031040345d00d00c0c100072520284103c88524a031240a402900e008074000c1840800c280c1e1001400070740880040411501d9110101030b1812401154000c044040c009001c1c40010040e0b04000007900d854100000071181d0030aa64050702d004407814031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 398451294 1250 398450044 398450047
    0x509040f05010b010507031b02010c0b100e0903130e130b0405100507110a0b071b03051c0204080d03020f1209100f0e0c010c0f050115030c060806100e03150a02 70
    0x1041c04000c0c0302d8083e48040908040e850000707265406131120384a42c80740340403000c08007a90402e69029188018407a6423010743c0000d1464103c1c00c000c1d249505000d01d0389200f038102c00040d81401c0000071140b090786030a143c102258507080382d000000c0002800c0503403001c6410410000100ca40c1c0703203580a14401d002400101e0300e0b012200084602c002c040d00c08000c03075222440301200012600a420540044030320546641d00001542e100c4a01840c80c440c00002d41100401c2c5642300002d00342c180580b00d5240b140b905441082c00a038091800380360440e0b000222400c1d612400303680240501a0b51001c11b5080c01e0190131807050100c1d0444042d0180d81103461800600603da100e002d0b4019500366080001110344422070340d40744000240103043c451180700e42000c0c841030320100c29020b40d000c002403055145e110805038220300c0074803003200d45a4040b81d000c038038940100c2e0824403840700036000c40402101c81c54206c400079031503140941c040c083c1280030126600321100c1644100e2a840c03000d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 398452544 1250 398451294 398451323
    0x6080a0503040e160e0d050114070903140d080c032e05030114010e130213051501020f030a080f06040b10051c020408030a051b010501080c2106010b13050904 69
    0x2050760000a0101c2c004c0186100e4400b0425003261914824a90903194641424010700d841401410341144000c2911440c00401540c07540c00043c0360252880340480c40c0020030014909552408281c84c40404100420002019041c00801856021001c0007a0425521440d040110000080701c51203403800068035083c8281d080902420710315501e030b400404410340c90301000704490030000e00164000c01d5186002000e40d500c20b950881d008412072001c10260805000311803070385500550311030260207240c0e440c1c3d58100c008810f48044601a44500d0783c40e81e0350020b040800c81c2c0c000d1403154803c1d40c512284034540c032258030066900b10b854490750341c2c0f406009070902a10181032000183e050042200388010a03010054542d81d601609000f616412000030404d030250006200300815031a11000049021000440891200c0203030f403a440c03402030450306107003200e1080c100608541d112030010418031400d0801881082c1215901200e056100c4002840d041c2040e1010f82d880b000311446d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 398453794 1250 398452544 398452559
    0xa1205150105060304050a030e03010b18041202060c07110a0305010906050a0e0c0a0515091906031a03060f0406060b161217070e030703210f09080304051306080a050304 74
    0x5490240c0b8003203074071505500c0d1944c1c407142e652400340d070001c04000710321202c202c541d202504400400e060081c030a0b00702010b0a0714003142071204403802d4550205c951002121680045019402004030480d100d140581c0c0e503c07110213068074250015004200300e000000458800e00c100e04219116139004141030030100452426a0340c0001c0002003500a6a00f1100f00d07500e11004070122101914200402d103248030720790845020f16400560070614210700d421007400d0340040c120a4900e140c40030010b01c0b40c10101c0d60800e40300355001c0d5415a11980204000e88080403460754454420800411142e4580c6a940794030b400200080340c1264214004c0d000300320440c007040302140c41b28a07110300302c040a00c03201a181c01c4094552000c0c0800b4807412801910b05010f010091a04100c1c608215000e4694641c44100d07032100f4080040c1598101c460101e110b0018407088442180045003050304210812204041808030460344035610680018010028444c031540540903801468881d4074028a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 398455044 1250 398453794 398453833
    0x3150c081005031e01020903301213140d17010803071a0a090503070b0a0f200d150b030103050f0d020d050c0a0204050c040515030f150a1205 62
    0x603a0788001c828010910694400265090310300c01d80115884200002000c1c42d40284142c80582c1d8150142c80d010038203120000e10341a0100c0708038000000101888290007205000351101d59100742c4100c00850b521201035451000b4143c060900c03054584580c420071854140d5030550100441e6001c4cd162054002007040d90f401008018080c605d4180b03d56501e0703184c40d06c01c081c200305450602d00416110b4640c0d41c00070f2000783c0d204040303036510305460030480284102154440e002d541450b00400c40f502041c0282d0f030008600c065000510055a400000c503600b0130340700d048550360b0399692010b031440c2d1001050000c044040106549504500740203040ca0442c07000b00140390f001884440780c2d2a40040e10f80e200601510f0041d45480000e00e43d80d0506101a4010350b200703090400f405180c504180c003e1088540407280080e0f040f1140a6442c05404100c540c90510314014001030780070143d82802c19002c080040c1700495164603041d6001008445603010f6455510200b546ca48a028208 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 398456294 1250 398455044 398455051
    0x80703231e0a0f0c0528020313030309140f0901091d06180606060a08060f151201090f0c0e04090206040807140f040b0603130c210606060f17060a03150c08 68
    0x940640750580c1d0110300d200c5515085401340d0b200c59100c03401b2080510034400c0d200c03603d4041905440b000d94904005004044500031310144004007242d400862801e10703088010000064030a0b01c0903860f1900500081501420300c10004541039030300005c08505200c0f051013403107800c0040340b51801259100f850210014074860192a08120100e841d60704003500c5980410203d400308503130045003020a00c4100c54241c040035800020480d00000f000741002c01e410390b034440c5410460002e20803080320a54205620002c04103a61121407001d03420300340c22440103076001901d045d15180da40e03d88035142042e10b9022100070281c8000c00c0c4034614002615081c030f260104c80600410703401c440052070621000d45110034610003541018100410b614202d8003c0c02c10681c0094402c01d810804001c048140c00211141031a12a000c1042400340b0a59241c6120036a6006c0c0038186c00c0e082031080740c3c40a44a80c0d8842e01b91980040021283c1180441396400340f4004100c07644c030b400c0302510300381014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 398457544 1250 398456294 398456297
    0x1404180b09091e10020313030f0216091d0304061223010501080709090c11010f02030108060403110a060204060914040608280c060f080703231e0a0f0c 66
    0x1c5050100c000000107003e503440141c070700300002d03030341d0007005192a02e0199032001c0ca002d800402000159900c91182c03505207400303600c1d4a032140801c4c030001c0f0380700d881d901c0140d2244800745205020740744007a400550303071451140090728446220300310140303181c07c564803038000158100d94070001000b0b5802913160f21010144c0c0003c81e4840c044030000054014002c0b54108843e50f000504100c0c07196010310300030503080b001080040300d0b658004200000c407a074134a04960810071a000000c1082c400c40b412103004101400d429200c968040b138502e2003030404c168035880346011b50320201c1c40620040c4002c1c072107625903c4080b844c003544080e1404003244103d105038a482c0e810001020082115000501c124200c00d05040d6100d01c1c420b40a4424440582082d449241c00302d03040341c2000041c1c038011070b992594405565040e000300c090355007a1038ae490640020b0f40104103115805091283c10003803480c0e00ce181802039540007a5240403c032030f499100c545810406218819521403030000041c80d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 398458794 1250 398457544 398457559
    0x10f1a0c03091318030203210907150512071809020c0607030f140a0b240a0c061b021c0906050301180b0d0606090b1215071404180b 58
    0x1855944030300a082c641800751800801c5940b8960300b42c0e014000c088049908403030404145d00300255a9001321409008880d0713006040001c0200c8244081d1007a0032103070040a0803400c10400802c3c600307910140c40c003484000d100c0703148014154100648100001d035034801880b0b42c0901c2035420794007681d00c41d07040f00388104544003400c00301041d5aa4410b203d0700340800c1c41c1d10480481c40c014003035600031214a00980041c000403240e03d810a4130f90002c02c0b2418112000717002005500465a6504150800400c0150030a0280145001c0c54401d02440c03000500c04003021448885400b002d0704200180c02c443ca410900c081d0340b90803209010810718208402d41d0404000ae44903200600070914548082740035111440b40a400500c2c40240207420009011502d140242c0a40101d016200f4070608190540c0e00c282809501c402d10382c8031500041400010801021000c5480076240d201000020305140003000810710080006000c6c40c502c845a42c2414840c100c01c40c1c0310075080038468250f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 398460044 1250 398458794 398458807
    0x90e07090c02030d0c0504080106030804091406010c110604090c05130e010f0302061806070f051009030e010e120d020d031413030f020a060f02070302100902090106110a020603010f1a 80
    0x14008282e84e1291816130000412521802d0240e806005036401960700c0e40c2000d0001c8108480e01e000741040ba1410502480b500c02018030030441e078002125a9400111268420000301d61420709410308520b0142100d8505511017500b00140c2e0221308424002c24000228000d001802100c2c00004110501c003039440d40d41051040606145c50380300207845642c01040044600c07420407824039010784002c1c102030381d94070180382403011100c4c02d400640c0c2034007940111094507a01270042401040c5d05030b1b034142c6a05250320041d50283c0c0c040d080207411450050003541d201c84200007603407000429030014140c082186400600780c42580341c44000d035103182d00905c217a20041d441e0002d81c180d0f16081001407070030110342c12481d0100b982d2016101c01d04091010420a445030b00401c0014040e50956050300203070300d0054203980c03c5c05402508003210800410565104002140440c0c1403901030f25150141600083c80301d0300f085e0040001c5a00400c403c1140404452840e03c1e02d41c81c403007403a0700308035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 398461294 1250 398460044 398460047
    0x6070828090b0c16060f09080102030c03070302520f170f030c04060f0509011205060307031a1e090a060f0f1e05010906050a090b01020c0604090e07090c 67
    0x141c8a00c98080750200106050000072000d00142d0014500036503100c030381503034801c0024450402c00e8215400315071500404101c444040c02100c1c0301d411942c542c14a951121801200254010704d0400800241c464400041007410740700580710301210b02c01c501182c00c2043d40100b5004100310a010410f0a14050000160b80c3c910301006c10b540100c00d107562503a1384070316011a44194120504214000410004442d600c00c02600c180c3da0603607a030390340054812038161814400c41c1030a901040c0e014039005450f000c241c02030360340f102c03001d020b48181641c2da80d100c50000842845890442100b43d04000310b424a4180303058516032659034441160600c4400c450301d548109c10080c2410340c0300c029115131480c1c1a00840e04840085a00300440340c400c1040b4050540d40310188501e09003010000108461640074040c1680c100130101c6001915100b0300000400000d24183d0540c003072150030700740c6559020b010340002d081542020510440400c200307410040c16070000380c41140f40c1089040802d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 398462544 1250 398461294 398461307
    0x1c05060604020708090d030f180b180102122106030607050f030601020a0c030501140606040602072304050408041526100308270f150307090506070828 66
    0x40c0241c5005a072030b480c0f410582c00360b2181c0300040c0c0c2c01640d098560420140c0c0090740901400107607855070304081c6002c00c2c0c40005015407040b0074950720203025012409070407201c3ca04142c0c40500413035000891030880703d0215000b100c1b081e403103001c0039511500d0740250090303480e0340420120068941841e0240003d03003580500490f4101c83e00021001495590082000f014601c1c2c01041a15074581d80345407c0b4043d0082880705882c884c200404500f603814088242d0307090303400e82d401410909040448003450611014001c00c600401c880c55010300d9100c034403c0702d0141c1d001d0f19076141e0b03c80c200cd6400d2025140540b0340000c010040c01c031090391400b0306c0c591a0050042e0044800c01d51201140d00d10b5000d61900050455200007804441c41c1c0414004030000b100060010586a00201d081000c1c0c0400c900c0c4540e08a00401c6141c900e0300040c00045610242609100517943d4aa80110f00950000e4608454200000605014080c008200800c10b0800c4400c00f200b404680341005120 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 398463794 1250 398462544 398462551
    0x1509060403031803050a0627080409020703141305010f020c1c0201030f0507020c0109050616081e040b0301030308010e060f090a020702041506180305070521060a09021c0506 76
    0x800092400783e40d90008070070100b000541e005400c5490101290070000c00500050741c00d110013500708445034401c0380d407811591802c07542100a0b542041d00e0806e411010703500100c0110b042184404846405803001d0016048a07038460440030310f510b08000001d0100401c8001c400705540c0601c092290341d65034040740c1303910340c0310701400a440f40d009880103a01a05014070302240d811301307181c01c0005903036002481d2001c0c01c2003603a405003580d81ea10180542032142e80d240141c6070518007000070101d1180d1008101c202803da1811041d50304007040c03145181c01c0790300144200382c0b00200410506600c8a8424090280141c1481250070301000294078076824130001c03805800c59400107460b500c5640e05030b41085401410030300507a28442e04039040c0c035906005a4020505e100400c440241c9502002016245c0c090020004203041504014600c410860030f1130310140e0807907081200382800d00a036401803810280200c0c0c0405188100040002d40c14043d9001c04220a00314012507000690142c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 398465044 1250 398463794 398463797
    0x319050f15060d020409120c050c0d080d05090708070303080f060109120f08220e1807170c06190306060f05160c031b0602010f090209070f111605150906040303 70
    0x707001046101040c09051201b00c0039101c0e0904410f0081c0e42604200211b030340300e209000b91440009410708009942c610618054485602807002c0c05041400d030b4403841c0c020407418110b482c000d680320341d16854030074580c1007200062210814042d180060140305d036081035090070705421080c20404c2040d141020104c003d09680c4a5940c0902401220412150f000c01d502c6d51500e600c40108c83c00e24000c030140c1c441c400741c82040320000390b00c0c04010101441040e02c05006004800d03e040c8041c01002c1e072044401200e030144804512840d6540d6004140d9405907405408980c8080308020b07049071404d6100809101081d524046529401000c880c041c40220103804810b41160801c05554582c0d904000c0405060715600b080501c5040004801ca88182c1d00902c02c00002d548110107035144018001d401c81520f0340820f07001e5010740c2c0481d01c80140c07460580300d4001c04144445c50140a100007102c184400c20007446142030210450301a10940b81e0a94548401031000c40d2085c400c81c48083c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 398466294 1250 398465044 398465059
    0x608010612021905030607020318030a080f0c10090b090d090303051911010c02060105100e0609040c1110052a0f070302030d02030903040617071409040b0319050f1506 73
    0x70f4010405145503405800081c04031040c0d40b038052000b0b5960350100c038900008038030703903c00c400003450002482e003001640020228100342c10b17400700c0900c9030441900380b4191b0040182a2405c00c00c40c0c49080c4000303004041c04041400e001c2200750804041d55801d03000c10004840c280042a08001141e0b49814601c2c004c42240c400d541d401c44003450702d0700c0f0f08007642d4203101701c51503c180d0024050303058a0080714680310b80c00b1506000c1c0c2d54034030945a03c6805c150f05000041d81032a0651203030310307102300d1400e0001075a14000c1c80d9500b40302c4203a4651032010b6440060102d00c184001c4c02165290700d11004100c6a05a042d550742e150180c0d454194059000103820b03002c0500c01c0c03059070b446521018040d034590500d64102c1c0c0d01c03074001d8010840000c5040c41401e40180c140380314580901d009803138150380828110245012907009800c1581c0003901c8161101302c40e00c080118440a07410101c0e0740e4089880d80c5072003070405080d071000302103c2d480f0220b50317080c4414400480d80c108034200e9000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 398467544 1250 398466294 398466319
    0x41d120c070e01080304030b010524030a0b1807111b090c130e150103020a0507060b1f03020712020304050306281121070c030804060603050a080a0201060801061202 72
    0x507031800000e0303048800c1c024004000041c00d110000064816240b042050340c0460380c8034010300641088408a00d00d1426404130340400c0a00250011a0094030180002c9400d10400001c01d00d05c90011540915840140c420000100c0e8404451062045240050601d018040c9001e001030702d0401441c500c0b0b00300305008a40c110550300c0460712a101001180e0300c000b5a1140705600c00344040784c0324410b605000e12607038072641c403170701c01c583c0320810a1300e506080460303680300d442c0101981e031643c542021900c120031101013030120343e0725500195560056541e1055252802d010300d6004003034001d550050205100b155004500070341d0045000d05001c408148615052010104824840305c1192601488090f0844101c000300798690100081001d011151090300300c0405080b1101400904c896400c08006071041e4092504140945004549503440307455150414401510031140c0d080006201c03e44c940d02800744000030690b00c802000241d1615078805041d98a00308001e1180380d00e807044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 398468794 1250 398467544 398467567
    0x50d020f03010f110a0305060d15020306040b03010213060e04020301080c01212a0908030d0903140d0b0a0b04080a1713080d020f0f0d140705030f09041d12 68
    0x141003524445a400d10101010b2020013001d0750080f0b03200710019081c4400543c1034200840148891036010728031108008010351904001e41000e01341d03907803040d10340c0e440c01d245d5a001d0010b044025040c000a201003441c5c94006401e2494440b40715000741d005100410401c2c401241000c070340c04d02800d142c40340005100082d050800d80c0c0741d0300c0f03140301d01d00303112916004200c003a842c6066540140f5070b446444407240c10303030300c034046881010030550003001301800500d03050f08100007440c0b02c0d003071640038500f81d640711075070702d800c03040c0b407650450b503100841e018074500070912100401600716014602130500081e5600c800365680b010740101c440c80303600c0840304010021600c0000120541280c00c2c5e440e0b4890b55241c0c0c0602101a005220b00c404a031420640072401c07400318112400149007c03000c10ba010b035600b100041401016410030700c1501c0108006200800d0110f004c42e85081c4c0d144502d0301080110794030014024268400521000e43ca20350006500014802c01610030b0340fa49200d45a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 398470044 1250 398468794 398468801
    0x201051008010615082208130b400801020316050a0f05090d0f03021e1501030b0612030c0115120b0f04060f020c01020d0c1806030515100e01030609020301050d020f0301 74
    0x2107850703101540041801e07c0501c0e0b010340944d030000903c02c01e0701d6a6820f45984c2138020703042e101c581d805030101c603a00810003001006810900104c0780e6404040c2d0011500a03c0d4590b0703111420a0b500001081905d0b41e50488151001106003807a9081c640b5021000f02005841814141800000501d0070240c0e51504245034619030b000c581c0100003101e6140007921400c3d0800c640c40c043c0c0301201d02c0340c00701e403010441100e14062003c0c00062780c0e281d07444062207032001400c0030b904606002641041c20b4418001400403914540000c282c40b20702c2c004500050155501c00035905562030340e284000ba05411800c2d0700305000c4082c117001c5e0b0f15142840300050418101c2c0c00c0e80720344001807500f000c1c2c0042d00a44900340c44403078100240c5c2800c0c14159a5807a242d804110340d503130800c90038048640a0303409140c200380034a4540e103082e4680c0c1c0215000c641440b2110011032001d0b07000040c00d603031500441022b401020010350555140030049080003c515000a21818916044c2201500d0960 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 398471294 1250 398470044 398470081
    0x210604050f0d05180f150a0e04063b010f15050a090608090114090a11060310030f030e03060c040e07030c020718020f03040c05030f0c030d050c0f0607020105100801061508 75
    0xb00f0307140c0c1000c01555101200c0d486241f48601140c2440c441c0710a81c60644101c0c0112000c640d9010b4242000c0d00d010002d9007030141c1c40002c0561101101d820310700822503a10302030207400788180c01035803c1042c0790060460b451030728402c1040811a0304440c0781d118002c0002c071a2542080b00541e11011076050245c00482d18103410300040804000321a1800580500300074012011006507072284400d02c40688801c882c20071015a003408100b000a083d0070a01c9a001c1c000e10381440b07001f8101002070f0031b050040e80c07284500c502c040b405000c0c4007010410301307070003000a04040050641001c40a03442c3c8605128260048404142a024034500b640464a000020002090792440c081c038204800501700e0181300d000c0d12881150a0b07018000007072100602400600505141c44400e000315040c0d842104940064002c008141281a208100c010f0140610f0f40010174a4540301e91104034540c51507012010981c101081004200f01010341529005e505240c4004240e40e00003100300b03104083c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 398472544 1250 398471294 398471299
    0x1a040903050c0d091e08060c090d060204032001050c3c010c090515160c0504020a0c0b071b080a090f03050c01090906060518210604050f0d05180f 64
    0x181040c3c40407a4000e02080980f03031000414010480842c64845c01c08400d4015024150710420215441c203044101504168000804a2464081640c0c0d240141c2c2c2080e442181c1c03000101844c2c0b24100c03810f080000041800703127040c13410301b0b40034140030350303141d14008014900480c42442c81c0c1c010b1500c180d05118055080340b11045c01a04078020600a0507590b2070302e40003d5642401159528100802e40150b0a41c00809030901456003011610282554412550802c4211002413141c40b03e001038801101641c5540712703e51418148800140c000404500c2080403105810b00b803090740d12180558550041801604d0b04110f4406451031300441c4c11280c030311032071024000100140000c294445540a0782e50340c55a035038a10034a01610490700401021074018002e1540c5442c41401a003982d0b00d00621a0180c0101582ca100700c120242c0400c0c011504070108010a12004000100c1000d803140d00402401c4019030005103a4040c1c6030301d50f14445881d1403074468a5540340010840007500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 398473794 1250 398472544 398472553
    0x50d080c0c0d110321101505120a1b120b0603070203070b10030f0f0302010c0f09061220130510021f09170c060a05041223070c030c091a040903050c 65
    0x3005e80421340d0243c110f0f140341c865010080045120041032070f4480c4060040e031102800c15010f100e11038103120004003080209c0d031352664004e0034140404618910802552245d104d04e8111880c40c0083d216000000c1c1d004070402c20600000c1a800011034414940080d01c02d140e6488040f0040700c1180650310181c042800500d0800601002c0703121442401d209400812407500000400e680c0f0554015140001c034600c02010000b01d40155088004d0440100f000240c401240502c024142004107002200c160f010079113101c1c40f41c1c3c24481078043c0c54219030740001c19241e01c000030b40d2245800c0d003c2e8030064051200a884800030781040140540c002150500d07510884c0991120f600500c110b051140718900128050114920410f40215041103d007100810042010f075600e103003ca1000f83c09031051090390201258400207003010b80d20a403900306105141d82003c5050140365040469010302c2d080c140c41c6005a101c11440c006442900c011584c1d0419013825925130041201c1e0144500a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 398475044 1250 398473794 398473837
    0x80301060f08070c1211031e0c0f01020c0304090b060c0307050a0b0604141602030f03011701050c1309050604020c0d120507090617150d050d080c0c0d1103 68
    0x8114284080c500040d980c1c8600c41d6a8001044031000700085000d1725905041e050381c03100520494401c0b0340c44d1020710449203032070b03d03801c441d5854600780d580b076541f2540081440c2d51540f100f400700540c2400104000c1d82840f084c111026124403492040b8540c0302d0350303001500d6054031001e01b9900d0820f44142941d40b2400f44d414500e8450703010300000c035212035080000943e41d180ca0301c5804100b04082c60080700c0e59460140000b0500f0b42070814106500c03080c01551982c0c203000008501910080340e03007111401c88129001e094480c00b4000009502e4240600680700306000c4082c001c079401b0340c0c0e02044030380390000498001c1c403514400418a000d415a12500150400003400070420040b504105c0c681d00c003142120b00d10068056400010580841000d0407812920030940011040810072003010007040042c100c0f03285502c0c02c0700ea9810820000f8070b540d8001e07501030b0b840002d41403694500340c110903d45440b001304240d00303030a000d02880d80e018101d43c104195100764010704040b82413080c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 398476294 1250 398475044 398475047
    0x3010e0712021c150b19080f010608010605090411040b0d110307061b0b0a060e0f1e060a05060c01060308030108070311061207442401120908030106 65
    0x2050016802400003405150b0080d00a4001c00003140c0c004414070b0640c0c1300d80b607452000c0c00c056609581c4c4442e11109091500802d0224000208036039001020f07049101c0d80c0403403d4030440c0d40150380c20303458001d0802c030308d85404000341e0340b01c0c1d4004485411002e413500042e0080c103800226a8004000e070428904110186d6070b4600407103003ca04a03610f1941c1d420703048070303100b10179542200a001040c09010001d00c048400b240c10038202c0c50045000c44c1c4402c4103440c404021540e1200d840e5820741401071b82d09012000100c0ca50b5144191403040c54a0804a6540e42540c402e280c000c060000b40b40e98600300070b50000001d55400314900d85d407540c0d00c4d000d80c1e070b60f40280d0009a6501018600e03c1c80c0a280c400b08a030780050504010703ca45030340b0f4500036595941715103081d942030405106040914040a03607410582e6440d0000c500744900f42c030641c9107560400406001e01d0280194580c0383c0040c444da0b0f0901c0b800000d01e8003000c10100c000c10079000d0980f403100189a000d02200100301340d03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 398477544 1250 398476294 398476319
    0x15060309020315070f0c06020708160b0906100512010b0a0b0406020c031501030209220602070b0601050307080a0b130e070302091b030a050c161b050a031e0203010e07 73
    0x3607000710111101040702c0380c00c1101d049010703100381c0c011400c01038483c07a100b0b016030709541d40207014090041c20000240c03214002a0f2001c4102001000c1c155041d90070013185501942e001221100140f80c03e140080010b0f28140c51809010700c11282c40c03203203558424094210598549010308101c1400f962650544602d801a00405002d07014103101c0092901b00058100c2104001e000a0700081c0d10316000c2c070038003c8010f0048202c2210fa108003d69681140048404a070312031040107036290364508251007841c0e400303000241044801c01c28403a410303501c2449260002d90380c01000aa002e10440040c94402c1842c1d108507080341003206103013100300080f61020489009407640d01e140e90302d01da02c443d1f60400c49600300f850040140013103400a102035002c6540a660008154684085440220407019807214100d07480040445202d403248000b0800c00010442550340c1140c643c1180e80b0f0014020110381140c1c0080c00090020066540c02d400c0b00e090050040309071a0010b80300c15a280e221f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 398478794 1250 398477544 398477561
    0x9090c09050a0b061b1c090e1501051c27050c03060c07060b0301060b030a0e100c0c030c2315010501021204050609010e040510050411040602070e0a150603 68
    0x3080c5041d000034503189041c0550441401d004000c1c504e0640c507001005c09244001000007803d204016011001c4020001c00001d400300f240c4405202910345020303450081401804041d24108440d10400c0c0f59800001350b440001e000215640624900010a0010428503a050390514405112100c47c801190070244409004400b5111112086002e15655140a0701c10300c90080e4100540404981d00d40d015440c103010082c00807a00560b0380c0145415608180d0b2022102a40c0300751580d0040d1041141220401141c1c0c0203008140702d203840501071243c5801d002d400d2142c454140c801300315051007080c0c4042c070803280210500b119079424603541c60004991000c3c00e010a030002c503556000185030240402d0320356072180b070541441c051105980014806c07505010903980070311510369850044a11540004004240f42d03841c00d0704110542e204d000b119030351827500300810301c61240d01052040903154900c141076a1902e451500100074080b182540540e840209404074600d82d154014140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 398480044 1250 398478794 398478809
    0x521091501141f140d0204050402030103150c0c03050405060706090215041d060a14030f1b01020c0a0311060306060c0601030605180607080612070801060803090a080307111909090c 79
    0x106600460b00740d200002d8142100013260345500d4071651080c01e00001c0042031104071001d41071a40c0d601c0820141e800a030011203980ca41c582800319462001d1040311469a8545440640c255071910068211f1065014481c0603030000039a100901100d40c0000c40965800b9042403840c5060242840490300310b802048203c0d0032500300d002d00a00e80d100014010340c0010490f2110502d0054504864024100320680600850100d000304820921a0412220140c560400d9110a2200081c02c11108a01c600e10a0f0120038040c0003086c00d5000f0b080c1d02030360640f074290740c0ea180e0100240c0e00c0e00411041c080039204010010081090580151380220100c210001588000300e242a485d1502220380d007000404e850300048952070000c1c50b070300d115490b050a0340d04503030b2181d68642c2507607000d0300071090580c000204519282800300030030303000345220000f550400401d580c40d201412000020b044c810110082c0d183d03646101300944000034481c4000800c100b0030980742140003c0100c1c801e290 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 398481294 1250 398480044 398480059
    0x108010b0102030309030f03070306080a05061005031902060a1b06090b06100e090c0f07031e0c0b0a0203060a05040c17060306060f06070606030803010e0103050d052109150114 77
    0x2031495000005590040d138401002d1070a0402111300340b0025040149103d04168952800259100007031001d110224080c2014091628022520041c00e00e160362042d4040c0e80000d2042c2480301d08002c2d61209a641129040ea5a041d01d2208131941403c16000c030724000d03850804c4100f008140d510410019209980c508003d82c1c2d079a007004001c42d8811295400300340c5009540002d0300d82407110a60103d010194581820306480300180950404034048011401c02e0b46600004040d100c000c94071001e80303103091646551655240d4940d410080c14402a064011020401e9941c40301452000703044083c02c10030908030741d1540102402010401c1840c0b01e1684008240c0700c0c18089a458410341000d4041603c040b10001030101661100e001070300c12320743d520000300016030345000450090010f01e00103500c55046050107418405456409030500c401003100c01c024048000c46112100182e8120035056a03466903c82c0c24841c0d440800004a148140040303181c030f4600d2041d8003146401e98445 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 398482544 1250 398481294 398481311
    0xd020a03030e031204080a02010e060c04030c0f0b22031203090b060f031b0d0b04030e1503090606210129030102040b0706020918190c0f0905060a090f0e010801 70
    0xb10346910401c8401d0341d4829103040018085405c00b00100790940c1217100001388a2404c520701030a001c0c059421488006002500300700340031400e00000c3c0689810300d0f10040d0503280a088070f016200b1114000c0c1d28000109c0000032500000421000654101c54440403c0000d900e0040040092003030450303040603400c0202c1c0050806a11003001721002034020a1440d429500342106101011403250740070380310160820000c0c11400345980958800e40300c105160050000b004040d012805000d40303e07500c01c2c002c02103031aa0000b841c84d0064401d85000003000e00744054080d240410442444880d800d05101c10000c0d0000c0d00e001084840010300d141c0320310801700802d4240c0c441c52041e11512107081c441c0c0e80100e1840c0d4010500524020a0050564202d201043c55114100d07000e108041d81003503000b03005020780c090903255880e00c0c0f0f0b081c10703421003001d00a41003000501070540103a40200f95040343c3c41c041c202d0341000e0800210040c0403e5540d0200701e200c00424045c0000c07a50800700302 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 398483794 1250 398482544 398482571
    0x18150d0606030e0a0f150f020c010b090106020a081602010e030f10050604060302030714011709012403020108040b04020a0801060e060a0e0f01030f02041b0e0102010c1e200d020a0303 80
    0x342c10151300680b0414411203a40f1b4102083c800c144101c680039640300d801d6005100346100404488669900101d40784011a0070441c442d03905903c00410340d0460044100001c507004102c505842c280c86041815000d1400101c40c241d1074508601d40500c1290001460a400000c2903640502002d00506c101c0c0c0d00c0c40701b80410b85060f0f103c02501684945000d1005142003d10490505410300d04408014a69668032000003020340e0750081995442d110350700ca03a94015110784e24075071211480c1c01450300d03582c00240b140500400103020400024042411551552800384c01052004024004280c943c0c80031000ad0606941c000d104125410001030003104134085144105000783c03100800d41c4c41c44c1ca641c80e0030720781c014040340e0081c1d44e46c2d80c1c8149501c20001c103410319a1581d450740070580d401c0380060b0031038600d0149001801b07e4001c40b01302c2104003482c0d00a0791515494031a124100c00e00d400050703600300740026800c1d0300034003120b140c100e41c4c006010010b03603010f5902401700785105001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 398485044 1250 398483794 398483803
    0xa09051207031101112109010902060f0a02070509100303030c141308060f090718020c010c08060111012c0f070b30130809030a03091e0b18150d0606030e 67
    0x1b50000b036100442102d017450414520940e8401464000402c01d15000c0c0c2c009003c80d481000c010800c0036001c074680094660400a48000d008159521703036a41c100708014203032042e40c1d44001010107032690b0524021611409186214039218030360181ca81038000240d80340d580072802440740c1446807100180c584200c48904900074100e00003c3c0070800d0a001241076482e4880c0d40101c1c00319020410406c1000c0d0900c00d41c14140d07129601c100d07a03801c02c0000100b82c8500e9480b503400d1607042c0f00020862251306403541e80943c035910312503101c0407034030b03c0c010b8145002e5490b410580c1c003888a00140d030100a0b0300612000c9a414100d00103003011020501c44540138001600d4407e42d210b00180b000d0201244540b102401440100e0a1100040029103401c4030104120b0010f03045c01d4081200400d05603082090303410a0548030300071800d05104242a015407204141c01e840000740c3c0043d00e4650404007041c0401e144070f03c42e0b4800d08090104040d0440e0320402001a01e0210300304000e0700c1c00304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 398486294 1250 398485044 398485057
    0x3e0102090604091107240e010c0f120b090103081801080f0610051209011505011d041517010507120504120f0201020f0a03140601080f0a0905120703110111 68
    0xc20890425082c0b1100b0001841d204c0342d21020090b00b086541c000c5000c03d030701d02c00e0380e0805d00c0440e65a049050b0b07003181511690724a01485a0501c40600d6403590016203a100074050303490321511502c049034032500940401c128950308400b1050020061185003002000003c48415514030180c002c2401164a00c0080f1100314a1082d0300d800315031245001114482025500d1a000f824040d8291700c020080c02d00b59000ba005079503074452014104415030f2202c0041c03009003495001c102001020301210155651070a1040c1e40e00c420f40c0c9a01d0080100e0780b0702400742140d2205030048010010b900902d81940c2560100385d402042c425018218001c091241d0350148104020031103441090301c10b07400c128000e8040d550240710003403aa900d42c40252040404503540410251094440d210b240100500620f040107601001c10182d1918601950303005208100f00054104030340c2056820524501951041d241d40064600c2c20706034000c0b40e9201034aa05c90003000400c4014039210031070311554 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 398487544 1250 398486294 398486299
    0x406050c0c0706081b0408010504020a2405032d040b060d080a03021c05091522021c0203030f04090507020a11010c110306040b16050702060702040c3e010209 69
    0xb0380d0521a46100f0b000791a0050200452500502c03a420303242e1030380b43c0041d0000c0485030b54170801c000661070402040070041c44070b0340c0c03141c3e0406041a41000e107203660315010381c103005000021500b080000b80035910001044a0034800d1070801e084e07164028801900e0030b03501007211401185181c81e2085003800740c17a6102c0c01d858504100c2d01810b40182d04940e940c9d80c1302c900c40c140c450010050500405d8856403010f006082900492030a42065450140024208041600d00c420b0800d0103401d9602d881601203d0440903017050302d045990303043c000e00000307404d80004584180303466800c802a0007951070103401400603648110049a650b1074158018040c00d07034201d0b030a000ca502130b220b02c4c401640034404040c02145150082840c00100f514100c4128014100b080450560212183d8501c0300e5403416924111031500021828011104003134440c0e59642220714a040c0140b2036061030745042440f41e00c0c6100d0486a4224620308503500480e40380394103089250110040c4216054034000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 398488794 1250 398487544 398487553
    0x70f0602060a0b01110604121b0b0105193204050603070504050a0b0d111207030b040b0c0d050414060a140109020a0203040506070503130e2a19080406050c0c 69
    0x40600ba403002c3c10751202c40030706001c000403003d18040400c1c000c803031045014134a82d2052a002c600000c21a2000d072800300181c00340c0002000016601d420250b044400494040040e0f0300c00a071600a200b060b903200d4003071341e0407c441c2d030300d03080c080700d4115800684802c0341c45251400710f07010300040c0d440850302e040e41500401c2041c0141d1402d54400c580040d140000043c01d289100e02080070320740c6c0454183c909031003034a40d01c0c3c081d2410388030307500d442050180944000ca1541e5210b129039280640003c011001c910000390900c039125045c2d490700c024144003403041c0c2c00c207030810240800c210800401c403400b59400040c90029640a0a09211241c2042440d03d030b20b0b104044000390003031403800f011030108010000304c540e00e44001d416507500550245a58460062840d10990360550151710408018000c10901d03000c101c05c00c4200710290003000401e012401090a101e03c54170300311908076000742104290403030b800b8641d40d200e00d2140d5010010340e200c5881c103500ca40105540e07030045520 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 398490044 1250 398488794 398488801
    0x306070f0e0409110406090b1302040305060708040303020d2c010507020c061606061d0603070e04110301061707031106030103081b100f02030a0f1103072d11070f060206 74
    0x1801e601420307903d809464110118200031000030207592041d0f10051004d91504034520300c40c90618200c54454022800c11450240b03140d030751645481d0028542e805003c0002c0004003030500940441d032014010306002c02486251010114000744d0191040003600402089407031038010511610340a01a560000d20b01c01010101300710859100f404803145180e44a8003d1000540c940682000b034164111150f8a0414110304540c00f500d006021511950102d0742c20448078a4164903203400ca504400036519021646000c03d0140c8403543c0709844451b00201c5d43e03031510b800424071105a078450100c0003c400304501c10440710340400c0c04042d1840404115018401b44140006048040404103542c80d8407211031850f01200c500034415070030340d0f400100700541e00708a0b100d0008000c030048410881c030200004140250701000b015841442109000303080c1e05040e91804486140c142a00d603600010440c60080c040c000e1416440d0345481060700c040748102404203c90103441c0c0942c0140369654 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 398491294 1250 398490044 398490049
    0x80703090b13141e16050a030201030216120815010c051005090f030703021509010c080103060f0209120c09060a150f09080f1f0908070b07140a0e0306070f0e 69
    0x380c030700c07000c85200480000c440c00c60941840b180e44100180381c00880300584d10340b900c1d410041401649102011504802d000d076503188102e40c3c003038035028680181c40301540040c4403000c40950602038011080603841603211f0344d00544081c07141640048021811701000010342e40340290060042107034209400f9a4051440c81c0e00569100c600401150881038020103140e046a020100036001a08000101200c4080c2503801940094241d8020018440362807401809444103000042c0100d48810403940c030502e440c0c0542e801d90303400504200054054aa603740d42d1281841141c1c0103040715000503049207010301002d81192900f004041c2c03800d0a034182191a1103003c2c07403040c18449521800f02e50a4810000203000d00900b200410103100c4000800b101c0c020803502e581c946c0c900300084140010030300ca080da484a5440b228400641d16252000d544141c03040700c90420958001c1500040715074007401070f6100c840168182c0c0c0071610381c4007040382c01c00034100d002c4c80420512560034070b060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 398492544 1250 398491294 398491321
    0x60812070206041a04151b06090809060d0b040c020f0d0c050a0c03030c050106080c0d03030b1c050a0309060203090108070c020d05030406020705120a1a0c09130c080703090b 76
    0x141c40200000c1c6010349070040c03291001180c44010030400804901400640c00c440d0000701c41001d64142100601e003002141c01d59103801c1f190041c840ca85940e00361080021160950305101001094603485501e403242400080101d000444d10680c1409022035400c1e00204409074000e55100140004400051003940d1000758284100c59510a03d120f9102007030174443c1c180051803003030381e0354074020764141401401e5400350740010320705030854080b1503000e07602c2d0b0024000042e03150801081d0071407850001100464587c40303606204900b107103410104040071035040c281900c40c0d00c85045043d01e410007265a070180108440c04039900e40007040c0c2c01da00540f01801c07054402030061900d000d040d903a00f41550440e41c070803805a400a82c040c040c034605820019106241800202000c1c80c280d00c03001412103c00c411502c2c0303042d6140106410000e0081110440070001d4000003408208011241c01000c00d0021100000c0c05103000c01d000340e100340181c0003c2034011750503000c13607111402c410050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 398493794 1250 398492544 398492557
    0x201050c070b0706141005010905150409060906031502070215070f0516170303040b0a110d110910051306050a031d06040302060f040308010e041403121801060812 71
    0x503072140020004164075088010700c0c10a204d284085580400304c141444011700151100080c419000d00c14812640c0c410803a6084410450307042c420403200071615803491090390030601c001800c2002c0800c0c603115940008048030300c14058254550401110301003203018010b4004d5010714040e0000b118204000041c1c13008900a6211551480c001d075552460300c80390410310310110006500800040c0c0620200260000080000d5417452600e0780d545c102c02c0100400c0d0003034050f5964078412401d110780c0260303040c1c80381482e4100004c6a000c55000016001034400d01c1c480c51002c07108054452085080c0d40c10040030604000241d81000b074252841c0d00000446401c06540d042103040c50030140e03118103000540080503224608050800a0400b14014010481c5100031424480029800366101e4110703005d80106000503295890003c00103212403004001034030000c50088000101c0c0704455010b28400c0340c1c00100999400714081c01d80f066032150104ca6000300705d0034036a00b03100c00300412a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 398495044 1250 398493794 398493817
    0xb040b09060c01020a0c050d050f0d0e0a1b090b010914041a0a0306050f0a1e0c090e0f150f0a032003070e0f13120c0510110c1216020105 60
    0x108441a02d0140c220307001a1010780000b40c040ca0144c00f03020040c048a400c0f490b50b840c3c45072a194007121214080d100304c1503508841c03645ca6908a03030540702804080401a807000c01c605c0003181c924170315400c4210740d0017030b820700b60310381a0f10820340c1d07001d040501e0485014030769050070b081d44441008014811000c01540c2081003681794500c0381d40d002510f2026610403240006d0a052010070548a650000d01c60141c1703a2511484a501240403c01550f0f0381500b400c000c64a00f442032400c5602424a5100d8651207001c3c10a1100c801303000c40c03081d4030401c00011000e188011080411909028200040c0d821200644007030020500f13242503a0301207a51042c1500c54501c01c040881d18000e0903501c41000c101003202402001414005c00d1504141441e0000c10485415200c624035a07244d2034038182446401908001001001d00218107005042c240030001d4404032244205541d01c51a0803c9d03450103100c504550b84c142107026103005a004881089600000341d0040d580c0764080124503c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 398496294 1250 398495044 398495047
    0x90105120708030d1d0111040e180307120201050912180102010e0312010f0927022701060909021801031d0304091514010e100302070606031a010f0b040b0906 69
    0x42c0d5110100002d00110015940004010106940d4031064210742c480704441039041207040501da0218009403001d50340c0c8865000c2c1c140d281c0007002d00b50200190722a24a030700000c100c1d03409100c519030004280c8025a00203108c155900c610b166201d5849104001010300248030500e0a000b4034805521060010b0000245030007190442c40d1850304210700000038255800010301894001d045040000d0290311003d01180700c1c0095070821581c40014205042e500d0b0b240f02c6c0040d560f41040362005003100902640d099418845814517a2009008031000b00c1e14120001900d00082e200704c0b00104000510608800030003270044002c0c00c802d40f501c484003103c0c0e80084210f5942030004100902d02090000351120410001c4985e161055002000185400b4503420250740c101100014000c402c07200d1001c1408200740540c020302404001130400e51614102208020400b540100d00564480c560041682c0c2d031013908003450601d0045102c060000d010030406111044050482100000e2586 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 398497544 1250 398496294 398496299
    0xb0c0307021c09030b10090c050a1b060b040e102d2004060e03010c030606170a11072a081209030102041a09180702250801020c060a06060c020901051207 67
    0x511804402da5a005049140c200100441f100910510100c0b46035414880d040c0006440058441101a8400340e4030801d210b11500400c81a9030210400800042040000d00c3c07403260599590f003483c86004200e540303040c11240310116842011001da00141030043c0c5000156003101010303258444003906103c2029040744c0020000c000640082c025642d902104480c00d4001c241c00d45130241842d2040c180350420078402d580e40306080100400c0300c01c00300b02c40d90b15544d4036000205861800910306c0c06001c90310b2030030081c0c002041070f80d28055940945206002e84070540c15941d0a1160891030f0340254038400001e0f4118001c1c241401d00200010309041c0d07500b50503142058000e4031205404d5000131800018609a54030700c0300003005c40c140d00ba0ba03240a00d000b966482c070f20b070581521030b4044800c4c0000c1f641c040403074038050105800250340707942040790f071217695903819220541002d0400b60041030b034078031880020a99070303001420349a05918010074088903d2140342810200d0141d008003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 398498794 1250 398497544 398497553
    0xb03060723090612070f020105010f030f0b060111011506090b04150c03180e18010e07090e03090a08030a111212070201021608030115080c04210606090203040b0c0307021c0903 77
    0x21480341c5115118031b0001d2105040085c00c64105802c1190b44c0c02c070041e81072002ca075031a001c190046500c00500d1401c0d80350f100058500311083c0c0b05814880d030130203042860214007030041e2002c9036a26212404030700c1c1c0300e106820660140303019900b410101d80b662441c00c64402c08500b241c80f40241000784039080070b0362100d0a0050140c02481d0030b21180818411071200c88181c072010000c05000800400c40041406600d941d501d106421803140c4036441000110b81c00d100f03d03421000020030100c01030b40c1d51022940c50350041101e00d40481d030560b40100403030002280910440c440d50031280e280c140c1019032a108150003074441c404540d0300b030102c021216810440030405d24003d5034001c0d12589041c2c040e070203a19404110004000e8403c0c28810030080500c03d03075050329002c41c0001c1103401d00628091682c00c240380041c00007810b00b81c1c0011480702e154000d60140e80034008035241a6100d40c52646144016215080140c1c40314a038484000184042481c3c0b91080d4038100f8012580c940b134 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 398500044 1250 398498794 398498827
    0x101706061c1a130c090b090a0b0310051509071b081813060512010b150714100902030d03020909060409060e0d11061003020105040306020310180b030607230906 70
    0x81055100c241200044140018464000c0042a0815007886022014008107c8100c00501400d50250302c3d903207102c942d40e0b81441403020700e10034040204090b2074480e501e84000f0640c0000c860040d084030000c204013034440c17800e0100e41ba00320200403915989a585000c4c0c03650041c01c0e209000c0076001c03503122696584400070008407990038030105105082008100d880540d00c400b83c01ca07a13145c001c1d1244d56441c0c000500d0085200d00e2000e580380c45950900d41400352010500000c14040c89001e00301c0d24413194400d0018a0098045440035081c9103070075022881000b003995400803001000540c1450f003500304280141c42103e012400850800724945000400354050f008100300c1c0b0340c4041c1c140b500300022030344a6050458400755516540000e0b160b40700d24040074208540010003e5020100f010014004003401d442c1c020303241181c44002c8000700020000790384680038000108061a00c43c0400261140d030a00d280d5200f0755802c4030140d1607900c10600240c02038810700240391b8a00044a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 398501294 1250 398500044 398500051
    0x8070c0c03150b09011809050c0402031017010614100c1401021804021305090a06030f0f060e010501051f14040303110715020a0b06030a0506101706061c1a 68
    0x1c11041d5080000c0840030b06858840207600e00038100d0f040104004484000390100e080b070000f800080c1240107041c111704003601c1442040c1c205e0300010a1084010301e01c0c0341c9004031141c50014409051540f2903180c26148944111005441c60141c41210351a012190718010759650a00545a505560703c003d07030710100c003100c10f4980c2d50201d0a0400b20401c00c50000e80d400c002c0f41d007185494452820b495040724180076080c000d00c3c40c600003401c02e49141d44800d01440c0c0108100082c07031420318080001542e080801c444a60400c078035405407040500031103061301c41c0100540c00304d025412a00d9140c1d038aa4100e0f1042100c542420305d05040d00c800140091030283d540e60f1403041030b02011a02c0c015980c1e1003440714044211460348120360105503a403d455004a050545868880001c0c3c94950300403409080d80c055003051064140586907101c003112002c20f288040e800b10584165103401040340c0c181e8104e403a00440c29016200d070b10100e03d6142c4030b0500107403054142081074250000c101d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 398502544 1250 398501294 398501303
    0xc09100e010e0604030f06050c1c0207020f041503170f0f22121b15030f180b01030803100b07150b0d2103110d0b19031208070c0c03 58
    0x898610306550b0700c114046000002941d109241c545141c2c5d0f44039207030402800107070080e50f1350f501090210032080200c41168032030303c092151050315443d5020003940000022845000ca44816004c0740c1002e0146005000b019801e2003492480c544410072450407002044440f40404c110040300301d130441000d01070340340d8a201c0503911200b00c0301958503800c032941c07a50120005140c100308204ea900905512074290311042c140030040020401c1050400d43d600a6a0301d00705007010441d07000d034554064055030101c101d003400481110300f801184a1303204ca0001d000440c054005101085547c0021500b12000d06030588900b55240352003139003904080c10032100000e088906486258080c099007484d42d900320340d261581203695980c072580710418125402401c540314201c0c04107078000c1d884401c501080400c110359400b20020040c00629101060500c9072510401c1c54103418001c03000700050300d40c080ca40b20b000c1050f000c2c003602c41d6100141010100951038040c000064003013001c0c880194440d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 398503794 1250 398502544 398502557
    0x1090606030b0915070311071a07170705070336080106230d0c090612020306010902030c2713091a04121803060908071509030f03050c0910 61
    0x118600b4542c41240035100803480d41c000c00020310380010441c0c06a800200908000074801301e16006941d090003a00000307800c13800708040108125024241140c03260a841c2e9440300711003a81104841c600c43d05030b51420004000303201920020b07000c5c0c3c44d41019820402c8040ca545070b40d65041c00001160404809200011024200720080c1c09000f1900505400030349074407199840c20f644020b080c1039000083c41480104c42540900080141d1840a0003142500b4072203961140c110921844140384104e02902c150400082c14030498401d0700e000d6034185852614000c00d40d483d00220421844409840c5c6040e030880c03400956030182c5603512001e000e40c1c0484d0341441c60602143c500b044105108509000780d041100148400304041c04404080c20a50341c0e0402da48a41c580c00840d0b500000d0009242c401c00340107001c0310301c02500c0b60320705c914200381c00d21404482035010342c2d007018402000300300300541105409000760480c0707621004844041e8141310b405800660050210104103002c68407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 398505044 1250 398503794 398503799
    0x309010207030f0801060e0108190f02030105030706030e0303010e0405070806011517060906060c19050c030c06070c0e25080402010e0a0506190203071212050a0506030a021e0301090606 81
    0x81143d10800c010b642418038000769854008054400f200c0c145045041000460005204103030b480e07202c25218444100402c00580d0b01e0141100070b51081c01030b1440b920a0120000b11148207028500703011290a01442c29039180409a80e214200a0700498013070007451008034609000300481da0080001c017840c0c0800001c0b200c0080d020b80101201101d0403206202000540d40b620300d02160440010f4034040e40c0c0742c0c4010056030034002c2e82080082d103000c00d0102c810910000041d0409000d03c100c0959070004000b0781002040e10650740d00410700c291044040180d45002c0c811143e105120b0316070f00741c1c0400f40b40284a00e01c58100329403004500e44906010035544d00070034190b8807540503240010094100300004101d400380f44001c0d070a0360600d14003090741502c21700c162000d40358042c801c1a00702e07010302d2020307040080c11f210010b041d500d40f40c00141c1941080c000c60b80942d1000d405401d0840f896001c1c01100b11604040c014050180108540c40b9142480348000440c012040080c0950 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 398506294 1250 398505044 398505047
    0x50c030a0305010911030103020f010c030509150310060906020d1407020901061706090106200c0a0609140301020418151e030b0a0207080a0c11040c051b0a11010e120102030901020703 80
    0x2d0707100170800202c0206100520042e281c1d07584a019070301d000d00f4428054451880c04030356034401d002440b41c02c0b2850780400e0300e851fa105000f441c012001034082460b00e540b43d107400c94524509100b1800181e0011f1707001a9918056132400740c1c0074034101c148510b03102d45600400d10600d0281d00331400128190540901040c40da071074980c018200302e8050303046500d4401e00809000e0040b2288900c0300a05450385040c00e0300304a0f950740f041c009004c420300140e9130100903050071032910031505250b1b011900c107090791a06108640c04d882c1148031004005102a0100c0010080c440728238030000c803d50008643c240440c802880c885181007480d00368942145400300400001400201a03a4010701428000801580503207060050519154046003441d00b13002d800d6100c000b01003038000f440c2040c020500d561000007818114100800040304806000060b5568070b021600601810301006140b991584102c40000e02d9400003040803d020703402940d103031308a900c25122802aa94000760750340415 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 398507544 1250 398506294 398506301
    0xf060102010e0a0305091203070b011e080d020624031c11150a0506060d05100f14090c0309012d0b09011503050c0f0c060f0903070c1203050c030a03050109 68
    0xa041140c09820b0803201c44e5005012401400d00051280c041807203540c0c10a042001901d00d22a0014401046540d4544141c009600c1116a0703001020a05101050107030001400c1040c5400d154000c0002d03075036120b101c012548070300c28000300004d0944008000780d42d08212800044070400720645425005142c0540013445405112215420001140c001060b011126991007400014046002d41d203490025481c0d1003000f55030212946010140715500016040c1081681c1c01007200b869060b4440e2507008040e0071740c90215a10071040d400140b281c004c00005550080c505100201e0b01c1303590854446080007140700072041034002c0100c4204154054060000a000c0540d0054074075410070355010f810300d03c2a50544141034803100811505a20102114004041031005685070b19903030016a45030305054524401e0700c0c105d00c1c08035826010100c1220081903010381c0d4803070180e00e4a10914400d442c2d0100540c00d200c2c00b4440c102c07440b034052000303103440e03580c55070002515818880c001c4200c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 398508794 1250 398507544 398507561
    0x90b0f070905030a11041103010b030402030709050609150301110406110d0302070c12050a0c14040608121602030f0105010315270f1407170f0609070608041401050f06010201 76
    0x3003204846003080252004a0104c104542145140c1240c8a9500c04580980400044003604140000001805054850107275005038401c60a5a121030742d40c0c0c00207002c3e108240ca01d02e5000c03440f0f10101e2480b110208035100c3c0c100003c0c0011400292020a0f5001904140c6c0000040782d100c4c0e00d0410040800d01c00815a0301084c1811405c044082e00d80140a4055001d2480c1c0850980380c940140b080400140d01159404411489007a4840c1d03040c403070900c20143e11034062414004045015a0045021443c070401c0d48455802c00401e0303090f50b1503805d04280e050340c15009a58005000800030700a85011350f0154050104080070345060404070307420b041c920121008240c507c0c4009545442c8080021500403081240c601e0150400f420701d8810241c44aa0700d103d5004001042c03910000c900c1d43c0b126049090310310350b96051807801d40742d55044688440e580c02800302842010302403600940c2080c01170303e00000d11940d20003134900b180d0050f81c0c11801d141c2d4180c20014a0369090150102 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 398510044 1250 398508794 398508797
    0x20010801170d0c05070909060c080a0603030e0d17160c060206040201120e1009030206010501030b0913060222081605180a020a0c0501090b01030311060106020d080613090b0f07 77
    0x40341516952581c0c948007408800741c10004407030124424032900704642d8006c0c1c69000001c000c05030303d07864440000c045402007240403505c4040002e99030303c90f501c075090499030140c46100c0e60704840c1082205241901004540780c0c181f12a0941d00c11b000f07100505406e115401e82c0012009441c01e000200c3c484950100c41107502030740030000180d901156803c8841201c440c01305806020214060400540b080c0502e1400d1801e10950203040d400200b59040f074000703880401c0618034000030310440f9a02213400c1082c1c00c1c0500103040000f00158010280946884148201c00d201600c0c1c80f60084070395402402c8a900c250010190064102c00b0880100012501c0c10282002c025419868000050060051650101c0d040c141c2034050024064029400b030001c004000b801e140134401e5850038001a00021a00034913000366410020b13029060780d0440c0c00521088815000890b0f14040080030a6000307003030498a911005514000c041c40c0b24805d00c2c4100041c41c1100c06a10f503080000c00000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 398511294 1250 398510044 398510069
    0x20c010617100207030c020d0510060b04031124070f02010801050103091e021f03060e010515180f060a02100507030605100507050124060e04151205070320010801 71
    0x140701071001829944140c076105015850365242e0405982c3c0a24100e8060340005500c0050344c200100800e482c40d0549184c80100016074403440400801d01840c00024100542c2c4241c9980c1d0b03142141c407408441d281808240c04903c03074146040065040070208a414420b401400e00456130030940082c050308082c60304000c04161501c500380d28455010a01c1540c00d80f80484405540ba0203c13120601d601100e450b040c0404c102e00001c0003040d0510810460564090000c603042c135015408241406210007417078107080356a184120010100290b05502246094000e8442d0f120351015107990510742d006881c14007042c03000032055990040543c001c0600e4064140300030b503121402844100f1161902c0b07a1035400a242c03180c010308802c11040112021000c520110724001241c12066030041d5542d0150080e0b081e060000342c4462461210460888400c00e00200012541040155005501b2a4050b6507070752900c0c1030a030a90a611a10284103c500d00800d50b00a800e190040c04170f40002e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 398512544 1250 398511294 398511329
    0x3071a040201050d02030a09080c0c0103050606090108010b03070908100618060503060703090201020a0501050f100e2406120a05071b020a0b2d1902031e13080709020c0106 75
    0x90481c0300d13032040d00040710342c00700100d1084001035100410b040d611440d8140d03034041d041d2813955204680c600300c0d07001038207081c0080d0907030514505561003030030107840b100d01d141d080207154082074100410000c00c008a00e03100151a10080112209101e0000303000505581040369a88540c0795040c4d503503140c0c03814007204008079140010041c3d4003001a160001d02c2c00110310040782882e50501000e80150b00f000300b030180c04514005040d006007002c2c140c0720905640c030b114246001504607200a040828108588801a110300050700003e200510182c80c05a19a01c0c48858039002c1d1100304c902c0fa40c42c0304201a440c0c000042090001c50320840000c94680707980003c0d070800c1e09002c2c0801e14203002c00c5044907142d15801411b8104010718412005d2030340301a08c858690000c1803440468501c00211424842c0044102c032208011081c0c922054520056a107440ba440100d18240504400ca0006208035083c824400a09048080541c1e195486080316081d904107030403404076101c2d1315101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 398513794 1250 398512544 398512547
    0xf070b0a0c1d01020c21010501051f0f050d0507120b06070c1e0f06020d032306011116061d03011e05060406050d06020c0d18050904081b03071a040201 66
    0x205034001c0c0d2400c4a202d04601c0c1d600100d040c04101c4840c3c40d00414031103080311050281400c40803000284200030445a03983d4000c0164007040400d071100258200b0060312060303885242076444034074071800d08034036000c0e03403981010480e0030031909503001a00542081c0064075450241c032011080480c3c0d03c03420040140c0f2001c0e5802054402c18007050a680039095002c40202180030042444003840c80443c0c1d45c400300651270316032844811001034544080c0c4200400590441d0098810702103803010135907100e034019100c1d40c0071544440120b12441d00ca40060101c10184800500301d071381c0c4c4142400380c034032420082811039541d80c1c4c0e1099041c041050503500e14002c514020000010001c50305860b048041401041541c1050760855030009a010901c00c041e0014400292013800b100c000388103800302180c90104061070303061604020081006149040e21405030040c0c0940c3e01985042030400303801034490b2107138019070703415000450031006008019100f290400100c045d07a201a01c3c16900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 398515044 1250 398513794 398513807
    0x30810180f0603080f040f090908090d0f08031003020a08061e13020310091505010510120b030712030f020c1c03110115080f070b030414120f070b0a0c 66
    0x4403210166524001500901a1900454021904040703801e0343c4104076072003841e19500c00d004803d40402d0741140000c80c202c00b4400c500071940c01040c4141024402c00c00c200089202c41c0c4140c0340e025044091401107210040218014080c0e070207600030b42c91940c8188400031040d544289450380224003040b00800c500250003480340c02490300b0b030040750344580048460b40c0380343d81c0180d0184140070500c8008010342c2d0100d011a8041c074240d04802d882140042c0c2980c001340151600004030090740102d1398003401c046003211100f4800031403c80e0550010a00d020f0850f400340c88610450021b03d000c1c10340042d602801d000d090303c013070b01c502c031220340109020ba81e503294800b8003550602c03c54018103200300c206c48000300c2140028010307030203041f8179004405028011200301d030240040c954142e00c07001032107104640315160b1049c00d40e902d44d00c8041900c0c0301812100740c5801105014080a81c00c0e00090682a0801401603128002400c00551080d40204860785241c6401c0260700c0f1181c2018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 398516294 1250 398515044 398515079
    0x80f0c03060f0f1f030c06030513020d030305060607140102090f10021b040e030d0b0a050d0b0a020f13030506090d09060c0f080405030318030d0302090a150c120309030810 75
    0x90900000d500d44c0d60840c4243e60701c0034410503030725451413008010002100904400c98401d079030280301d6500c9507441c108070b64410880c02541300001c007100100090081e004640e1110000300032a0400d034481d2184160304103800d070390074016540002c20044c50b18110100d4003501c4400c3d910032041080101003e0750fa102010116010900100400d030071540e266003088000d0f114000c1aa5102e459844080380038001c00c8261380d01c180c00f40d0f90007040a04040074500400744c5c0140d070101e159100c1c41038081c02540841c078000c1c20410100011090382c0d48202805000f140300d0401403203140f40c80b0803490f0800c060381c4241c00070001d80103010810140e10414825200c5d41060f24281603000d0f81c0f401d1106132089500c000d40600001c9161390195000b1180403544900c10303000e0f01c0c002403031008118102d1040e4803505500184500741400740c3c402501d6071134500911810510b0340218251208041d454441603101c00003a00c0f60440410150f212120369006028035041450450600401c0c031150720399030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 398517544 1250 398516294 398516311
    0x105010509010e130618143018120604120e030a0803010303051804050c07020406090c02070b0c010f0f0506040c0906020c010e1f0522030c030209130c080f0c03060f 72
    0x48800c589058982c3c0d9240540580c0f004903e4440800c040d92641c40d038221104e1004190451000103c19803104102904078230f100726111464141c40d8070050007003120f83c2402e241c0211070103011611100341040080d019038054a084d541c0d903202083e0007040045c410710124003c4d042011034500250103030703090b00e041d2541030138102d45561101040d865011035040300903902c5810708052007015203a40c0d0080c003400d4000c1d2000d2100988510350781050b140b11f2030820005900021003040a1000d86018210340b5000700c00218101c0d514000310026078001500f80c3c04141d580f00c0600210f49071510800c0c09071703101c0d8202120241d14050000c3d444d01600101c180c1800303002a03d02c2d103c0d0352482e81c0c3d204002100008440c1601c0798071070040058200d0381c0d90181c000100580345100a02012140b011690310015800b0558217642c24044400b1018204052011540c0e061800042c00030760700f000039102440043c07d0380c5003405c1c0c225150501c0c2188a80c001d82181080c4081030180202541d4480c600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 398518794 1250 398517544 398517551
    0x2070b03060d060c030c030e0102030405060f060d05010509010c0e01170c03090f0f0a031b05030702010c061d1f06061b0317090d170f040b0702100c020105010509010e1306 75
    0x140c00c0030849400e01040000c041d90324104c0e088900c1c5825038400c1d10820784a079020440803e202c42c0d0a4203d110a4402400c1c1350b100c0d20010300c1e4080a591515401080940720301c401d25100d0361181d09480d4181c40d03004030b90f5140c804c0c0c0002107030303c000c80d054908000d103040b04400848003070b003540d501c0002d402c01e80d210100000042e03c5000400c14806a116644d088551403074850300380301d031292400d8008600150301e10502814000000c0d0700896030741e402c50702840c83c1c6201940190765809001c6004c440c51034580c0d1466103c800e1900e00e520b24500010040c041c50007450010750b120b42c401d1056440d055142000a12281d0350101a003c03600600c1e10b4a03400403034242c00d09440011000c540105040c1e401e10400600f51404291b25100c2500c0b0b403941c80540011500c003821601c0c0480d1600208402c1400007808130340d040c0145030f088034090059607280b108600c140016622001850b2016039190001004207041031082d4a0051642907a003081c1c9007046940780e0f1144203030200c0030740607a89 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 398520044 1250 398518794 398518801
    0x301061205061207080303010f05060703050307030c0e04060b03040b1b0d0f06050405010303050d0606031a0103050628060908070f1505090406030f05010506010e0f12070305060703050f1602070b03 86
    0xf101903050840d16500e00c102d0b604c141d501c0e01a10303502d60090103080558540007070000b81c5814158140c40c0003603030580320242159100f02d4120004d007901c2d03003150308100740c0c041ea60041e03031124858070001d403a1300350b0810b0380c078a4079003441c1d01090800b8100c41c5031131881410803600340241406a490f0440c1c52040810003840018400b0082d00042d00641c0d4800e1825000004040e0844000e00c0a560601400d00019640310815421aa0600300b200e42c0019090001980d643c441c4d4030181c0d025500810803241100a8a0107048008100070301010448081078184030a07038000b14680018400c100051070041e0806c009040312113464030540048801d201442c603003031409071b0269214100094020401e4030343c0c0e4104000b00790440070040d103080d4a810082440e652042002c0104000040c0402920148000902034021000704410001c0d000e29040880024400d0082500a461660300031510342002c042072000302c04050301d4007040c0d002c825014142e482e004a118030854807440c241c0d903201d64 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 398521294 1250 398520044 398520049
    0x7180f1503291611120a09060206010b03011701020705100b040f061d04031e020a060b100801210b0c090102060c0a090b1312150c051303020409050f0312010515030106120506 76
    0x40e0001d01e017406010380500034100d540700036103403101c49540d410504a0340c8201c141e8658900307010308400040100300501000c00500000d04460046600051806056448041c18420251844a641c684076509d00c4a0781c54140100804001240340402500c1d1602190f20501c0344070810000d1031750401030018042c58028101491140040311402c58440380100e0b00a4071440ca43c08219480c516000ca012501c0c101180003219441d101e13280c0c68140e90905084807842010b50007120012045411aa00064400303050350703000f8810030340c42a40b20340c42d40001a007480c40c01008019a560107002c0380300d945600c0496001182c804000d0b0581c0c66401203100c00c009822500041341d40030511503610100888002d404103800c202101c10040704003105004c65103803180071502d0100c03010185040c005480c1a40c0300d0b2022a00c01c000716503804501c44805410b50300424500380340300415000401413810700d10720070100000d054031200e14540c10084040e0020040e40714600c696076680b4005090f64 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 398522544 1250 398521294 398521307
    0x29060711040b0d0305031906060f121503061a0f0607060b0a05090108100e010e101a090903070b070305251107080c040b060c07180f15032916 62
    0x108406000c00f0803032601c07410050204d500950340142050072074490300c00c0040f2288285029280550f4854000c850005012964066080468401555141a509040c03405d1241c40c0008511410340401c0b0317003d5862a4100342c003c185991409801c020498030903660701c079400c6807030fa00d0340200d001a0a000510128401c200baa402c444e41003001140041581000083d50b030392241030901d4244500c0c40103007030050a07603c0700654051594130044558600304116000014100380e0301d600d24011a0b80310000506419058420b0100d070b400000b030200602c08200611540403285007005e0040d403c010317400c1c1c84c40408035a00b40b11080b2408202880d074601c155640c4c0c40816481c021100c1554880411944a04c0c0800113240310714a00440100203082003403e0f140c40044420103000014035010b4400c22000d2010708a00304a86c0d00c004401c03205034648100060403619102d0118040d00318a40b00241d0020600c400105800c00501015a80744024038168411900d110305a1207a2072020191043c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 398523794 1250 398522544 398522561
    0xc0d051006030b04051c0801091e0903030b0a0b16020f061209010501090c020f03251a1b090f0f06070c0306090b01170d03020304020f030d02012906071104 68
    0x5050918030000240070f0420400f0380124042d0341a240c4400740c0f17002c0400030b0015003182502190034440100120503069004044a120090700014840745004000c011101ca040781100840e550700788445250400b1020312000d00060940e1916207108527100052010a24030001e00c01c002403146125035072a06000d0f1091051601d40c0300001c0e041100c0c0460182409000d4007a80601d0070308c00103015440003030840b458800c913001039458028640003100c6640c0c41d1349030306804400c0076500d03080000c0700e180b0029080390071441084030b0341c01c01403441c11100590b80505440400c05121102c261f80d07d0360f803401c071040f00884503140014080700218000340a10354020341072444002c00002400425045040e41910032180c0841b16a01c4940151080c0041140d51106074056881040824060360041d074015000a02c6090058000340000713141a0080c070360100181d454001c03698540c2c3c12a980c44442c08600034980c1c80340c0340780c4404203400c2e024010700034121158003500c440050f12203a203c03042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 398525044 1250 398523794 398523823
    0x3170a081b0c010c030603060b06040605071b080f0105010807050d02030d030504060f1e1407020303130201020c10021b0f030d0302090604080a030f02100903170603151518090c0d05 79
    0xe2100c1c84d0050300904940c03105490041c20001801c1c074510340902140c042d112291601820804583c41d00304141c008403000001d800d03002e01c004250000200094016580c02c1400824558107000685050200503440304d4012103c44412000594012410341d08071401c5140014031540c490500754054400c0781d41c00460245001c07012001010301c0344880c0e00040544174144002c0c01c405100c1451072070b084030000010f0300b0620204000d848045e451200190051040b14690000c410009048120302d0398002c015a020020390784060f610380380010b001a000700d0b400130b042003402001c01d8540f203034005540e0400da40000c02e843d45584110940300640307005012250619424500500302ca906200ca00d40944183da0709451400d020340140340703010f44d1680e100300d203116050030060000038001d09035a0b854051100c242c100c0d40703110080703184074007a00403030044501100418031612a6491905204c18000a02001100840000d0040b4645000d98910030020301d20704040d41802d18003132040720f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 398526294 1250 398525044 398525051
    0x6030b0115090519031e0809061e0d06090515090c0924070b010f03053a0201050612030c0c092d0403080c07020906010302030a0e1603170a081b0c01 65
    0x14007131310701c041c006400c0c2c03841030940903054140c520b00b10595210120000342103e0082007400e0320340c2058000f50440d03003054491510043c041d00d203940e4541e00701241c80364a6580d1140f0401016105008881d00210041d212140004250b4007243c09e66200a0540401d1500081c6001e000c1c0c40344000009400312400da0160302c1c030211855071005070300c081016140140040004a043c20445001804481d03221300100403030900d01c0c02c1d4078000000e041c001c0801000d04c000f1070001034524007120002400310303400010503140240400141c0c16910000d0312960380f007800140c030008800501071400b200c007190744a09540e2010050003480440e10003c038184040e44901201503100e800c20280907611035190720310300b5030300c8078801151401440f41c082c0d4000038503004110254029030042d900000c000d00b000c1031402c10561840d1916405c02c240030319068010004005002d0a0300c02c061110240d9102c203858a144940000c0102001500c00707070300b0907102400100c01c102d01001712440360022030000d2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 398527544 1250 398526294 398526319
    0x6031510080609060f01061107180f090b0a1107020603010e09030403020d030509150708120411030a0f1101030504020102061b040f06030b10030b180c13031b0906030b01150905 77
    0x540c032103200b1703280600c60b00301450000c0b41440c040c4a41c82210603035180140207036403910006503982c0605801d21b0013641c0e0341d01d4280d8610a100c0c010080024000c006180160074429500803c85c2c4501c0d03002c4c10202c40605c0281c005075500006c0340d04403400003581c8405500e592013844d0440c403c581c0000c0d40102001805c00400d070301721002e841c03014000c4820449515a9000d091003912400d600200007980c00c01940d06442c401240c0030303800901500c03401b40801d0a820111f131400113400000e80702c1e140010110020840020098a0810030a01e001d00281c00d1690010f0356942003e003100e4001da006150401808102805480049c03407101015000e0558544018005040110110b40211a410300c40c07040b40e4024080c580c1a158040c1407042075604994004450100282c0642d0714904200070409510006030f1300f140c099402003040100c00101102d00c2850300103694401300c141c60400a0403c04100e105029504580c5101002d6082500890040307952900a03085194000c98200c1203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 398528794 1250 398527544 398527561
    0x30106090509060f07080402330a05040806100e01030f030309020d060c0f09081e01020c033108060a020f12070e0a090b090a0213090911100305060315100806 69
    0x8840c094494600e4000301526001c42c106e0707402c1d00454019410680c012000303505404101f0800002180d40d080c56503c030481071884a500794080240040020390200d4203001c1c014081c042e0340d801110610300401c48520300707440e81c0706c0f0030b005110180c8102007100310f41c02803500a07001150400d50007484580700021524044004010f070460850000c2c084186518480d4050380c11201070b915800014048a05022242e0000b04e40017100644555004e01040c2c40924007000a0300380608512124603c203c040d00c50284041e110340c002a0602d10048420014100041040768000c40c0d40b12015a0b03421119410350601d1013241c29031980f43d2050400c02202550013143c80706005821a003400a00d5071741c005c0c16041d42c51001000d50b2203030044001c5520108240d0040000302000600030518a40e5031072218200d4040040032b589400c529110581f50385004800c0d210000e810381000c12640c245030000c240d0780c5241103180e20b004030040c0d0105244000d113140100041800400702c8810703103803c804 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 398530044 1250 398528794 398528803
    0xc06090a0b030c0a3507020c0d0606050301051e010308030c0405061b16050f120a08040806070f0c030219110d06020c1506011704060219050a020f0624030106090509 72
    0x8201d400220004200034079412541100740d03c0d0090fa5000c0500c10b40014403030031613105e010b00b951043d8450a07840401c242c070780d040c0c00d0400714025280003c400d45003006050940b40020151000404043c82401841202070141d03415241c02003417164a0790703504200344139203201c1c075004164070410104a0328402e91a010001c1440a01001594200789600d13b5488440185009950744001c2c9007080e413005090100c94103804881c050100c0755642c071541c03500081e075807041e0020681c1d500280c00300440c058000c00d16a80e00e229615001c0a00006c1d80c6009442c1c01d114004409462000a01c000901100821005501400030089642c180c1c0519104c002580b2110000c4034900030000300403100403002524900c54041a100c0c01421108240740b044c007082c00400844c0c015a00784440111041c05580466040c0881d88038031b40c3d0b50703180e0500a46032890001164510350b0115041004c2c600610700e804080ca514090080005200c502c000b034003610f45074200328800c40c6410204440900e0028 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 398531294 1250 398530044 398530057
    0x30703090b0c1018020a050a08030d05090316050610050603160f0c02030303010b0702010806030c0a06200115060305091c0c050a06050a0b18040206092b03080910020702030c06090a0b030c 82
    0x48850001b140d4810600c42034001a11600d81c80c3c1d08144086004251586c00213030f07100c100d1600f9030703140c01d88400c0020001c106240c015561070748184108020041b20f45e4024000c0c04084458500310300e031402409080e2a48912040e04100e400090003010501492040744841c0c0e0040030f4980381c1d03846510825298100f03800503400100000081807540c1404100039224141c040d0a0310b844a00744113080d01d0441a60034060741100d081d0800005000c000c1c4604442010b44004940b0000e190072170013010750707002404010180d0064803003404800c01400c40b5040001c0e50742810011002d00d03003412804c000005001400441c02c001c104030003140c07254001c040708442111901d02281221503000800c800c00c503402500894108a40c0c00245055406100c0454641101403405540700f6111407486440c508100e01007003140c1c09210f80f441083c0110030707018042d50011400c0070010380000380c0d265500c86040380611000220071480d42c42d8116440060003001013071580d81d051003107214450b0b80c0140c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 398532544 1250 398531294 398531299
    0x60904112a12070f0206030c0d09060501050f030c09040312061802030a06060f020601062001020a020a050c0d051009111c0501050a0c0519110f0a0b09030703090b0c101802 75
    0x24001411400b4a240030341e0aa5900300000d101182e80075403c0c45500e90001c0c003030409111061042c0c40203052075020303103402c3c98850240030805500d05014001d5001e001090b00c1d00c01c0c0c1210030755190a48514600030390203a01071520300400c0040d4102c100060916070000304641501d8030010b400b68410f1307001236005000b05d45081003665561501298441b058641c200d005811000042041511551003490380141d02c2503004411020045560308903801f072132440340560401c2202328248030051040d1101c41c1404da038446d1144d00103030703030345d13030311001c1c0c1180ca040c0306a0350b200190705100070380d03030700140c4081c001c5c0140c2522a58000c0d4074041c2c07c2580012103056091600081401c0b1443c015880300703820907190682845110002d81c020242c0c800c4203107041108002080107002c1c0100b050740c0342c9407100009004141c03a242440c06044100818954aa600801a42c0006130703000c044942280e0200d0b03490342e12446000086070510000890f1001158148143c0380e05940ad0841400d540303034801c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 398533794 1250 398532544 398532553
    0x50601050f0102070305120c030d02030106360303030e0a0204050907090f020a090627090f05010f141018090c021e031909050d05060123060904112a 65
    0x9601c0126a10000b5003c02000754000403502621516101e0240c1110050b2400ba40d04007903002c2c1c103410890300241e1086000940d120681d503020003410700c0e242d1032504020902c00c5a69602c00c0142e0000000d13100c01802c243c1d9030980038948070810312184036043c0d0b0003402400300307040405901e6941d40d458019a51510301c2c0c622504207144d914421510401070b10b4651041c2689418029142e004070000b0409028440d010749040b550f440c404000050070802c01c00147c00305e08803290004807441600056074020311604148140703900c041003070341e0032801103c11a07410703c40300c42e04883c1c00c2e070050389548003030038000c41c00309480c142900b040d01e8a0b4400e50880707002480000310030301c09602801091006800400c500c1c81105118100c440c1031a520b4200000d0f01582c5502003402118045401e0307800c1c3e04908010702c40c02c0d1340d1031107140c89003042101022000c0ca14400085043c031940c14241d02c21075581c0484104d4004800a5900120705218900111807a5600800b02070b140d40300040028002c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 398535044 1250 398533794 398533819
    0xf14070309080a033513031211180f031209181617060109050103110c07030609140304060e0409140a0c0302010801050123030916121e02030604020409170705060105 72
    0x744280710801c520317840b680321141c0c1e151542c1c030031822640c0c1d00003681000300c8440303040c40031f03e01400303518800d950300520180d80d07030301da80c0441c0010210241c0f001d02c42c0c0400001d100305c40d0707000541048114107245ca815036a41c0c0180008003242000c0b16100000f92001e810070070b13044088907a1007035071078090301c682d034140100c030341c030358910f03040895802d4082001ca80b000c2c8603d500c00d82c003204140b2800c8861a207004049848a89000300c29401100c5040e03c0d01c00034400c000c081403001d82c1c0c1130035074801141040d090942c00380c0f901400c1d01003180030395900e00900c0c05120a5043c1c000c15039074614140e9006054a0400e1454a025070009a01140e60745c000001c0552140349000614200380c0501e40481ca107150710780a450784090700c8c0715150b12907625601c6045003030400e45801043c545062406551140c500790807242401c0c1c10b43c111420800721140e001d42c4000c14030b160b01a904440004100c03030705280400302c00c610801640036410000c01c1c814100100003400a05842c8101ca45445000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 398536294 1250 398535044 398535107
    0x90b0415060e01031503240605280b040b0f0a14040e062b0303020c0f0303010b07030e040b060a030c09180b030f0c030a030813051209100f14070309080a03 68
    0x420361b10001700301070001c09014010f005210019140c04005140c0403c3d680e030790f0400916800d01c440000111084104800112401c00003074104c000c02000c0202420075250400d034000d10302892440c0d1101b0080002e04d412940c2c86041035440100126100648030f03626100081d0500c08201c6016014402c40324042010641020985218440f0340c28004554455980c003100a0b4000c002c25200034403615000e012204418000380d806403010300d11050300d40c84241001000700b41003088050069260191104864681608951100d207440c1804203550124140031201e08503280d02000900b40750138034604ca40c4c4286e40054618040440803901280042c200d050307150b00300d114003a0f6066204180120010340103140080d030011080c8080305505d5a1a1103460030030b14000c060606c001800642c6210b2464661451070b441c441500e0440403d100892004d04410380120401a8502c40130412004252054464030003802d00c8105a45100c1311916001e090301807414005d0346501908450310389200b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 398537544 1250 398536294 398536331
    0x614010c020f06090607080403034b050c060c0417061003121e090f1d01090b031e01020901020601061107030f1401021b0d0302040602030301090b0415060e0103 70
    0x1260014100d92005002c0d03010040c0d180d002070b200136000b04040c0b21490110340001d0181c002140640c466020542046d24608903009254416284003404201014480d01111310040c03015003002429202e0f816494000759281e0041c40c00500d00ca2040000704a180403280003d8800ca48440000300005183d000040b5110301044840c0c41001102640030008911040d1841558150034100000120030403400580b2418040325a0004500c500e00c0401030340103030201c10001048645000000000041d040105000c0184070396548241c60740c0302c06140d03079400c0c080d10400810640d1801e9a03180c0c1c3c0c0ea00c3c0c034080d420003616140940900342c00010441d0140c581020b89180300c1020704549402c42c0c0c2c603080d0030081310002741c400e03902102001c806c1072000d1000303080b21001303541c61070b032100300854855140065901d4007030105401800304204060300042a04c0c10740c0c40102c4040b402141380d80219009004084002800c0e10b010900003401d142c00010f4038500c1c280c280d07000d00c140e200640040303250 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 398538794 1250 398537544 398537567
    0x15091905040c1814010503040602090406080717070902070209040b090f1f0501080109020d141f0209040b220911030d0807082206180c060201140f010f03020909031c061401 75
    0xb140c41000054002400751340100bc5081004100103006515551540e10300381550b0000d00c10000c1740c0b1113141c50a201000190010907a141c420352400d00d10f80d000c03800001c2d000c2c0c002048244d042c000300f00310071024031003d640190444116407940b1850100611c03110313610600c0850075881c010011039040b030180032b6041c0c4103401400c20000c80000355101e4038036100c400981c55950099070b1aa4824070301440030304890b48485100580c86810402c2080100d031804003141348030300011000f040d1225100c241481d120310202d40d000a4204040c10481903081d9a441c8507076140c054858804886500002e025001d03036080d036107011441ea15640700340c1c00c072280c03440d501d4652146500c030380c0002401a003280c0303520b10b02e82e511804200502e55410100140640110015035184c0e0003207102d41c95461001c40d4001d540b00454a41c6524195002d03d80440602029004550006c00545030a10400031a94501c08040000725010f04003803803000100003074024004001e000181c4c0500941c89400584070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 398540044 1250 398538794 398538797
    0x52a10140a0909020301170c0315060d03090b0c0303010303020d170f070c0c09020432060c0a14011d1f1a0d15050615091905040c181401 60
    0x1080e055002920500d421800440c1c04014000c00003140048450000e58000d00c61441c0110803144010303da54140620020640d0003a40700c49808040d105070442c2440e0046025600d841c20240c030fa0408075800311540c1c201101c07003074000a6111984000100441c1241e001e54291011417042640031900d01c124403a00010940d0b030900841c6064480c1000b0799001030040c10320500e90011a6203080391483c0541c002151103a010070200202c020b015003141001a08101c100c10b01c581414810f0b213103980c0b2264280c0a65000700700b17a0071102d01000600d80340d940011009501d005c4003400d1901805103403014000800d080000780c0300014000641041c4040d00c00c800c2c188a2004032902d07002007405031540e121040310304505900640303483c0c0350900d15502841c0d54103049000112001c064800140145020701507040b41800300c40c84902c01d5900b010307000c8400d40c0c051400400842480943c9400ca02c4e8400e18114a200c0902e811001140c1c0c040307801c040002c3c0507a501c0ba5a0300d81e98030303c080c2560 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 398541294 1250 398540044 398540057
    0x111807021203070c05150a0506010203040602120306032401062a1b0b0c031201050f09041704031202060604050a0b01020a021203070c0e1801020430052a10 68
    0x50605041d000519030090349464410190309040d122140b034484800601c000b2400f03207034284000d80c0400c0c046c180c1e01c56801c3c001945058903001000b07595511040401489181c04000f258685c1d030113116109000c94040303c0311a8803010450040c1040703e0a07c110808034060200c0b280c0c1c5111014a584101c91a03140c1503520400141c55060074a01c45480c200d4154003510400300d90000c0c0c40c0082c1940030100380042d40c4500d410105801c840606800141c41072002a500030340c0303a5a00c03260641d2260388607042c048010f924800d1207016000c0d41d000109950030401d152240554001500c2d88100c50480f001e10890310b58244860488a04640da10f00603000460301001505100d0101d641501012044902c2e00f222030301c0ea1017142400c3c4d0404035101c00d25034103010020508038071802c0740342c1d2030714021440c1c580340c684807440c05040441c80d000501442070f0345d0150404040c403d2000e140d003040640744e03604480c85000701e040c142031103000c866031400045005141803c02104902c1354040d110403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 398542544 1250 398541294 398541313
    0xc07090f060e15010e090a09060b03030301080307120306030f0f1a0402090a020f090a06030507090602010614131401031104150e040201050912010c0207090501081b1207050a0311180702 81
    0x22003e07000c5066003030502240d21102c204580342da0680c14402e2603003201c002121942c0e403400d90150340300e45100d94866881400180300b00100030049a00130b0b544030003058a130700d208100a401800041d40040d080039103003c4018103210400d510f0f030950314811100c510040320a00f0302c40281060a0f54040d410001c04000500002e1007540242910320f908c0083e6810408810001040c101d12a0002400a6207d4080c8841150064010006803502e40000d1090b80d040540c680030365000800f100d40700d040845840804509554404d00c1c161075400030343ea0141d03850307040c61031040104183d4075020354600140c1e82c40c105a103034007110542d540c2d401558000d0300d42d6001103a00b904400e40c41d99101d10030008030020708400b482024280780080d0094030700d003403400304460b00300d0343c050348103001d1504242d901440a0385031000c03500203814111100115041c2c20039106c0e150070100d421060f0030003868000841804a81d01321941c2ca80b00881d650f280c0001203440c7d14101c00c0c0d00f03850b1000541d002c4a0007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 398543794 1250 398542544 398542561
    0x20d1b0207050f031e160e1302040b0607150e0d0e0f040504060e06010f060e100806130e010f0b040605100804030c080904230603010c0207050111030c01020c07090f060e 74
    0x18002920780042c02c540044a80c0406001503081200b20345d2490392141d90b485000b26058800b1000605107250303440d0103450008a0000000036141c4028800c65444401581a1b40c0b408113035214580c00c803404c01405180d00325500700901103024582e01c10701c07680301c4810300584602000491685c0c06000d400d962017030902404060711019000302d61081d04d44580e04051481046498020040c540341d1081c0b1034030b85032000d007403035101d0211980a11601c0450380c552640002c0d0280c0c219505503090003e05e40b102c0d4004000b480240d807403122550038240c4441d00b01e2003e820040584e071040710200701035036490082140074448585024041007140c0c001034082409032a00308003660040b1101880c180305500007500b291130111000b015101c5000c103410b07554408405d5154044d205800800152180c408041d641d03070601d2141c07504010420000d4040e1910900541302075514282c0250344401c101148a910303208070380110490541350032900c45000400d40684004c44200b81c50b260a140c85078080c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 398545044 1250 398543794 398543809
    0x61c03120e030703020d1403011d130203100b090f0f070c05070f06080a0b181506070c06090e10060f0c050c0315010824150111030d020d1b020705 64
    0x202040c85a5103121080e41c20300c080c802441d203030b03200b640074001d00700b100f01000e003a00f400780e6408404000180300602061001564500b58920b030000100046c0d40c442401100704011002d000f909401040800ca1543e070050704001c0c4d02d08c108407001f4415669445102440f8142107030723943c60440029020400c0c2c81d0081da02c0c3c0c2c03446801001510900303905e81000d140b0300e9005501003400200b81c0c0080181111803440f80b048900c0c42210382d103c1c40505810f106540940141c078112a03041c00d1113015040d60b0700c1c90100c4000591140c003ca24103a90341d040a4520f690381c4c85031401d2066018006100c10561060f85070699940c1d4031140100d60003410110307001c02d104135003200e040c8101c024280d00d42d07504010100000407218003d44007907041c50a6141006030a800019155520000030b1014403c10440a170f8003410000903460a10700342e10049403051030110300136840340000074079401900c400750003c103061084850180320405080503600204040012100c3c01031b08a000c003400743e8500f048 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 398546294 1250 398545044 398545067
    0x1b02060f0a0c02030c0303281a040b040603050708010e010b0102301b0a060609090309050f0d020604060305041e0f060e0304081905150f0a0207030210050906090105061c03 75
    0x104807170034200d201d1002c0c0d140d43c1c01075500188070503000100001606244045241c0a910400184010241008100441464161001c4c07081e52602c03540b0a464585900240003182c202044078103095490010700e00a08109100500d00d500b010f500c403083d94000501070008905800d0840d1107c10901e2800c0007040c01d00040c08100c140030004452584d0788040c0015402c0802e0024107011202e0b40303002022552650300610300142801c0300b403400310303412583d0030048607815545040a00a000000740340e03000c070b0b00c00080d445240442c010039030b158558001c0b40b0551140700040001c90302e9403160b19060f0780954004140c1c46c460040600007030600d0304006401c04c55070741103134102502c400e01e00f400d00d0481c440003200c0c000706003026002d000c1e08020018450b81d200407140124280301c00d60072070042d8001c6c841e14030f0726000203654042610802456141c2d62001c0c000b0455403d1603500c2540b02c0d00c060f680c00c03c0079800d25012400b81d14020b1031107145803140c81e4201802500351313135045e991030340d056 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 398547544 1250 398546294 398546297
    0xd17010b0906071a061f02070b030a0f0905030a4d0712020102120301060e12030d090309031506050f0409021c2604060912080d06091b02060f0a0c 64
    0x240015000114414990700283c04243c13030700741e99898544140001c0504504004a41100509100100540104440c01618500c6d4070390790f41e070ba80354641f0401820010100303041481ca007854840c01e0000c040041d022004159030303041e8200c500c4040036448040d0360000105a00034108a1a400c07042c0d1240015024000b4030910854808aa031000d0070300aa590044d00b0417020703075114204544c3d042c031548140c2005035851600355414400300410b0b10f080e224405001745170068080e40120b404005070b8041000304041440154049d18008101c109a4131048902d45c0c502c242418010145005a1050350030141c140c81c0ca10504400b08000341c03002c50016604407402c420102155003c0b51251200c4600680c9040d690340544044032180100400300300310002010711041c003440360700081c100119416a401c1000150180c2005200c82c40f41940c11400c25281000c00684030604c2d800c4041144502c0e030a01e804644045026a2201c2c0201c0d50800740b04250000110004182d40c08000c03c018903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 398548794 1250 398547544 398547547
    0x426070b21070203182b230a061404030c02060906042c06030601030c05010311040504090f0c050609090103060507170702030304050c0f0618031009080c0d17010b0906 73
    0x20035907900120240c4405005801c0091070b04101c0300b215680c8007040c102a9200021a0b685061040764080020050008041c1d407640e00c8040c8070b04e0110b120107240c0340300c1e040d81c050810400c02ca9981c40707035148202c440d54140010304c44d80c21103913024948141e4054999400b1a0115070070044190301c110403042d440030701032002080c00190a41080e10003480c5444660314007408469030309184200410f554400e510910061001030100c1c001041143d5003828081030b0304111680c403000d140116004075801c1468603810006001341341940900040c082c0b44044201c94440c000d1240c01e00c250000c680e0005503980040000881541c820b55207c035680c50000d507a140002020050140203554020050b4008030500003800400d002c0030340b980c80100c0e1986800c6c098480403480501420207905030f40c03d11504007280a8900384080244421031070801c0010380040c0c038009178250046600081e0390301c618108001d9890140d10000d5032040c844202a00b40d0380780844050680c0e000d90700f00c5401010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 398550044 1250 398548794 398548837
    0x240301020f0c030301031e0812100527010905100303050f0904020304210e10030209010216080a030e120312101d04061b05160309080f030426070b 64
    0x501c0280404440100141d50749524600304200158140708105d885603240c0b40600b00011404011501c0d418081c102c8039911303903207913802d01500c04041d07842103800c0300314014240b00c1d40b5110711400d0b0600f91840c401d900030b42d88071441c907422103a0444040303407070890701c10742400806d02840240c02c0b034829505201c0d20306259080850280c3c0c0040d1000c4880b10610044003030000c20701c88520b50001c20701d01e4620054092040020040c4006004030381c14107034000307459030444c1d109003c8040d2000204101901d0315a07610320080e83c4510000c001d03130018192048a000b10b10309244840c1a400404004505092000c03043c41311000c03018010700e401c1d00c00c2d90000030320420b1480321100f0412000510100c1e07841c00741000c000f41c80c001d440518140440b281d04030b881d0358000c0140c5600c8060940300c165800040d10341681c050f41140c00541052040d001c84455042000000f4804d41d044001d0307418156019400d8240300c11305807120b11140d600001018800780148401408800e00c440d803400507080e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 398551294 1250 398550044 398550067
    0xd03060326040f0b0304020307061106010e0915040302030316080c19090806090d110c09010e0c1c060f05030607050a030f1b0216060512040204090303090503030108011a0924030102 79
    0x1030745a110788441300303000c0204415403400744444001803405041c2a000702c059850080d0301c0b0041400381810820040000c03c00300700b4100000203589900303000c1503015041904000e0340d40d400880b04903032548203081440380613074406d06000340600d5076079400504010b11904010045840700110b43c0820250810001d61050208092030049001d00060091002000c10060941e00300e5140350100394001454070019846d65819241111211030401003152210440c50846210318940308103000119051f80038949507a0303000b40d040f129151102800b00b6554828542c4480c4112050030102c2c0003030280700302250094001e40300307080202e08001a8441d850320141c40d80d000716401e0360010307405a40300001d43c82a0200d030a01500381c50800a0030b21511161540c2c502000800017400345445410403420540a40c11892245070702030266503ca6840f1580c03107000b0068140c9001a132038040340f0700e80c0d40c1e06010755110b000d844c000e984411200d6402981110009000c034205030599400c0240402e44c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 398552544 1250 398551294 398551319
    0xd051e030c0d11060106090503100b0609040c030509071401081603062c090f0a060b0604030b13030e060a0c110f04060b12060f0603042901090b030d0306032604 70
    0x700b403a901c4242d08254285a071a00c0d080b0160400010f10072075200910055400050710611070070b0b441000b24980c035803c008254980509070b04240c2050808801100850305504407911606401049601540d13541c180800d4181c1441a228040b032811008600d250321a010440d42e0700505080100b041c0b84c0e40d40407001412801d0915034014600c10015400e100720004201e40c01508041c000d14076074041032140f5490340682400104942d46d10040d003185525400c094600030b641024552086141c0000c98944c3c9503502c0008500040c00c0710a2004103280c40c1082d0f90310000256540100048941e8507030310a90040c2d01e02c560b201003522a075004940d110700551020784400b17120b0580791224502400c070003880103001c05205540011007851140c82d00801c3d40e030b22940042044085650380482c0c219034003d8400036900c402100000030404c0c0e50345800c01d45680c002501112103000300e905084040b03030f42ca40402081501001c0f08250b0220032089503400c0203440d8060746250669603180002d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 398553794 1250 398552544 398552563
    0x3090c0d0b0402040c0215010b1c0f06030512030c041404020c0a12020f0c0603040b07050c03040303051812070b0c0312040f0210080c0d020d0b090f060a050d051e030c 73
    0x1551007010401181800d00404c92406020300041041180d030001c041240e00050054401101e00803c074112005603e40180f90300404001081011000c00481170019003c41c0c0010340b02e921030103c4c1c0e044850b40101c1281d210700300a000e154280350a06c15000410f1107483c00c4150710580034001023001c00c2040c061040080d10901d80340410712907101002e4208812a002000303a0f400c540d03600041502c5034401c42c2d52250307100c030b07814905070307a0100d05865a0046030705036126440045004400c1540002c000c040040c05020354503003a80c00c81003040355074900a81c41c480c4035004070400304811601034019111030550303c0280d909140005501c11182c0c1c0d021102030310b40d00f140310240c1e801c0d414030039403800b004019490035619600d02030249110314030030800d28032001030b800142d1041c509126400384a14600c0208200c6881c00c1080040c0800c2d00c069803414411250060002880e1070400010031003545d000d00604000c5821002100c160260455502030074002000070760243d0b813091101c640f4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 398555044 1250 398553794 398553803
    0x9091f0f0f39050d090c0305100e0c04050606070609020402040b070c0504060909030f0c0213060303030515030c030705130e0f030a0f030203010e180f06010b0a110c01080c03090c0d 79
    0x1ca00701c2c48848801244a0340c65540c501c8a407403901441e075160f10804840c098990380e500401e1000c6a403a202d0760829255001900740d0103000c3c800e01c0303101016004101d1040804003150301e11050386c0100b0084480c01d640351039028200f040004001400c0e600441d10542c0000d00050030300d90f840031104800e9004140c1252045203142040c0414070341880b0f010054064144200024000c0d40c1d00035204102d000744030800d214140705200f0441d03955030840041e07110103580500c0202d5036482d001d405403105840b1182110400300e42c185050400003110015920010000c1c03d155141c881400b040c4240f020680450301d48030104000d80c0c000801c11180030607241002142e40391110f104c0104041e102c0009442010f0041004000c4070070801c407040c4c0c100401603a0700400b0b41101007680d203803458014030b201407030180390000105000100003400e211003164403101c42c10740100e0b4910391600420880c20b030214642c0804a2102c0f0b0203500038640c40150841140d40000d00b03c0b0014400500c041c1c001c48 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 398556294 1250 398555044 398555081
    0x3020c10050c06090604030e1e13050105030d0c030f140903031207090b03100314030c0703060605010f08040b0f0403110109050303061201050f04021909180209091f0f0f 74
    0x110420803a980c4d011003010040d007224101903034002d220b180c00c1d03c0e1091260114112011248240004400400d20001c260787c810350000610070300941424840c040c841c3c0a00a51104a5806072544001c403035450f503a030030008855100d05840149140700c400d030b800344040c81484940d0310101b00504034624552591700c3c3c1451701d898003c1c400c0b2407a0304101e840002c28024041640055650a010340c4e510a01390300d03100052086031455030190051100036440ba00400005001d6140d00c0101034130403e0340c500040c01d03100d6000362032590003624018101004c1e880000c10186c50030a01e02d0b00300b407280c58070740c0c010300e1449010b609507928040c069845070000000e01c43c41d0314110000c40c2e01e00e80300c00024085031520342c0c602050003100800181c06141000758140c0035110030520b010240603a00410800c60301c2106051405808204080340a50190740c0800d02e200710018241e13072000c22200811200440d494151400761044080041c2000e0720361184100c038540c2401008180401c100600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 398557544 1250 398556294 398556307
    0x50616020a02180a0c02030a0e010f1704060614011107030611040e070503010f050114030406092a0302180112030f4d191e0506040c090b011b03020c1005 67
    0x40d041301c4049030440309661081100d04223858000f05d485030181030900713004515030640202615200c01d500301c4003078070034034040801003089041d910010684a800ca1001038002140005450741044030300514030303c0d403107201d003040001d489030000c1088004011840c0d0800f0f5444900200c0c500054581d8408598040300510a0181a000303a00060200f460000000240141001801d11010700301506d1640c840300400c00b0702004621031051800010700c0004000010140e8022048450204038410102e44045481c0714010000c0780703050784c00010041003c4c07402e5550696502034070038540400c0c4508104103c800b94102d181d25052560600f0700806201d00080b00c40c0b1080c042111030100481e103100e40d00d14240380c00200c0246551080b0122a441c3d0b8040c1820a1039154500030300789440440e2841104005001c03804601903881822800450368540388010151881580c2003400582c0b106805a45060b0b0340c181c46860b1402401a20000310100004c1095030100c80c4030200458400542c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 398558794 1250 398557544 398557561
    0x22107090e0c0f0406120608030c0d0914060901081902030f010518070e01030e0304150509090a0204030506070c02010309050d0f1d0d02220501090f06080a050616020a0218 75
    0x50380a078202c0e01e00da01e09440000c00c2e206900a030300601c01000315110300c4851174030382d65210401a00b0100122901c03907904104103071307481001e0010540001c503203440029030610511030090008200400b102e007408801001141e040304003d0a0603c2d444c2224091440c00856200443c043c0b08440800949581000140000114402d040c508134070280d508100b969940300c0020b00242c9002d10300070420f000c002070240e16500450b007183c98a0100c12140c23a04c0142c0000c024050b44400780e0f08810296540440e0200724055880054142c0e04690000342d681e40c41403d456810601c1411300103a0f1034501e8852503e051403a0840e10b021410700b60702c0342060703a00075900381101140d1108030300c5600080c00c04540045502407009009440c5400c0c011450a5050003013502d02c506014200000c1d0380d2103075200094000e0952003031110b85400004649010042101d0000e2500710004102035240c9882181d00c0b000e10f0301d8840c086020703500c01c81340107030717911149641d50440da945016900d04140c0318 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 398560044 1250 398558794 398558819
    0x51b030109050a0c2c0f040f050702010b030d0c0206090109080a03090806060609010e060307110f01150b0f0a080c1b060f06030f071a0d060801020a08061e0402210709 73
    0x4803003400940d1104039848505600560303c0b09000c01030004003e00c0c1740d0085040c1d42c840000782c1d5809410001103006442c000d61010380b0424441d030081c890000c07a482416251904004800f0000305081340d08005407c0407030080c12040d00c103141200940e6665417a40f8148101400100d0004041400401c0140010008590000c40458040d45408941b40c0080d00040c0a07024240c042d003030200010344002c0c0101c201402540805065800e0300086101046c005c107052007603000d088c011084080707021120032050714040c401c800e20061900100117400d9810301401020340703011600404c507441d001a10f490403250707450038000041c0f0050030002e11072200404018900340c02944545240d0030114000201c2c202100c80000901c280300e04030f004c6441013071280f4127420300c3e003905080000495800540c000c1407003840981d102c45180e01e0395410000c3d03001c00f80110500c0005550244111032410b540240070342422510b103034480b10060030544582000803a41c007408103061000070400e180301d104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 398561151 1107 398560044 398560061
    0x162106090804061e210b031e0106050a05030c061902100c0c060f1103150d1e02150304020d0602030a0905070b0a0306080304120303051b030109050a 65
    0x202001e0520400843e01d0003c44d1400480920514401c0002d030890a200d07910050882e85400342400280c000d203520b1550501502c84952010032412080100031a041800851098509000c10007100c2c91540054003941203040000960307540c0e0421182501c008500006c102c4014410891511041e00d4180000902e4055100c82a23504611b80c03030040da12500b001d104048240c00000c4c26280900740301d001000041c0080b5241c001c1140b107000007036801404065001ca01c0c3c0e191494107680740c001e81e4075201c00c0e0210140030360401c406015080303020502410703c1c5003003990110b448a0369480000d4001d030b6000c00800c0e100350140d00300a4034960882c0490700d41ca52600844000d6034040120040443d1420000145881c80401510110b070710b142484a60300f003a5071010f81c0a0720000b04540a090003041c510100081d200010354081e00c1420301c00290b910381031040303008444000c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 398381294 398561151 := by
  have h0 := BRFrame.cov_init 398381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 398381294 ≤ n) (h2 : n < 398561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
