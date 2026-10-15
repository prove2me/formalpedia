-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4495
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:48:25.492241+00:00
-- url     : https://prove2.me/submissions/0a5201e8-98de-4de5-98bc-e32fac0c71e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 808273381 ≤ n < 808453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 808274631 1250 808273381 808273409
    0x40b072303070f061509051501020f0c030307140309060c0601030605010b04050d02090601031d0d090503121209010b060f04030204050f0c0f071a0c070201140408060a1812080a06 78
    0x145807200103030f0034484003804079a11503100d00386100c005d0001030081e0080100420840c2812000010002448001300d4003500c40d103041e070718004000090311207090380000e0055140c10744a680d243e02d00040d0440c419260310040c08003079030b00c0e541d10000c0c003440391000c002001c0561440c14800151141a071055680d000c0404c81031205440e0110b00080050301503c0c208601d03180e07600102c005082d820b08080d5901c102390b4907c14502c1000c60711310240c08883d5a801c050300d03290410540c641c40716111400985404000200d8541d02d611032140e800150040001a41c184910100b1466400480750400c4103c00080c14021883d251040b282c014020705107405251901704506241413082c455886038103007000c00c0580c20812010700d04001c401c030f17406000d03942e0300307201d00807030040d402c209022400726044200d0100141c103480191003c64100c0d074003d0190b43c6403030840308000c041c180ca20040100440342131601044d030102c0382c0c81c1942c20729600c0459520307200c40d0000c201d400c180c00a100d00384c100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 808275881 1250 808274631 808274633
    0x4030809300f1e0d110309030a03050903070804090203060a14031f2a020d020a0f1704030b09070f05030c18060609090106020c030606092a040b07230307 67
    0x50009821140d214006142c2d441c404100106498042c0b0390314010101400640c00901c0040c1001404421658440c103001454152200c090740740000c40e01c82000e41d1003030082044a41c443e4000f0354000050000b078070f1502541d0345a0040542c0305400440d9882e8000042c800c80381402c0340d2b1a00244030400a503440c0b8a05200004c0d11000c0905015030440383c0c0011841c4000c185a01115100340700303411800c1403981815421640681c2e5803107450260082c0100052018004039010000603800f20004000785d20715030b903021301001600804894200103000110028104403015030146013800f001f0502c071850861400d60481c80c50b042507000340c200743c05081d440e0f00c84c40b02c00c00c0003900801c1031110a65034007002c50b0280c042c017080c1c1c0e0b40c0a100c110002400c0c1d074000c50038002e98601641540c3e4140c0c0c41400f40315051205445504400b00c8526002000700c00400b15422522030075950380345000d603201c03a82030a41e049400e050700c0750416800d11140c0341c2058507202c0f880060700c8001c0c40c18141c031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 808277131 1250 808275881 808275943
    0x10090b03040308101805060f040204050607081e030f0402030607030e030906070f060203040803010e0a020702130203040c0905100503060907052d0306070816031a0f01090305030304030809 82
    0x3014100506006641002c5140c1c1e115080c070310b070058134403030048590719140c0c0d030320020203044182e54003400b8140303c0c02c255015090030b0086400707490002c1c25051a01540303a403034014a0f80407401036000e000c00c0d202030303c0500700814000c42c0118594880c2c1090780c1401d004050404d507019158005147c5081e9403111012030120540c1c6c40640120764843c0c80f10403d040040c136195080000030079151001007040100403401c8017950503180c140c030006075541d581c0500e8608038416444007070740c81180d5071180b07500c0303410940003568803a218030780c509000c0ea42c03006004207176581030704c4aa054054003101403216042c200310050344610400020500c1d546844c3c0440c8507600c1171158000c02d8000c0309240c800d040d001e242d2a900c4028080d04817a12494174600042601000303403885066540c42d0703c0c03a0260584070740179a241820003444040e60075110703072040003810090208418148aa00c150010220f07406002440c800c5001383c0741d01d00b041c80c00500c0380d420040c8400030440c2851110650444d0710103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 808278381 1250 808277131 808277137
    0x130b25080f07030b0a080d17011202010504030809010c021e18060f060a141c06060e01021216140606040b1813061d0d030c17060607080913060510090b 66
    0x2c00341000600c2507026004240504401d401881440c400c00d851002807550004400c1c10008000498580c146d0f01c440c0019200c55400704080d000850a10060003c103594400418500005042c40000184203a010a800c0340d5211603070440d4519040a1680c03904102d0400d01112840303889520181c5424000180c0300c0d01340945041c010000420300c500e5090140d4080614100c40c11603540d220301c05000c1c080c5014142d02945152242000400645e0a010b001c030841c080105802034200d802690821002a80000c5105142c0d00144502100402ca132403154042103e411000344c20285803410078442034800c04501c16002da01c05080749030703182040c0d40c000c91300840035010440540300d0904051014103036620710406160a2802d40281c031880c000b0780400c3d410140d0b20288004e80381c000d03080e21004101e4003000a06460304001820910b007d0340100002c620510782242021807290104410b441c00d020988030035503035403100780070754500140440e94900052510001413403c181c14503460380 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 808279631 1250 808278381 808278391
    0x12042102010309080c2b050904321e040b070e270f070306060c0611070b010608041e030c0f030201090506070c1707120503130b25080f 59
    0xa000004002168400e8200301400c41e00300b80c5450729252800030164442d1000c50341c00190a8580c421070209003000e0039204140001c0c0d031038560500c508041031001901e407a11030201da00d4400707445041035031803600c00d203480701c0341040d04a21189410a42e50a6104c1034030610140b60008000b0400042c240c1100d0551254103440e25503164155180444d60200501081c2146d80c1000c2402200e00603028464510400154011101c90b8403a0b0000754102e40a5010340c00000d00300200d240c01041094114080095568102900d03050041d100c11003541400e800140010b52400240418070581039448246074454212a4a4006507070f0790203000200e437110700034501140600c60302e00707041c000c0d4030542402c0d8010065031107074688207800070100c603017042c0101e910070101c4c035070072000000c20000d50302c1003079021540c05019044070500f601d0581000340444550001c4510140004d84c440c080940107141c43e03146e40602d070010018210103040404000740c2003141ca413042002d90741c0041c0c40c9503042 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 808280881 1250 808279631 808279679
    0x80703031409030a0609030329150d02041e09020f1c1e0c0f02010915050c0415180e0609041419050715020604030207182c1204 56
    0x1500703903655038007103409030030762441c0c0c103000d0b01c042c0301c081c440c0b0754004601300f41c1f096404014600307040f014108020012114000c00c50148078504100d8240002c4d00b2035881010460507050203907212502013685d00c6a084160910310880c9000e9601e1142071650010786134080095090411003501a489400380c1500030315811a1b80800505082e4142e101042115940c40d40c1c403108112004204042c009840c096400070340002c0f08a1103061041c4607a960140d40002034030300044103040c80d0406080090412200004200000910344480409281c2980f490340c591183d070680b682482d658040d903a030300c0f150694460804204141c0c0d01c00d040030b83d0041c1d01440700034901d01c441e04101d140000d07220034281c002181928a800b0b0090001d461005c0740e640884000200314005001c907202ca07001c0d0b4008001d6840301e0320038040100c65125000300c5005410b0006041c0071610140d41040030039141c0c0040c1751030110b01e8455404002c1c040a074296981e45207062800d1f2506203294060304510910201e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 808282131 1250 808280881 808280897
    0x6090b0f16140d020703090f1d040b070314040b071e0f2001091505011403100225151a0a17100510080f0109020901030605060d08130501120608070303 66
    0x6503201400c140d44185500100864458036241b80180c60210540603400310781d000e2040c00070b4401107800812001c03002c440340d01e00c081e84850351405080d040107410b2000b03140e291504100c0e1494000030451181e40100c414401600b03140c07402610324404421f4184140f540a451105555001034000e01840c440b441c0800100c00404e10084100c3d007010301d130300d100e0350800410030140520081500402c0807160f00410481e640d4150317510480c161401280c5d01034001171502e20200c00258007400498a103403034a40341205410006c1c960182945000b00c5001400c140c45041e28000d070303c03944c1900d8030340c0741c2e103010490752440001e004680c2a10403c00b4141401a0700e000760142803211400c21506c030301003804035051003651881030782c0c403c0c0550122841103141c0e0b0185020140280c01032981c025041203216421901c82101408005049582007904c6001071000200300760020500c03661110150f44100d824400014142e0001d0700009110350b0a04009118803c0042005400c81e9414181104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 808283381 1250 808282131 808282157
    0x906090a0e0d020d1706180406200307030b03010614060c010b060a0c050f1b0d050c090c031b0702060d0e0a0618032606040c03110706090b0f16 63
    0x25080d5041804440d009041c5a0b40c0643d030000b442003107086458a40c0000303c2d010300142401d0301000c50b40d00c2d40c85000c0c08100c1c09002014210150480c3c001d51010130742ea030408400d014202070501744081a18000020045000d5151043d8031004008800070b007c801e250001c02c0040c003281030403191050000240c0f507880101c0c00d502000c91480041c1c84a600c503480300101501410505409a901c0d0282106c07914072000081409840c101c0080301440082000c1d006200f407001000178100c0752071098014582090b50b840258a00c01d0303041050140d40c80c54180d01404001d00c5038400902d070503a0600c0500d00680d0b17000c0c2a514100640d8000081d1465141c002c6480c000c803040000d00024a0481c1000c4004540f400702c0390000d00030740380c01207104030000d02810003003682e1401013100344803d00401e001d0318040c0c0100040c0c0150385008105146200303c3ca515940c0000802c803270140c1d82e0080382c010040c941c01000c0d07000f04100c05c101e819140840209800c0003030307400c0c3e03031040081d0090044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 808284631 1250 808283381 808283401
    0x20103110705150603070806070503160e03060a050406111215190608090d260603072d060c02210703080c15010f05060703120207020603040507090e06010302090609 72
    0x51007068000003214104a0076484003401d0140956400d0f0090103481800701c0d440c0320000d0914000c0480d0340e1042c1c0717181d6405101080000f1041410001c001009102200703a0b541001243e001e98000e0000054a00707080c07501e00d00f21034ac41c00a6013690002448240d131204038046100d98050550600506090111320005501c1039500811070000c07100754070040748480d441b004191040c000c030412142c001090190a9410354100e2544c07407040c03001d10907180c1c8045140254250000700180445100546600030f03c0904202c001020032052802d00105c09544407113a0000700510980c206440c1050154001c00c0f52889c45e04076219511074111030105d64020100b201000641d0481c00081d280d8007550300b03080c0c07901c50440c0c21001c002c0c0d1003400403858680c40f0340c0407801c68400030700036858110070340c1c0c050340c000390480750500c0301079824441c1e500542c46103002148103a1242c80a00036003070410f10500100c074004041d550440c3d0201005000680790504007a4000b0004c80700310126980b1410031b6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 808285881 1250 808284631 808284637
    0x50601022d06040f0b1e040f0501110a05071b21030905030a0b0f0610121508010f05010810090812090c100f021504050712020102030c07120b01080a030c02010311 71
    0x191450310400d0100f00034044862031204000303124000030f030400d84a0309002519011880c6660404030080404070b40003480c007a041c103a2036880b07400040b424000748840000260441d40e4a203010903c00103000e8100308280b01812031890f00f650942011a0a106a00c0f003401221440c015003004401c54141c10b140c020403544009100c000c0807910800c40c949018400c039038096405a90103540d00002c01c0c5071345400c0e40c1404031181143c0d070300f00006007410300300c10192802c1c08184c2e20000c40d0500c0400c41c44420701862003400c040c042e000c6459490400c003185451802c03000c2124035490900c0783c200040416044900300e04141c42140410b81b05c5406050602d4007075a00c40e503002102c0f021040034075400050242a808a41d0240e0f00310b04510381007012038800840d0018516046942d091000384100b2510341042030062049070700300840c114070b81707190200c5034228292030300e441c0c9500d13010001d20056a501500400b006081322000d169000740c445014400024140b5498503101c54078403102c1001c1d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 808287131 1250 808285881 808285963
    0x204020702011806050d05180c01080601090509091c05040f050907170a15270e030c06040b060f0a0303020a11040f06030c030b091926040b031905060102 67
    0xc54220144c0d00c0310060711543c880c01901c807101c3d007403400103901d1441460f1030041061a4034050814545140c0044403410070041616040c4000c3c0840820151201c1031401c0c0300c0d2201e2401000101c11140a143c2c0c54000c403d1480100f00c0d040105101032038400044104569083d101020760f80c03030712482a01c1e420851102c1038034035408981003140340504c1d60008a55040100c0d01d192103262102d16001c00c00c800030120400c80c8041030922011405c0c1a0720034040045500190707410913400808913400d100065030700781c6610040206001540c607025400904500341110284000e81c070710741c8e01030346030f50401e0b01c0907003909010188001d941c0c85507040b016084014880030891107849190011624070340f4001950300081da400002e00c403940000da16001340700054048014803400e035444480d24200307030200754091602c11103003028003400100940302070080c0d21800bd80382d24200854100308921588100d00d40c03400e080500c03040fa6000325040000105450f10702c15032825041f80410100c4220013 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 808288381 1250 808287131 808287167
    0x3010621082a100509031e03060f1c0309120f03030b010e0a091a0a0305060424150e061914120d0801030213050402010503160c0c0b031e13020402070201 67
    0x180a45682e1000f04104407080401001001151a0490683d035a0b0044d0520344040c8281103020030345004401000d0b507442480200300290407490a00400c600b1100091a18980000e50b00703184100742e00626454080c050340300b07442450f00c042e600c40b510744418101002e003c1c0350b92614441c04d5030b4801c180202a280010303180701000382d0786040307200052541c044200405e003120700b0b0050945c0f038010000000c407500440141078644454441482024942c0030b10420700b00f084010011083c96401101400400607400150701480c1c440000d02000700285010701c0b134050702d0300103040d000000340300b001517a081c41815155215a03902207004944c004843c02c0c43c51181d02c00e00d511700b80d408208a41603078800c6c0d0b60001e84541d610010000e4a00641d0020b011030400c1c00015481280680c4801c6010500c0c40c0c04030103120345858134544c011003500142910140001080a1300343c90550344c004d239407003135044100640b400c4088510700d0303124200024840c03030f00010802d041d60701c41c40e00c0c4506244d10364 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 808289631 1250 808288381 808288447
    0x30203070f0c1a07020303180703150507091205010501060806031903030b0a05040908090f1909020a1b0501090203062a0705070807060306030c050409050c090613020406030504020301062108 83
    0x14002c3d64903041101e070b1020205002c8100c0c1741c8c165022460f902102d40c0403101c001040981c00c4400050700d0000e03d0340c1c0070801116000103803021340c01601e1007018018000050b1950400c040244132100082c595406907001c02e00c0740c8140c2840300c000b83c041d150540b1b400500904000700003600b0502951240c0d50090402c00207506201d2400001c003107200e8115601a15450030800b8010030301006552030b042080c050408010490003070b0000c061920b0720341f4003000200b200e419403990a04080d40261103580d540c004090440c00d0800807250400c0c1400c00b203480000007030700c800ca04180d110a4101203040c1c0400c080e800c02c04104201c20242020750191a51103494050081c0106200d1106445000780742000080c04e0031300d4030039105100e40081c0500011854401880050b40c8040c1c13001ea000344180451910a44c03461021740050f00d41607801140364200b90041509507034031500280300c005440301540ca14030007007030040c0d8091b50344220b9a0342c6440c07079900410a054032507041030946031114 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 808290881 1250 808289631 808289641
    0x130b040207110a0e240402040f060305090714102f061e311b1d010e06100302040e070e03011b050a0c0501111315030203070f0c1a 57
    0x34800c036489858040d1030390612207a58141c50340c40380f0010394100708441040307120402e25003800894102d030b0150146c005840d0070740d42d40707810a4040c1d06900c503100096581c018409044014024a4010000181c0c030092400c0e07000001823001c9158814803060103000540c0d2000c005c1c055410882214820b802d040d020900d20600607140c010440d8240c04500b400300c0c81c5010740a8201e03071720340920050b245416241a400124002c010386208000301d0b20002003e2a1001507000e170360304410441400c00701d010340c1389840c19400b0041d030303142c0986454411010061100400625400741e2002e0111840740e4000b100d02c205038020702c1141c001c9120180381d03104018485400035100d0701c00c400254000c00030481044072003002c615910740f0400c000f480030000702e680d0500c11403a844003140500d000250311042142250190b61041c1c12840c18441881c10800c540e914540801c0d000c041c4134181949145884000142020b00f07000741003060085e0400071a00340801500f0766030080e04d00d01c208804038100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 808292131 1250 808290881 808290893
    0x1110705180f010b1303060e1c0203090f061608030c07080703030207020f06030708061011060f0403030b06030f0a020d02040e1503010b0d230114010b0403050c0a0e06130b040207 78
    0x80301c0c0030580c0d05102c400002c4003c0c0841c2210300e00d80002c0c1c404c1103c02e0031075503840003500401c3d040c02910f210319400d4180300e402d80301d42254811090340046039512100b10621030340c4610040345621890b000d014604130341e40341c011403255840e48808440c0d0b49980341c1041207035070700802001030446503001c2440c408054140d402031440030300891381e48840c0c101d8042002001d2104903420800141000042480b80c180b500716400070b8821401c00c510000d084040c064501842243c0b00090140170f042808203054144c0301d03140c1c41240690b40c00d4614130701001c2d10b031500c1c0405130540038010388c00246d110114a460b07054501a142c2121034a1581c223101001700002d00000c0c94107032087d480d00c8890800c92070802e082e145510b0303010050319001d85c2c20303588081040e06038409120095403a81121101c1d1880000c01d02e0280181c43d42140d240c2e425800c00171b15007a410300361680100b90159041c01082c8140801e10ba108004403454400c1c5840303071180402910a107009250400e002281010400c01c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 808293381 1250 808292131 808292179
    0x5070306060e0a0528020f0a0903110405041a0408040302060a080f010b04151101200409050703020913090311031b01050a020702010503071808030d06031203150501110705 75
    0x1440d42810042c1d0315541c09010460302c058170101400c0300d20444401890b4044500380e502c84030140c8006051919481840030749a100c3d01d004000203c8100d000e10404c0306400003030f490220161400c02007031409558012038120445003030300c00319844500260401400000311009154007500a640f9a900680064006e6009071590406080803000214203103409400ba90111510142ca01204a4400e403080ea1a003500071064982952603a4207505401c0c0703d0890300d50090344076103030700355120300d05036030b4a04490001e0081002c06004001c903c2d645c1e5266004a40d256007003100c0051414028903041d101424a4080c07083c440c000850401402c5603000c1401e81340e400003100900080da40d01d9660800c80c0b00e240c80003030101f503062020481c841e10074509544450880310b901101e90ba2640c5031030746103801801182a4094603070806004100c0b144c1c0c0402c04510352401c00f80001010319103054070985950082c2e0b4108980c0d414130340c2119604118460040c400502491301200b400180c03035214013 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 808294631 1250 808293381 808293389
    0x30602130e1b040510050d020c060103020306070c050c010e030a06050108010f061d0103030503060a03080f071a0f010e0a111903061e09020706020c010e0c0103050606120406180507030606 82
    0x44042000500302c00050722100380120b40b0400c801d8902401d010401c920b00380e210992008100c020300040007000030340e1000b4104070170064010081585188101854840b00410100810007a107550308001003001030340610014007401c089158045080c0442e10f007805003840604900d06000000400710707010740c082d45c0c02200c0e0328024001c460711a480d80b010209011162400c040043c001000440c4c41400a95000702c4010310154520b03a490302c801550750041c10348412211000207207202040321401840c0d0203514a60a034080b030f85010300340034a0039001403195050a21508000910501182e070150359074260400c0f20903160421001c0003040701d0118004200401c1c503050700412440d00440158604480004071214221304154280010f0742220404658181d0207105901c0c1004013130203804042e001900090500c25400c50004013503420140a450142c80100003150382a00e607080031560082e00b000005c194040c4403071001340c000c0b01440014086009400010040040c1c40c2c201100315 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 808295881 1250 808294631 808294649
    0x81e030f011505180d1a01060f0e090603060a0f0b0d0b011e0f120302010b060f0c2a0409020f0901061706090c0702010e151801020708030c071a0403060213 68
    0x10040c4900030740351446203103a00d500051211320142c09902c3d2581a510341d00d40f065800100a1101890b034040864003a0429800b1907655544160040d5001400e1403804400b00d0307228800d8180080401e854010182080784002d4072001e10114003541604595404100940101c00d54540b03410a00d68014080c086c00f00c601c101e640b8651400c440b820b100e030042d5149100c2515416180c000404001ea5130814201e06554990040b105a03035074480280c9003071140e03240144c2e907911001460320b0900e01c0034401e5424446144460200c1c1c400d078202c180403208019100050754071054000a07550003000f00d00c2552001211b0000b0034107951154038844c1c075032803007140c0d510745450f50010020b200008841200c000c40c2c042c0180030256100d0014010160009404488180100444940940d010610351b42404081e100c7c0298175590401184000b0b09080000e0b5051100344003034591944d40b98490020072680740404450030700561000c58000b181d01407801c55845001c00805034400b02240300711100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 808297131 1250 808295881 808295909
    0x5060f12130b0708040f053708030c0f0c010606030e060a0504021309030519030c020f0c061b03120907061e090603020307020304051e0a0b16081e030f01 67
    0x5107065505007405003a8014444041591190340440f10090010f1043d1503500789120000d000c601e05020b01004031100004541001526220301d83c03040000d207003c03805480d100704031720300442c600030240ca0b004662159502d03964449a140c10304107000c2c0d94002081d55103046400580c0913050341c0490300c01544017080d0350303080e41c03802c4408080f40c00484000c0d411005038403d41c031214070301d039000d08500d921a080843c100001c0c010b00b070744200e42c03e110340804640e65060003401507030100620a0000d025500400c2d9440d562b00100304c1d0f50084846000c2d00b901050324050001c1014010b84603006c00744030180010345170408501340e407502103202e008041250b50018039802c19001119404114890321480759207860705404030020b50008007000110b0100f400080390a0b0345008861032090001d01e01582041509002c00181c1020b41d400107408000030800907102c4424080c0410307101c0e80100030581c5030342c2c403d565220000c512b5580b0200040c800420407081c040c100c0000c81c1031f02c0d003500301044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 808298381 1250 808297131 808297141
    0x608090a03120203070c060e0a0b0907080c121c03051506120402090702190b0a053402011418010b1005180f030109050615040204060e06070c05060f12 66
    0x1803944010003000e8005060a95030010b01101c1d5002940c00080c14079017251404000d4031402d04070b03002e95400a0b6540c01241e5040706128101d0f070210b4015084101074601c05103841c12040e55180c1c400803c6020700d045140c01501030f002404984501880c0b00f0300640304041d01180140140401c948807480a049035240140c60306254003660003400f42c03501488000d88a039020000f02100080074041140b182e0882c4616494041403c0414940320380c07050303030182c10481554001d489004084121000c0090241c80d0302c203440602900c160f41201110003000404060228098983e00c6001c0010b104078205102005001c4400240c000d8000d8000300700c4001c03070104100a8250407540c0800141b81031101d411602039841d00c015121200800790000d2410540c082400e4404564054403580c00c00d000304a1241025031624034001c004450840c0740c18180b04c0050024054a211705d4003a030750200e481004c2041c20881c4501a1800400340c545803102005c0c0041d20781c1c04071030303d0a41050f044022030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 808299631 1250 808298381 808298383
    0x21b0d09080607200a020310090b06040b0a03080a110313080615130b010e13020c06090d080c0307200d090e01120326150f0303070309050405060402040e01080601060809 74
    0xa409030f0003a030fa4a4440c00c1c00b900b209036004140704100c031400e00480581c200142e504000f890540c10742c0c0c01f404541241e0b1030411540c004001080c4901a50800700c200c00284d440032107440c03d0b07d501c040c0301a1104120b4800700c44010580440030035a1000195034000c0144081007030f42101c2003c0120f4156980c1c0c5814840301d5a0b83c00700c0c5c41d0b008000f944203c0755030700c02904000c443c800185062201d20070030301d002805c20a600c10105500e1a800100c2c81c132078420511020f54400c2e100402084201d40d220ba00514600000f02030400c0780c000480402e0480d44030b80301c1b60001d82e0f1804e400000d80c0f140c0f0000c4a0701e4000590000012603100140000c90a490200160481c3e1034a03540489034882501c00341c421101421003180c12078521000256224151b290f0680244483c0d00c50302c01a00480090243d01d03100e006000d4441e030310078400140001c1e4001011420780c0c0341a10003041988425000c42c0c0a40100d402240410b044000040f891504c0064001c0c1210f030039a41d001102c0d15800c4040e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 808300881 1250 808299631 808299643
    0x9090c08060106230c1c14040b04030b0702032b0e030304051f0608100b03031b010f0b0d050d0c02030c12010b0a0b0403080a031a090114010215010f18021b0d0908 71
    0x980240c0002203140706000c1101c100000a8806e810a2081d00c03105c1c2503a0f00c010340c8030340c10205400c40e0208083c03083c089014569075002c0c1450000b1842c0c07500050b00b0744001c0c00501040b4241d00c84c0c46061400c00d1519801161040d000b22080b01d480e41450b01d400c9440d0441408600070b1004064802441c925003405010222500c910103010182c0820000d24040c104400c034554252208104100c03a64918050600b4040403d10000820200010f40ca1040e40e500101d958450780a034591000030400101e62259161305c9400d1a01d0300c06001c3c40441c0c02c020007980380d02d600c0440c0a419110130401904401c180e403004590140d41d42c1c0d120000e08603580124040a86965004d1103100021070080d4002e402c4034041040c45d0341018451400030740400026005580c4041084010240c42d580401c01000e009424440c4005c00e0343c109000860708092034451118507402030b14541001c0d0825038100c030b6006008a21a200c0400d0084030b4540c0d60300c00b140c0d940c00080d002280000d4807140413441e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 808302131 1250 808300881 808300897
    0x1721270c0f0126040c181a1207180b01020601350106080106030c090506010804020303180f0a1d070215070c1a160e040b03030409090c0806010623 64
    0x86018826a800442d00c0140c010721800000003901c02e084100003d51851070f105620440782200da50382000540c1c9000c41840b030041100a00303040c101c8401028881d212209144190780d0092000e4105258902c1d010150b4042c003600c0c001c0558010100c030180d00207031020002a0200c440c80c0e4cd0310030a038284000b1041d6046050904e92101c0c0c10f03600c141d0a1401c42c482c115000100313855403240341e00c170300b1100e07603a0044031030b5041c02c0d40c20030004810740561a80f020003424140e4040c41d198003c2512841401c252030382c0103801c0c3d044d9285641c1d80d41a441d80c141303009010b0042494540c0522602d00f200394440d0034a982480e00062092880002c2c18034400f200144c030701300107407250807040d6100d0800b00c504550300780035844c611028003c600c80f05ca20608480d0f1040710340c000d03040300180801103485400ea005604000c0c03190a182c400008880445204000000e5044103a0030460f0141d0141d411050031070180307000001d20154400e07030a8072103a0304170319403400071014185465240c1c401c5100d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 808303381 1250 808302131 808302139
    0x25140304080a021c030507030f09120e03030f040f0801140702030711010e1002070e0c0c0601030f02010c08030f190506010c0b0c1c0e10091721270c 65
    0x103000942007409040c0c0401e036801240c48405040f40162420b0004604400020341e6902c10400419414041d0705048000014100009410f5403103008000d40e04041d203d0601145000c0c15000b62070402c1100c58954401e040e040d180c44e2220304500101c036580c46200190343c00c0c020207103800903800e0256070040c0980e40044d881c0640c0c03a600c900c1d000303860307402c01030500140030030000898480b4208540b56140030341c00f808081e41040880401c081010b095044041014401c0030740305400042c0880c1501d402803074850a00c802880126411150014001d2111f9004020f0214000140f22100d0186450340440140944084d0b82c12040355800c581041c002540301603000301007440184155006500e0859481c50030300600641c2c5c07199000002c9074412655130b180042c01105003808041805a803541080c07004007081d0701d400500d1840408004584d040014038048016548402c50b10700960a160824051404030100b0000e8590f0a4140080d180c8e020105c00c5036886c046141050503038010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 808304631 1250 808303381 808303387
    0x203070504090c0c080c030a090b03011a22030f30050d0b03071e09020f041a0403020a0605030f10030309090902030a0209101d06061803030904052514 66
    0xb25440302a100e25048501807002050b42c040c080703407030321008000700c01503100150741d030783d40e01340d002000e00b41d0076440500854020b000501c000d4800d610900c82070031410010391307160001400420640000780c0311914914040803400001c101040c080d0f0300d070307113405140560381e12948c444500c03072140a4103440c1074144030842c0b84009102d02030005000360389c503540da0010310070318042c001c03a2500c0f0301c070b4202800d82502d0880420205c25041882d5018208981041d814000582c42c60607841c021030055001c80040a64016006103251003620002d40d0018071351140c4942d940401742c40d80d4401e8880d01c003000d07207032800103440f41c098645580c101d96241e88c40c0d658981c54601481c004006458049906000d910803210159036105c03001400b55030101d01c0340000700c2c642505080c14841011103071140da8485030420420b66070b0f40e020f07501328948101070035500030021000203082d1700c070310361000740e01610300b005001540142c0071031070403004848000b540d0a1445500c0a540d04203032100d001210207010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 808305881 1250 808304631 808304639
    0x4060f080105180d120e0c1e0f041404020d17030709060807030e0c04050a06030812070e1009050603070c1a0406111303060b0d0b0106080a0f0e0a12020f0706020102090a05040203070504 81
    0x15500546499151b901a13403001c0500c2d40001d04040035080b00d440000e0202d052281075443c0ca0602e1b080d8800040311b04201d002d25800340c00b40c10801c000e0010f44034018002c0104184a01400e40070704041040340099501e25240a0140c44c0800340d0044400080001002400340c500a00c01c840207614480c000b42a084030b0901001702408000300104002034540d1800000210044052300c040c200d8211800f42c9482c01c0f51009241c407120500092090072100f400405960f003245a140988100340c3d1095a01e507150b11041d108100031f0328005009600303d0462903880010251511f0245101d10307800d0118412003640b08055005e04900c2020458194104000195242d0301c29219034034081c160b011a84425210341c1d8809500341e002801051228081118000b504d10920a4003c503d0604000841400720110b41d950022103000f0701d80c8442e408580303001070007000105100c110f00403c6a03900b03500d40384000e0103034203c0303c001d034025585500f01041518003402581d11440240d61058101850 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 808307131 1250 808305881 808305917
    0xa0c0605091807090515220e04110d0c1d0f0907180e06010b041719060506010e030607090501030e060708220206030f041118130204060f080105180d 65
    0x207407400083c40421301c070029480e1140c0c1c40000d4682c40504411fa1118011114041201c20300c3d041b01c1e8007015400810b004004907411201d030816085944800d0a0171808041200d4105945011300303116080040016030791215081c10440c8050450000600d4803400380003189100c041d03d001c8941d401002e8207000040c0d03507003019960a00b0701140808d1405410b0040c5040c1103003a007080301480c600003014011501105104005184008020100381c1004c2101c3e619126440400903d410348801c0420882d030312031101c1c6907921038028151030317840c20811320151501c00a4400ea80c04242010805140c1e1000420710380e00c00ca400b82c80c0c0c2c05031690703040c455082c6c011181401d01d00d001812002c603000740e103480000c1c51161042524550880c100350174558a14004020305602c65504240061800300148603000e8100356040c4e00c000c0942c00c6480090040c260030340000f41004e004c101700240586054000714041c5840d24840c11641c620203050545801038803580002149040c4c0c00380d01c020031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 808308381 1250 808307131 808307179
    0xd0c110a020906330c0706170c090d141c03060e0705070503070b010806060a24080a021e070204180b04020d150c0c060e010b0906101407050a0c060509 66
    0x1e1185a545034618000300c1555100044c4041000c002c0007058180b03081d00200200c80283c011400c2030409603102d50b44010b22444024840340c4207150106004c0d442d0340705e40c0c0d512040c0343c1c0e220b05101000409881e945580b0300d4485c0c07101e15509003607030703a240b8200d01a12440d400e982c02d4001d5120765a80303840054819901c004412182403004000c141c000c2032210f584d15020f404a00041d2610341021010072500100380d410140c915400d807115150f0082d00501500707103610503420720898560341c1c890358000030700403d2008203400041120f00040100a20300a1003418400c503001c101b010403901000360075070b101c0c0b90000d105040300004140945050422052018820b9000440d00c4203c00710a4094850707103c010b1002c5042c500c4040c007045064007500c0e0b40141820000c100c0459103100044d92140050318180c0500101940c0c801140d1040c514410744c40700c0e00426650320100e0b460a150364450111060382c0c405c220070390110710a0b100c2c2046a008402c010403c0000c2c0140d03020300c6002072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 808309631 1250 808308381 808308409
    0x3190206070b061c050a02180906060904020a090606050d110309070303050d090609110102011a130e0a0f08040806150904030323070210180c06050d020904020d0c110a020906 76
    0x3040c103855441000100b004d0300c101e45104a01030300d09902c0720300c14040c0c20f451601c80c0c2c141d10303285803082000c15940050082d50001040b203200240741c545001080200b481a00105421401c0039804115140c005000b08421442850304207d030b180c0c04c04018450780000e4540050f03076004040d040000c41d21034400b40020b025144400140041c05070f80d00003c895000307404a4030100800d0341d540407582c082c411301c4640c9588100050a00c03201d14002120030601822184c1c03101e55840f138100d041c1404020112110360321481241c0000d607103080000c015042071150341400d103c1c10001813401e080710418401006006880e01c52203494654054014000c500c5030048030194111003e8905008034041b1802441c841c0c018109100380701d400c0000b0b0340c9200c807229945854020548000807802130441d0122016880c2203512102400140d8003c1d1042d103941e04e92140c004140c05e80317080401e070f00c11700300452a07854102040803a4030009464800524010390700c20000c8000842c2824400d54038085a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 808310881 1250 808309631 808309639
    0xa0e0d050a0213061d010311030703121809050c09030f03090a0303030f02130905061c0f03030e031c021207020c1f0302162006040f090b010c060e060603190206070b06 73
    0x25210080400c41d2102c10421098290703645c0c0040003441400d4520002c0c04130b065016221a40c2151100f4483c0000320000b80c0402c025400a0250810001c4810000d40105001480942480d268042d41d503000b030135800c1e10034029800f40201800d0004100e0f13030500400341003607103a43e286880c02c2d0010609824982c1d4801d408001c2500c40074154112080a0440c0060018840c00c2c2304040c080ca005a006e1003528080032800c540c00071420742d5903403181050303140c680440c0529646149900703500840c8030b411003090071400c511562100b980c000c1c0104003000c6100f40c0042d60750030012a65950001c5c10f0540015143d0300e02126001d228a501e450f2008034100035243c41508401c5400164001c80240e940388014003001141e46c10b0300c83c180a00000c100e070307581d007494107003c6490301d200158410807044590f195000d180e964060500c4034000c50308a6010080c00004007007480d22080c04441c1d141c032074041c01040d02d002034400720451051a07006401c0f0350034144559180410500f014044a0788 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 808312131 1250 808310881 808310891
    0x804080105011e061b08040e0403120e0a02210114011508160c1b050d030e1201050613180b0f0703051021050703020d0510060614190e040f020a0e0d050a0213 69
    0x300070080700c00c06e0245112fa5140c040309080708e001d800403108c000d01c2c000540d8000a402d10017680d02c00c9600c00c4242c1000700200300c85140318100741d0040ca90b1203e0121407141c1c0038000540d508840801c00082c203415141d861680d5103011400d281c010002e01d0010114880122541c003280540c0054844c0d110f504100c0326000c0c3e12240054820309141d4021400114004403030003540c01c00540c003400720b2120400920480c10180d00080005460080661400c0d541e00821007054062008146405130041b5200445050451480c180a24100c1b00c3e0030119082c040441d40c840f0041008030102c407150540f0001c1e40740620855840c103480c40d041a117040c41030000c00310150362601101046144500000c2501c00b1490142e10284c8010b60322480910540b8184a21850074400450355044421034045242011040082d5103a104803a60250428905141588050160350081140641d2600c800c202d140300081000154000200001d065030452805540142050400407412110307140021031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 808313381 1250 808312131 808312139
    0x1605010903142a04060503030a09030f081c05090105092d1e0f150105090402040902040f090b0714070f0305130902071b06080405120901020a0804080105011e061b0804 73
    0x1c6070b483c00e1191000c030301c42064510040c0f601313206540c000d140550140d8100940b81d2030103805400544030140c408960100480c0410180004460780f074103250001401d1b00d0020301d0304070b000b0101120740003260b601c3d18020400d400d000003050100c0a0712904030480c2c0b10b15411254140080300399090006224100d0503041143d001d50202c0c0e40c2d82c01410040810308054045c0d5450400c03e01c0c0d4840700038001030014052a01d0740c040360b551298055802264042d40b610105006201160070072207500e00e021074210400c000083d509001d51400d940c3c88011690418040d41d031842441401400c3e0211a059640000d00076009400c4c41040500251075460760b48070000180e0f800742401310b846019900c2c0b242e1482d0345945100b40034008920f052039031894240c1d9025540c4050748106c0603030400101e4581d170668420014401825440402c1e552125900d00341c4c135020302400e0007800c1d6010b0219207400a816000c40c0b00c04200e44c440c2c3d64000007148050000303048195005025a021101044041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 808314631 1250 808313381 808313413
    0x308060301021e0f1b15071e180b0a030605031e100b0103110c0f0d14120a110d06170303100e1306020a080f070e010207030201030f0f110c160501090314 67
    0x42c811a17500d070041c01d4046206407502c411440002c281d4414003401e40c0e10f250712405908422403442c105400c0415000070080d940650300d08003035011a904660001340c000d840c603495000b90040341c1095046550a40304040f0300030724400e80c03004c8900d0561100c5464000d0224980045a980c42c0605001407540c030440f500c02c54903070148101d0022940010240039100300c00f04030711510300b141407807c0044000c034450240f820384519001099040e0346040450519022a03100644802c05003103405d40d5800d000c444c51020745038a200340720701e420301e0320f046144d6010007004a0b4411101c0031064001d40e800c00100d4071141c0005003501a0800c00d03503210074000b401c2c910040480358180c1c4c079030603810b2504000c44170112400401d0700d82008003166007080d0a0b60006028410740c0c2c0e09080114400702c2001842d0014412a1194000141003078000040070203082d000305030440c2000300352000d0034200441c00710001040c1c880c81e8002884032000b0030110302c03000340500e04079450409513880301c0b40300c580107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 808315881 1250 808314631 808314667
    0x605030a0813060e13050405070801052818020d0609080315190e2710060501020d09080304091a090f091e0c010f1403090a0308060301021e0f 62
    0x1c4584480029040703020b0031404100d440240014541070450800c2c00c004190703491030303200507110210340340c5000c2010450300344918006804040c0082089181c2015170f8000780d10b0382c0788510b4040c042404c0042c60308600c1d002c1c2ca0b400007105a0b2407030343c2120039800c0c49091342d05034034150b560541e036030b1001c4005001b00d4011400b41d03141a05030382c100118071040001040c40b00040d01441c1c00c40c4032040000000c4600b80c42d40c000c100c8000d55224041c60910317401038990280180f6854001d000c034800c0a00d100d0742c0690291002a400c641742800306060a98140c8041d002d2445154401d1008022040140d04103e0101c00d0a1182d4030035400d44001040e00e0510650301b0040c000d80540c00c204000204108101c0c2c1c1c4800f2200c3d9008403451006400d4860f900043d0440c100140b188041c2c030842e004000a01d840e00c050511290f0f24900340e035442d03480d08290b08044000455250204800d440c0500a4030b10f0130003006d24000c5440303446059125540c0c044008900224810301029480c85085c070745d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 808317131 1250 808315881 808315883
    0xa0b0c03130b03010f0803120408090f3012040312200601060206090a21090302030f010b0112020a050904090c05041e0c170f060103060306060b090316050d0201080a0605030a 76
    0x8815101d504100c2030707011103c42d0350000100b07031f407060215050301034900b58400d41081d00302400759a12410742c8080796035a640c80450310340020b031074010140000c00d8030540d07000c01800c0c0b075480064a03040c0175046031544103045411803044800e20060021681d03a01d8650740f518030b142410804051040c810bda82d0300c000034002411a003220004019070b50301401310590007401c54002d40401c05242d41c030400c0c0140e400601407a940310042c0d400b02054012821000030315002404c80303429078248130105000e055500516400103010826a1003410320324000d07110800107039102c0c242451081e00510008000c0200d007503440114440000072103440740c2c4141d5008040c50003519002030311040410b41941e945420582c02c1102d00e0107840460f00256046940200e4005a00109903c0d8480104c2c082c04882c0c0014200500e4000002100001c032002800405416000e40710007886500040b07480c0344103445226084049000c01200642c07043c4160303940801003c00000e80907450301d010078134000f09460 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 808318381 1250 808317131 808317149
    0x1b020d03022a1f0204050a12022407050c010e090a050601200a0c0b180111011b09060e1912020105070f0f0b0c030c0405040209010c050d080717060a0b0c0313 69
    0x2c041d40c00340c0c500c0c010091103104042d0f0561810703181c040810031a41042c880c85401307032000746c210340440d610007020319100d501d403464411300840d002290180079031100070101c03024070070340c011a4180e50051042100c13210008008580c2c0d980c40110441c0034100003402d00381007004c0e102d40c90410300c5102654113401500d41c8014000102c0c41c1c9401410070002d0340040c10f60b800107000740400003c0da641c00e04c00340741080c41c0c905007803a01140780b580034001c5003410707000e03580c2c031640b08070f01c42a400b110350003c4900170764134220352401e0b01091050208212103610420409050300344080420f09021040192062400501d012400e8a603001c0789202d00324225110b1001400580900c01e4035048a500401e55005561841c02c00040341809441980b00315030140d03401080c584c046030301445c80e9202c01a0003a041d01c094880000008200c07600440c0c8110200380000341c464514048210354500c51400a00004400c1d4104076405401c1d411040820240784001c00285803488565180b94005128001c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 808319631 1250 808318381 808318393
    0xf080a15030615060e0f012312061c0b010e0c09030a0b010504151215060e090d0f171b130603020a030b0d1a0405010b030d050d1b020d03022a 62
    0xc182581418003a03004c40b0400008141030070340740d911151001d4402e2003d0800794450000034002102c5001480c2d2600242074002c182c400c4c0c01144444403a102d03800c100c61480d011580c0c20f00c2042c405a83c0400644000d085038018058001c1c01c0d240b403600014103080c1c0e24181461500040d15180209004030380907808500100aa41014020002a607101407000a0080d01781100c40801e0f1240c4040030f042500e004400c0c41094400b607100320050100108424400d10f44207003a259030b070f0200c03884c143c0094515184091054851b03c07425480c1c81c40c51840e00c0c0580c9030803120301029801e0a14804110004106084071040d03000d000368000c0080d07171000350701c03a0805600070f070440b20b030580a00d014446210407240060000c250708001030311045030a003290f0319141444d03801860f00090251f0141b1903065048495904500908042c0402d80410b00c80700d0301d0030000c21050049002044090703444982074020080c02038002d06800904655658000f13511902c0e0b00100038075007054032100350058 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 808320881 1250 808319631 808319651
    0x40c030b031e030a030c051b010e0706050c070317211801060b030601050d091e020a050301020c0c100519050a030c0e0913050c09040605090d0c030f080a150306 70
    0x2441a42c02c041c0707006504442da8195042c4164491040e03441038000c2694440f0740c2d000d014042c5041ea02e460290f40c0104106941b0482e00300c2c024017003c2040d258511035608001000e901c00d1040342c00495005c006041c0152940c0c1e13440c02030984410807410f1802d4107002c12440701c204142c04a40b02a03054541a03032600b070901e0142c100000360b140001c0c16074106002841600700c0e40c0b0403240c1100d42840d0559503106c001c00b0301d0300201031001e401806000038258688810b00007200001c000c0b80203c0d01510916581d104040c201e100c4c030a50840d017034006128041c0d561410205030650880f803030502603d030041da040002b040c054051a1070700802e20210768a000385070b040c0309011850501d400c1c015102884400000c0d5607a50080610518440b0b080301c51040090038041d0041003000034000c038150b410325150050140c1000c5482d14002d1050403102815a8814281c0410241e01601d4154455200d070f00101c403440c0c00200003011054480441e160b644007402c0707683e00114041d0780e0003e0401c001c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 808322131 1250 808320881 808320883
    0x305103305061330140a020405150f011d040209010c06020c0102040e060402070f1101121b0e0105040b0904050402210d020105011502060c071e110f0103140f15040c030b03 75
    0x444250030229078460681c00d401c0a481d44c08240c80d50740102e8003080b01111180c090b0302e80355001070b00079040342c11700060212002d8800c944442d00c02d41241e0b0009a44221001111741c0380050580c50f40184285240300300c1401c255005210b0a8018900b0004022540d140c140c16a071142281031456903001034208030032a10580c400382c02c61001c950951a00720a41c960590040312000040c0c07030321210800d496251f038001c841400c030540340c1801c00c2c0320f1821003201d80044040f00558480105143e1064086598440c40445044d144c07030f0140f441c200442001848002c08000380102d80240d0542445184000f114110396098040040203017000e239040c501c000d081d540c040e40920b44405070040c0030506590007181c2070b030f801110840e45d162140c03c1c03810b2100381d40200c414207203e5030450003500424001c4424440131814003e403081405810031a004500f21002a180b00b85960340c0107002c80c0d880104c684205420a0702001917071070800015002604561040c640d503004656100c0342c0e9200c43c10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 808323381 1250 808322131 808322159
    0x3011d0619060b0910021c020106140102070e0c220915140d062c031207021501060f0e03011107142b171003051033050613 54
    0x1caa4400e220403842e080fa1030103140100c440440c4640c9803110b24800c0d00b0f10801145203001104035401080d60b148401c00790003400113003e802d05403003070b8500c0c20030207500000703500c406c0304da6000b03d20700c2550b1522085041038004000c08806403d1a012010b00c0c03984c1c3c2c0d03d160020300640c202c0016006080700f4072521a141d00c2c3d02a2000390388524030f40d03029a40e0090721046054020b000401c015a01c00c001300c46103000d05030304800c1c4100079010f4034504a0000043c2895221820040c005500c0d500d006980c2c0b0700098104200701d85900c0014003110b881803d6020358200c11b0f003485004610041c0004e030944502c002200c45070f510116031032046c040700b11010000c0f00c0c1007134080c00507501140241420348480084a00c42c116000d030940318010300c1501c014525032400d03601140c0c40e0a00040c01c0d41007500c1440300383d4061250b55a640580000ca00c504203449404811101018100c034000c2290701c010751822071a29011140c000410340c94a00c01002091462b0844146040c101203420181c22 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 808324631 1250 808323381 808323421
    0x71b08191724060d020f03010f060f02030423032103090d0c0c090e0f060c0706050f100303110f03040906080601060c0b04080f16030909180302031803011d06 69
    0x102010340621000240104400081a001d840c83c65a551141ca01280a886079101001d8036940000c00010082c010b5101d9005444460762515212190036030104e07030342d02590242c148440e078211f90b61038001c03202d426030001901c805003d80b4020038022600e000c08480c0120000540200042040844c20007804100840c4c0c0b06404e001d00311560603100d61086440c18080c8181d010b1ba2091003125030002080f5030045d01d0040c40403111076190000d08013009070400c070000c4403040e04010100f25404404505a0b100785004c0140280c0036186441c1103032582d5074008c01d10405d000d12504084481c4007030004202800400350302007001443c115510385030900585c005e00c100160090300d1000644c2401c0c1d0140c01035040629203403509240301c2c042c44144504c041c625040720200c14003808058110614200b110106002001a0b41110302d018101a100c0e2100a005030000c1240e042c000819014206031a02c0290001540c02d80040a43cac045000001300c00c0d00741da001004111540c10340b544480504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 808325881 1250 808324631 808324651
    0xf09121e050408120711060a12270303091e05070e010b1e1309230703050105031005040c1203050408070f0506040324020f0c0c0405071b081917 63
    0x458602031143c1c0d128001005900580d001c00160704092102040524804180c01401540d0341c1c00007400180c11600034000300f00c81c440c20040018801d0001406030100603500014903004400981e400324010002c41c1406c880c3c41e03041c5018800d0110807405807040b020312400041c03510900300a071a240e40702c0142d00840d842c1a0030005104c2510281010584e400038041c0700544904c0d0300216500b0780d64440e00044130062600e00c041046000100c4000c4c1c160404c0032030080192101075040307040d03035024000c141d010361012110307040a205030352050b0390103801104510700080d181c9a0803250703109240e5064001910205040c449264148030b828028820490040a07081c50180132400b54015440080c05201208484028140c1008091000120344a204555400840e4504990b5400100780260148191001401c5031b0410f4802c0318001c40054603800340541d11004600c000d050a0722046a080c0014462402500400e041d50b8034040240d44070b00700b045010020404030b400c0010400800c1c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 808327131 1250 808325881 808325887
    0xa0b06030a0c060c170307030b0f04061a0d0207080708090913260903010c020f0c010903080702190306020a03060617060a0b030a09080f030406050105011706040f09121e05 75
    0x5408a5501d60484020f4107040c00114130b2410701c2e070500b004035074010038095000410815003551590003c0951403044444018a0071a40c1c10320044607654090340c50309804640280d502c1c8038814016100446200030301500d070a2131540d9851407500304180071500c01074085058201480d29080d0164000790408031440300c56003a031110b4458000a04591a814100014801c00b1301c440004440c1c440300060000d00400c0030401c5c00940e0b070b03150b03000d2801450080d40c151124070f601c0340c410341d4112074200240c0c0d81400690740030040d0009403c200ea400d41e540c54200000002d000740040c2c9540f07100b60701c0c00505603140407009000f40b4001e03a4003910511170001041180d0b5586801002643c201c1000c0301d80303d40c2c90440040c000c00d07011002404415000c15054000b0080c04d00442c0314510130030701030000766031316001520314904921203004240b01d61000640541080da014000d0f100d48020085000001b0361101c0e0341d4400c640076802c000403001000da14400d4043d6441e90350b890402c1c581140703 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 808328381 1250 808327131 808327133
    0xf1e02072d0308060a03050a11091501051c06080d0503100b0715090203010b0604080a0c0807060f0804020310051807050f010e0f061323030a030909020a17090a0b06030a 74
    0x5041c510080003400e2010940111300d01e40c5405030050040c0d070f80542119444951410001c400c84600359140c2e21400c10b04000842c104409005071031b1007c0c043c0c442c43e0501410405002c504034804101c038001c5a078692001138100340800c070059105e006a2100707642d074142000c0c00ca00d403070702903013065104140400810f0000703946645600901070183c4030000f042c003110300c0000e001d8407070a001c20341d02c110080b4020420440c04501c1361766083c0308005a03040c0540c3c0d0380300c0d10303101d1865200740300c00714030101000350030103014410b8254032030700c001c00703039005080400309240448100fa220381c150711500d480428079419003088034901800d0100c6003418400000b81c002090145c02002890061861100030103054581000f5540c0252408900c0040b10f078484558680c00198548281c40f001c211900c8041a0b040100e4459041e640507550000a1402c1c5040708010b503020724400c404000440849440040b0f81da0056400f0b516144003401850800c2d05024843d9140074240c2d07403094000d450020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 808329631 1250 808328381 808328453
    0x106090c0c0f061401060513050906061b0313060509030c0108041502090d050102070f0215030601230702030706030606140913090311031207080109140601030f1e0207 73
    0xc502507001c42ca941e0010301d503261143c0075080e28a59964101c08520010801c2071b0440064602d010a14440d070000d07039601c0b41002080346081c0d80198006008201600c0d0b40d0143e662802d4540750094116071070000e07014208003185189500c00c60029030b011400300030720b25041c444022942c000b4a00a0741ca4241601c80d812109420344009036140e84c00aa4030088bc4c46c0e51040308410b031b0f01300e030003191940000e0034500404005048103d00c40c13004100f030765810fa908181641e0148206039101c00360f140214218500140740c0c00d0503034401103403d000302c2005a8007042180c028010316039002c10303e1498051f014080009141240c860b409090000310791649070700c091551400d0089a01007a0500e0600742940c1013805002071904501001031040c07419007440ca101c500a1450b90707912000c03a80e84d0b00c005030881d490350500140701760250002c559039602c41e07049040e039100a808000f501640440b00c0d41d0080144e01428100280c020584a00780304130143c502c54444078542c442c1e401c183c4001040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 808330881 1250 808329631 808329647
    0x102070815061f1e0e090a05060909120f071a1905070306030807080d090b0f01030506132a090905010509010b06090108070513031a06040c030b03071404110a110106090c 74
    0x4036140c408454048103c5621580c03c08114002c05800b109645c181f0b054800c0103400201c40d043d0042070148085a552003001a00d0352900000011003810030101c3c440350300541c3e10803801520005890204140480c0e0825071a0303015a0f803100e00784034100381100d0090291341006101e5018035140c0031040001c42c001130126080980c1c40f0769601c0e0744000004140e0010501d1903005032540c0003101c00c0000d004501c41c07809041e030b40120120f901542c2d034400d000e45054280c98000300303c501e140802042503405071075401140006805d070202c119483c0c2180008036200c1c0501501c0e141c3d10b2f0402c2c04983c1c04280b048440c07886081d0b0741d144c501500c51001810040004d80702d40304005c000515400250750701000c8102465002603000b520805000305048158003c0e10207900c00c46c9440111103095000344140100110060094042140f8001400703655062004907150000d44a01c1d05030030207001d28009012100e00c40c1c0303900943c801c8072079145085861a03008503606a02d010700d0307428910307002051 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 808332131 1250 808330881 808330907
    0x3040902071407060c0b010e01061b02030a02030318150703090303050f0d0603030e040f060305070510020f03030a0516020312013003030609380102070815061f 70
    0x409a61240300d45480c02d94020669040d29280c011000046402a80601101c10b06800b40990303c2040e625601c0091012400b0710900c0c01041488070118050b0031030001404c0c144e40001d09403080541190013103819944005001d94810409408a0510b031920a1050342c4240c14802e9480c14683c0b00d90f00a44101c0c0140809002e0004c042090a5481c0c481d4044803480c002145062104a94070700d8080c1c1b0746041c030903115105500300544418540c200b0302c55201141e420800602007146000c050044c10000c01c20084210700400c004400c4042c42040218096240400c00280794900706404403032540500740540d045410421401401d401c600724054190f5121440f44549105003030401d503c00d529011642034426401c840100505801d41c1c8041c00720360000c40180000c070b00d55001010a42c0c0056484208907450158100007801005041040b0800c1030040f11172160300c0e05045450a0360101e801031000c07420208018090601048200341e581d4100400c0e00c1c00d4180c100003070010003080d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 808333381 1250 808332131 808332149
    0x106140d02120a0f050313050102010902130209040f1a04180302100c0504030b04050c1507051b01050903031c0f0e0a0210180f08070f030c030f02030709020c010903110c030304 77
    0x18072180c0c440702c24405484002e50250482200c41072600e8100c1e1203800c1840c0906201039131000020f615401070140300d1545600601c4d8052400ea02404a0000d4200c122165003041d9144020728015125100391103220120b010402d003003403945000c20040d501403440080c000c400062a080002c2e0b00002e0286c07000c0303510400031031250310f9038200322040d009560015089800600512042c80b03070100d110100d04001382d442c013025a00f00c4c1c03d08407a40c416880000d005500c0008a15114549000220072410052518a24103400d100003c0e165410140b0030341c0d02060103c25420705a0001d200d070381544a0380038800e214a421300345a40c0c1d03d0760b1540e00e010f4060862980307810303040c5220b0340d004007420482d0964415030f20348400504841640074040c00c1440e02c500342e0080b034410b5a4015220461b540000b102c1c4115081da03a84c80c1524100180480e00341c840d0715004111000e0b24001740003c1140320000046c000c8050800500820450f10107031480c2d04084445a420303107011003100d090302e100310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 808334631 1250 808333381 808333399
    0x901090807111c0609170307021b1f021f090c06120b04060f03030801120507180905070b07111002030406180e0903271e010513030c05030106140d02 65
    0xa408035030209450b8003440c10104400d52a4410000b2642c8445c81e90f600035411585401c419030000c0c5114402603919001681c40161a4032007102c440c040e202200340d01810703003440318441343e207a50800510b030031280025030071007000e000b428807881c4800140c1c0c070314004007841640d8072620f079100c0c5004c6d1381c000da0041010001c030000303031900d1341e80200c0d404c010047c004000c215038035464040e02d142c003070004800154a240000035444130040340c030709100c1d80000181c844145407503448910710546000d030f24100c1f501d600500c004582c003880814020240000d0f4295a46418030301803600c000728101e2103200d00ea1516035950400d6002098405036607050400d01c1034040c501000401002940c0d0240e41310503580c00802c200701c0c0000c40a0201440b0f2010504c1c80c1501505100f40711020819180d43c01c01c81d040a46403414014002070804240c060520302d141095002c1440210a2650002d48800400355410003090400348212402028440d070709102000203040050005040c0301700181c4101080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 808335881 1250 808334631 808334663
    0x70f1d040b030c0d0c05030c0d080306220c091802282015061002060403080a02120a091709030705150906030a1b080402100c060b04020d0e01050901090807 68
    0x300104045044014130030090103200d85001c1c4000341c0d02d40a500e00a01400c2c0c550a8141041401074080e07940c081911401e65441c0418805418a00c1c50142c1e15280c140d089444240c460340b26002001e01c0c0d59442c41c18590a00f440f1800a050004070b040c1100c0c41008208404c201a1050030b400320385588030b801c07840d51100001c8802c14011114031101c40b07404000e0750504140054030f506154810384480505070340b21010000002201e012200243c0c110307100141c00640700c1d10900350701a8103268010f040c800b00002d00180c1c1030003101c0b5450150f44c1c038000c00041c8402011300440c18500c1222083c54240d400300480c1c5c54000300d115080c002d07000c416644050040c090180c0700c24100142c441c0f40c403840c01c440e0003405040500140003007a001c0c035002d408050300c113400c110300c40d03070300504182d41e00307450840200d4005503110300c1a90120fa60700101c103019603c0e400185190b0301004070219005035811821400c4a0b4007900d2184180e142c000208006600c101c159920396811a51084800a807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 808337131 1250 808335881 808335883
    0xc10082401030605060a03020c0d080105100e010c0c0303170906070e2e1815081f03120c020102060a05011a0708040906331b03090e0f070f1d040b03 65
    0x3e0b80c000a83c0410f0200340011599803550103030406500c04012503954601c090300c1a43e405000380aa2504000742c16071104029010340d03080c44d0345d1441890107d400ea441c40c0c0300c0c4c0104c0782040e00300700c0001d0700001d6242401d241d01301324150000b50240c0503004a0904a90140110450b0f610b26030080c651914140d029809d081d141a0002c001c43d54420210071400200402d182000c002c5a034011b285544007085030100301010007541001a1112042c60b22107045c45040005080c0b641085681d070700704040001004070a1005c2c0c0d0094030385582540220030701c006424280d005105611052600c2d00400c041c5040004070b03465070021280b450360780e4110342420800c0d441a07130047c04c84242004070016050001d226100d4000c00749285510012121205241540c41d03e900010000b903442031581041c104880300030034501d171003400d01c113192031380d030310f902c2035111074110351203030b44500407008024809410107441021240c2918001d02d44411620614205450700800c8034001ca80c1e070080c207003107510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 808338381 1250 808337131 808337141
    0x60f011413060809061003020f012d09061412010611030c061312051806030a0b1512010f03050a03050a110313050f0d08041202010219050c1008240103 66
    0x2510545403103400392140c0d40a000c083c07095070100e103036105460004503080303103103510102540c0e03000b40741103180e000c140c0c011030760702201404100c800c00d005203030b48503803400040c01c2d108921005d0700d0b0719514502e0700b007029004040008100b19103010410521207440b100301c4550b415901142842600342e040a9441d0f4514010f81c0e10b000b5a911445041c04444190202084000c41c8141c4030060702c2a0524012241c5010320780000b103e80e1343c10350380e20015240a201850340720b0b200d200c00040ca0a2854006099001d8081d6001009500000c04100c040d00c46103443d80989840c0d40c0e000c218500e1030381d541e0b96404084401900f0843c0208105031628840c0460080c96040e4a080303903140c4144e00700300c0f42c052006204a5129040e480d4007441c0d40d0a0003e03000030340f280c00000040c100b601e081c140e1884440c001904030b04502450700803152a0360505145021f0600640013064462a6081440b64401e0411100c0b002d01000c802000070a4000e5000c1e0803481090040240c9204101d00050f40980 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 808339631 1250 808338381 808338397
    0xa180b0f151621020a151a0f01050c12090f240a0509121e0c061b0102040b040e18061506090d02100f1421040c09061715060f0114 57
    0x40f4452416080250340001c60f2284103009003418846a2202d00060b000c940380d5580d106e05d101c01500d1516442d00c0d113888618074154060416500d0103241c0340c01035040c11000a010303603d009000c0b03107445071411714a1001d4a03940c41541c0c440715140c90841d080d004003400d0094070113551400144036002d94814003e0307a0392507101a16424010700c400103507684500b00d03804001000071401c000c0c005949000104881c0035040a04581c3c54840d450b501d24060030508010701c0c144e503408100010300c210320300c00103000900c0780d501307141a14100365040901d0201d60703414940150703110805002031000c070b000014010ba84216240c1d0b50300c001c51008560b0080e101c09000e0f41c400590510020000d0300020368050044641d41c40407901c071035040c010f00050240386151200c204248484c4100d0748285440e6940160085907180d0758203031323a4040d5400792600e64100c104910306040340125006001c00540d031100c01d00d0041c9143c0e524258001c070321424081d6180a0411000c1e28614020242c4481124144 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 808340881 1250 808339631 808339673
    0x40318030605040b0f15120114090f1c0e0603060d051203180604050a0b1f0b09041a090a0f18260301060503070e0a180b0f1516 56
    0x2540c81c100351009040881c0c041e980072908600050a4040030080140f007200c000c080d401132146040306102c0c402c03054090404180d9030b0b8016090071500f00d214441e11504048000b407000029003c2d00c2e46c06c00700d403503a80c260000e000e80c400d24440741d000340c02c0000d0584290742d01d903200d0366100001000c01c482c07050017401c1030280c0c20034641c4015001d001103104000c42c0303c0803500e00408001a640e1050300300d601412079005014144005190149210741007002405903024503140742c0c03031400b523848a6501c40c180320324001a00b80c242d030505028090400d0881c1d1070309008600300c100170a02a8030000c1c212040b03d9988e060640080445a0012640e604030a0401004516038586101803402052031405410102072500c00301030107034403c0780d040c0e030364a0792054115155024181c2e4224440b000c041d500c9003515a0104109417207840040c03d2414800001c6001c602503000c1c40181240595a5809024400d080d8103850710705070204c8156036151001c034001004141440910014000c100b4402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 808342131 1250 808340881 808340927
    0x4050409050a031d01020619090b130501060b030105010807181e090f0c170723190801080c06070f06060b04090b04020a0e01030c14030a0608061506030c030403 70
    0xe008000402d410314910907141c08039007035041c0350480346400920b2511030050703000000064080c80001c00190341d2044011012954a090f9a00c8410200f0110f139001c10b084100d0785c020f01400424003510009200c0c104200e881c550500d030009080e11801019401401420340418804100c4040700c100102460704e961036038010f20030200980500b19224841c011410030409501e42c05540c41108103100190f10741041c3c8604814200103510402400c540034440c0007400c1d94400c4030300b0040c0910202d0315004040d40c80d400351022081e199034a48010f41045851001441030a00020783c0301244841114400c1e1110960301e40900c054225902c010710090034241c00158000d1040c002c1d1080d40c0210005020a041f05801e0104900410002d40d00140f000c00e826015135000c0c4e4409519503c0b54038042c22495003403401c2402a51041c7d50200d1561758420341040310340b200b4841940c00104020160058129000010b04140405440d079042400000003080406029041300f0415106601603419 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 808343381 1250 808342131 808342133
    0x1e040312061202041407050304031d091314120d1d01020d0c020d0c02150313021203090424060509190603140105010309020a15020307050a111807020d1404050409 71
    0x340d1042e694000b24003907400c01c60344c0e140d8508480c1d88548905c4440c0d1b9401e0031507031251021107483c43c40c41d0354090b0131113201496190f291262450144502e2148212a01426881c9810004060420740803591608001c0210280c011114101c82d00000d9004010624070030402d11248101e02191000d4055880000c0d00088050560482c1b00c0004442d001e0780c16a110080c0280d40321052018020742c0310000c0b201c18500342180d03001542e00180c00842c0868000102d5020031100b200355800c01c07000c1d0303101141c822564a01809074402d034003610b03036031241c00940d03521003a007044c20140500d40034010040391402c010740319111003038072900300c418400000d940c1d10540036005090305940c800000d1422800031443c0c1d4002c0c0a0882c2603640544001d0056182c4409a40b008144069030340c11804104103440215004020b01c0c0105400b074020308a4940052040020400c030030f0f10100f2543c0320000c104070180c0d80100f01003000840f10301b0b01d2080d0504900b00314002d84215006a40d10500d0704240030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 808344631 1250 808343381 808343399
    0x8010911010206091903050a0e04020d05010e0114030a0807050a020306011518060215040303060906180b01020a030504140105090402030405011a0a15031503050307031d0103051e04031206 82
    0xa08151007a002d90f100d64845184c442c1d200c40c4d0660100b00489014694103000904c601e005190044103458242c162080d0300c0000340580e071002007860040c1740c80d0700c014403440c2c04c4280c0081c01080d50507140034810585002080d12500488405410000040b0701d03541800020701c008412a907008041e6805503840b41c61203c150140030410000180350b105840392200c01c6980d05034160740c1c59400038090220340403602800014010822005c050301c43e0400180e01805010303d001034182c0c00c00c0000d90302d540b1800d010480f2070002f03c150455010414040100740c00000301c0e016501100c000d5034403100754200607580d5110720440c45401510010411092000643c0450746032011201c9480503055500c041000307901490241c540390740c1e1440100312003d4041d50207183c20440a041c215041d6139640c541c42d00710f0b0031450003900841e04602400041500100408080d00710074281046203061940c161280d600007042e09e0001500f0000c046410315024420706161003081100510109031a80c050b1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 808345881 1250 808344631 808344653
    0xd02040c0507060c0315090c02250302030c0a0e1603020c0d05030109150501140a030b0a09020a1214070503070c050d03061a030108150c071202010902120109020f19080109 75
    0x42c1c0f4a00d180c5200c016840d480307400750444507900303082d0440089040410031401090074189040a62117168580c030f9100007080100c401850245106411032890342c014182814003100e10184642080300c0c0a016603615101e8281e0426410b4015260f541e43c20403056000b8450712840380398510074031030890444c56101006605940c0d035800c05000b60800e038181c081e00d10b9244d02415010030441071a4503080c48051018088880252401040d0041c4880206802100340e8100390742050300000c00504007904103c0d1301e40e62643d0840304221841c803000882040d00d001030039100400400202040341e203840345200c81d0615410000f640c40c4840c071020050010600d0744101c800799481440c4000d00c0c2040081642c1c102c48203000030341010307003070f2001012461800034260641550300380b1040020a0f068004040c02031640d40000681c150b1a00412004a141503482c110982c10810800c00607265011854810b010941300482d9503e10780c0301441a4501682022040d50f181452190900c601c0d0995 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 808347131 1250 808345881 808345883
    0xc0911042616120210030203040b070e150f0a0315030519080d0510080606060f031302012028020d030f030f020706060e0603061e06150301170c100e0f0d02040c0507 72
    0x1035105d4111202c10150180c4c002150301034210882400042c50085c05071006034490840100100c44003a11090401c6160300b02034403a400e00e440214501900c6030305071041c81d0040fa03a0300f100030305103841e40e905d0558400e400d240e841c0c0c0d0840c14208031130030030294206540203059480014040c9203400800060f42945510840c03030a8894500403410a04085081707a600c2204280d02c00e03d0342c1e07160130003410b2017009954100d04014000006040c250f500060f050f40002c680400f901c0004001c4107210b451a40c804000d00401c44002610f0340160303030f24081110310a074141440d540f40c2000500a80007070080031081c10900f8000076421080107003a40c006000d84041003e88a0242c5841061503170f546c1c02105c4800980b4504d8004ca030703182c404056025400f0320010416940840c2507411526680c00a9001184009810003200c4201c00180889aa240c400707880c0607da4446803440240703408000f121150040e50020303240d200c55101c00b2454440960054070511000002e507200070f044d50b00180c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 808348381 1250 808347131 808347139
    0x70201030515010c02040b0604090216051b01091809120e15030f040320070321020a0b15031203070509130504200612040c09110426161202 61
    0x19007028107014414046141a51085a01c806550900c00100580c0d00052351000003403200140c07125490005200452040300d81d03c0341c0050626202e0b29110810741540310341c202c0042001156607000402d075044070080c000f0300c0f90891501c00e10200400c20303c0030117070808500d00501c14010303802480900407444191841014848078060000050106540c070020340d4441c0400700b80840d100d80c0092214444040c41000128010190b07140781004940c8201d804017011821000c11080e429440079888403140054055411540c2c1c0e501210400100615010f200c9190070820940302013000e8452003a80045e8240c0c0ca0070124005499030b00100e40040c401c2c402c0e20100380b81c00005000742c600555200c0d49501d0006046803000130500e450445590300002e06003c6420203910040c10070340114000c114003d805c6042040010582d00050450014400d040004008460300d10b41c1110800c8400e07800c00104055141302c0034105072014032400c06010b9000d2001ca1540c000c581f03d64103440c401c0f1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 808349631 1250 808348381 808348391
    0xc05060709080c040203101a160b0402040c21150503010f020904150f09021b100f0b0a030215030c040b0c030301090b150306190f0306050603010e012f1e07020103 71
    0x40130001680b0080f200c200262020040070004010144195100c8031074040026081c4280c2111400600401403070941e960010340d03044c8820350800340318202e0740b5110b500d0007042c01030f58051120000303181c042243e00c54a950f4040c440103200d90242c204080d1074014002e1100b59140e0b27107408042d40140c07040740d1089250842240c034200707034080e108084071000c2d1150b030441482d144018009400c8240c0400304007843d2514620400700522142c209891510320000e0084417841d004011200c1c02442140502255401032015a070f814252036008000e0841c06a5282d41300010903080380680d50002000500c0864041489107022000d14180d800c8000c081240311200d90070001040031444c2030081c00760b02000498614103018802210060f001c02ca04202e407540d0f00030000100810380d2060702d840b41e592042c40858602802410313811015a0001d10a2150001041a500107441c00440011902a081e41400305e4544162500000030a64052405c00003140444060b400014100d002074500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 808350881 1250 808349631 808349653
    0x30204060e0106080a0218060703081b0c150c13030f150603080d1d06090703030e0307051c061404030c060510080616020a05012a02030a02150402010c0506070908 71
    0x40d0304941040e074804c00540c4848840c18000d61010051380c4154005100a204640314400108211b6110f551343c0715503460800f00c0da043d4040056882c0301c3c0e86204000200004030002080b144600044030301005584940180d00d0562007103002a4000e851b011400106018014108040b018007a05804a91a500c0034182c011900e0134000109021424011800042c2e0154084007030f1880f49907041c142c004040707024924283c0119a0719145902141c000e004040d80490460304108040c1e000341941070a0100041c0d0000c94209060070000c07148150f00c00f888040d42040588003403100318030040c0d04060400501070301000805a03445804d24000c0b44906d120b10b40d04800302c0e204034010b0700f007075103600c618540c180301d1002c0000b04501c034048010010401c2882121454140100880708890b02c14400024840e084c80e2200d080d03400a01c0a04a003d802140c0142200d40303141c14505160360f20720060b503003c1c107885400345c464030480041142a5400080d9032003501c1d40503007110550001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 808352131 1250 808350881 808350899
    0x180614090d26060d0204061502010e030f03010504021c05070306050f01230c0304080610050a0608010602030a080402060d0219031a1c03030e0604030e0108070311070b04080f120103020406 82
    0x30810314110719101c00b078286500010740441d45904008000c0401803c200d0301e80014060f40d10f2034104440102d0250003046802d5024411507150010502c0954100a203180742c052190205102c1c0c03900a0b0340008407a0f0070340107035100101e0f1020480c0c108002034204504000c0081849000b1540142780b500344005043d8001c14074440c0c1c20401c44140c620107003890ba00302816030802c2500840c18030040c0320118035a01d05110151140c010038014400c001d1912007003240c02e50842c1d02007400c1c00f001d100107000c050750120460701040c2c41c1d814403080a0b15244085440d5105c2c41080701940d52001c2195100072074103105c80c1104007219038042c090811110408690b0818040e88142e1140e8040e511360001180c20079090311550190900045100c07000415500340b000071642100040da48058009007503802151085d08095180703010082c04030440304e0450144200c803800b808001e40040024204a65407084841c442c0e10390302050340740e9900e400002c0d4103034000c2c04101e1040c1e0030030ba0003045003d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 808353381 1250 808352131 808352147
    0x2103070312020306061e19030b15031603050411090c0318030405060a08040203150108070e10050a06120b0604060c020306090105041a100807030b09010e0601060203040504180614090d 80
    0x50080040386030554910410b48404202001c100501c51b090003e0004200940c1a04641800b16103000c2070801464040016040146855070000c850a1041c1701146883d49405c180d404a94107000405484500300307540310101004032113030b21080300010004000d9510014500840c9400c40300c9003140303404045580c030390240f8002d03903030080428007024043c10311a00c1d40540182c0094190340e1241807002d401c04140c0000d030840c55056000c08000c10414200b801400d500070302c0081a003034a80e0810b00014105d91452080c0810454140301810340d0740b5007a4001c07c0b618100420702d83c0c0c1e480d654079000d00ba014018500364800e001d0b020018000c0704060180d144510b51060441130199040043d02c040303050003a100903d00e48403000040341098041005c400918001c5214900c540742185846003900c50645405210b038200c17000401803940c002003511b040c0c030b00889000c10315040d070900303907280d03c405050003922590601c3d01003030928900d035800d940035600000c00e49010010900060329448 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 808354631 1250 808353381 808353391
    0x6040c02031c06090213260c061b0f070503150103050a08070c1a1213050a140312010906080f12030105090604060305060708010801060f0b07080921030703120203 71
    0x7030000c01c41910039415440e8001c41c080b10b20507001070303080e440d80d550600704d0700002c40c1d40d1056040c1d800c0521200500c00e40e030300803041388406901c000032400791407145c8441c9420740e0640602c6012074451000408000008415103044089500c1c44005080d40380e0798440c180700704d900a004028102c258000380b012440e0582e030300b00e0000c240c2c403071803079488485640c01410285c4042c41907800210744243c11008803000b07410400d20040d01c1e80981c040c0b0400030135014184888024403940722600084000c00d00d4400150080000204024500702d1281148030f105c10000094101e08004100040d00d5071100003962080401c0321001d0314640310f00c50f9696250100c04044100900c0100440e00d02003e400303500640c05000400c1d1140c0daa0b80e964603001c0c054030000080b98460b80140040310092094800400b1035003540d600040c5440c2c0804558442e1441c080c046200c00074132445507840780040002c4007401035243c5122160080007003616600028412400581094141e0070f0352800b90003030300c0c099 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 808355881 1250 808354631 808354633
    0xa1a060d21050424080f06090f270f160e010911210411010905011b05070302031f1406100e01030b060d060504060e090d08150d0305090906040c02 64
    0x1e002048054034098000701d088000c1040410001c5840e845003000c21044190310507060300c2d00e0010b441c004c0c04003d001030450b00d18050301410040a595580303c0c45401c84015400c3c500e2548507081c1481091045000b00700c3c9040d54002c0444803401300258660945070b4003c20380b428521011041c1e411400780b440740002c403109200040c08000c44950041c3c01140b400f41c0c00c1480c0c200111081e03001c10001d10f1383e2a61000307158080009101d20020742040c0d5002c24a0708505d058100b000180c12408140303501d44215960180c0003080040405c0403c0c055600101110b0740b500d40000c000b901c200c2446141c000440c02d10354101d14106409500074001d02c002484c081c1c4c000328400e403c5501d08080710301c1d241055200e00000b030180e10303580002c0c00040700703000c000700c2c2081c140010300c0190b030b29503801860100d00e02d000300034180d880419081a4500329280002194440d807102c6a2200040c00359594040031b440c3c4003508040c1c00c01c00815030f0244c155868407141e902d0b04204404c40d0310400260003d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 808357131 1250 808355881 808355903
    0x100e0d050307030f0c030209040c0e1003090206040b0301080a1a0f06121006090606091a0910211b170109020319110c01111c1109030a1a060d 62
    0x1845024001039039118080b4a0002401110450703220151140900440080b030790008020a00b801c060144070981c10305800e180b000103580e4800714403610701e0b820202c020940e80b00f503180e046550305c000b190010410080f44640320350b140d10075552541e09070141210b403951510768482c0d060305100682c920440003a1120200c03a985c2609102400c0e41003030800c051401400c6240c00d9480507031190402910107150002030303403030034420003030007001064000074080f507003c0311440c000180100483d2000042600c4036500c0b003031610030030f591404104e4801c00b1b00c04207800500300011030703507030103101c1102c412159020200302020007556800028941120002183d1005100c0780c0307010b400940e000f000041ca40c0444020900c00e11007183d21081122940c86400034601060801c24091088070a241044d440c0c903007018643c0710000b55200111721400e1680302d8030403a8840b010701054801c00d02d03018090303030b07602d008618000a1044054040c08044504e00000c42d41d0303410a940724140da16031040340724007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 808358381 1250 808357131 808357153
    0x60527090a1119171005100e04081b031c1415012a030504140603190b0103180506160509010203090d14010e030a020601080c0d0f03270602100e 63
    0x500e000c803098008610100c6000005a030358096036095004d102d10f43c058041c81c41d8144440c0140c2d0400342c0350040040b1041c100780080d01100300c0080e040340e48010540da98820b11403185203412100d407407007403941c000401e2045a5038090000e0039030701c51a0100070020001501405481440c0541c0c46503e0000b5100e60312026500480b00300f001c10860b0144498020a0700400d038262814500003100060700c040780800c03049007056548561a80b0484620b821498410503000d600000c2c0d241c03600105883e070102e501d441e4002e920283c40180441c4904850901c43d06003145d03a50b2086d10f0069040103c804018105441201a1802d40c00142d01841c60451001c0800102c0741c6142010354400b50008001c1180d0701c401d206051040d004d4401035070300c80b5003d01003e0309140301640503460982189854845542ea00108605030aa00405610540e04bc5003421107040e840d03031104c041300c480051910981d076003900a00900300c60741d0b03500b15007901c01e0445403c0c0942c0e249503160300ca00d500c03521a0740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 808359631 1250 808358381 808358389
    0x3160c08011b0e0d0602040b22120b0705121014090c031b04051216080f07030605190e0c031908070602030c19080103020901120b06090a060527090a11 66
    0x20040c03d00038036050700c0c2d000c03d8031442c0032a4042d80c04102d09203000030314803200d800c100c80854118243d243d03100702c41d98a0029214031303410b58494010f1003082c502c00000c140c140148165901c3d403482c109084014900306038100c81006483c001e07132160b100e2003c400d440301c0c903082d007106120303207004040c040c00c1d91240c0341140204d80c00b03420590308100040c0404600303074580310071000c0700c503c0100041550105100003000c0404c80d039082003c454000e01c40c642c00102c00010b900044a900000c001800d41e0740d0020850000001010007107014141102642c02e00340000344e902103150118107032500d02c48544424504540b072030350001c220300c1090102c9004616035601071a440718540440903c0c0c80244d2100d000030750215118000820450001071080d814009111130250104a140009948007916100c84050000b4901031082c0b000000043c5880c0086e080080200005041d903841ca043c03103c624002001700f1411050301d02120000600200800108000c8207a007000d107051807000f0410500c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 808360881 1250 808359631 808359647
    0x140102070620121305032b09051009080c03030901091802120f0a14190b060c0a081e0708040e04030e1f020c01020c1e040e03160c08011b 60
    0x14407140c0900314542c002c01c00050128640390704003019110b07512403a00305404510201e941046010368130041e81e50100380070405141600a44070a0060601030308071504451059858201c16005848000d00b42101c0d500f018450b000c0c0c45403d0191403610802d072081c1a920b02504013aa40003e211410030400150a0348048501d005c511001601e04851410884030000041c0d40d18030300200140e0408c1584844c9200704030454110080020b458141241c00202462980307440c0241c0341e903100c407000060760300c01c0201e44500394813409a4114040c14103001030345030040c00d10015021210000f4201c001c0444044615290f8014840342c2824107054030070058003c0203008a044c09800095000166294003054248201c80d000705d007510340c40701c0c5000f410040360406081c19980702c0e4103a6000f43e40d6840510b505c5620072071210400d140c0800004020304607800307010009000c0003410b105000500c0c044591000d00458900c41c600d07644502c002c1c00c80c0c0c18600d0003007034070300b800001e01240b92080300c403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 808362131 1250 808360881 808360907
    0x31806020705070803030403050c07060f080f280e2404080a030e150603150c030a0f141e09120d09030e0315060a050901080a02011103130b0406091401020706 69
    0xf1190002d441e6141189150301c1500d09401060000c501d0300f60204040068070040c080a01d40021016080200500080030250098061552850009200c0034103c51002002c44000c1001d0215031419919132006102c40101e40d42c550140c0f0152214085c00d41c40986c1990803d10680b801564036601e03034105035000079092504054550600c0b445034141044049403c9041d003034101c0d11350508004042c9070450301c40d026083c00ca000000c1045444030f51003034980c48036010f000031401e802401c2c041030092000c0001c01e50b075002d90100703120310300b46596450780c505030001c214054540ca0380316a05968005c9080480115041081800043c0615030030030580144207003048070a00d5074050000e8203004424005818007007a5604009013460f0220f01000103090560b041501541000c0740c60342c88000f41380c2d010303041c4000d03607803180c4407600c0410844880412303c1052042d241d8444060307246961281c803d0000291014001013040000c26103d100420016001018041d140040076240c0000d0408 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 808363381 1250 808362131 808362133
    0x6070807140307090905250305090a0212011a01080c0a1412150f10080f040807021f020105062e02070b0a0c02031b01050d020d0617010516031806020705 67
    0x600d4000460102075030003001c440d20f4000400e424411460200c820040c092000c0744581d94031800c40d04181c1d034450740143d5680c03230045542c1d52002a00ca240c284400402034025031203c181c006040b0041d40b1110318016040c8022034aa0200760044131003503c10358110071998410000880e0f8180121001040c03102c18002d00c5080084010344820913203800c442c01500395841d1a1056154070b01401014010b01040b268a20081c3c0d9441004081450051141449a02c400d0101d01409290802d65201039030060001040d4071411444044810302584040055802d081c04152645400705461414201030f180c9000e4007400d040629400740c80403d062020340c001c1d508d002c100f049400006003210f8000d6201c0c13a45248284c41454500023507a1b087c4208007a9810089000381c1e0f111007103802d0b0140e10100075844d0805012501c00400d41d80d4025903601d02c582034084030041064004d64419244826142d26021140f101502036446046080c00e100c400300d8034003000030301203038040d00980d40150 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 808364631 1250 808363381 808363397
    0xb27100e0c01080c0702030c041e0b1906080a02040801020a05070614012102180a1e0e0d0f0215130614100612060302030d110d110705010e061905180f0306070807 71
    0x1e020408507985404200c0c01c003200c91440c030305000c0c0e84d40209400480709454cc0078112500c5400600e0000c91401080100120784020500780b05548d0107880c00741251200071552018204e00103809035008031001c8448a00b014110305030010804022030481d030003c0d504642000400c540c8080840310b001c812079000340000607160426100500042c13050880c800e0014940080300ba402c8140c10382410b050314114200880702410790700100f43d03060011114244034a06940006040e824060644c82e8404820415810004c41a0a00185c0c10800b0300915080141c100000d227540b451100448124014a00d500c00400c40c141c4945841c1c80c02848642c0001111500c950009081850224442000500144034100884c005100a03a407442590801c610418030181103103448407154890541400040110002291102030071120360b82c0c107004800c1c4c0c0040e8100005050758018401210400c041c1c03400d070b1861400c2005810008000060007404d0564030081300311042ea00080400c0d08000c0c143c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 808365881 1250 808364631 808364653
    0x501030506011808010e1b130b120d0f090603090c15030e0102041202010206070903030e0d230d02070603060503060109020d0608060103080304030314060108040b27100e0c01080c070203 81
    0x10340a400058500031001081e00b0f40101c1728940f030040c4540803c0b01f80102d204410b07807140d98402202c00d2480c00040c1c086569030301c5d803001907401c3c07141d240a40814000d40d0005104a41d11842c0b52985009641b40c1410315600c0301e2040b01224980340f4010700340c107075039041405014184124000f42d100300f0700c0d000c500d8500c1d011000d401c0e0f800caa0300201919084001c80c0e021913805121042d0300000342d00c1c00c0c1403904c0c0345440041c40d8070070304c100580c01000c0b0700034210305001d1441c05103600810498100444003405500b196500c0031440e8091006006e00b40000c507a01c0c2c0f0078060070007100c20060050041c2d03400c00003442d00941c0640d003002c0340c0c50b0752494002a5030505000c0b440c021402103186540b00d241c58240a01621191a0541401401c16080002d142c0c1c000be005074000e038014102780b19580c0c41ca02c00c1e081031129200107800c81e4445001d5002a840c0000d2824070b0f17501c0c00b80c0103007d40c40a14002c955144801c0d4405804070b016140080e030076130185000b41841170300007001ca8030241c80c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 808367131 1250 808365881 808365917
    0x12180d1103030d0b01231b1c0203042c04030804060f0507020a030e0301050c0f0c03040306060b041d0c1b0f010501080a140106080d051303020a06171602030d0b1206010e04050f06060a050103050601 86
    0x1148d203002581020904028800c041079030400110701d408045400c5c0c5840322044080d0060040c0000d00748907054001c10180300c00d1341d10202c002190000100304500705904069a58070030a90124002608401c203c0150706040c0a4140a041440702d800d0030b1820380287d041480d0420f9901111038827081c8400008502140501c40050503220840303695503040495040c07003121101008248202c6038000d22081d80c80c0c00c402c55508076112a10317039401414800c00704c0c0c10a000041c00100541c20701001145104006c07902c08000d9100c0c40d04003a100000040075400d81d0803511400070150032005615a0540c0100c000303001d040a00f4490a00c00c03902d80e8000350320011070b0303001180040c0c64040f0706881103080c1406d1a80020600082016908118900941d01d1207000c0381824595101c1081001c16158520f403504d0351408042500c02039a1500c13001700f44d2110889090318148640310418403100c41c0401c080d0301809014051680e03c0d81402c0c01174004d00409046103041040c400d2502c145104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 808368381 1250 808367131 808367173
    0x11040903170a050f07020a020102060c09012007150309051c23030714030f0a0f06091a09014703070309030212180d1103030d0b01231b 59
    0x40c1400001416013482105078503400c000070030744401c1d9401404118050b030b2700010450341c0a00e40700b200da540c408000b401280d11642070380d4840002103400110b20181007002c50048107031480e507400c66001150301c0b00118141c40002202502c60b400c40900c04100301c20341c1c550210a6810fa040500e0042c400b01000c0c6644ca01480e52540710980c0441807101a5506c0480a603581d50000d90880c02d600f016003402d80e492030090601d03901d1581d03541c495040c44596410100c010704e0381540403c20350054071a0305c0703074940f440c21615208180b04070002ca103084000350002101e501d107544030701c241010061415803200c1142e06c1c01e800d804503074880b1643c20a0380802907202e4078035030340c010400307107881c3c940070f0719085030041030892181c0c00313204a004220301d00040e07503510801295202015415401c19603050080c0b1080240c26000005858070140340030340104103c0842a0386180310710100360303018091110803601c131424000007080145001058000360460380340c000340a1300d0f42d4080300048c20110702 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 808369631 1250 808368381 808368391
    0x150509061011030a032f1903060b07080904061d0109020711040e0f150112020d0f0506041b060504030b0c03070e090702010e070801090c15180314010f091104090317 72
    0x40c0e151011404014080803014400c0c907843c4a69070104c105103240c10b0700d140aa070078210f01f2a2111800c0300d401510907001107001701704000806641340001cbc10524410307448182418055810807000007540007019100319401a58420b8598cd0359003800e204001075400440e040d2010704003541d04904a58032403098003012000100202160400b111905042540d1020240b00003042d84004001601d120902c581199504548401d414901841c0180704009000406001307807080b403040200300110480481034000c41512a00c0c10503a841c82d003200c2c0f62040c4d0100801c001c8040c0041208544a0006580c00c058079040c6040410590804503103070b0001180e5580040c1e44400c0c0051200d82c0c11b000180180468400a1180744050346481400c82018812000401e140d040c042080a00c1100664040c1c80001c4c00d0500203030b5a0304140d1405240801c4820042d46490301210f020529031243c031175041d40c0000000b03503c1003910b0420008003035442056040c001740452414000502e00420b51282c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 808370881 1250 808369631 808369637
    0x60b030403030b010201051b0a17150a0b0c070e04050307020301050408030a14010f15020f0f012007031d0f041d0c151c0605190801150509061011030a 66
    0x40d1800e8180141510b07008000c1c103056900d40014001da0300f00d08004500c4440b00705c3c5281d40d031a412000c0444861414109000301c100317040080c040d04155002058042020844940c81c05d103440701c000b80c0c5c042c07250351508903456000075010000030000c82040f603030083c054000e580c201086900400d00392041240d040b25100c000000b005038005151095000340140310150034465810000403101e4641203018501103040e402038510300c002d2007040358008410b000000d46410703481102d28903028184000031115442080c42c03104480810441c140d03280a509a41c403012501100c081d07032001c10f48504491a00001100b42c04d00454580f40160294403070700710051034210044500b26802e148003000818442c1c500f241e0041c03c0e8410728401d030344062150420801c007100c0302c0d4444000800042e40102c0d00034400c1d85001c0000207034100034208841d1480c009100c2000d01c0c4420064408090195550042d003039004100036060a03288010686450705281d4440c00c49a040b862564211900480c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 808372131 1250 808370881 808370887
    0x30908130911070201080f06040b1c0201080c0313061a030102120f0708071706040621050d02010b31090804060f030b0d0b1b041811160201081306060b 66
    0x10600701d403003068014808403085070b04090080d800240010b802810124031174443c68045004c80c2c0c0d950f0300015200000410701000c10420500320044205006826408207000c0b900042544040000302c905ca0940b01310209010380895a40f04c3c024150340c0080340700b170158001101c00c03988092009021142c2a04050303a0103192010540480c158010301d0f24040202030340c24040c003103803c0b24501c2913032081c1c0b86800c10181c0d54403010070004d082540c4404425150341030040185c07034883c2401c0103a1805071058441d40e00b003e00c0281e081c2e420518049801c038aa0404045107400ca0054040710400e070030789503645650354000250f003035030700414080d2203c1000140c10880a074003d0115080c4480ba0f05050242d44c4082d0006108964104400b07440c00407140300150306015120310ba0102c4a21344a001c40d11240c90b114008040385030010b840c11018505003204c44a541d1080070784000c482000120300013405964011942e1010160021101081310780700c2200103800350050f000604504207034507031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 808373381 1250 808372131 808372139
    0x2030403210c080c0f030d05270c12031324080c031b0705011d010612020a0308130801020f030406063f0609050a0524061003090813 58
    0x1c03001c003031456404269004041c003440001c1d08504001d88103600610881d4a80401c0c000d0707641400304269183c2c40b14040010344031100842603200701d0140501502c1e41810050f03100002c60040d402e00c00e002080da00c149070064241c0307000030318681c0901140c000d403070400900305510003051045030810391b0304848034500c07000603011000f28100201c40310320300400c85080980c218030081c4409010f0138030440500e803c1030403032043d42d41101c03245603001000700007003d4a2a05100c4105c0941d148030f1095080080004120f882040c66106040e0020407182a492440e560181d05601c41c005490241081c07050005900301d00384040d052071159a800e01740d50746002c4c98650220b40d041d4001c030813846210741c40d103081c101c2d210b0003001c002e19202d00b03645540c9101c000032111500079940010140c505101c96802009400b0a00f1000c10340310700200c50064841c25020b05a251001c8041c1080014590001c2c1a500d4040026451040303242000030300410b9545a031000d6910041300e83c11101c1c1103442c208 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 808374631 1250 808373381 808373393
    0x40c030201030e030313120309020306040f1403040b1b07050603090a030327020f01140f070b06060702060304060507090f08010c09050103110406052802070602010c2604051005010602030403 83
    0x10300e6012020000d140765191500c01b4100c4031600d003001801c0e01000c03ca19440c81402940701660041d001000c0b03501c82d2900c2d20345500040140720080b950802c2840170b00010f1000041601c1c00c0e00d02034101c00d810810b103124050101c0e54103955002030b5101e4000000b9080e1134483c021406441044040d0507145001d043c040d040e60742a03281c3d2440c12280306051120028180010401d0a5041b5007801030107900a004030b46c0e00040111415058500249084a1580c001c000305407042c4070340c51003542c81d90303410100106402011400394120701c003040040c0016040d0b030b02c00e0f40d00030201d00b0039000e06502d44812510044150f004040d03143c1d994684100c1c080e8001d12800c2c024442403030700f406110f1049400c500c05020314402c800070f106020898030f50007001211070139442003003d0b40200c0c070040c0300c010003035443c4440c0c41403c000d0f5180a0000b52290b00c01c22603d40888030034802ca050302210540d048485000061041e10f1a000c0c0c070f0345d01c4039500324500644e0300801d095070095803290b085003814 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 808375881 1250 808374631 808374641
    0x40602210a0b03060601080601030218030d02070509012115090b04150b0901060207170c060c1f020f0307110c191503140601140d0c02010c0e033012040c03020103 71
    0x8644a0b070701120401c0390903a80407d805500c41c42c20301e00503807544002c0c005034400145002c0200d80c1405081c400c0124158005194411200100d0784089103990701c01121055246100d40382206114441c045008a400820010b080210403c030000d0458410385941030501e0060300c04892101c5100d00098030701c201030148401001040341c559226514100c40a56540024070a4140d05850803010003120a01402441040d0030054491540d40064881494a2302c00d48030a0f444400702549010721a524203100369500c00740c403000703039a20395217540c81c0c00d031904a0325075100d41c107038418104e801460b922103003400850b07007a096440c04c1802d07090040001d21601110f424000b01440c02c070341404800c0c6d00c040501e4003c64207007003401d4100405a580081c910402c045144060f0500d10100760243e0705512406810005540b040c2078035150608158440c2800f0005102c0e0315656040c103a49040b8010b0400207581001070740d40d01c2e01d01c08001102d071341d10b011901a1703040c0d0324000c002c0066503014099 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 808377131 1250 808375881 808375901
    0x1204050411160219030213020c070b07050307061808070f03091409130c1a03010e060409081c0e0f03030105120d02071712030901020a110c06040509040602210a 70
    0x121508050240d915403050190345200a803248442d110b13007484036000498442c0c05550064070030507001c03515483e41c4020394000c9a030400b9601c920070000400b0007064080d500500d6020b805186000d140c0d4440e8000b030b010481c014400801c3d4504104001170640c001043c034988640b0800711020128100503200300712543c00030100c0c6007814140a969582d0503001944401d980610800f5146241402c0d40124010b8000002e80401c00f0724200d12400403d000d107040761502060740680e40ea0b6002404152007004500030203000051168142e003814030139001c1c2e42c00b003018100081100c0032605540c900b40c0882c03540409a00008014009818600042000ea41e5010000c2802002c3c031007001390341d102c0c3d03031081015056040310000704d010421722603964602c181590768cc0d00c90a0001e0307414000d45c8608000030100f20391440a440002000c11101c0e0130f8078004042d81d040510309018030080f10703002801150960360130040c044c61002101d1720014024801c5441e00b9052408845031000c0b2004242 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 808378381 1250 808377131 808377161
    0x30112170405150c01020903030a08010905130206040303031a0301060f030c0b04120807052401061107060801061b050a05010603020a0b0415031d011109030d0302040e0c070305040812040504 83
    0x10050000751101d0242002c11083d42c140c403560742c1150594580207000f01c000c4144d06010016488943c903900200c442d050340c4104208020b45e072078110301c000d840580e10400941000c01030104101081c042c0d030108030032500007111001c10b03105100010382196000d17000b00b05907d1505109000340040004c20801412102c0040d62509042a00f101d180c00b00c00381c4020000b17079001609400f004024040b540c9100c1150030200f94241d8040030103c4030410900414001594100c0c141c0b1031100c0000c0c0c0c0c4012103045071510140d40e402e0036000c480205460042d46003081101540b500083d108105121080340104000a42c1604510401c456030307034039034840441c2d82d1041c0000e00181c01200e4072a8007407100341c1000100034490780003003011040390b05d940b503e0951a060381510312092140040001c0f060403001c3c1c4a4104c0d5504094040740106c0c003070440b0300c1403d000010160140740005000c814001d0038140c0c01c3c80d03520044a443e050106020bd11a4400840c04100c0b5003002d003d100c24000c0014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 808379631 1250 808378381 808378387
    0x17010503030702091b1603030b010807090608070203161a06060712050d060b13030311070f051c050f010207060c0309050d030902040b040e0a050717150a0b0603011217 73
    0x100000e5a6402421000307407180c00300e000812100c0d00f144640b641d141070450f00241d20ba000c52401c50704c0803002d40d0010740109080104051240d031040c1c250038030500d5240c507040c00860a00404490b6640000c080c2c03c20740c80704100380d006409680c001c542c030b014450442485c1d814610080e8001507039001c1c11181c05903100b4001c4000082070042c0e4031038080382e185441a00d90000305c4114001d000140d015440090001440b011451000d0301401d041c0c0b0f00036200c031000718440350040c0d5928580c510078650704d483e03188014402490002c0f20140c1e9400b402050b0200f160041d01d9841c1800031140c03808105030b500180c02c504100d050b0007212943d22090030100007050b540d88920f501c0b80388520381a020103035101ca40104565641c0c0c0555040603003d40100003402c02c104d0425a12450000c0a54503445514800124401071500b10060381d140ea802a020a45401c802a88010401740020100f0390703d07020312008603210380d80554000d00706411084001c98942c2448040b40b0404160072105000070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 808380881 1250 808379631 808379639
    0x40b01081e0c04051e04050609010f12021324060302070c060318050f031c050c0702060a02070e15040f151203120606200714011101150602010c1701 65
    0x80910020200708080344001d4036a2050050b80031842590801544101100e001c0218826a400031419102007a1401c0095844603000c001103032409100d072100f4a00950001d004030400041d80d640d05520250040c54400e602452031415902d400c2d1301240012080034041421040c0941c0740d000502c140e0400714900519512450404005030280743c083c991141c000005d01d402c04002c0850654022080e00c1c2100c1c140c3e4a8207459500900e983c0c861034111807a4001c0c005500d100d000c0c01038001400092400000303600303101c07254100c1880003003540030368400050038000d25829035100c1c1040c0d147c000c030303050042c1e810482200c1d0421094003203039150000401041c80000101d400303984002d0800900f207021031808940e450a141d5401d600c20741800c10000e030040d00400c0c1d00c0d4041c4040384400100b01c0400c100169201d45512450078040b4000140c84c0103540100c20b0324080451110000c2010b07100d901518541284070303482800141c1d5501c90101038640d1052601e4101d4054140801c441d501d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 808382131 1250 808380881 808380901
    0x90d08070c0b040b07050c0d030c02010b0102070e0a0b01140301180e030307090b030603120d05060f0d030905150f07030c0c06090303020c060f1314010909020304031b05071805010302040b0108 84
    0x288002c00141301074010840c528050416122001c500300d086a000c0c824002c0024003404a000b40030001d9800c200c602e018560010034600255800b0450110403556100c1602e409443d2180380769050100900f048191201604001c3d4040c1c148150a0001d140c1c0400001c0115114503504c0e804581080c030038000081d500401c0c0368110382c00003008507140c2e03e13400000390800c40c0d04600540d10420000d449910700781342e504600e02c6146d0468103584010309607400c0c06a11001d0300d80c02000510280b030b05011503d06140a0450788142c44462400d14600135a00c00080c2e01a00003900130400d244a00d804004145103614090301c0a8600080c005255660203903503140c4d0400801d2041002080c8019001c145100f83d82040e00e1400d0102501d41d40e510324200101e1640c0001c40c0007980c000408503600515000b120b00a0b03915645003c1c44800350248440c81d010140c600300c03900e0107041c40000d180c9100301030b5041100e0a90b080000e25500d1131040008507400c0109542c18130891408210307003200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 808383381 1250 808382131 808382153
    0x90a06030f0308090f03070303090b09030a1202070c0308180a090218040f0e060f010e07020718020d09061e0b09010b070f0309030516090c090f090b030312090d08070c 73
    0x2e41802d00e5195a211148010f0416000a0100c001407102190304030a1661540040c4501c60103400c45100c980c81d100e164588a100714940400840e68040d440c00b81120254010407810313009822180c000c0e500c0341d603880b442c1e92101c801c2c00005031043c101c148042c6020711003d0020800c40301d045140c120f003040418500c4040240043c4aa6507607c0c4801080a0580103071505581c8241592220b03d007048030f079440040280030b2500054005400942d80600000380309050300c50b259011000b52180c041c200c0c01a6014440b80e85100303444007945000150036025401403880140390b2240043d2a42c0714800840760b51160891150b084440104400e541441c200c410113038110a00012030031048c201610080c246030310017040b503c0f032031450390f2030000c2d440308a805844658009202101044104032250055802800b4080c00881410040150507a102c0401c0c240b0103400c2d6410700148052500c59100c0484d20582160401e80d03c40d104207500c600b103160300c10700504140000c106544c5071111520 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 808384631 1250 808383381 808383383
    0x150204050102011b08190b041404051018080f07140d03200706020915031905011d060613090e0f0c100504050f040605060706240506031f0b0d0209090a06030f 69
    0x3000c046d642c5c10301010a41c00c1601104d8015206020300c030740350720303076200c414004136429503140c002e0140070146000e80d405a070400040343d801c2828088803d8030f80240c2a4400f400442035840104400c0d8002090202101203148002000e411640f414400160a0368658800c0081d4804851140c031812020201560500c942221005031140d800202080720001c02c5040140036020102c10000b07029255549688a40360001c81030042e40d9840c03054000707450000e9a200803840d0700304005010b5040510140241e610344440340800d555855107820201c0e180b1600388c4489810103810300303001c418200000f484110080e5851080030724180c000030064020360152728490b0941680c2c00740c0c155034540014000d08401082c60b0b0345c4407000d151920040600c00e504161081c055070301c0000c0c6000c000540411190060081c501d9035035082100c4a0a24a0031440c0c0e501d01281d950219161034014040d0050411000340181d40c1c001c60340402804220050202402c43e003004802d1000815680b0307900252 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 808385881 1250 808384631 808384651
    0x290a0606270e09030c0a050c01230a0804052805060121060f11040e0f0903090d0204091b030308010f090c0e040506010201060527090d0906110307150204050102011b08 73
    0x64541c079210908510581782c1c2c000380b900c2900480001d00401094801014030300340c0324010030030240712074071030310400429120301000000d000c038013051030180e44032a502511803000e03a0100c0c0710401194050380140041600c01c00da03c0c0c602041040410080a8090003407003420222001240c105445030301c200c0d00009203410b8070340d01e04c05903010b2030781c1007680041003406102c0e4403940c50f060103039205681102d2403d2400030b00c00105107a580c012003210415907000d0300b0140341ca0140d400b031102402c64a0005c844e4000e1141200e00110342450b044005903101e0740e24101e5a5140400da4401050640c00003804a440e000504003100d8001c0d0050000003c10340d004600b5170740f1000140d0040c0019848a034103d4050031507518981e208040264a80c10207402c0522181ca640b040e05950700d40b804000e101280b07481c2d4060051078020450241014414130841e0f00e0038046a0b200e405140039604003004040d0007182c01d21040d82c0a004400010202c146041c5171801420001415500060540720301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 808387131 1250 808385881 808385909
    0x606070f02100203070b0a23090c061c0c020309010807080105062709040510060602031e0c07090c081b031902032e1509080703290a060627 61
    0x5190013442036a96040d004100c4d100d280c40c2120140b4090020f01c40c0d03070382101d580b4140c190811041480c026000702c5180000b0403d086d81e034018031a0583c442c84031400708003c00e21050041d42c1c2180180303010050561301858560f0382d00c0d4009070241c100a081c00c8140b0501500500c030b141c851905991100428881a01030090240700804181c0c0102141c140c214900b08104000d005000401d0894801c03c00c1d0100151aa03482040380c40b80a00e40900c0300800d00460255412214580500f02071410310f01500c1c0d0250759010301c4012101d04940c50008a1064810041e0301010804449100c2d0131203a0304a18516080324131022405025000b2590298044082021a40f000c0850310140c469160a40104216002d40040c1480c840c03040324841d81141d1800a04284510905411141101f00501400342146c0d036090035035000d0110a02450020340c50b0b80740000403282c00ca40035088007440000c8440c03d003a00100748024643c2e0440c0b41010064689106100b44c0191310110b0340c011480c510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 808388381 1250 808387131 808387159
    0x906120c01120b270108030f0f071b1d010f0b0a030c1e17091903050d2c1b0d0308130f12021b01050702010c02010c05070f0504050606070f02 62
    0xc003c2c00410416030b00081200c2804500542c0030003022508121140030101a07a41c40100a82d40d20401201d05100340040c010304c0500c0481c000941b00c41841a08002040c0c407130341e2000c0e500441e155001000c0000e8440c1030010000709402007070302401030580040202c50400854160360f2040354070b100205a41c81d20f1103170099100300080e0382e1400c041c6010413086c8401060040c445954880d94480654080c004646044070014a039038400c0b00501703261508442a03142900e242c2c008507003410449465441519900e0401c81c0c03500f181040c03040d003003608200c0c00d05040303241c0340c1148140c215500906803901d4050340d50325042c020060780751410b00d005945001d00b4039020036240000a01c0380000892074030412000e03908021941c07a0b80e1b82156410301ca00c030320344107075035103001000d0b40450401c206110145d441074084003620350041c1408a10302c01c85544040c03500106d64800000d0360040c200c2880300c6d10b070500451382c01100c2118114202203181d240d00c41c0020040f01d00a206010b031213840c070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 808389631 1250 808388381 808388417
    0x60906010e030a080c0a1b0f060807120c0903031106010b03010b180301110a172719030905010e060f040605030414010f05040c05100e100512150906120c01 68
    0x100c550701802c8691170302149906103540d005501c8040722501003a2880d103400500c0d4060100407100507150300c0d45091b1504206456034000940300f002000140d4052100302ea500d4000d692030351201da0340d16060140703181002801000c903200c008540303070420001005420004005d4905442c040d80403540d8403020020128222661101c400d5015400e02030003001c0030011102508a01c031050f21074241e048c3e150303481c4c00b50064003120f1104466040c46113406c08203009405030b00d12860407034101c0d0402d40005128010420310b41804a000505100f418005c1d564003c400301440041a280d0038281081845d0b0840b06004500802003000004400107050040ca40039000b0301070300200c000c10400007160348440260408a4080d0b520840e104000505400d00d564803000b8511180d40750074140c45003c0401c8028103e00c00711904010f000c0c800e2900341074201c1c1455000d21a80483c01d24071040e207006010505034010304051044000d0212210110b202154190604400346005050040d0081c025 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 808390881 1250 808389631 808389643
    0x1020102040905010f050a15020a1b120b010801060f0605040302281206140603030d0c120c09090c03060317030a090605040503030a1401120f060e030309030301061205060906010e03 79
    0xa100c0ca9402c1c00d0000074061107546180d0260340c411f5481345007050302c84224800120441e540c547c01684a100c020f00800e03074880b5158803080d030002c603244040d9680da603c4150503500320703000c1c0d80e681101c1c0010007000e0000d2007618014004441c044d41c0d40e07490b001010300903010350311000e4000c444c100c0c00e10004c03540f0703d00e41c04441030b894500410b4654441d42140c100900f00c510071038032a03141c000c00d109815600000280b0542e4001c0040d890710f00c0c03510300d001c042c01c030b07002c40c04041c030101d101080c4005095001c0d1800b814a2a03035400d1405150032078640a9138104410340050515152050012510f02e48107110000c03c240703541641ea880c1e4405040080500c4a40901424035104c140000c01001000030350203141c0c01c0c0c2003409109000135868206100c207100f03000e15003564080040c00900045e9685150500a801c00a0217441c094641c81c1954421078a03e03d05400000c01402001d80004408414004202c000c0001e07180010100340317100d501401280c14094410810300c010341d010080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 808392131 1250 808390881 808390889
    0x30d2f030408070312090803090f060d092414010303172505030601080f090705011b150915090c05090a02091807030b040b060a0305340801091404110102010204 70
    0x483d40b030503076a401c1184a0f030154801200000301410400103d0510010640d0881d0600404280c0104620344c20000568000c91010b5086900c0d10312030004540c04002065410070076941d507083c0300304038010000880c1d480140008a0900c3c4d40d0061001c240d0250040382119103010306201613490340350850900d0030070b050b1003510240282010305d000d0b0394000090f500883d0280c943c0503c03501c41a03002016070070b04450310300040d402110208160740c4685500861491200d820303501e0381c005031b00c0390903140f0f407a4440300300c5681d2031722024010440c071024445035110340100f04005034107042c2d480c01e8000c6d03960302c42d06201c1d1141d84007048114115070304a910740000101054400780342c04110300d401d16022039080300400d2410382003159270300740750048480401c80240103920b404581d80081e001401d01402000700f022550a4030303035000030b040d607071031028480244038140c0300100f03600c1c02030074a81c05070008004181447c1294074480020481d850304103030700c841384048603507842c00100d0080c091640 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 808393381 1250 808392131 808392133
    0x614150a06033e032403010c021c030f15060801050117060d11040504140706030618020711030a03030207021e09130212031201092007030302090a0b0403060b030d2f030408 75
    0x101744061845214000c00040204901d91820051440200350803074003503d41d9080543c00121920400c0c0412480b030036150182c9007000510004040c070110b0031521040e031030b940903e408103014001c860b0802d580c0e0b40140401d18103280d06000d44a00c4090880e001f4142d54000e01440d0000c0d030400c441514100222000500200081d20b020700385080b081513000d110400030f004509002c11028882c0c005c02054407000d0a00c07810b40c0040086081c002e604c1200e066a800898069480d5181d03024041480c02c14065038001d41c4880042c010000210070072866041e08a404504480392900d6952000d0303806900c60765111010300d000c1c00410007940314540d8241042c0000250325102103c80c02d4650706844444070104516802054010030011840d005090341c91024090600002d109400820325500c010300703070030040e42d981c54201581ea040350700129206915070a000a66040c01c10919507480c40700e1920741049184002c255011501c001803c0b680040c4108840610620030400c481c01815900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 808394631 1250 808393381 808393387
    0x92307050409020d090c0602120724090c0905060a0311010e0102010e060a0e2419090b01030308041415010b16140718050615070614150a06033e 63
    0x7000c094010044050100ca00e1540c0c41d03001f040c101d100040e154a40103d100c291490141d680e2911080c152070340d5185440001031210a0f070129030a8060b101710b081c40307024410241c5d401e160180040d0f64000700064019001007000b000440c04035285140130580a00b402054a650100102d000d0801e86030740d0b0761244140e800307100140000d580030f243e140441d141541d030f80d00500c040116000304e840602000024190022550185540c8040c901519180900041424195a805400d820242e1090b130108000b80200800e10001010344880e11240d20064083c0341d89203030300d004518006000b10b030303521407000c180011000b28401c1c00520b90394001c0440e942d2200406600c40d40c40c0c8460207403000010b1100d4800305a542103004d10b90003400010f00590101ca40c00c0c004d044c0d01c1d0405081543c0c000c0c2c8606684820800031004240150300f40d2002400030000c5501348000c2048a42c81501003614228031400040c2c001180b14041031484000c0e40d004400115a008401b1031403200c08001e18000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 808395881 1250 808394631 808394647
    0x110f0c010309110a14030706030b1f020312010f171f0506060c0102071514042619090f05030a080306060c0703021002030702032b1101061503140109230705040902 71
    0x5c0c40190b64540c03021021540744680318074080f410340781012940b5401003007040f4128140001c0c07548414620b156071040742d0034038140c0c0340440c0d281c1c1d0080e8040000c0b03501502060100401d442c000081c1e040c0c100d00100154210200d4040030219969030f500401941c4201081160b51000d04407408400010029502d075a0701d428050180e150a401c0f10044c149002842a801c1909030100341c0301d01e030400b41400d20741d6018000c0340d6000c0e0b007034140407a0114040050201200e84142948440c40855403600c4805040680f40a04d1a4068214034800c0d44120310000c00141e0b0201240c3d8051401c0d90f080ba201d034045007000345000641c0e00001c2d031100031110580c048540c0000a070403031038000c40840700d9045655000032040c00303a250740920000160140c83c2c0b007460099100c50180c2001e880001076103580c1d1030700b540144c80c00040f03800c00a40ca4031500c4400420fa64242405400c00000c100140c405403184c0d040b40110241c0c0183c03017440d107440024001070054069800401d56032a00303544e12801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 808397131 1250 808395881 808395899
    0x6190203040f0e162109020301110d05040201080a021c11040305030c030a03230a0c02210a02012004030312090c090b09090c100c110303040f06110f0c010309110a 71
    0x4200c2c2c80181c81e58004c00800c1c074540c85150405c1c1200545480b08000c40b003200b12000180c106004c05036055900c80c910b4800802c218001441120700300c40d0b001400d800e051000500c07440e0050200c01541c0c1c01407101420704070400d000000d00c2002d0a000160125415036022418021580064524080402c05c0d2851450110081c5480c02c01c80c3d904100180c0b51741450b9501c24003284284e0369007259440011140605503120403c05c0032640101c8030b0320319003069454842002500506260b0101103003441c4d149409008540d0070004180f240c41041c000700c0840d03c0940500d110181c01c100005180000d1207003550302044115400108100600ea241c1005402034220500024091203404000a11005001c20300c0e18615600500c100070f11103032480d084030392464803079054500700307881c0c18a0202d40c1c0e410801030008002d408aa110740342e2410784041d01d0182e03020322603c4240c21810186030b074202d000c500100c2c100000d081c0041d0294150404601c008807000e42039030480d003050804140d50300d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 808398381 1250 808397131 808397159
    0x605180105070e220c051c0c0c1112010c1e08130201080c0705060a201e0309030904020c0c010314160503100b03130b160509270c040302180606190203040f 68
    0x111035580702d0307c0391404002c40c3c01200d03500007a9000046046400e2000940c56103400a03c10390b004101d29100038040038820308540c020500c1201043c41c0714041c0446041c102c0e18000d81071883d09001046280015036000c0ea01d0100c41c00a0410544c000020030720043d032000c3d00c40180d00107045404034502100e181c802850401c9001c0707140501500517440c1d1080e00011111683c19004101e400404540800d000c0c0d90005412182140002c2c402644691900e01c068016a4031450082070914000381c00507080718071802100c890742e0481020441300c592030140c41e5000205c5840e0043e5696104030f05001032290b6138101030040f4000105001003007807070100750f0705043c1c00f60110005588032983c220810640744180e200c0459402d0003032002511b003400c8400b0b4070304211603c0c0005500c1241c8030380900c110803103914055060200d03051065017450614128032490a40d043e400303a007803240004200303005851400d000c0340000d442c0c0e9203855100b442a10014007100f06070066603500c8a9825945e84 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 808399631 1250 808398381 808398397
    0x1302040e030c012c031e0f07062003070203070b0411040e030702010311031003030507080c0307080c06060303040b070609061d030d050604091707030c020901030605180105070e220c05 80
    0x42005031480401850b031512098028203040015490146d41e4109079101c1545003500c203600b180140480300701901240020041144511800503083d0718101c8560010a417100903081c4078041402004540c030340000454000503042180507200c0e07074862500100310a6119916a0064204000c100980b0000000b0b0f05500e4403d03201805410b20310200814980001c403080888000c9507081000402d003c1d000500b032060181c64240d2500d0b0000c6052861503021a4007181c49a50018207550010300601c0011707040941100554a41803519085000078000c241000d848590341d0410001000140c1d48084d0b92444039104003084020303040c40e055240e40280c48482240350411000408501c1c19200b0200059401804014582461291800160030003c0e003201404518170103140543d4820340038074001d500ca1f64011440b843d100b8620585201c9480029569a04107020b0100d00ca401c545492200d240a0710500768240c48041d1035442121011081050945021004204a80d10600a003905 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 808400881 1250 808399631 808399661
    0x41e0c0f05120105071b0302030c030a0503180106050d0305090418050309040b0f030a0f080c19171c2d0504020a08121c0b031f0b01171302040e030c01 66
    0x782c14014202401c1e92421107202d800104407218460300108108404408580a44116401c1000045580d46568040e040c0c502c0820404002c01c01c0d10840715521200d142e281000a010a61a01c0c1c00724501030382a800080030b011001c1403032425503c079940a00c5c4081c20703040d0103241c81001c0741401a101d41c0443d400e18082c82c00c0c4501c140c480c2c103080704150f81c1004060000c24503004071b6210b02104810440c4110703107202040011940c0b030b020400500b08101c942030b56501b00004035149c00300c62801c6100f117210280300144484000b980c44240c50031a4201e0044011a0410310001c41c86040c0700071034204032820307295041c0b015080007158040c1344550b20070b940e2111400d03110084503a4688498515483c1c0d54020003101d00300100b80e05c0c800c3c0c0c0c03001e8200004a07607064090006802d08503e000c4860144d03049070304482c3c07042e01d40c1c064040c3e1200280ad0a9000445202c81d040004400400301c01210381a081c0000441d100c030383c006000f801d4034900384c2c0d80310601e001c4090f01800220503143d44c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 808402131 1250 808400881 808400899
    0x435061618030503040504050c04050910061d090601030f0e07090e1e031903060e040506090c241e12070f02011512020d020a060509120d08041e0c0f05 66
    0x394460100525050b40d40120085090501d0982000701030310009182c50300d07041c010300000509813500104203008654580403802c0c0e2038100180244100b0301c20708403072000e0003540c221048644036400c0350382e085482883c01003401408070203504085c5c03800070940a464469850001600708041d401031681d002c242080d1040c02507100c01c01b0b8600d04c44502e4012854100300320703031241c0002c4614041f00e4922a802c0c007040b803aa403400d0341c0070102d1044405a0b01e0786c000300104503811000340102040c18100b210080c100c038101030070300e0707864208440280c00c15010010340c40c4040c2d541d46a041c5c640004502d1030640d16128403150a00500041e82c0400100e100c281144400764010700a01040b07190a0342c181210601d048c0b100c0c2040c20403000140c0e00809040110800340c0c4555003030300082c018a8668564400c8224140100001c50034000d0109401014000d244a60320580d40381d080382c0c00810840304c0207440107110303505501e000002040028400c000160300054031501400711a001c6600a41b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 808403381 1250 808402131 808402157
    0xd020c0f0301050106020d0c060e0304061d1806100512041a0f13020607061b050a020d0e03060a050718300b0f070c0503071407080304350616 62
    0x8240c3da000c0c0124000358105000c010310540c4126120200240a96004a02038060f0803140f41554019004031000075208950444251f41c8144141e28040d01170301c280c103c40e08810740401c1070070f201415880c0300d4650440b01d070704802d10480035a4014041000c81007010f04052414040140184401c000002c03c5000090141140788504502c02c9401d40f101130b240f00c10365401c0129130350051204482e910780da03a42555140042400c0783c40089003c0d11115601c42c1c040394084d261162405585c000c001d100d0300d040c030032030701c0c04105160444810580812280c03a407540c103035800c4842036402c02400050000000b070a201c0707000e0010b00b600d42c001c0f0090144c4072010b5013060000d2482000382c11030400f0004150300c4880c0c0c10203c1c3d404802d9140c02c1e610302e9090340d01c07070303055500c54030054a4120201c0010b011094003446038000a21180004524141c580410140c0400b00e11080c06100e658400300c182c1d2803a46940004440c2a409098441c030b8500350107040c04050014079550700084a00e4180350b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 808404631 1250 808403381 808403383
    0x3090105160c02100909020a030504020f0607030512130b04150f0203070f08090c060f2809090e1e0d090503010c0e09060d2f01090f0302060306030f0d020c0f03 70
    0xd071540400b5912200400c440783c00307000c0c007482040c1039a0108401c51200003140c040314409030806c26400d0f039000c92141001d004001d410062105240c0c4140010800c0e0b00020750010f0458080e6182214600001d9441075900340c1100c0e4441806001740100804000403c02c086128860305002a401004021451074000c0304a00048840901148101d4195008540a00d07000c1d80d0215540c01115101c7c88100d0201d940c507004000c8244c81c803100450102c20b10083c40d03020300f203c9410485440100041d10300c0c014038020b51849010580e41d558016140820402d21442114000d800c0c540c8441034404010b4558442010000e14001039100001148034039060180c01030880380c560f10035801d4200d900400c072051501603c0182c1c03140c214001c400014400c4000400c0c1e0741800c010b841a100218060005140c00c0640018100150318005008400c181c40040c015260161280ea450f0303598007010915154032800c0c01035051048220340d103040d960001d8142800082500c190201c507020714141 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 808405881 1250 808404631 808404661
    0x703051e0a020c071a0a030b10090302091003060212040201081b04171c02030c060f0910050a02160c0503121207230f0d0501080c010903030509010e041103090105 71
    0x240d004903024010900c1d21100d50058000391410304181c43c2003030741c0c0e05103030400344030321042e0350510210209407000145d0305441007860f442815100d2002c1d600c401c40c0001e0500045000c000e2141c0c110001203100703841c018040340040d5a100208541d902c00c4c0249050054404541c100c0c0001d502e04006480c480d128020381c0b5946242c440c00b641400d040c1040c0c40d01c0c02000b10450303c0c00340328250388142928240d58041c401315665030050f50340c441121a07554140200100510030007250360080c00101d403000140300c0241c103059000001c0c0f40d19100ba00e60042d10854105104401c01505481c0511416608060844030204c080303a5840307217400f01341041d0b030040090b5407908a4900000880c1180201901000500e050031240c0841400ca40070381d00e1038004100d149015140411100e4001404e4803885002d00103641c018004042c038000000c00710300305408000d0400c103012410585c0c9034001c0d800307101e1081006000740014191044140d006400441e039440300d0390700348408180c1c540340900e46 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 808407131 1250 808405881 808405921
    0xa050d08180a11010807170406090605060a0b0f0a0309021e03011a030312150d030e010e06181306080703030309510c1d0402091e0609030d08070305 65
    0xc1043d010000d5005450100004010205208400c1f01c0e15030342d20303404103103070303100310710500c400143c405a50812000300da03001000b0794028000c444003805010850410303602e0503181c8141e000e0b50b960440740220040c003d880d40080d00504508561000001200150b0300d824a09800803c501000141c802125400a41e031083d01074004001a007c480c0e5540003007540b0520340301040300e0145031031001c00d00c502e10210302030b0f0000d00ea0125510681d039004034013081c42c1c9000c43d0303003e06104080e420740004c45080d05055202d0141022028810641ca030004001488441c0680e1160340e43c0f410098054425498101c0c1c400b0403000102c2c6096200c030720702c0408406460042140070416856540c0d05080c0340c64200021000d14a158100903003134091003504040a607548541c42c84064440303445500003495483c8a40e005020b10720356a10b03801c04041c02105810000c0031091200d00c00f095640c0b26007135146405000303d8400412040d0000704290251895507000c12040d80c1d00200014041c40e07080e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 808408381 1250 808407131 808407143
    0x3110114071d041803050706150501050315040609181104140c0f070b130201260c1b0304030605010303260402040207050c1f09090e0303180a050d08180a 67
    0x2203000e00ea6000b285114220003000d030000a00120041004111030840401140002c10020b061010400c5500403000c402443c841d41d0010340d0308210018015000c010000aa425412001a016627031250000001007099200402000d80e4580042015403043e542c240c42204c00000f40e00100d081a2107034846125505080d00415150100340c01480e901c10090201e04020510414010860550140e0b014580c15408501d100c907181c40054800b0100340a000d40440b02c01030f0400180d0121b0090380d6101007131454030303540c62168144641980318002000f00c80351201003004001c009695000a058078001d03101c80201b402078840d800800c2c2c1051040c031512545103804a001806c00e6001f8050840c030910a4070301c00740b120340106461707030000e07003134031443e40c5803442008102c640001a03e40900801c050601c0850f034181d54055691001800d880000d00042400c07a074404030602064014652207406d680d0f941820071001422480b040d02d00300c100c02e8020f40035003d0528000356540503264011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 808409631 1250 808408381 808408397
    0x100e10050132031e0405150601020307170301050f121209061b0606010e04060f050f120303070503090706090305100518030406031a04200a090f030311011407 69
    0x2800445480c4080d0115500407450700003004816102c003030714510a4441c1004140e01c0b0301d491400c05015900c0f40a007141201e0008003440040740c40414100e0030045010403140040d100c00c0d004074554070961402030a445680c20a08554480540041d812241c040300d1006c4110702d04e0f01080001d0b00d210400c03080e031f6804040c3c034009000f80722010f4005040020401410589120380f01c60300b6865105041e555900100c2c20804650380010882da0f0701042030b68104001402d00030002000503090245520a0440700410b54131541d941c41003400201e2241c040da41c90741001038018225402c00e880701c01c424001c1c0c8402080c0300384100d01d0360040302e421800805212001085560040c040544000d1203031404c800c40c01030440042008000070101654006032810101d8a88100485800c3c0c896200302c0c1808080700d4481c0019150b59141c0c00c501542d180e880f982094162018107441c1c0c400c225442d0200400006e064200510042811040000740f000c4a04000210a5001c0c12106100810544 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 808410881 1250 808409631 808409639
    0x240c1c021f1a0414061003050c070b130210180608070512093408010c09030209070c0c030c0503010c031e020a12020d0501151106040303090f0f0605100e10 68
    0x1e90000035100003500c20440c005103420003c00c069a4008072000000180c000a0100e6410b0000941880c0d05c03540c502084642450760140150b071103103200c00b8080d0304814006c6000203025401e400c1920713900802032048805151006803101411800001c222040c4c0071000400380e000d082101e11400303031075552500d09069a58900852440603107468180d01c40c1d96801200b50100440c000c02d04c08030341500c40e42d005200504120114100d03045504680d0401400004030768201801c0c00503260304031000306155035242d600315450360a054000c2c10748c0c0151070000060141102c028025154140c009002c092115a81581641e9114610000c645210f26030303c0c0200c180c42c1d01a1600c2c0b0b566140062840907003110150507a0032810080100715030310001040328040d0843d0951170004682003000c4296120101262601030050000c3d090688507080007040040250000140f180e0048602031515418280340b0b00518080300c0c4070b020f05010000c003290041140b80760b01d20464024000c0781010f0b041c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 808412131 1250 808410881 808410943
    0x19050408030f04030e04090c1703070203030306010c2d030e0103180206130305030c06160c03050901081003140a0519020d120e0303030c18091302240c1c02 68
    0xf0001c1d02042a04541c66000d82e589024050b1264000d40b40d44001608014001018445000b003001d1306030300400191005803400b006580e40308600b420701030070030061800c1091041350882c03094a0a500c0c00c035020359281d4120042c0d0415103010b40d81e0302c8105080200150100c50760940702c2d00700441c403095441c0c01407500034004c0144e07804000d13030505000c0d038039078860740b6640140302d07c0c03070541e046201004002d8180c07441e002020303100c503d040d000005140d24094030b00d101c0c2804031410400820000b508510510400300300666000200e44410b4030812482511448070400c200c03081c0c01a40b192001210307040e5216503201d40c00030715607032409a0382c0d0307980d44034001002901c001b80981995885060780d030074005507129264042034150340d003810080d024401203e07100698410200401400f5490300c014140c1c04900e030781a04d4014000c12910314041c121110009444260080040c01e02c41c9004041070304400e61050440b114040307440c1d0a01642c0f248100e4100a141e100c0c015554400810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 808413381 1250 808412131 808412161
    0x110d08190504140106031a1303080112030203040b040b030f090d0906030e160e0108061605250204020f04030501050105061603051b07032102010510060c08040b040e1905040803 77
    0x48070303c0c92007680b1128071440302d00351070443c1c1c4190b80070b003459285610102d04004a0300c3d408100000312140d11085568003070030030001030142400c0c2005401c103d2040600070421900502111a2143c0c3c03625580e800030311040c0d100715041204100003c01181031003400149441550400d0b44600c0d80140c286001100103018505e2600401d100b0100c0454003842c8900064000e40180c608009140d0b042042705480e245000d0011039410007540800a40f00c2e03032220070f50b041c00189104800000b0303d00f400101c0f0ba1459100c011b940240b0014a8003490b0221400074811248210001e210585e45c07442004100d004680711a6440180402c0140c0000c3c425002400d4084e004c50705010002c24140a50340380609941044901040e072a203500c4035166030320b1599640906520080c00185840700340504014603511800d400c0c0310310000c0840420189005540c0501520119a6144c1c0c1d5101a10754503101e0a41e825030855102c500407005120b0a8001c451040385c002d19041e1a5031104075440b40011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 808414631 1250 808413381 808413383
    0xc020c0306071d040f050f101d0702010f2c03090a0311030a050601060e01270611070e16030507180b090a080303070903060e0c031b01030b030d110d08190504 69
    0x2c00400440c10550703134911517411840ca100c040026189050b4100d020380000244c02da01404905c94403c0010141042440c07881d484082c2000c120364030f8401099000d41001c481c40003100742001c3c445030786900165021000391010940384d04c40d1400102c41c0986a11400300860341000700c0c0c460a01c00701d0b40c1800c0d4007141c13520180880e440039203291107080c14074a00780c00c030340001003810301110315035a88002842480310101074803c0c54000c0558a440d01c84a9038401d100a11251400d040c101c3c0d403040c004400284801d40040300c080c074000d43d01220001d4840d0000003c00c1c42e02001c50013541c4114400070054171000c0094010a0428184103019000469031b00e90240c142000802c5c03000341880594040c4620382c42da80805803c40c5020000d0f154030b2640b600340740d84003115541541c1e0700003030000c07034203001074940c0d8801e9013090300121b003c2c21020030b40c180c141c8261107101c0790559108030055445100c0074152140108050300c100c5d03840c201522154410068000c4809400700d89038000c940103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 808415881 1250 808414631 808414667
    0x9090509030403051510050f1309060e0a051f060b0a051c110712020c0f13150e15030a11060c010920213415030c020c030607 55
    0x30f03a2a030b903480c0f41101c045c16418a8002c010240000311044661041c00b802045a003642500303800d00104000c03d01c18400110340340c1d02d800c3c0d03003028841c80f41c0c0b041211340142d0043d54001e211904040f0781d900c034030021401048010014842c1106c42d90b00c0f4100640743c803c6821840c22030403a1088845400c40c05d204d5032003010a201c400c010548074030a8614403848070042580795141418846a90680b603410748007950401c4070070003c1d40d036600810004c0e810003166a4860550220b070f41034010a411034020144031014134010800c2c2c113a111400d8420381d4001c84284258440c83c084c50b403105c41c9540b0050544008501c201d21a281c004041e1564081c1c4c18000104007103070b42c5900e411078105800740c010000d0110911030b041c0c208071f00c04414a0b2804880086084a206606580d43c0c181c3c807558134001100e0b061118501d000041c4030f4140d50a8a0170001010340c4441c0d103840366643c4c45600341c01182c03803d030b03110840c41d0001c02c1d040c6500d10001c01034452660385607030a6030a112000e03880854 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 808417131 1250 808415881 808415887
    0x10917010f020d0506010f0e0906040e0102070b0408131401080c071119050111071206020c0f1002120f0f01030b0619030803010614041206020a050c06090109030e100909050903 77
    0x5210303500c007803c0031003142d400102e40d40c14140000350440803080c0c500c40400281106032070303a9440d51550181c11000941e0b0001c0e50540018419009014083c0020000d02c4504c081c0801d100810029052602c0c010070541882c3e60380366041c3d214200540b01c0c13540440e83c2c0e00001810664020090700d04a40500c0c4107141140a41d4001010501640076001e9220b0b02c5100500c02c950b4050040d15120604000501c20941004091210b91407481c030002c00d0b482c1c00040c0581c14032820b00c030400c0007103802e90440e100d03481006104e1003e9040303e41861140e03603699000801a02c171443d0040e0044e5401114100c581e4210340300d90003a4403009060b103400c41014414110490205020720004500961090340c8030f50510000038151005604000d901c1d9500740801e02201201490304c01e04c056000d00010f030784001495003690180a05805c5405600802d002c0000010b8190030681c4904d110303035a00b4812910000400408851460f42c81c4005050604244a00c0b0300d19071006412601000480781 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 808418381 1250 808417131 808417151
    0x5061b07020d1b08160b0a1e0809010f02030f070c0302071203050c01111306080a060909120905030610030b04021c1202060a0b0f040903111207051204030201091701 72
    0x10b8015045044032800560461140200100c0c8003100141034900040c02c0d60406500a81513503501500856080780c0340024455452806403041c1ca40c2190b81100014031200d9100c0082c11180003214500083d50070f005020f2109841e80c42101e126220117040c03042c1a03180da600c200c0e07200d03500100407015441880c8000c20024021111800240e21039a900c603640d01d8030703104207130039544014044039040c0c200703124a202d1401c002c54043c0a5540c0d901c4d01e102145d452000050140c00340d40c1c0030690991425080c0400e1200024540402081c40d448000c0c246558005140d5070340780071503220b07091212403081400003620042c0f007150441e00007403004041c042c00751007500700c841d00554200d0300d409000c4042d048a540500c105540f00c20030240c20003108000c1c0d0003258010b42081c96140c0300d20b5a440f2640c0c02c16000e4001142000a813204480e030340e28006502d25240c1d405010140c176580314284d134403120320003800102c1341642d5040e55400350141c0307802c0c03000102004031010340300155283d0340015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 808419631 1250 808418381 808418389
    0x304060f060b0423040b0913060b041a0f090103210c0b0a020915070b04122001200f1815130617041212020403020d200303040305061b0702 61
    0x710103007100000901131008440b003080280ea00c00c9003914012410007652500e5a55808445940720404082c50310b148207040c5401c8c40102940c0e04c030030742d10601d000703505242d42401005041e400e500986001070f901d400d103c00c1001c802d03001d1100601d500c810301021400181c150300705083d468054200004c2c030b041140c0d5426501c6a00300d404010f8117030301003600b400318603003d55440c0d25100060951840c000ea07540b1504c040f03480040c009890302c070034801d0751810144102035102d9860310b84004074582a50b003407503031401703032070070140b191901280d10318031400c6200e000048503075400701d068216142c101508030001c60409020151640721028450060701004060001c00c0920401202482e4190400714040d00003c5030320043d0b040f0031800020003001860500c0c45180803822820003004444c1c48020000180c42a80c20081d0800c0120b41944104010800c6260036040c0e51131027041d60400b000c1c01d1594a0089100c0940150f1180012400354202c00d0340705c003842c109040103140f401c0c0040d0089 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 808420881 1250 808419631 808419637
    0x90709020f04090216050d0903051005061c0b0f092b050f0c07061706010518190b04050a092306010c060603050c030d0e0312030910060e04050c0d080304060f060b 71
    0x10105100b4003c5c200002c006060044200f002c44a0401c421090701796142c5c07075682d0a901030510794007a43d91001c590b0360b035518440041e20a1000da03035030780381e00014a01151400001d44140d10f141e8001000f1441410020545406580000214025a4140740c4d0704441c44040d08440d8400c0c86803c111000018504600809074017011000400320203140000003803080010102101e1402c25940c1400740307586c0e0101c101c6008828000c008240b150716100003c00800480095031040740c42d1000015044070340d50090802c4400495032880c1e4580d4464001c800c1d1403008524a4810000c0a00c1c1540400c134620304a42120741850907034010700d072941d14502110380d260000e40305a03009821039551480c003048840034501c42c514004124030501c0b00400d5640100250540c1d14050100001c2d0f8801020444910201c1e80d480381404502d94604074440508002c3d41d0a4440d0301500d0210099420100071040800d40d012580b2413039650790703403541c2009020380c0042c48845900c0307040010308010100d001d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 808422131 1250 808420881 808420897
    0xc0a06230c06040c15021203060409020411160308060603010b0319020906040b19031b031a06030703061a03090c1c0606030809010e0a05090a09052b120203090709020f040902 76
    0x405650141800f017038000b42901d1100300d10071984030007401e902401500d41900d030001002d45010403120070920018014244000c140c0340042808121096000c18442c948004540640c03151007171034449005101886c4000d00920310805020000700303042070301c02801064004002c120060800303515200086e4203a200d51703c001601c2c00c01040d400307042d4249008000c4c40080d941402c00c070b00c0d17203202104002418101320a0080c0760381c0b400d0312240d024204c2c02d8564202401441503590b413610b00000b40c01003140c2e00840c10307114808c40040114454400c11240104900c00050840d041d4a504222000c2450f12502e41d0303507124a2840c4001618501032003000d148105034283d21004407a0005007072021000c1000d03c500b004043c03c010300c0d2a200703141e5400c8540c6c0340c40441c0e18042410010b20f040b02442c0d9500481c54210303008813440d20500d108410703003c010750303c05500300c80d02c041c0282a40810ba072100333020b03002498100b00c00d421507801071071000d10380c000003801c26a43d0261503007280c00604c6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 808423381 1250 808422131 808422143
    0x160f080309030a0f0c0309090c1205160f14090405040c03050d08010503062802160b0a0203221e0321021e040803070f0c1a07050c0a06230c0604 63
    0x51020140d6085100c048800c6020b05e08043e140200d514014121a124451401440d03524404989041e11405d09111001d000c00c105101a00307103903042400604800203c100080c2c0041c1800e48064894241c14500791540410b80b420700e490001003100038100900b0803550040650b40000000c0d400b4000200240419199000710b0b61421007494100307800100f00e00c4015500030b50410340a101d00412001d04207e5400040e15820303511010001c441040301d01511102c00c400800c00e0072001900110b2040e013081004034411480301d5810f80d07a80244003002840080d07446404420310f016170032459620741c001e03d0000a980c40d0a00d40608003003848619112143e000034101100391042418522990300682d44a07191502e80340c040b646a004600006212028100e02d02c4144049070094038082c00c0f1003d1040700c0307803400749072000e0b51364032000040340e1600860380400c00764940200900c088030710b00d8031030000b800707000c6081066a003048109814080700c18050b4420781c480030018248114883e035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 808424631 1250 808423381 808423387
    0x506060306010b0c1b0616080c2e2003010f08070f03030801230913030e191404021b06090609060106090501050f0702040f051e010506160f08030903 65
    0x2109050400741d05800c50403a080042100506041000030f204503a04030004504035410302c1240010b02034030a06408852003841c3c00507410a10520500401c07200d0302c400c084a01d0000362807500e88102148030b26111800c800381c0c1c1200d8101d59150000040c1c0818809004506001c3c543d920102e500281c200c07411128000005002c0600100701e5200589003100c1c82c41c03a0346182d44e8001700b0034035050046410100c803040d02c2448a54601d0312054165000604000c45803910030010100810061001d0380018803400060200341071501c090b565a520340100b503802c46080030556115101c040c20001d401507800c0244003180403480c0c0d00d680c10070440c0c20203070845090010260f490f00c80c0c00f902629160f007000004104d0690415101002c5a6003824140d07202c48480c0800300490040e51000307908103080403003d401403012540001d210781d030b07000c2080200c40303480780100d101c480003400f62075040309081041c1141c079500440f0072540140704031a4041201e103903075078103d003c0e0000c0d11007007096072001c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 808425881 1250 808424631 808424641
    0x20414040c1508040209130c08010c02030a140c100b01110a200a0f050d02060f2803060803040509090703050d030c020d0309020f100216030f1a0f1609030f0506 70
    0xa190341804100e8a443c283c0514203080d00015a15800038020301c1c184a21340640c00100000c80941d04000c1c20004002c2003158040e5201949a44c020302c0e0340382c002000001d841080f0328148042d15050140c1030014000503607c0f05c4c4100052440c0d2282c1c0c2c0c1400204014a00201c80030070640c40c0c030f148220308001805c80e034010703501860b03945050030364803a50700343c07005201a106054020088407c00c0300c01c0740e0300c3d00080c004a2043c0c03180760705540700000c001812a2603aa0440310f0380d407412694150101d44e84420203011804c40c0c02c1e90080000c5070b041040200203a00c0d00d85120303a0002500c00035141201e42e84d0307076103620704040b13a45804046a00d507849070300e14a8040c4140781d00d1000e5400c0500095656034000340c0c404001107011032107140a14401d81100d4405c0116030341a12480ca440c0001035164101007080d0801039a007101c0c0c4001c020541d0710300c0444040418011160301600a00f80d0701c6040c29001d048900d01d44150030400248400004100c043c024070745020300850141c000f074244 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 808427131 1250 808425881 808425899
    0x9030109030c17040b160813080a030206090f030a0809010f02030108071e0e0601030c122d0c0203090d05100606050c10060312180e270622020414040c 66
    0x24400090a260428001000811201000c032541400d02d001c0300c4803016210f1a000946008010032480401107500c004500c003540000c0c280ae020f40240c00310b03a800e5035900f00392a034403039641c3c41c00ac41d10380040c004808114020000503400c60400d60021070600c8206c01c0c04d100720f80007640109000c0d4441d01c0108202d0000c3c01c0500c84001f0744601500d101410f20000c6180001c0140c0744504059640b481c0400d4948a03a92107002d400140c0c1e03081c00301d8000800054160802100c2c0d600a1002029241041c03101501c42d140e00d4101c44d0b00551b050100344000c008002050300001d80c1c0034001c40c1102400e00051380b0940f000f92100e0b0300d40a0310740c5000031007a494012210b1a80c80420314008080c0046031290b910442015a18601030000c0300034400444013110455004c44283c0d00c04905000380c4c0140489038008100b14501c910000692040030180e0302e0409035080400c24055582c11605138800709614481c8600142021442c0d045102502c202e01c1c40072601070344c02d582011818040328030703 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 808428381 1250 808427131 808427153
    0xa080903091507080702030a030306081018020d030c1b15050a020717030903070924030309060f05121e0a02090109090906060506130501171608060609030109030c 71
    0x108510095050030700090124441d0b003100c0c1521010035401141010400c65850100d0f40450307800780c155000d0289038a005005081d05001d01d00c13040c0181c008001190606114080c51108800841c0000800716024040e05039080002601001024003151021440d280220200030310f0600f90040101d141644165a540651820310700b0050100000044c0a6000405200b91035580307114000080c0b5a0076010b01d588101c40810390540a84400002c1420890740130b0307612520700241003406403865024190b80b01d0294080100860405079043c030980788039854032614820310381800c900c0c005003d00c3c2d009048000300c5140c2042d40c01110108004921500c10070340040c14500103505190a80c000680800301d02c3c0101c10030036a66040003c1030240641104009090150083c0d5031528000c4841001e0021030040030f010401a00781e101c2d0719425424440d204849451404010301c15842044540c0c22000d40a943c0c810340602400c80d2994080c070030120610f00c03a466801c0c0c0400140380030001d0907 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 808429631 1250 808428381 808428391
    0x1805090903030609252309030607110304030606290c0307021318080301090b0d020f0d1109180708300d050f01170f0d030c0e040c050a08 60
    0x44040800e10540aa0000589811003012a4000004e80d10b048501105007084150820034100d054117203182550007003030400d20314802816880025610f9181040c0c0c521420810a070541e10000000390792a100d210340705000113118094a140c6942d9407100740583c1c020390015194420020040c10182004044c00e030420400046603508040300c1a512507200d0062250203800b5074002090103203940c1c40c03030344038039010003180c0000050b070b109605114a480d0030034080c0321840d03850302c0140000e40c0741000c040100c5680c01460880f0441800041c45a26203d070081103030b110540004854890392001c0040f17100f06200c45262918981505a42c0c1c50500160700811860304035950b03148e48099407105940d4032021840005103464510b00d855a854401d0600c2442d6052078a001c2c40090080d1400c0141242c0311440145105803400280d10307200c4003440c61982250340051580d0500c0350182d003100c038644001c1e0034480285805400030400742c8900082400020300c0004801c42400c0d0031840c225004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 808430881 1250 808429631 808429639
    0x10051309020c0c04050f0115091508010611010908090f04021201091505120703081c02030702010b0906030c011d0d02040905010608160f0e100305010e060a11090d1e0c061805 76
    0x60300300016141c0c1c103801e06005c8e04e008420902521a28640540307126002040009510061081148002001d14800303000f04800202000c110061440f01401103484a13030b042084c0a01c1e15444400b0004000f88110150303410030740a02c841011940801d0804d4000d010441001c02c11545504001d01b140e01d207030700414410360030300c440c56500390303000034494040d6907100044030340e076640c800703030554580c0801009260528000000c0050003039042d00700c0103050304192515070868441800701502c0c0d9030000f00c241d00040b80360141c030081100c0005a0390358224050801c81d2031144e01e0f0045010f8a140c8e00e010388003691580c00c2000002c0c070420451440c3c08480119000b841c1c04c081070000210308a118040074400c0c201d0200d00f51a9030b2820f084010b588c484002c1018841c031410058864404a41d0b80b401c82c0c1c0f8105020588050100031261000d40081c40040c100040e0344e240c07030381001c1c40c0442e240078100d440c64070000034510f0803480e009400e6607150110119030b501c5200c014800660000e9000d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 808432131 1250 808430881 808430891
    0xa030506090a2906060904060503061e07050a080a0f020c0d030e0606040504030f0e03010b060a11061005180a0b0909070801060506070309150c051b0103051e01030210051309020c0c04 80
    0x4507240c00c120607004001105d40b01c0c0e80704503240006024001541100c0e038140581c03014048144040e030b000d0904048001c030f205516546034402602c5e14011410310700081000040011008840fa500c4000240000340d030060402e48040e01c1689000b2451202c00c001c2541c0d458000c883c2c075010040a0340c001d904403802e0110b0301d044d80d00100340400002d00041400982c80940321640d8003034000310301c01c40c005006113485410740f0344014802d281d04130700c0301c60502504000c201040088040b0f0000d4400c007804080e40c03c00b280006401c0e00030000c001c00c200c595101121070381d59a41086070760003100440014500300342814101c41c00c4032019405907228041c02c0010000103500800640c040300d490030703c14403040c007420800b5151894804002003250041600325544038a0700e007032075000501c003a40e08011a80c0c4030512050200c5101400e598035900b0b00d40100018603140e030311580050320f0341c54210f080008442108010200641050b03141e41c1d00071503010000e070020000d20803011812101444 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 808433381 1250 808432131 808432193
    0x20708120a1706031519020a08190b03120a140403030519170115030207050d080a11030c030c0a020703060f0506090f04020a03060b0114130329150a030506090a 70
    0x951025840c1c2c4014030740c01c080002482c600351b8403078060526241c1440c190355601030b4000060000404658920003e070302c0340100108003890340300b0018480400303001826000b06031074161449030441c0a02c8030401403080c000411090000025100451103a203e0540760396801260401111502c8a0202000750f01c103c2c00d81c6201080404604403007401609090b50714903040c0c200c000e4407030000301810074411500d860b0342c0b440c2e11a101c02e100b00b03881c000400c0700074014900c5030303100c1c4020388070f25181420600c0030940060a100c0107000149160040750112581c96071900265010a510344200c00c0d074600411205080400b51298810f0402000b0000f925056002495402580c040903203007580d00c02e06d0b80c0117030f4040c1c1e07060781c3c1d54850501400d0300d8010443d050070541c1d803240000c40382410018080e0041009241c480c21240081074460306841e507030402d0042245112170a42070b40074030904000000726600f88074540c0200c04940280080722494284080704c0552802054007075180138200344 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 808434631 1250 808433381 808433383
    0x606090d1a0403091a0904020d09060c080609101410020a0f030201020403050d0e0d140705130b1e09150303070b180d11030d0b180c1908100302010f020708120a170603 73
    0x1c011006c00c450040e2a400c1120420008000c4401d006250600d022100d11507550480c405522030f2030120703400a015920350004203400314142c03250350140c11201d4440b10141c030340a19010303032000107441114040d11080e1110b84032021a000280d0150354005030610a008003880003141c62122400c002581000000108110036810030018240e0445060520f05045081c01000020400100304401c4800d000c0d85140085c4022048584540c0001c541c0c81944901c41980008200e40140f5180729540c40022100400c0e4054980c998580400c214000001c4c0d58051024010000c0e039441c6070303040070010341c010b282080c0c08000342d080c4502800e22401c251781c00000c03202c0061000f00c5c046003091801010505034004080d50000984482042104010039400541002042c540e440324650140007010b50b80110159140708001405990600255005100b400a0503120344125004103580e24996802c04425030065a04084000750300020700d540002e5a02c01091070700c10028550a14000003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 808435881 1250 808434631 808434637
    0x70e0723041502011418100b0a0b03040503040e0a06170f0601060e030c100c0c0909020f0432011e180518061e011d0606090d1a0403091a 60
    0x342d940d10b004840741540a40c400c1d08000c4402c3c500d000113528500b0080e0900754a129020901002c4d1b2041000110701d1540c50b02a0002901c4090100b012a40c14901c5d000312542c002802611544810000080d81c070240c0d21845101c0c0c0e22215001a007181026001800c1002000903030425502240d400d820701000400e5850445510341071641c5451812000f1a09009040903601e41c0010a42c461075601c0c0c0c0c000c41d5450340d85100751529a001615028072004456580e040a90444078481e10305030141030a50200c900c0c0d0382c02203410742507600c40340c010701802007010b80310011046600c4010040c4006000c0c500d181041c0540150b01030500b09212009079480200e04850007580310b1b404a12440080c0040000e00001d19040c1c03540c40c5400031508c1a050941e207011142c4c02c1d203d0b000014403020801140340454612078840c0c000340c640c04200704254112106c003546c002900200400001d0100305018841d0715240c140e0035091925090190164040d60b010040220410780390a40c101800700032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 808437131 1250 808435881 808435889
    0xa0803040b0319231b040315050708010617192a0e091501050c060406062103021f0b03010e3307050d021c0b0a150f030e0f070e072304 59
    0x100703071595850101c42d1072404510310b900c40c885e0000080102c10b0103c901c03081da901688581041c84580c480620881c0c24020034401e003400101c203004180c0c458007142c0c0440e5000003244101c91211400f001030039040ba003001c0703040c2035086000340b4506002168080f1001c0602d1179410880307000c40008001c44c092010041005c40c4641100c00312010b00e07809042a03035079600906048442034034207032078440000d00660046030300e69407881c031914101c040308502e841c070b400754164003504900b00101081030002e01d24070914480c803900c800154803151400d110350a4060100c2c070041a02043d21035641900003480421102c0f0709024005a84075a00d00b08a099004070180c03504503550000f8511810090041b401c44404884103c0144e0f03040c0c2946030001c1100c41c02c11114111820380d100100c07580c036058030040101280440c0d031382c0e200b0180240d01c4080000c0e100c50549500795100c0742c0c0b040c207002980d0000005d000c81c01c02442085a40030307071026030812188400910081109002c50040d0042d842 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 808438381 1250 808437131 808437191
    0x111160e0a020c01050903040e0112020d030f03061e052b020d030c02040c03090308060d0b060d050709090606030c0f06050306061c090b01050315010f05040b0a0803040b0319 76
    0x10030700762482507040f51580c0c01c20000811446c18602e602a469a20621a801c2500340c000008100f802e0703105058000e4035802840303c0c0841084e40d03429a00d5000d914028030505640d10320002d45401044d0244518946142e0180c0342281032008001c6c8124415914030340352110b15192490b0340798540004903021b9012610041c3c040640e00e02102c03d010140d00081d04141000f481142c115003503000410140e00c86c3d00c840d4015500c05040c4181c04048040140441980300c0114485041c05880701c000d1900940a4504990301c4000034015200e081d501150380f20b07552001003051200b0042030401a010b00c1f0b0401e03000c01c0c0740c100d0040582c000a443c0c24841c00d000665000511a040413211015680c02002d003c080390a050143d0440002d00c600c900078050b02d2403400e0075103594503445040c2d414091403000b0081c282000e020042a04104540e00f00ca1602400714444a08001400c003d1031018a407135540c1c03504a030f03480240e849603039251060347d04104d07030914900d0f4850440880f2210030a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 808439631 1250 808438381 808438409
    0x1203020705070f0b03041101050a020622210201061d06010806130c09140f03060c16080408010603050106050609090402190510050d14060d060c0909020408010b011116 73
    0x401d000d42000351691100b40c00200d405800200d0130310850255201d60701419020f03c004600000540300c5204003a40400160002e10015a104850f529200390700e0050350540b0801e18001c2d51000a01e5803a001d552102260304402d20700351540c24080c150280003003034007181d08131826151401500d03002a08150500c0000c9000070000e0b107540403010311004910720b00b4003003144050806444407016003e40c60f0361107407060401246090130f481350702c01424091f00800c3c1c40e0343c45842c0101075030000d00c0f0031007038036043c040c2c00f00c0803c41c120090400762214100004003585075107495030840d10a54052401242d080c4018a001d42d2440019a07106805440401e405445401d211004a074142c0042d507001194100c10800c8a5201c00034001481c0a4a42001490344610010070083c5003100c407960f000d408a03080c0c4c40043c40940002d0010b44003400c080310350036203402c5540c041c0d81040c0c100104980d9500000303200c542c0d00016000903401c032040900040d048c5600d103244080d45078045c13146120000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 808440881 1250 808439631 808439633
    0x10f0611061603150b1201060e1008090c181f06090501180b0a03020d0b310608070303050324010e010c0809030703140609011406090a09053712030207 66
    0x181c2c0001541103136030840c01c041242c80e402401143d400603401c0e85489118000046001c07401803d104006120003040c030001e242c142e81c01196022070081500b030160041d8211010981c40352558203a030740504007602d4280345401c0445204150400010f20000089100c0c10403090b07421407242d0080d40c0c0207280c850302a5600340c045d0382e06a0300c81c2e032001d20301c1c400014400a50a9065014140c5410505014004c10a410007001240f5400854122000c0c3d82c1124603590b000800c000410701c0707941d08001107041a034038240a41040719960050300030410002c1001014a442c101000d038001c0d44070034103810262008002041c03800c2003074400e81402040f1400e8000d0000003029100a0440201220715a0b9140c1ca450b42d0034980d01c0741c00c0b10540c1300d1080418420ba6042c0142641e010414051034129520b081c1040344203040905139801c9255034848110101d01c007407011708000810041207120743d03050900750030300b003110391404028071100702c1181d10000ba0542e110f4085941451a0140c0c0303034261 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 808442131 1250 808440881 808440887
    0x70602210712111216020d021501050d1a090303040303140f0403230d09030905061207050310080109060507080a09030905060c031303051b06040b030423010212010f06110616 76
    0x82c1480e03040b850915002005880170800c10056030758116603094070810200b5800590383e610040c810000480d00c0c580c01407042d418076610803c0a180503070407111500c4800780440034070074003d841100468100004100074550180202c03400c809006805d42c8246c80c00001c45500f04034064030090412000d1400b070291021003480116044044180055680401002400041607105401c40c08502c541c20000f0f11792900a0650315640c0403013403a202c56907270b030741001c40d09544028140c0c0001c5400f881d010074515024070800445901c60701c2d00061380c6c01c03c42c1024041c0340c030041c800e2031914140342003800080e510035484000c5510540d84644c4421380d183c1254114001e1420750140041401d81c00007d02000040485401c0556200030400110000900c0786500c110700599103a17078000c0020400181c1c02d1811885115011010804018103247e00c4074213907404040801d00c95811355005019540e140f10161004016504041c02c2da40c80d00c3d5170080d11130790003c1c080b00f0700003410100100e80c540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 808443381 1250 808442131 808442137
    0x3010b07030e040b1306360b040f060603020703090b091c0c0e090a17130315060509130605090105010828020a0617061203090d061107060221071211 65
    0x540100103090850070f01c4d100d80006c21a511466221840d0084400d120242640410400940c1c1c4c2401808441e0350824080240141103d40360b0401d41d00c10040180c2046031240c030300a00b040b0343d00075a807070140d03040046c41c0c5c90858100160060041001d11074070f6650094400c2d0700c1f4502c0064481480d110b040075003a01110358010808040c4d03020410060510103d0140740e06072080790407a1001a0300040f02c1d4013405011203115000510440c18400b05044508001c2c1c500080340002c1002510744002c134110140598651060800d410b001104006090080c83d900c20b8541c0f000700900d6140c124015941c0c6420540c00014102c4c800c940e41c0c8002c02e40c00e10203512038000d0000c2140e6540c1d048000c001105640c0c100b5001c0c400703000800c0702481c01c282e480e85070341487c000a42c188844081007022004040380121001039840c0040320f407406d03512010f0802c0f03900076200180c40d004c0c04600b1001114011100c0f100281544007007003006904031111a4a80d070720f501c00022442d0743c0001ca040700b0b00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 808444631 1250 808443381 808443401
    0x322080307080406021009030905060d1e02190c0803070c080c010203040312141003080a11011a10181e0518060a05010207052b02180411010503010b07030e04 69
    0x1000c0010290240000c0c50000e004541e16a401ca4002c40c0e0740710007000c1207600140008001528400d400c0007a89003001c043d014860302c0c5100003440741d138540d03090310640780c071056100c43d5103030042103904404269044004190f03400d401c00303042401c0b60ba5503419030352000520b140d0512190309070b04170130301000070b01f900c1c0302d0302052001310340e2403c15040c05448003690700c04c050a8030b030602052000040f070000140d8003400c00216070148280c01c1d43c0c2c4000880d00014015010040c03c40240c21510009010b154102401c03910003440f8849018240550070300580d00400070f010000018900b0076074003420303040446050814031b50f601402c21001c141c00c42a5a4072042d8403080c69006070b0f1440788828165401280c0494000c01410350b0351005a07259285403081546c44000020018040d03041484600d100e5a4402e8045060218560025039001c0103211008450300f00b940801040100031240642c001009080c2282158035021010081e4415103000a041221444400300552201d402c800c4440c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 808445881 1250 808444631 808444633
    0xb10110606240f071709010507030c022b02120d090b0a141b06060906060703030b1f080405010b04060b04031b091e0b04020a0806011404030b04080a0e040e032208 71
    0x14100301c182d02c0f6440e070042c09080d12000f142c40401070840034a4800c0b2034101c00d040c3c40300f90512450b40c6054504404d008030682c3c01003120320302c0c1c8420a00602c00030000c0614101c0d0381030311215900500600c10012100400c480c1d0050036503203a401e81010f41ca404403101d58191a554020840d82118040038006261a11034804141e00b1814032505984005d01c542203000c840c0c0c9540e0314030810007014402d450098000c18208400004244a50032501c41d820014041e54001d108410940950038104842c100001d04000c0c244000c000f400e024140365a00300f150184204d80c20240b201da454840c1d44401020107950001c0c0540c016880c5401c5401810003e208005c0c600000784a0004d421904507408a20ba2810394842000d20307007442580c8007615182d442c8001c590f10400190f4520340640140340c0049400d2000000244441b4a114400d6100d072944076150210044091b00c50b4460807001c0344501d040452000c000003000050380d40400f4118034911000601400032401e00195400003215 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 808447131 1250 808445881 808445887
    0xb0f0108220c2d03081b0f060c0304020108010e0906070c032001061409010308070605040c0b030405010b04052d0703061205070f0e161d030604060b1011060624 70
    0x201120042046826040c424000e255555800002040d0f803110b400700502e40710050050354281c64100280f54071080200045500020701414170350314084c4100c0361130355034003c00000c01003196803012281d0700409502c040c031220343c01c20070354040c0c03140801400c0d20200826680e240e814544110036100e1890550039141d2806036041410902900590054013000314118400720864100038066a0407240c01c400910301300f4030305549a6016110192083e900248940e0010858141c2000154000c80c0316000000ba001005400c0c0001d880e00281310100c002c440c081400c1c080d0240700000b10080f43c4188689140341c2c0c1c0d049055004106640148041041110f42ca0041290008d0190f00355154160f0b80c4c10391b10740e1aa407001c2052012207100740d025081c1d5040070042401003a00e10741905000d00c4005000e43e07454042403070600b04450070740c0d0b81600e44031010840c1c20a401034200744100351030550124500100307601c4d50380c0005040d4a0107114400003400400031704400120074040319006850f0303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 808448381 1250 808447131 808447139
    0x405010e04020919080d021501140402070b130b010f0b0306091f03080c0111070203030a12020d0e010510060201180f050f0d180605070c030602030406060807090f0b0f0108220c 77
    0x500c4441302c0c05505c0041c46901043c8400c5070000550100c0c81030100b070048a581e0a00e4203255151002420107a0001d409000050000e038900f0310040c070684418540c849020b04034180b4528001043e4040e1805203203060301800070241040440b58440c1080d111145942c840b02d09020012180d10220204801001e9000c0100130783c40009100c1c075400c0000038443c40003019031b018680d00c01d03404002d41c59030042180c00a4580a51410000218240c0006041580844803001680c1e03480c48100e034565581c0f010880d03801c000265044c040c2c4100c0c03000300005220314010b103503015a51480680622105540b0800b001000c000740f040d00b40300034054420708550620040c141a08a82040b015642c84e40c03c00303c0c001d48104190744c15241c010584040192840d00d0340c000070350000c3c00903500c658441c00d012498001c10404540104440400040c22042038402c0c10111a00d40480920804007203070105208c2c0e07841110180c01520540b103070502082c091a26110441011100411121800d9000a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 808449631 1250 808448381 808448419
    0x506032a03071502070509040c090510030b100b0d0b062809060f1d030307060912030b0405040b040201053f010b0a092c150f03030703050405010e040209 67
    0x1104450060303048a040b01e40341d081400720b00b00302400040069200352401c005525052010700d070490b0213007882c200d1094035031001c2403d4582c110340141d07081e0f4803030004104010101000560102411040b0360307105041040040d0544039920f00c2800c4544c0f1014090601e6442500b240d00c2c2c0300c0010f80e000002c6000702c8901d03400f401066109070100d00b2202c07000445600803503004100ca001a511131520200340701001d0308404442c0d4810341c25201c1880071400061071031003400506805001c1101441001d8070000b403d50b003441413868002c80c10721040c00001007010b00d9840e013241d07090a28075101c1411006413507252440502109400000c021a80c120603e071a40250005d0110844c08020ba030701c401800103240b040f034107060300049410a0030440039015540e101d0745203100e01c40f2502c1849441c10102c000e802c003500c02941103a09001c8004880ca01400365200400d0250090340c00e103180d545000c0c004c0c0c000d0b07104a60520011403a1482c040e0390b80d50458081240050801e5505800c0c61100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 808450881 1250 808449631 808449703
    0x120a0302090d110f01021b100e121506010c0f02060d02070b130b0c0a08070c080d0c120501060306050109180615020105040203010f061203050d0f0203090307200d06050603 75
    0x901441001002903005e52020461500003940b00760101e24444000d000d02124039a0401403000300003010282c00c45a50b158105050a500e694000304103800c1c100700403c0309101c028100f80d040c00000f006050000d01c948907210455601242c40340e469846074120b2002034465070b00d006191101030801c00103104202e02e0b070822520b010760701c900e1107942d403540c0d8600e4600c81c0020b05004180d0540004d00b10912410000c0303400d80c41401420300781040103035118241c80581f03486401080140e01c140416a0141c030910b03004041c0ca00d814000c5628001c0007901001c003a01890594500c0d50904086500c01c42c0c01c854001c01c100700c03840b84465010070000b4000c01040c0c1d0124841e509011007510848071074015041a80c030740407983c044040d02d40e039050715260301440e11140e030a500c0e0512002c0d6100140301031885000414003441d502d45035450805850b81000c540001c850448124500560b1190803101900943c4060001455114040001d1900c508050940600700e100719003004804160130038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 808452131 1250 808450881 808450913
    0x50d0c03050d1403060d050a02120309041803051b1f09023a02010e030d02070317030c030a1a0a06030c120204140907120e06040b090f120a0302090d 65
    0x2520784000549100701c460303079500703c1c0c050038003d410301c0030481c545418059150354902c500200c840703030145607012609424003044190034580020800d90343c1070505018245c01c400d214131400b07100d4042a80c014020b401036810048044031421030720602c0b802c0c02c2010070300c4400c1c41e1400305040b2403400318400150501a800728020f0380d059811501c2d014511044040c05440362240c803150003030350091070f20448154102641003184441603800c480d28284500f0011040580c0901005821401c250740c10340401740007440c0d04241002006103040452069075085440c0038000302d030803095482001e001101182083d94400c0f079031030b000203980b034060344850340e8441d00f511150549100350380c80c0422405a0300c202c204403144480102d050b407802c1c400300c580c00417003410b201c41c3c041d01c6203140300d04941c0342c03010000341135014005200500c511000c6041d230040703000008003960400b0303d00c05a211040703880103050128001c1402e4886d94060f4064030301082c03014240c4848900036050590000d048088 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 808453237 1106 808452131 808452133
    0x120203060d0b1008120313060507092301020615030c131415030c0f011b260405040e011b0e03011b0201020310051c0b040c050d0c0305 59
    0x70090150b0108945080f40600b0030752054070b40080300108610111092040007038401c0d441d0032a0700c1940d8401c101044944030000d013a581c440c5250050310f2221401e040000050711450f50603041e09070309908481841d00d07910411600030000034040c5070581c02401d074060707260030000324040c00c95040f42c00c00a070041440c48020400082528500b8100580c1042e0280c03500e810414840c54000480e10501d21019440028001202e0000c4141c0c40c900300300c1030340d402d22094000301380490035078569441171020280c4000c511541719000f0140f045103065411b0b04c0300c11052242804080030719100c680b100c2c542080544a0407082600075030f0540d01c8440c403044a0a041e158482c4c100741c40e400140e100e041544071003400001c150061402800a1680083c1c0d05881c416921080c54101d0000c014545072402c00a4480c03034540c1210360806101701c0c11a040294451042040303030702a00c = true := by decide +kernel

theorem cover : BRFrame.Cov 808273381 808453237 := by
  have h0 := BRFrame.cov_init 808273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 808273381 ≤ n) (h2 : n < 808453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
