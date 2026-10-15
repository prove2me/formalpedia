-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4347
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:19:38.660039+00:00
-- url     : https://prove2.me/submissions/f9d80460-7526-406f-aec6-a0b48ec67fa3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 781654676 ≤ n < 781834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 781655926 1250 781654676 781654681
    0x120609120e0312070f03111f0606030e010e300309030705060124030b0111011d0706020a0c050f0d0501060b04030b0c0a0e27010e061005040b090918010212 68
    0x1608000e90010802500c140f04d2a140241d42c49100b080040f0800030300780808004201c9800009010301141c0708d08540d40580303250115040f50000341000e020b0346002c640b42551042c0080c40500c540c01c58031024030300030074005442042409041070711000c0101442071b03000c0e2460f6200fa000019600500800c0c00841e06c038449840c0203030500405820502c8143c805a0210700c00303411501da458103105039814005000d41c0d00600480d01c802d42214604059130030029018948522009145415003000c030a803035040351184001c03a03ca843c815005400c0605401050049142c07904440c0460180200f60071065801607954900b074a01681c031202c0e82c0300f00031a0800a00c0f50005019078468100450545410340000d800b07400f078000201c1d400e00072101e041004409241d03100b4692680c503880c81c80c01c9102e6940717a003107000c02241114198000c54040361040c0006018006560a0742c07021000181810407041c10b02400c3c0c2030040241180c85800d100000301140203100408005403040c201340c2251 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 781657176 1250 781655926 781655929
    0x30714011808070b040204062c0105010e22090507080105090c060f07110f060d1b03050403120209011b2003070f0e040206090a0b03010806010f0f120609120e 69
    0x461031030008804000000c1ca40600248465044841d00d079840900c84400792140e0000c10014a082e1f00044007164084101040b03030310080400103030170701120034886500d0780c96170300455941030004086500f025488000a0081030103078000d00701507048410000300060661941441c2a840340d1000030a65503810a00c81107172824804000e000400f5184546802c0540e80b0480c1c09100d000006848884100074a061036036a8400c0d404001e07a004000a81700c980d245c0c00240123044030500d040c034590600340070715042d5000f401410b1146800d0f494040c0743d001c140030041d010f540041c6520b41005494540041940d8580c040080118007072040d604901a03294030720070102001140c03040c4a54000d80040083c084a031900303505640c00c501c008030080e01c843c404544a4010071042c55400a11a20302054208040300554125405d40301141c11340c0c5d0b600e42941601d07607028025110203c540031400e003c080a00c07034000840c98482c1c640080c4031961919090325041850f118140000c07400f84901741c99 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 781658426 1250 781657176 781657181
    0x4200a0f0503060a29030a0c08150a121b24031e18021c031205040302190320010b01450902040e0a050f060117100803071401 55
    0x40d2445040151960500100159000c510340c81040c10324403404061007000c00e078101c00c0715003c010a505064481c106140090b000d0169503881c0400241c8a00004800c1008110420040580648456a41820481111216245060103031386000f00c4036603450342c01c840295148003c108000b8800b826400c2000c6a8090154941c0f10b201058140f8510744250ba42c906080300d8604503042c0002503107203002d030b0000421032031484041d6000c018188401c10360401c6000c45a0510720a60300c0064800e01c0307000c00e00071600c0503035000c2c00690108104c035801403403826000031058060700380081c0008281103041056070451241020170794680d0345110340c0c2c0d41c001c1580e03501500c91102545a20900f00c8070540908000c0102c00d0420250b9040405202c00c1c6080b880f01a0200b50400e540e5241c42c1c00020b1075060040d10300300c0c01640390a00140e05418020b403098001c401c143d544d65500c1d2400e08840c20192809044001e0100341490001003030b4070100014888944103540c0c1c20701990034035004508 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 781659676 1250 781658426 781658447
    0xa11120a09021f080c0d0b0a0807060e010c050303042003060a1b090b0d050c1303050601030b010b0c060609180118022806030c05070b0f0603060a0209060a050904200a 73
    0x1c580707040b00c00e15410700c0c4c0015507168804001c4200949500050b003030740000d400c600c002139030043c1308c141e000301c0d08038804656241500c0309510755032981c0f000030004407040c14403c140a030003a002480443c000507140740300b601c010120202c0e50b00d140c401d4080024240101a03454184540d0b8849101e44c04015001c3d8031400c2c458103051518620349082c1145015100d246100310403140c0e18400503541168034030548100340c0750381e07640090068691400c80d5441800f0700080e50000034040000611036001800c0740e040040d4031020b042e0a407110814483c031008054000740c0004030031480500d1045c4244109030100520000d603540010003401405100c0e003d100001c3d00c168580e9040509520f00e80a40104503101c51030002100103c1000c12038440c043c42c900240184940e42c00d106a1519000e903e900404044041c0d5590f5112000f80d0380c00c906c02d420049400000500c54003859500407006041402400341001c912440102c20400e90320703699070b605510b80b030400b0032100c1c0c0d80d6500c100c80c0e81 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 781660926 1250 781659676 781659709
    0x17040512030a080906090312060a080f0714040b0a0302010309030e03030d06030201140313030f02030f1206030c030606010e1c02030a030302120a050103020112020a0e030106180b06030105090a11120a0902 89
    0x403071743c200550103940300c1c840d200428180380202d0380400c4140c2c031040007003c001c240d901c05a0b01b40c50200e2403841e46036002442468000c0384040c10342c6d27030b0303c0c901480381c15603800b40184407107039051440d801500601900c8000707a06000c408203c2d1001900c0520090010b040390303900c00a1140d0451002609481c0e411418143c0044140204228400c50301040d140c540d4141c1003500a00d0300c6c0310b0040f0f14505c501d00c00307140030100c049140290030324115101405404202c040e40c04401048040c15510039044074480e001a134052051034190509075008508140300d4100c00d00ea503d0103401191034820102d030100d0000385d0010307070311000240354940142c10001c2404140306651554000030212032118001d03048480d8001407020507640250201034101001800903c02c60386d03111807500c01d280700e45440681090030448210034601c0c024040b2810b80e0001000d481658844100b032000030003c01c0d001c000c1c803d03002c126001003010411140c0f0710807000c5100210703060803103106000c1040301c2415001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 781662176 1250 781660926 781660933
    0x1e05010c051e2d0f191205100b09030a050f03090418050a02060313020907091a28170c031b0403030e1e060c1c020d0c17040512030a0809 60
    0x80703000c0416a8a114410341c0d4815040660706910100c0d58002d120b005003a0303c2c42500040e20041700007008084c0301d00000c01d512200c2c0d503007826010300401c0c0d07102158529400003d002c03060144c0000c0d000034011400001d403c490041c0b02e02d0356194036000305c0041c1e1208940c80401d45050900c1d05000c1c002407480d48141800c1d0102c2d007541e400745e517048507440c024400c402c040001984800c1c008410b071741d002d40041140000d03041c200009031801445024540d250340702d00c0c0c01500b07445010000c603802c0c50b403003400381c0c40501004142604a02043c0d013020007008040c11348030802c3c2c580e000a1034000e69207640926900d08080308a200328450410560410300001c4c081000445d40007800065060000d903022604c207003405400003074440103880c4140d80410085019001e50100040d0050710100322003540f4003034100400141d80d91616192001d0010700f40c505600c00040c0422901c401030604413608904058483d4001000740070150a0910300340e02c00316aa80900e80d12054140d0030002c5c54028 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 781663426 1250 781662176 781662187
    0x70504060815010503370b0a020a080901060614070510020f0a0f09150305091606050715180215040e011409060a140f0a0b0a0203042903041e05010c051e 67
    0x2440f080c3c802454a003000442c3d203981121b01b0049030080c0648241c1c07007518000c00c0e103044c0c00900020740150501d000010749103800109203420500c40c00303083c0e45550711942d000305030300c210041056206100454841c040d8045101081c4d40b280050311910608039807107074a405551000a04400c81e1588a904029103445c00b00a840d4016480400c0a2001c2c640441ca0743d81d07070030816103041000040600314050110001401a0b401005403804034400c00e000042140000b0080d0141c440304140210b030b200e4407101400c0103240c03180003500003519500b110386c1020b079596443e40301d50500341d00c601042e00d003829041560303207400702d002070f40000100c621940070b41c10071401e1103400e090b0a00305805400445a5080e99a5a903000040100100781090742e482040500094994001d0310950414401c09071806081c00210b00240c09440c04219030981107a880341c48102c40300c40e84202c0484844204840e80c8003081c02070041108542003902d996540c0e44102d01050407450844100700c000080901c031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 781664676 1250 781663426 781663453
    0x903060f01060f031436010f2406030c09080607020601030210171501090906140406083903030d0e061503190809180f010b090d020d05070504060815010503 68
    0x102a41c0081011440d00c2e100b044405440c650302c6444246e01c145c2e404056a01c4a00500541000c0040c10907604144139803044e0000c0014171241c4001000c400424910050003450712a9010320609919480e14500d11a0385072200c030b0400301d0aa400320016000340005000b0b41c10003c0c036521b40628545801251040c120140080192001d040c4014155090107100341c1d5a100e0b4403c030010300b401d80e8081100039901d00b5107000803903418114502442c00d00c0e0000588000104040c04d2105400300094904179000480c000161070302d540084110503c0c0b2000c01d0340e0346040000e4500f0000c50000080c915007006007241c580359006200d1122086c0b809244c815940b00856140204515960048001140752038001c0d00380c061001c0e02034100d4038002030300c80c0100103080000c0c0512011641040c8613622400300304400e106000185030031421444051006042090028500c40d015400782c8002d1030310340700001e0544003203a10030203503940501103419542c0410f40c440c9004080803002400469070040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 781665926 1250 781664676 781664711
    0x31b02091306020c0102040603020403020310090b130606180f140907030212010b060f071202030403030905060319052d06031c0905030304030f060510050919020903060f01060f03 78
    0x10001d8404024401c910010060300e43c041d5080854840004e6446a80710701000300250018401640301c3c1c071130b100302c00210790464030892102c01c0c0c0102c1c42e1040742d41c540c66698900000a0812141c0c1a5102c00c006620200303000e000d400030440d0440401e0b0711207000303150025128502800342c448030f2100e0910805040004443d022281d0640c1d800600308001401e0302c0c0104024101c1c1904101c1c00130388680e41d004890010b0564505c1960101050022481d040f0b98901590000401180b07101c8028009490300700d010f1680042c200203aa107001000204840a03110180e40c52a1240035503031010780d0303410390300d8078001c41801c0f03400c3d042000d80b500c0ea00199031803121140c3c80300c0040302561100ba00310300c15002c590142102a085903a07842d920300c1c0080d1031301442042650141e1070100841c0c00d0040b0200a5004c507940104550400c0d103c0091094480c0d42089498803941e80c20404e01c00c075038905000040c8034610762000f070002c56140c0030025003d114804000c07001c00d4030b0f1415000c0c1d02005603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 781667176 1250 781665926 781665931
    0x105130b01030e15060a061701050f03010f06030305092e05030718030c0e07020a0c1e1e03020f0306040c03110607080c0d0f0203090f060d060f0909031b0209 69
    0x20900440c01410290068004244056039060f0038080c002498000710381d2a1600b83c041c14040c2c441c40c02640e03459504491801707440400380010800071004005626104426201915006000281204a0098041c205c50303140d40102d000c50800b0400d0030403890041100b880707007000c5586a07070b014601c000341586041e403404800400e012011001c210f0340340c0700d017016943d40c041000d400d84640e502d0313090403130064000c0d1080301e5144203070310001503040780b02261070b80006512910380d45041c1c5c01c007800a0b260305a2a134401030b5a910000380080d0280e1201d001607203403040b800f0034842c4c1b58103500600c40c500c0c1c1030895017400307a4806014807000440c030701412402c41350041034000190f518000000c100d03104c1d04802a103946e07008600901c44c41d0012905000c0d640403030321548400c0301e5100d810398a900414030385503849841c0c054104a03c1c02c00300000c0400400c40d4100044160311031114203290205500300c170480b69a01c40e00719003015003102d41d031350884019440600d040002980000c4045c00c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 781668426 1250 781667176 781667209
    0x5030a02240c030d060f03031b030e040c050d060605070321090b0406151707141c050a0b060a0f06030c031103070f080f0708060603100305060f06180105 67
    0x4802400350701c0004014844480c03080040150b480441001c074903500d403c0100140d020500d030040009071140c124031410101ca0303054071130b030452404481c095011141c0c01c090903418401252412030159495114000ca01030140d2511034646601d92211011a540c1c1d800c0a000d0040c10800302c000f098120a500d08500a40301c40d2543c601c0c8460fa0f01c0001e04400c1c440280b5041040c000c1c03008201c0e00c0d8100007100151a19036000e007558412403a180f848100d03104213203c0c0c0000c0002d000481d100d0002c8902c2c0100940280266500c1e880c240040c2010140c0988607038002c616180c04000c01c040c504c940084048514100040c1401d44500f0f40c00d5280c480c0c1c100b4540d444041210490094201410055480d0751841e1a031030b004d44e000d07100d0f064140d01c50000484c560000744132400103e8602d809801c00713549403a0315558004c18040282d0018148051110030890000001042003001710703c502c0d0480aa6140c2c0e04007075040c01070001a103900c001d51990b00b540140015110306d5601d10b9070104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 781669676 1250 781668426 781668439
    0x6030606060c030909111b030d09030917010c050307110c03030703081905040305120a0f050f0106020d1b0f030c0507080d030c0c05120a120905010e1516121b021c0905030a02 76
    0x2004581d07d0b1640c0328a55404996078188000e0206068001c080f110441d039a80d2034440b010081503540c0d60880e42c0c8490400003003182840428510703807190340403016410340d42049807074405210000a1135a04407650440001c0d0401081044c844541d6524402c02c4001c3d0360103120500381550041d169010f44002d0b110840c6a01e030000f0044400b50b0454826000c40c4c1c08100141d0800800c1c4240140090007014090311950120284d442c2c407c0c0c03030111403010822584822400255501171030900c00003016020402c40d50f50090115405120b500c0041415100810707900c14000c0000d001c2e03400020900c000d204000726440c0201d100495084425a803518a4960310382401c9016185040400c052880d054600b40448080240c150312910034150000200e54040884030400a0352a40480b8413a0036091051040860340d80203400480d00420038000c003245122140d801c01c0b02c40c000780070b6000c0c016840055044100841010040b60584003807404001040c14407000c00d171f4030f041c0c03818028040c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 781670926 1250 781669676 781669717
    0x406150807081015030b040e07050604180b15070201090f05010f21060f0515040506160213020c0114010b040b090d1e2307050a0e0a06030606060c03090911 68
    0x5071240f1000c0007400541102e009006695038000b0000d1032103484140c0210f280009141da280c400040220841d400140740710720b010308000b49654a4046080450000d0362140070014255488950540055088100c21500d80a0500004080e0b403d01d91100c20f1044e5080e40600003660b03c84628008241641400c1511003844060302c24803d40d0502c00e000d01e94509a8040350581c5003020100032507100b11100b50240348910300e615000c0c41130380b00b010b83c05102040014205540c0e49101c0010500050440c441410000f560300c0c03da90102c1ca00c0c0400b41d55508419000b03552000e4803d000d0038404001c00e003090304108910076070784030380c450440c0b181c100c1060420400ca250102d14404200c04a414000c4031030320310308001100d07509040007031050b000d40840e0423085000100c04d4200c0318000c2202201c1d0340382201c4142c54220103081214480e45401011010400c00d002d000001d19982d600c21003110740320b0400905d41c4510390000500c05040081940d032448800081e0b81100c1c110903850215078 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 781672176 1250 781670926 781670941
    0x312100e010b091e3c0f0108090102090409061b0c030503070c0507051f080a0b060d0b1f1d04090b070e060c060903040501030609020a020706081305031206040615080708 74
    0x207200d00a0300c0d54402507288503005d0810132540f1400d0121141e001002c4100224005510804580c820749508400705445130f20f045d42c850601d807604402c221000502d07000c03150000c182524035114003513402c00d40b59098103d000001410b1241d84407001d24124504043e9035500500a02c00a480714040000450580c02441402d100c400003c000040140c070850f4050340301c0b070010000e002804c401003000e110002d000140705007c1e410515800900c040d281400306c0d8180c0000b0003417403410035001500c0e2140c00b00340c144010082c282400164441c6030003400041000003005085884190249041011100c000303000300e18080d070807050b1802c045080181d07075000302da101d014815000c0341500c1880240003440364040b0081054407401c0c0d03402d2000a0711900b0307803010380c4034200e039103401640124420004144207005150b00300e00c091511040a070f185d0340340d80d840d50300100058113482d80750405100b0589058803814000340804030010340ea240000344013801044005103028281b002490000c0d050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 781673426 1250 781672176 781672219
    0x90102070b1b0f1c05061c060f020f0c010b032e05090313030606030c121e050102041802040521070303050306011704030c030206070306080c1504080312100e010b09 72
    0x1203042c4030009440d01c903d0860084c03106194410b54004074540380105149060400c0490f0340c40c504508001190403940d80c0f40c4004140321140541c0d455802d012042d01d002840000b02040040007001066a01d1035404050a049507180890242c8400841d45e14602c5070000310300c8410b4074134803000251581c4119030075085110300c203402c1c1410b110540e800b0041200903404401502c0c0114400e981c8580c8411a8503e01c000300940030b40404100c1440b5507030300c0f25000118034000c0c402d5002500703017595001c1c42c40860903107180c040e00041e0041418880c5060100c24203c040400d83e202c40d50366400081c255403507446901019003009000800200541d02541c1480f9001101000401d060720302030600400d404d29040049005015510200e40c080303200340114800d4560000c060710000995004200400741101013141040d20103000c0010030403030500c007800d001c0e042c1d0341c5400e00c140340c00d42140c54051543d80000c00810303c5d0400501901d4410400c1e95184007050750342c400e002e01100300c0100c6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 781674676 1250 781673426 781673437
    0x11805060a0b040e040b010b090609040b0a18060e06060702061606021303030804030e0906010e060a0c140102031e01120602090303190f0e01080f0a0203190507020a0b090102070b1b 79
    0x103005030000f500051030700d051080300c0d209602448101c1c180340d80364040c007005480740760007150b07000c00244030040d01840d140d13115005150b001480307001c2040d40d90140c00032407203264420612160380e03106c040000c9884140030681c07000e02220076900e0041c0b99400140103003d00c208000c0000ea1101e003c804002c1c41d036045a00300c0294140b80307003040e662807400500040c0b0031601217000481b140c640c03038000c0c140304240e9809088144c603010076801c0190240300031a00291a8542040045107030031000c1008915a2901c01210800242c0d880c0390007078000d002e40c2030020b034910030aa003a00c0100200c6180606854059512040141c1d4030f6034420300092840c0101902c10500412082c0c4564585800c18001e4400c03031015140c0c02c146044810040d18250b00c101d40d1000d420343c030500010442c0c146540119071000f81000541d8050b202d0201e0082240c0c000c40d000405a8007800b0343d00c2c18001c038900802c0d4400900b2000b903240c9480b9070750f100d0715080050980178000907405842c41c0e000c0f07561804d0b01d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 781675926 1250 781674676 781674689
    0x10312120f09153e0309070e0c030405250810090c270c09170307330e01020405190510020708120a210212010e011805060a 54
    0x100d0900100c018000070001100300316003104122100c99400301c103500401440e543c101030300c031645500302150700904409899070100c41d0350851154004c00c8228101130350080c01000000d1569909040204808460182c096032519074144200300001d58009061680c03a154481a0442200a2603c1003860134094000d41d0b0140150307241c82a070340c0340550048001c06d00850b40d1404880c0c2d100b03d0044c2500100b00c2c12030081c0c0718a0507101c3c0c40800b0384c0003c1542d481c03034605000030542e030b901c400d111480300280c02161904000340500902c03001041414001000c0e0701c0e401622203965901c035400d41002c503010580a0344544908202403801e5060394020540a040b640010b80214403000e0101c0e01802000c2c031861000c02ca80f02c00c10b00c00203110b4140c881a000074502c1880c0035012103225084168440b040040c400e2142981c40103d000ca405940c401d8040580c5483d6180d49c2200060300517080504040100c400412007001c110654441d8001103110000d0b0903141c3c400800c500b81c15640022 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 781677176 1250 781675926 781675931
    0x5030d1e05070f0e06090d080715020301030309080d020304060815040915060f090b010806060309011116200105300403180801050c0405060a12090b070f0801030b01031212 75
    0xa1101c1d0490b03d107005410b026540c402c0401c40d00c2c4104440780c05114103058020003512600c83c005107518006003c0c440c011801000d000c65403024540c1641d009800031800204503800811140700200041d800c60071490018508250420000800014004206c03862440c018010340e101900ca0354010100319800090042140c050940c0c200b010300f51a00c580300049011810000704a01c0074468640003d40580d266601034488100b0000b06800140544809543e10407121003c65004002030030000b24040c0d20308446040d90a0521011290181031182003118030483c1046a038800221074071112540382901c0e101d080c1c4c20300400c09098070400495113810f244c0902c810b050b08100d20402e07101c00d1070402c2000b1515000c0803826034005440d42c0c1c0104c1d0f4180028007141c94600c000d060599018941141104c480040070030650715851019641d80c099401401080c03680a882c60080b45854100f04080b03514650f14000001c80511000d0310881c18140700c0c12147d48590141c010051034001c06 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 781678426 1250 781677176 781677181
    0x180203012903030c07090c02160e070e03060402010e10020a020315040c08070f050f060918160c020112022b0c030b0901121b120b010f0504050405030d1e05 68
    0x1006010026100210700d240500c0016a071450700200300d60b0605580340c06010300c01d113803162040c041e16003100c024056000301c00c480030000a2106010300100b002c01c25854960030010006441114640c8015020703400ca0420400541d0f04000000200c4a083c0e03600741c1400400c8a0490610ba20030030025818018885524110081001507a0042c1e01a00c6814840c0d035503400e03900e640f40824400c4514101c8503250402045c03400038000d6200b99800f81180c0e1412303400e40c0004a06c070441c05c02c1180c03040c24400600402e03c40c801c100b40d19071030450800500040312031300040d003448030907e25010565000501e000700b203030120f490a00800d581c1614130800c1e810000d101005001c200803d440040e26080d1f4a800614200d04920b04031303640c1184a04043c002d540741c8200a00750071983c40200101d0700c40004008010a0700c0441c20350040c029004294140f07149288100d0300e5900041c411401c01c800c0c40007043c0040101c0310031824450000550100700e031046810240c420340c0c0c000c40103140c1400c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 781679676 1250 781678426 781678451
    0x20a08031c0e07050102070b0a03140a0f0609020a020c06070611031303020f0106050d030f2003040611030a08060d260726030a0c03110703091e0806060418020301 71
    0x41d030303421101104500b4002c0d000095070150ba00c903010700c0380c1030040e0301400040154a098030004c06400c03010349804a01040f4010b03a1030707800c0105407001303d2040d41c0c030110810104501d105090160000c020294604010104000e50355000c640c440c03440384000144000810085503c90206006040141a1245081004001e010811800a501501501e080d14041e05010b2040c0b9050f0b510041010011100d1a1411111610320200c06000d02c00161032883e24071400c44100d00c0032103101c10080d0340d65410204000c24030701c280b04803404540d0091002180040d000210a40e00a2050b94850029081403c1c001d24030401e00070080401400d00004030309140104c80201821401109000628505020300202c4a59182c4000700c40e003000b4004107030400313019001541c04020078503010039418011442210940c0c403034a812004161091010031094561402e00d5031002d25180b022980549014141602d0350f20040c10340b0720696880d807080c05000c20761510b10129980141c02042130501449 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 781680926 1250 781679676 781679707
    0x20a06020618060106050a082205030901031514060c0a0b0403030b091e1504320112080d271b0522090206041a04050103110421020a0803 60
    0x115005034100b89100303085000600040c0c0e5504807455656003900d09555803100b21002131010b0203440390300b43c6030b09189620007140c0b07013460034042c040c030042d5540c0d02229001504031111345a181e08010300c144c104108518604031043d01084007680e45642e180d5400c8211801d00c00d100d20300900829401080c0400c1c10360590040810510640303015241d41c0b2812074000141d03404000c010781020b1f07118002103285134076a1400c103200d040030300702068103803000d100d000c072068281c11103008002c050200407000c617904010f1a401480c610005400c410000d45a001c5148205810459401d840d4405a5028a01c03c8400130a81032030b803980a2040c01180746c10180c40c10740c00034901c0103104001010901307282501da004840026565201c151641c1d0f41040009807900003020790340050b0031700c00080d140780c900040b0120120b0000280b507030b035403d0500260803030f030580c150401080d03c00d110a20140800301c0c05100d0b5000c224a944941080d01e20000318000e600d138100c03805074000403641802c4060b494 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 781682176 1250 781680926 781680931
    0x301030303060b190c050f0706110601050114030c030915070c030207231507020d0803010806090a0f151b02070e0609060d0818041407020c0901061d0607020a060206 72
    0x380d03820b1003000d550f400400b040f4003134815403184c94140c4181512030b03c2e000f51142c1001e41d1180066030303926814040e0031800c02ca130942c0000c01003a000c0b03051851001c0b050081e20301610342420680e005400d0105941054000144041a213003400070100d40c8103602001404003244c0309960100003858003001c0200300c284002001c80c054800c0e960003254003c5181c5406d410464030408204565180404000103100c1804080201c81c03001c02460300542ca4021402c41c44d10b000311144c55581d4500904140303802e200400e0340c042a0021008000013804801c1c10343e00c403d81208201c4100c2d44548440c03c01040d0540c5e0742c40e075007460000880c0407140c0100b00181107942d4200700b60300310f80d5140180407170301e9400c071800f07075101c424044400000b8840d98042c0c10141c0090380203000000c604000304084038035111400c0038070790341034040000341c0398100201140c1060030b40b82440030b5450303c640609800c00310f21052000c40981641300059071600805d031a4081d0700244424807050752408043d40302c0c1001d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 781683426 1250 781682176 781682183
    0x50708070b0a12052203090f260c180403032301080d021b090907030b090610140d03140f120708010605070f150b10210608070314150c030103 62
    0x5044402c40c0101584c8100e620130002c510001e075500203c140800100b008803041102403051042002c1003440b9003013044070103840001c040d6115a0120012040c1e00349400f40e032900c07a079020741550915625800c001d0024042400c8002000391242d150540141c0b45050240b0100d01c6c00c3d54085d80141100881d16040b40c20600550b0065460310504a848210030840d25141c40e144c860641202e0800007480795015003800705840030186c981e41c4941c14400182e420310521750000c0203118040c0b003403107010383c0200662800e5600c0310f8550004218941c051182c050140b080d4042d10480d41488001100c1d440704502d645250b580b064260000000750b001c2c0c6036040001c01d0000045502400741088035070050b004028142d4000316070303442c9603180c40b512549015a84c1c0ba09100807076034640d00800e00ca89042d42d1030785102c002c10001400301c866040c01c0c850744c2d4641010b6041001c4c48000c0f50b100181c80d0000321055650302c024440d02e145c955601040c0381c3c9920b81901304101113140c0b0b0040c5059034403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 781684676 1250 781683426 781683437
    0x4060b0d050a02130614130e0a03020a050d0807120903022d0c10120f1e1b030234121e03050106050406032309030d151202010507050708070b0a 63
    0x200324013602c11a022400350481e40ca02c00c120b0006c03686480500b081d02545002804039030401c481086600749010488100c0141e40308025020410006200d04146008140350038262482c1ca410010140702c01074000d07880142d642c1c401e2806052080c0460f0300c0000340911549a1407480c484008001c0030802e0551140e40106207040a20780b9000441040020740f540d40c916102044030744420080c00e4002080c40303d123503204032418074401c070842400e40344906404005072140080c0c0e80c06520005406609041510402c9502e002c41030071100c0d400070490400d120701c48074802900108402020000140c202076074004c04a040c540d119120200804200c9031070300d803110780307890180c007600d03070a00540c2c0210704188400d01100340300340d11100c441e190084082520343c01d10001100e441d9010f40d681441070b0800110098034a1907070017010070764421704040940346403904001e101c1035a00c1c0c0d10001d040000004082091050420a41015080e064161411265a07100c00792031a0712004200d0301040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 781685926 1250 781684676 781684699
    0x6090f1718040e0a1203090213020403050f0606100e0103060504020c0c12010c0f080402061b010e1b0a05010e0105040b19141e0c0f060a05070314040f060504060b0d050a02 75
    0x1401d0261a80a10110f0001d2a88291554848684140541042c403c0554a0070020056500c6050f840b5000b10000401a41c5030b06500301142894141202203c142d0301c420148001b544421101003000d8031140380070046030014800407400f510072a40001c0e481030002c01c1703040000304042400b4074000320403149100f9000c030840c0650f0913202d1481002020804e0701c1418040c0e00c0c041e9068a40c0a44014006e5140c07808500c078000040d642501a88070503907588200c41d5410b4400c1005003000c0481c2c054440529a400c1c0005400d401c45010700c0781049100011124030364051404d45010b0800450307900d481d546206808203030a001031030741c107000440d0454003d4940c8190300031101242001d1004001d0710740c4070000120340f9807104009509034403c891181282c003400f03000f11030085903d464007040324100b0b540000c05079100c0c3c1d5400301101107000d05000c005035182200364440c940c0900017048503541c600700040201301c108030040d000b0001d071104104020010503845022031003110b156403040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 781687176 1250 781685926 781685929
    0x305012307050702130e01050a060e011703030c090118080307030e01030605241611150c070e0a06350606030d0e19260102130306090f1718 61
    0x10030207407003040100c0d0042115401604006000716911480820045050342d00c100c2c1d013a00312002120710400869540c03005120441c10410440e00410400e032000d803040c01d001400c6078a030b200290281a0000f40002e40740709590060750400c21a0980ca041d1707600b190382e251103040c2c407640050310440005810740009540c41d030091140301c059440142605400500c041d103071040740d800740400046d019009105035a0150b0040441000c150710170140b420050050b80c0600402c40300889403040d00b064140800446142c00091403400c417040c0f1603292a442d01c684e03038880020085038100c0034000c1300080c08181400503e20080b2812402c001500302900f2541005070313204c000a9500a502d50042913510f0755035841000362404c1c0080040142c0b2060b2004403165407042555400513090f640c003001c180718040c46413542081c1c09001c03400254503141820645a14240740d902004140781d6444151109218a03001c05074845548403401c400e017040c8440007680141c0145030209244102c03094015060b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 781688426 1250 781687176 781687241
    0x3040606060503160c06140907050a1203230712200a1e021201060326041d1e0f06041a030705151201030b0610020613031d0a030501 58
    0x131640041c400d0041c0c41810000c03110000b42410a40c3c21603207442d203005400030800211405030007232000802210b441c000500145485550102e0b85000d540113107080441c0d08111908501c81c107010a0b02443d56110700d0200706400b41c07ca0240a030f00310350168100280c0c01c10858030415488030b125460b06201c1155103a5100c045801c01004000380680620180740d00350800940c50f807004001d00c8007258907003840c60840e211a0700548103040000e08039240342390140c0f4079070104010004981d01c0d103070a25000030301142c10040fa52580102e1000051208402d5411881c0e815008582160321401c1031400c4140164003554060f10a601c0c0c8000f10a985a002048100b40074014010705245483d00b000c10074201d84800710b0101315201046008000b032030b01c0783d403e4041c0d48a0121100e003810a0000c0c0014403030b140104006642c0f200707013405071002d9a000c1c8000d400d80e01d45030102c1111070213140e111074a03d40b2110107030803551440e0301004100303064100078488140c0280380501429985524402c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 781689676 1250 781688426 781688431
    0xc0409050f130809030309120601030b010f0f2601090b040b09012c0a0203161409011d0403051902060937020303120103150f060602030a1805090c03040606060503 71
    0x4000b008020081c00140201024003400003008081c0c83c1000350300004140c55071000840340d0000e0b00010010700802803c01103203405842500c45250202e03081948416014842d4090224000007082c13110f000d50900c401c02454643e0141c0090040c0800c6140c4151840c0081c0c0d801ca41802c4080002003422005229090306107000d501c0d440c0e08043c034a942001500d0415601d5030f030b0390084181075009a10100501402c115280c800c03080341500d48205122103212400045129501000040280380300c2601e5460300003010104c008401d48032480e050707550b0300ca80800c0da0980c413040300400340c0307003a000300d1150310500a14083e1071b200410301000311f149001e031040010190400408250724244100603600d0940e00c0941160701d007a005030300040062400340e0088401e1400000b045c2d44104035401001400305e0400d0052100c1400d0403000f031740381d002d650380d800c0410845905102049829114007001458007401c1c009660404186160003680119001d0381d1603030500500150051041d01142c0c0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 781690926 1250 781689676 781689691
    0x602040306151707060c02060c06070810060314070302091917060c040609120c0810091a0402030601051e0a06030219140d1d07060207090b1c0f030210050c0409050f 72
    0x130b0340f60422100380d9a4842440d0180e81204081c01140c00d641400c201c41800b650307040e01c0b022441e150003400c00a000c045600a1020141040c000068000800b400ea68001c642e5003405600c03030a02202045001c3c050340e51061030007515040000b172140024084440408a44054403040e55a59000150a1060b4462480050004042048401c036190811002103104031422600c1c0c940d60340c003a038030b0101c100480641030f680d100da14a00b04501d011000701d081e02c810f041c002003031405d90002502c90205108450280d9060746603992400c1110031074495559000b02464505030320388000600940000b002e21b80703d10f6030300400701c14407400740c403505480c14900000646040080802c0310044e08000c1481c440c80307032510f00d09000309881800580d01a0000ea80100481c500e0b110080b81969030310110789000b00d030b0010361080c0610032039842c45002c2d0f800c03401c0c0f030311904501d00d412032030040b0103e0003564981c070700002d001c40b80034848010011100a44014095615007076030f21958150b060700c014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 781692176 1250 781690926 781690933
    0x130605030a06052e240e04020306030a0602071203140417090a03050f0d02100212040f1b0605031b0306031005150a030311160b040306021606020403061517 68
    0x50000680da03402a90b070002c4c5920748030b610301d0b800242c0040b8400c00e0410080c6a16180720f824489800003205407403e8144d428071a4030003036940c66018003420704034400f56004540020010302503881c10408620000d900280031550340c9658244a0100001c1190f2400002c1c00c201080400d8086212501e004035084150001c56904842d0128a541e10680d0001e4110590010000100c3c9007801080341500102c0c014084801404400134102901c1c201a12035003031041c0034042031180e0031015250300c564040050442c0040034104425040400200c03140c01e034142a02c0802c080381d01401460180300c6000004510310032092106243d40402c4640c5038065010440300003101d0786607080a5000011450a11105284035010880030701c06a00180d010a250041c95a20b25008200c10409404096091a1100d00300346045100e0701c40c5200c06032000c1d40100e01c0c50000c1c00c11104010703065504c202c04560700c59991034010090500d50003940c1c0c11808014000511009482c1002183d01c40075014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 781693426 1250 781692176 781692193
    0x27032001020c2503020a080604120f0e010e040f06080d031b0f080a0b0312121f0303110c030307060b011206061e0903081303120f0507080c0109170913060503 69
    0xa8103c03105510f0542c00900c290501d000015884000000340680301c1c0700c0141105241c80d04102100a0802c1d007443c5c02c002c4014008001e5a030b10801d00d007a100002d107055804049227200003409001103039919500b281c0ba240d0700080b110400501d02c4d20b422101d807802e00000b06001e1810740355180013240c01e00440d00c6500031840c102e00c0707000f9182d440914440000b98401d03000000c24641440100e890b00b5007403000810110380052403080c80da22102440c0c0384199400d28800304108851144070003418010181401ca210b50741c2403040c4a5444c10140440c3d880d00c2450404201410303c0e0142c4a000c101c040c40528004140d9015075800e880107500c1e56004043c1c58003410705480c003030450200402c490048003100107a5058001c101c0f40072105248403150342903081c82140b80d400f031205d40301440b4083d0340d41c40c25a038100d01501c0407140c0060003d5150a6540001809000d0481008011402000f901d484c071184140c0030340303c245010754078201074882c140c1000d4116482070090603415848800b5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 781694676 1250 781693426 781693453
    0xc090a14132001021f0218040905032208011a090106080f01031101030e1b0901060c0b04020108130b07030510050604050a1401050702090c04030210080c03060427032001020c 76
    0x200d00c10350b990184111420880101100c500b02490382d80004401a00011502c00c0c500d04c25010510600d0115000c1250041a5540503524420b00d040c00d5040c041240b01000480c4100c00c080c1c00400e210b8000748451201c5074107000c0c2429080080304d00c110410070010405601c682560b61188041401020b1182d00359181e5580c0650b09006035410540c40d40c0c01118814014850340b52039043c907142101d01501b40e0010032024203c140c02003c1042844110325000c21144c20201d03030005d0b020709208170143c0f50800001a01926450301818400c004802d000a1a1f419440a8810142a0010b550301c60b180c004016080c0301d00c1c03003030580c404405141480642119041607035805014103140e1300c0c12280c1c3d404140440c1044646400c40e484c00b003002c10540c02c080c00700c12a08071082c903200c4210301d004203040d00325000260041d4011640d41c4031010003112112103030503e4801044071000308010518000700039151001d009007007001441c004240350704c0d05000340d5990303406060141032102400300c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 781695926 1250 781694676 781694723
    0x403080405120f0d0e163008030708091b0411120103050a03021005071b060b060d0f1d0d080c09150301081e0601060c050c090a1413 58
    0xa205075081c0c09100e40b03842010409000403d007000d0f0040045848200306800c24007101c0440305825100e81264414000301229940e0480036194031290302e490b0310241c1d034014007215000e002d10284e10a400880715082c0b000c5400603511403502ca554042d03a568809851644594042c811f42c4101645030542001a150a07000458400c0d40074040c281410b0061544e465582c1c001e81c8142d0345500b05104000a140c3e050064403060001000d050000b410900002005514807e40c2044807101d014240c404010440d0005d808142005002c161912064600c0d02d0042c40f00c0d05142d002c152400b56210f07080185108904a41201c6102822502882c031300d06030754241e002040d0b00c2509404020452450356008440790b00012891a400d40703940c1400f410f079281080306020100380c0c80d02084800c4043c08005020b0381902ca507032620b0300c6107407a01d00e82a0f1401804080195011010a08000507080954000909961000f4110b040c41c0c9030441032943c08144620040d000c3c000010340c0781d00c0b094008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 781697176 1250 781695926 781695931
    0x420060a0f020a0501090f05103b2508070e04080a1e0504260d0e0411030f06010e09090312100e07180503010c0503040b060406150201140a02030f040308 67
    0x10b0058a24403c61a5a05030031103e8100c01141d01c40010740d900350070f0000411100f40b0301e0011407403c11601d141d0205410350030b542208803030041000740c0404100745290120300b01c0406c020100310380f0309055030a41025110100340050703c484100d503400003150030700010700c40120b40c2c0101d1a901e16496a0301d1304042980003041c40400c3c01008014004030420201c580c0000e1550780d5901900c4500b40001b0151450200481540071104c07640501d030303800d0001c42c2040c1d031544141080140c036401c50011030080c00b080d5041c5601d03804080200b08281c005109490f204000c241d94040c003c007010410803800c00000d03a02d110b1123500500075100d00056400724107401080c03070103182000c13070703951940104c4421040b00c0d0040002c14800c04240c09109540e486005410110b000f80200c00f1044001002400010000b420042035a0301184141c1c13a16031260019102c1c030b51706004019001400640604401100c5031200e04c11540000c1c161141842641d015603803a003000601c1740c403961811594450007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 781698426 1250 781697176 781697207
    0xf0109020604170a0209010803090307050d0b270f1501120c090216080a031a0a083a2c0603070503060333130804050913050102040b030420060a 63
    0x1c03413101030007503512056441c0c000d10a02004594450100d01898240485a0b01c094029094107890b040043c5a41d2074041c2c0c80004400d9170202040364580210508000c3e10321843c01b8064407d000403407036000f08141d682180c84580d603c1d00c03640d86403002d01d0141c019200140540341484421300000700c540d0010400c2c02134000c5141d141400b2034646005541c800f2200d20086a918208207500c0003503e44521241c1000300c0c0c091460714a044165070300c542d2464020003001c1c89178020f00c070600f0b502a503c0c1d1103800a095018030425503026000e080e50800d450000b2480d122102c5040c8001c2034103007007041c059409066141580c40d444401d9441d5000035100541c18001e00b90114080c401c030802d000003400c1207004484070843c803030301c2005000740098200082c580900848102007842c4004480840710140e81d202242d030746003650700c1d040201a11004042d5400080d00190701159400514091402003002c003c0c0c0c280308840743c441084070401b00da908440203200f018401e40c011030b284180c418a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 781699676 1250 781698426 781698433
    0x150206040813180504051c2007080d08180a03050d050c12090102090406060c020f1c080403080a09090b13050a06031401091208070e0f121507020f010902060417 70
    0x703c07200c822040c102101c1c510358519654074104402d01c80300704800214006020108041d2020030032000713198062034030f40c080a4a0500d592035032122000c01c899030081c00d00130140c8010b880d95440040184000b510405200013a400c6a13000341580403803040c54450341230301d915107801c00d10144000074210041813154141c2d000e01c078000129805070303c2588201a124001aa0b80050340101310850340190041d00402104081800040e00c4000100c58004400c139009613011060b00f5039022038403140000200405004500001004001e1010309120741050300c817001d40503101c1011800300c4280c00101e0f6404070358020020b0400540b80e20458000030180d80c0411074070385079182c05031120800c41c0c0322241c1d81c0d5961000303403d000c02c4c500380000c00440342c6000545e608244900818810101403050310607d86104c48001660780e8510a2441c004104242c9400c0c1c1d07140314018660202c200c030014098018002001c4040c0418407a00030041c0d8010001d42c103007070419510302020076402115060707910 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 781700926 1250 781699676 781699679
    0x606040b0a2106022203061b0806060f04051009081b060d0e0f011107060b0405040f17070614070e060c0318040209060f1b070e1f1e030b01150206040813 67
    0x240410341098451046440f0744c0c00711480c40c580030b1f044403110500310844460070f41240904030f602c007010541003c022180c190316580004581491440383d48d00c0300c0d50003080001c818401c260007441060442e52000300b50b031040d0740032924154079003603070030240c83c0d00c010204001c030482c44540c0d1081c4098802e0108136845414862411402c448401008444982d40407410b00c080110b28000d4826000080c0c505000e1802d0503507950804c81c0803030900403c8519441031100e101081030040d41c003802c0e007245052120402d9040056280c00c003da03001d00001b082149540ca80d810890700303c4002c07004d0b04009501d45046da200d0419a099485450b55000c1d03001c005410f225581d50018028080b183e131038640d92502440d0000c2c000c1c0c0f1010441d16056001000e042015803a00c0518036840b00c00c1c1300a0020306000c4407103285840386183c0044400c1c1c032a0300c03070440c82e0b01c806101d07120070380780b01c2c7d551190180d80750303407608039408000d1328114016031142001400140020000e80558281e000e01c030000700707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 781702176 1250 781700926 781700947
    0x9041a09070504140301020c0a140114010b0d0b011107140303040f08010b0102060a0e0c13140106030515040524030a060f0b040f021908060a03060e0606040b0a210602 73
    0x80c6015114000000d1002c1014032031440b508880d4608604101d00840c0380818441145489100c90710001c0d051450200300c2c029414420b412031441d0700c0748000740411540c0c4a003050b09081d000304c11080515460002800142c1d4080e50344071468181d40c10003080c90a01d004a03214a0586201c010342d0103004c24400051403414164409014180c11000070500e0308200f4002484c04100400403100c140c2030100d25650b000f030100c0c1d00035042c901680c1c554034003070034641203c0182944498681000c1d2070100000303242e59155000b00e004440c1c18070000c01c80d41c0c105040005841f825a108182c8203680001c10420280301c1d01c9103141c9400103070945051519649641d000c50b4142102c00c2c0440c0e0300d0360110640c62a20b84541030001c0c2043c02c0850400041044142421346006040400e00006e10042000f5170b132100c3d1560001d6600c00c005105c81030074044032036103400c4280c500354041e07405c1412443c0305240114055051751b0342c900d040720514181c0c0d48070011400161100b45c134220340c20005040e10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 781703426 1250 781702176 781702189
    0x411060f031303110d050d1a03150106020d170a0b190f0501020705150a03090809120c1503070c03030207111c0b0c04050d030e2b06051b09041a 63
    0x20615005014400510382c200903200c1820148144c2003600f01200818540da08013043d50301480c010400010240614040c0c0c00b031106100d000580e2500c15444800c00d01c182e84600350381030b03541540c05e6802521341408180c507104a46800d20040e40b201c200042c11042140d8400d01c0d440707000425603001100312a08025100b034083d0852000141d03005004c1c08a942c041180c1c80040c0029655540094588400a02c4034041c10040000301600d03890100c00380702c1060190342d0280402406d246462200300c000f942d03240002446603000d0388070550400204019041a64446d00e501d880340c0d890340c075090b07070210000d50200004135229801c0b02c1e81d050316034442e440601809002c1a10702c602c149681d0802e04994040140094110142000103000507110b840075003101582c03608100210a94810000c0c1040041000014a50030506554642100c064000d01c0c5a01d00803074003000a601d944242d5090079009a07001d812010007041046400d003440da0011910405010780040110400400140c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 781704676 1250 781703426 781703431
    0x60306090f12050f0d1a030102030c0408071509050d030c0b070807180602120d02040306111b061611030702030124170d21020a09060e0303120411060f03 67
    0x4280007400d20400811400d416500d10320301243c200682032042c0494030010790300c18090342085540d11411909400809401d4604184400900039500c0345480041c140c01d64100d07108161242c0300b0060000342d801d803004050700056200c0c1e590104014213100034001c0031501e82070300b01e0401c40400d01c1140840d8014402d40c0c004c000c55568292142001140100507030001550a00d48a5502e0010005940c0004004540c00034003050a6103542200650700c0080c02282c0c0003519450401030400c501c0100c0c48002c0c16407a05041d07805c018912141e26a594035803041b100d24140f540742d204032080c1c3d02c0c0150f159a10324183c41c1c003200c0c41c1845e00e034082804c0d41d80004070030002491104d01c1d084048005e1800718017a224440d400a181c540c0400030559581000c4600401d1040c00440c1120704a02403070300b440c18100410f8199030310f030b8145000130540f000f984900400185d403203800c1c0c00c0720716010003140d8002980452075411078559807100b4905442d85654641d000c0d400708030260200901d00091403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 781705926 1250 781704676 781704683
    0x130b2803050714130e1e09010b19080d0804062304140115051c05070f03123b1c02040507090b030a020c070e190606020d0203040b07020406030609 64
    0x160340e00b011035010b00003207903412074600c0001040c010b152410341000303c1c403c1180d5503040d035450640c07a98900d941c0c00201c140f02c0307202998100c8040101e80341054202c01c24181e03080c1d402600707170300320601c8414005006c1e006404254200710500489140f058154030340082c0030703032000038040000340e0050709a058a04c0d0a03244504c102c004010500081c4024181401c44050092005850b10100d0300303078560290184a1180444c0350300c48018810703a503400a01e061340f20044801040d03c5407a80316400c8402c0c407080f15258440e081c0050007500c1036880f604581c004e28807981d00811400001d8000f401d040743c0540c1884204aa00852540d41075400008050304140c2c0c103040b000640140700544000078452001d2003480c4404008a190f400201c943c845464840113031150190002c0c4da06000c07295004103080d0040704140b2041503403100020038145600b420800c14156104020303030303c03524070350709035000743e001403004001a0391503100800f111171001700000b4000b1f40300d64902e4208c41c0d050700141c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 781707176 1250 781705926 781705931
    0x1d150d1a0d331a010315051003050a240e090723181504060902030c1b03040b0d0b011d240903030a03020a09081501090e03090306040b0a060b130b2803 66
    0x21600d945c041c80f13241c900f442450304041d04107041002256503600ca45c0001c50406565a0000e0315030801d0b5071001c01e18003642a110794596013030403524520548a07000d004403502c42e00000c40c403071030400103600c0112501c0000c0315249011107003002040c0c032101c8509607080324146082c2040142c105080c00c0c032508a00340c03811b2516001c0010f02080302d80c2c80e0001c0381e50510401c10b2000102e00c40069540244140900903400c0200c80032140c214080d50707008248107140404d1018490120340c000181e081000e90f10150410301c43c4103c004640143d101c21500400805446890b201d80791b800c15000d58581e03000c69142c01c00a0011078a9030b03110490b5000026800b02d510342205134400e11000050103c8002450101c448410395003d04406105034850541c0c1c03640c60201010301441520b41501e0010103868180c41e041c00c1045c0d240000300c1d04086001d20b41f56022a00c1031005065480014209010040860502c881c5250301da2180d0024140000a0344480290204407203044100c00d070987d902 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 781708426 1250 781707176 781707221
    0x10020c36011a0304141b150a0c0b15031c02010e030c06060607030e031f180b0a09020a080304081015061d150d1a0d33 52
    0x54616040c15680d5400000d000e140040220292090721441c041c1c00d066120755490321039103040000424480c0c0070480034042c4c042c3d003042c2c1c0408140b007010392400030b0f184499650003150a00940344180135000e00440c0f00c00c2c050502040c81445060b50003050550700240005c00000043d2070a40184032024142c410101540c1c4c2c1a5420f026072100d00541da40254285800c40041988a280040c51940241030109040c8140340c0700d00c040188019010f01944d545110030001030030840c0c044c0c14694100e5041185501d5100381442e000054640c0003075446440380c4030000504042d1039469010380e03204d940320101080640c42840100010030300ca50042441009000c440c0064403010000d00514402856080240540000228220340d13070800081c40d41c83d02000006801c0da40680146040140118400c1b1a02e18107501c491000000c000b80010210b41e030341c04001d50781380c108500034000d40d501e10082c2304030200e804207048000c1c1c03001c104030380d1107881e000a0012190151050b00412100691 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 781709676 1250 781708426 781708489
    0x315010503010b030c0d030c0f0c090e07080601060912050325141207060e100f060503160b0f031801020f030103031805030601150c020d0302070503070b160210020c 72
    0x20b403ea45001580a007840501550005031403070009040a41884280110700c1d0411280c20040c41641c3e9201900081d05500c49034424010500180111214400c030745c000324086170001f9071746040b40d03141c1c2d9a4440190900615541e641503c48c000c0720b20340301c188074400710a5080b2400c9000120150b9a1404406050812000002140003010a150000344442e5000f00b012021158015003185020500315000814585030100300e00451034011b10b400b6503808030030269041034007210760440885110050509482030402114070501031407010030010300303d03203d140c94042c55102404040249030f003281650300609903489100510000440000140201a0402e0300e6101c100b9081b110042c0f06400d00307020236510301c010302a80c6411810344542042003403080981c0003182d6805804014400300c0b5141c081e41d11584c5008441c441d0160741008100c103450381054a20119090040142c111420303000e00c8480d14101c5201030442c02400e4114000c0e4581007a5488070035032200300603044030f6100c00b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 781710926 1250 781709676 781709681
    0x209130212130309050f030309150a11010203061c0305040b0a17010e130303020c071e081e0a15141314120d2d020d0c2a02010e031501050301 62
    0x3070240b51100c0039050b5110100b41c0c000c40030000d8070780a40c3d0901101d41907100082c80c0d800750380c0f0240c3c0d000c0702030101b5504044262000d001108640d460704642c1e146405031407400e03800109e41203038201040c801c0e900048845a00d151020602070b081461401c1d443d144101d100360300001226020a00c40a048010b2000a800a41c014200c004001000b404e222210a403015081407000c1c0801d03401245003119004280011002005d918a030905000042e11b4540243c180c5445000090301480320307290344c7e4040404800003054041030261120907955901c94011a04207007413450615907804043d091442c01d000005d000d169030301d90480604d015071600c801821440085030003241c0004060b83c203602a6502505d0201d110010b0120711040c03014018010351080d80241c601589280d9808058234280c0d50041484880490081c01441c12401080e80c0d0b2940c94030b105604400c03d140580305001d11290441c0010f44145010100350f0602000030b440d101a00502401c42800440100510319091 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 781712176 1250 781710926 781710931
    0x1203060b31121403161506080d090e220305090a060f1407080f1b010b0a0605040b1c061401030b0409021008041406040f0b0f091f0209130212 62
    0x20340c40150203a0800745408012510450000d06a0903c140c0106540c1014000d5886500c10004400007044580c1801400e00d030100398040c0d48a0b15110740814400d80114400703400c0b64041c1c130b50220303052804e5000e45000800070701114080c0704c200700d03114803a0040303072030010218060354460380c41e00206010401085c46039400102409200070204070f102e604030301004036980680d44901d454003c0b50078408540d110f0117143c0d000940002810302c428104161160041d401150001c011601180703080c04848a071a00406011600502081007100c84d0b0300010300071207580421039081c00401200300ca080d501d984d000345604083c5000c10101d1568580302c0c680b44010b0441c2e090148000d00e8010542d030045421101081020400000d070074816400c502041001c51042180d030700d8a801c0c1003242c80074001d040226428003004000c142c1d081d100250b49c0303004100ca035000d4520141c04103400b580501c80c40c9042c498040e020311404a259076100768032085030080e814050b980e60308400c40803140c407000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 781713426 1250 781712176 781712257
    0x1109181e070b161704031b0612020d2307020d020712021203120a05040317090d08091002030f01150203180105031b0a031a0109121203060b 61
    0x8814102100c600012000c0032505815030702595902803003522429900034100180142081d000c0c3c1380d018140d10303001841183d0041081e502c820514050a01c82c9035860703c00c11001402109032a07194400301d07270060901e007001980001c0d441d030200303680303c0c99069444104c421410006007041983c50b014000d45044049510203071440070309042e000e441804801030040d0107400c180407181c150410410482c1c0041c0e07040e4110b01a00e143c210100c00c00f9200450b003c034005160f60900543c00c4000c40704003405882104082c001d4070071020411100d200d00101904c2c003074407a80841c110824403910003107001e10400030105405604001d10a18003040e40e2010000310340c03040000d00038101c009928124081006d10b03000740c1e2a1548014050800c2600c0d140c42008680010140021500750f40400350100c2003543c604c08848c1f4400040d61008001c0c0300b210b407010646444c080c001a80005500c803198294240003c11980b40e25103400281c201014410101b1904100340c038407420042d112040c148072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 781714676 1250 781713426 781713463
    0x905010e010c030507140f0a030b06220b03040317040c0512150606030412111c170106090803040902070501330801110a05032505090f0a030f030c110918 67
    0x80320072441411f02c56240410207100b40403d80a404500c01d801140350000018802602c41404c2480580b64800501902c5204a10314030001010f10100c4150b920458064403a6600003180c003603d02d080b020002d02c105ca81005440b00401c60350784001c21802c1d0700c0d1a4800420001d01800c40d000090b2034003034001480341d40c0c140304000001e0b96410490182c1541854020340411028107007600d05108842249115032030190b810601c1d17903009142c4403090300e414694110305d90703075200309031101050303130007854003a4008010a1141c080071750000c0c4903003449240002025035500e11210500c080820300c000200400b918944044c001d07502614000c1c22526000f00000828501144042d20620207540d00348600480080c401c100615000c2c0354800300c00d6007001e0040c13100c210040c001d5000e54a20b80c0b144889a000441c3c605040980d54241c80e40070719030b160114100d40b0195403140034420110350301d2003030140c000c6a0751074680c9001d00881440a0030450380680708441c0d4186120b43d40800a1034030b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 781715926 1250 781714676 781714697
    0x501080c060c0a0c09091a01082e0203092a0f0f030f060f0a0f090b0402060f0d0c09061202070c0b0c10021605070501090303120506040905010e010c030507 68
    0xa4041180c003080002100c000390740301c03402c14001c0d0801500c0c4002400103503040000044005007a00941c121500c42c0c810310152192000309204912401e00034401c1170b41c0300714124204d00e0519110201803220410b08801005075100f000c0050340c1c800c4550300700542100a1190403100d0104103840309401c000486041001c1c040089031404a100016621036140180c103407946440070b102e032440e10300e8403000f503038407514215040d000c8420081c1c400c001d00790710302042c05035182000d00c5952031442d40402d50800a480d103400f000542e4015007440071a0810411520307400120740d10a401075030b00d107034584840d03443c6094800f514203650141400f180d5401082880005184201084140c0d40070030140c0b511400740b120400d260160840d400a921407000a554501d0030014041c5154a48a00d085030ba00c0d80e22480112400e8a8910006000c42c011940303006248045402403a03020002600000b5111020307112103007907907400c0d000038809956503101c01d980640d0500850b6440369203401d1039075540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 781717176 1250 781715926 781715939
    0xf09060f051e090621010c0806010905090a2c010906050c03040f0609080c0a1b08030418091e0f110a0501021504080d05040b180d080c0a0c050d051803010501 69
    0x11982c80b00224802c886800c009003075951007601c0242c05880604002407805241c0010074001c01180c400c0c000801c400303e000805a61140c0390b0b44040c0c402c060700c451055161444880098801801c10740e82400382d002d01e00b4419a4400c4e0f000403061200c10011582c9001800c04504172080035110321920003040007000003061501038407041d919401070b40020710328464109444107004944040b07072140500110310003440300c1503801c2052600c003000d003000e48a980d03c199035680d00c01c900c143d0307038908c03c0810503000315034195001e54501303409a00c001e682c034820706604c4405c2e00c0c501c15084884510311180f280c180404040800a030403402c0d03c800c00d803070381427000103559405120750300015403903500c0000742000794140540710380e0740c0301c8a818400c5040c58600070040d8542260807841740b000c80c421030605076500044500710190251100d43e1580c5031a44400090781c80780100c1c00a01000c0b000a00c0007880811407101040681c1e952640c403030b90a02d00b864540f18541d15841d00c280c0c1040b0061240c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 781718426 1250 781717176 781717219
    0x120610050a060509060d150f03060b090f040f05030f0a0f1206030809040c03061205010501081209090c07031806030c121b11070f031203140702060615040f09060f05 72
    0x28244100c8003661a109401c1c6c9404c0034042c0c0c08040040b000740300714000f8510032068078020580b403151006016421094040c84079904088402e840740d84a10008100030403038044100354554001d4058070320b0004120001c4104d5400394034408006982c1c10b1039000100c0d800034010083e010b000409022003890358403010b18600030042030701c1c411607a440760100c02c54000e41c45403005101141142d1044136281c185140285424411a07c8038001d0110f516110140181100c0e48040d00421100d82901e41c9042d2454903000802d0860610440880f0740003030842d051071205c0284181c0d5800700303282c1d052160080c10031a210002c0115103081c42441520107000180c201081c00c054581002000d01c1e000b00e082c900041640a808401d0306183c010042c08501502d5400207036643e10148050303115054598030310ba60458181d00140c0001c00810301500c6c5c9440510310740310f42c6200c050f040a866811300007540c0c4460303015660450781c03944c04220405200362880f00030501103540f8001c00d00c880e03e04601 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 781719676 1250 781718426 781718437
    0x120105102a0f050312010e0103050a1203140f0103020a1a0f0304030e0604031104050c0a02030307111014040605090f060c0f160809030f0d121a120610050a0605 70
    0xa0140703041a2118440d610300c0c02840705034015102202c1c0160a04005441380c0c01250102c094140c4900003040502001d07828604a039404401807044d0748403911080e0101c0c1c000c0300740400701074648960400d542d108001c1d66005504410800708254514410803440072541d0341f0540b60298000b05440f4140082c00650f51212500100d5598954640ca01210000c21000000350701c07020210703000c014004202c0b40e41e00200e13002c1d1810041a141e0000c4a040b45c012005040b0042c0d2041000901349441005c0c41000304040c14112103040d0030041d075540c2901c02541e01c6004418a4000b000240300e0940210b80e0000e071014041c2c410710028012440d02c81000800c0c5214490001451380410300140040720003140d0382c0c00e0040207520b403d1600030495409048200d205e8030134800e80e0102c0d007101050480c58100300342ca400206584214907200900922003202c1c801e210ba0740c030140d1841c1c40785c030350000c40b0290303250141141c0e240c0410105079081c41c0d900410b0141c0081081480390580000c111341 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 781720926 1250 781719676 781719707
    0x10b031b27040804091a06070305071505010b070611030f041e150203011d070909090609050d0507050d0c0827040f020a02010c021f050c160812010510 66
    0x40d4040d42141c0d80100100103004040d46508103a02040280801e410140056802485044c031241d10b02d013804c00c2182801c008034660114040044a000074042d41c024054039204600320140d002c50f4541c00803c4400c2640310002e900c40000c1c469041010503c80d0541c80303070100ca106070650411002c0c10041d41e030020002005144041c491900200c0324549840c00d29602002c0d1404610910580d0000ba400a2013002c1880040042901007036525907900d9104041c1ea40d2100415454089440080c04030688140c4040d50350f1000c0101140c001d00c40403015031401d4555507030b20416450700500d807584500c032440c01c1002405c1c54030300040745641205c8015a401e9aa44041108071400c858004809403070180c2c81440d002119019038600d401801c5000c24940003008407680c801420b98a55101078111000340a100b11080c0e040c00c0306600461700130394110707001410314a03000209810401400003d840c0c40001066000408905004a501400d4152485801d0358098a40503200b1200304043c0b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 781722176 1250 781720926 781720939
    0x902070804090e1507020c01080106020307051f060e0a0506091f1401090905071e090506161e150c0903050c090405011104030807170301050303220f0305010c02010b031b 74
    0x443d50307000f04024541c0da00d440c0303030713044c4225050005000e551108480703000c0d400300f0240b03000003030014001300c01d0300c01ca00c0c0c10101400162690010100b400d9401012000540369905030125210407480c2c11507110b40003551001866007005001c00003904801028406500100d1039248200100342892034100d50f200c0580b143d03c2c80c07855005035403d90640d00000300d080c1c13400d4100711115901c441001c03400c010302141b8030b034a8600c0c91700c02c0f10598464090a50031032010001c000c00c2e460941822100240103170a013000a00b554400c044c0301c00c48241d019103000c0304034030607001403218600c0796407002e030b40c2810300441051556844985807140c92001e03034400d480070710000b010302000307410502240040440d013aa0301c0341c0383c0c40c0103103150304104019100050702000304414407424008690583c1d00080045003400640b80f5050705451040c20f101c04480301c515400500950480d6602014600c01c0c1700124a4061201c8004c0c211000360890314400d40c445030f8502856107000e00c090103c0001604c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 781723426 1250 781722176 781722191
    0xf1202040209090a0c112a040204030804060f09082a0f04050c0c0601091406101e050c0d08040209060607020f06031e011a0d0b0d02031c09090207080409 67
    0x36000307004010101d40c00c005414104029050300390300080e0481c03003a4031404c1c0008031442c0815038810208029007030341c906128010a00069440340e81e940301000800140c03401ea200d0f1341e00712a075007196020802054007280815140c0d9044030140024004d401c0051000003400b692251441450065801d407440c103801440ca07190b01c1d40170380c0003a500030140040c17111341400007441003164010480c40409001c2d01b0008036840b00315000340090180011400307200c80d12100104111880b061071080203000714003a140304040d180c5521600c810480d6250141c451103000d0100c0d0409103001111820446100e08210040e40c030a04850b40205003650843e8071b4211610118824190403000594460008010488540c01880b401e600120a09001c0c45960740d84150b06103006021001382d01559506000f641000040c1c2d83c094280c10800624035007001b1a99000310303013400315441d403600200e031148800c1401c854001040c0001021480c200310303c0c001c0640c0b0f03046040e00a43c0a00101d283d1103881 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 781724676 1250 781723426 781723429
    0xf0c0a030207050f06060103060504020c03041403071a0403030f2c010908060f04110105161203091203060e0c16110105210411040c0f0f110f011d070f1202 68
    0x503100b0442c1d1001c2110051040f0207602d50343d440c422101c55001905090000c05c0b1411300c0d00944502100b160000c6091a013091008640104e068000a8252003480e2001410fa01c1207001d080007030941e084025501c40c2141402098404102040d100784010541d03a03030345a20803a000402e814160720706c1d2102d07011118004076204c405981c0000007510807441400203022150f0100350150348070341865401c8440480041d6010300403280e28010340a00c0c1800300012402094001c0d00d82a014540020508915901c445a4800002d000b500203236072030109009101c041c061a81c1c0108c1a118560300300542c080240c07180310208800241041c0075140041156405881518036555050618a0020610550801c17010030b0459041e0794404000b0000c803420300381881400c030504c0c4690b40701400c0c400c1ea0041500c22460015880c010020703202255950b40c5c0040c4105140642107800209440e600c0d1030b4241000c4180b200b13520b2140d00304007030070002c040c00622854100c40907030740740141080c400e00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 781725926 1250 781724676 781724681
    0xc050702030c0d06110f0918061c0507030206040e0708070905031002070816200a03030e0d02030c0301020a1106060a061e0311070f1b030b060409170a11150f0c0a03 72
    0x44031040170340c1c40800c1080d40c0100caa00608a8081d0a54624801c1221070445400301082030f0b40340d9802c141080344c4148100c84261040325620301441c00c80e001c2c1c90b5a54086410360380994005101c4030f030310f241402662a4030490039a04074940e032605d21f1000d400c2600190300c60700d0041440702800e900064403820425204182c03001100041300034048010349040c28090111000507403c6110480c0030008400c1c9040c500c454243c1c0e0f0103541d0a840c0c1d0a07207030140101d10105610503a0b151049442904069500b400180400d80090380c41880054000001502d807040c040c140d94464008004240410740c1e11070444110b82040d41045845c000c02e4441c150018404908150309a01d0000340a40521692120007034405215110300c0c640c0080024200440e24414080181032002c2d000119032145056088185a01d0140120f0300c89419050795807400c641c0280d4100000c640030035144410300000b840340c01d01002e4007050305a804e203080411044000401028455920302c003150b0341c0d81103417195 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 781727176 1250 781725926 781725941
    0xb060d020d0f08030910110a1218140c0a0311040b12060c070c210b0604320c03130204050c1902010608060901020f07021c02030a150c050702030c0d06 66
    0x903000a0b00050f401c00000310b0344115036000080c49000007000804800c0c0c0301d49042c22050100726410305070301030803c90391000c141c0100550140c82d4522080c2d0030022000b140701642c46481a00401459203a0a90a05c00040d0041b0f00c28145500100040342c0340720140030036900100c800144c8504100001003042c8140c01c82e195407841b5400400100042c81c0d40181346c40c60044da0b1500c41292380380c00752035040c8001007903442050400c02d19400020501d2104d150000d10040011031003030081004840c81d12001865038406030101100280044200004980c0185469034041d02e503180c01081c82c400b0101121000703008139600d600088011042e541a10fa00a43c0030700c0c400551000140300138003808d11405070080c203003e258081001e4007014401c40c0e200103028004181040c549408001044001480850a081c503041c410380059409002c1c02180e144903442102414400c00f55032400c64088403619000d10008009000c00b50390006490010701c2000c90344800820028a401806000c01307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 781728426 1250 781727176 781727183
    0x20406030b040503070501142806082505060a050304080c01021e13050a0f38030702070b04030b040f050c0a0f1a030709060f03110f0406110a0b060d020d 67
    0x840042c001001000b00c014418180030720020703c5400f00c441e20766200c01005940803a40003101c596404407880d8180754011944144c0040040c45e00d03030701c0502c1d03411306c41417001c2e505000c0c01700f412918030384044401c4240a4031083e105c0034100ba4100708083d00b50300c4081c001a020540200c4d43d04540a0309404482c00324035581c508200c02c1c032888005041d541c00208848000000c035032004201070409280d014200e600358000c1035090fa00d02000c0c54100501039489a0f08420081690301a0130302034014030030301405600c07049503646000a03000b814204140c200c0800e15004000410210311400703856500641c01480c0103180168a1621625044a042f92150400c1414400048000407498010304480ca01a004202e0b184d01c90716017096440110769000101c0c0d05410240100c038804d170320101800c080350074002020b950f40700348500c1c16000081050301e510f000007414131a4990100c10364142d00c2e01d14008040c00c48042d59042c0e10028020223380c02500d6a0340d503802503640e41050705440386e41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 781729676 1250 781728426 781728443
    0x15050405031b061c270b06180a02070215070f12020604051f0f060b030a0f020c1e07080a05010b10021911180a0603030809060f060f0424030c0501090b090d02040603 72
    0x50306224503004070405d01095803c2d05182d00000c1c2c0905141c15903940140c21103181f01110707550003940e10300940010000f41d03008108882c000d8403014000000742001401112051054580d40c54050780000c400080c1400f150070401c10304c0700107000054460484512200744105013482c005052008184450100346507504008000684950704e600a50180ca00041d0a00112041c143c1c210160700c0790707516010244d88102c0380302e00604842d0440f03242d02002c80041d40c104a0ba102910303480c4c00c040754800e4030507943d40c0100410310f15107118440c90b50b2a1a0002d0f1a500c40302ca4801000c9149490014140302d030207543c40307600395550705413143c2d8910f1210203180c1e06050000c840f80040899001c01c07404104814081080c01d403000602510030442941441803680e2010284031040e590b201c00640c00503162800340d00d00a07048a0300201e9240716a0360982400d02d1401c1c0b008d40304001d0350002d810302885041c18041c2e0b100301021102d100e0001c0c0c070a081e0002d1a0f1002c2002414241c1c800360004d172 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 781730926 1250 781729676 781729721
    0x3030f09120305010f030b010902090a0312030507020105070e1003051504090b0103110d0c1a130312090f26030c0102041d060402130909060615050405031b061c 70
    0xc9204681c01448195070780c10056a80c94000060b0280c0c22800301500c800326000040010000b542c0040c05d044001070075035621540d495031520f0b0250420742c0a00042a00c0ba001c1202c040c0c0d092003084d0307000c0714501c2c0080071aa105408a40e101e8200070012003010b8a40c3e000030060552110b040c1d05e5a18090310410846510781030029182c0401c4c0021501c2001070240032145d4901020550714458100d03120f140307080d01d040f4558015144803942504036003014400860b0011041c81110300540c01000d82e06074012050b1302c000c10780007158101c0104440c40b0f00d000d20038420701c05c5400091941c0032100040d0300503402c1041e1f14500410103a00c5480d800020081594005c1d12803080300248401d600911686480c8104400ea001d03041044610901c0628100441015600b01038455030050705c0002d08a07071144001c08101c070040d49030b1408100001820401e40c1020001a032012046494039200105047d002840a1098800b94686052100c0352010b01c80b1055209a00f0100c40c094104042c6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 781732176 1250 781730926 781730933
    0x1030e0717070315050408090d0f081b0c0909071a0c1c081803030f340e030102030108120c0f030d06092319020706180c080a0b060d03030f09 62
    0xb8099030008482070340e80551950030300c41040c06018019548114064148020b1307505011050f00c010000340d038560f4425030000c0100c0d00d000700401c000ca4980c01d00c0d01000030707460005c900e44101c5d49981800741d280c410400035125004103c241c1a200440c0000c00d100c81c2d01c460b02d40c0170b405800200c651302d00440d10106e0503441101d01e82040e185150705d0703040c2141d403448440c9140402c00b54600b00035800400000301c0d001c0c0c07240309107039111010200300e60428200248241248501c0155403410036001d22080481030707004404410b42d100120000d40c55981081310b0243c40da9203c1d07520464401c40404d40411450b000d20140c02c5600c0c8413030840340c8680c1c29400481c0546031030302c1912441c51500100c4c40b1615411034149410801020b490045603d030192103900c3c0700e60601e81090b0b545c1d401d00903400000d40780c0c001d4959203010a4006461901da90412550300459607100d000e840e4002d03410f040011b051a0f410b941e200c403086035024101c0c0d419003004e8020302101c11071040d00d940340c040c984082 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 781733426 1250 781732176 781732183
    0xc09060d1406090115080106050307030f240f050d060b010c1a150603041a0403051b06040b0609010e0f090c09010b0720010c06090203011b09091a0d0201030e0717 71
    0x1030b2821079640010307980e80d481140910440b02048000550791100500c010750140004540065a038900014490480d060400480340843d00004c400140c4046c0300b1b0200c19440c510b100034101703450541903458540b01c00241f421504503c002d26840d110307880038400c0da0056141c46100c94000c100f05080c240d00181403c14514203c544ea0031621000c90403684a04164003a80c2c441e46c0c0c00001c44101d290b48200d4107288500081c0103c041001c10801052100d800c070303c2c00000f0300600360080965003050f152142649130020159030051503000010085403094018403904181043c10401c0161940c8101c5410418608100d9030840f03070150000a401c8042801022042e0040e000300c4e01d41c4c0100e4603808403050740d20b0010f41c00145c04135204008034110398400d802c1c03148010000100e52922400d6010000308800005010824005080140d60418001e6a074858040840146403480d00b50009000301e98820000c0c0c109940c03460507001c4401c0400801014041d00030340c500002c0c2546881030303074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 781734676 1250 781733426 781733431
    0x60f0e0d020d170a08132013020a0302040e0c0a050301030308100e010f08061003020f0f03100c02030910050903030d2c030a11010504020f041e050c131d0c09060d14 72
    0x80640001480c6108006e0300090b03042c1d8401744405c1180c3d401d01481c54041490001c0f942d1040240070198000446440181111801510090380721031904140b40125a0f004000030441041000000c0000d42d004080b02d054a41c503040044041e2220b400f0078480812030b07001003a81e00d00c084000b0a1030010654958100c0ea80c40007225580c2d500c0c80a035a250758188d00c4001c0d042113603124500a80d182c180f41c02000d104001c0d0407140b40380d071003c11b514280c80c0e50050103400740c0c00004061010303007420b040d480d1000509042040c5002807140110782e03230344551090440c0d45a0f8400c20010072030302a80503848200040e01e0004a100b0384100442d0712640b004400c000407940d00d4446202c45030f011301540c4e09c907580042940b01c0c0c403180c0b50244009018110203021380c0f5025038607001740304a441d1040c103020307604210000f611070742080e14004003200990488000060f035500c501c00800b10081a540d8405002c042c0796072074520b210040380f40d90054000380350341c030703403c25400c203e1070703001880c0561 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 781735926 1250 781734676 781734697
    0xf030409020301300303050703110310050102071d0c0310050d030306090515030303011701020c06070f021516030b0f1003050f01090209100e0a051810060f0e0d020d17 73
    0xa000000c13100c50310248507184604642089103864581d00400c1c000c0d404a9480025400c010486000092500020b54000c46440554201340f440a00240d41c0c1006844e01038644c08940c1059050407007a202098103008024580d00c4000200080c1460301c072078842c10003084082c00c00300b007008070f614019001c0d11603405948c1800703140500041031541c0341650a80006000390246280d64241036203810a60a58890003a0640d020440144103100400002d03105800301d0351b8050b0340c0680540c0003801c03c200075a155141c605100f00384407031039070081150580114a4100003489518044c04220862403034207680358012035400800b44065010781005201c1e10100c494809142c1e25858900708900495050311b421100c501d603103c0d0b4031400307040d035400303640c0008216805140e91900003403041c182504c0c02c1d80f1136000850500900e444020b42007030150200f4103080b94110309806000700441002c03052540316541c641e10a20a5450f001d43d40407801e60402c3c8503540101803c2c108101c194403400005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 781737176 1250 781735926 781735949
    0x60a121a0c09060708210103030f17011a031f091a030a030504030b180106060e030d030c080c1305090c090102070b071e0203010f09110a0b0f0316020f030409020301 72
    0x30740301c10200d004448030820010525414644140c407410f110760440780744000c0d0700445004100d6003c03081200240210303c0b0795248160440640b0340140f06110341d40540351001e42010041c0720b00341d400507504281c41c440141164813a40c960407035015298000e032070b501603041420004503400820b40c000140043c038811011006030b555000381540c61420f0003002e40010400e00c001e0000842d2181030070f40000b04104105040341c08040d905084070720607030040c404190f001d98031400d1802d05008114800700541000c0010f484400030203480146c000b895200c00700320001d07000e041ca60b00010000007524000d0050f04680c075000c0e0700171190f540110f8000f40540305025001074140142411520007541c00b21322079580418186415100c00703000e20341284d06540300e1800088040701481070b04041030094070100c41071241031050195080c11500410440c580401c050003011030308404032608400c03961155142c4040c02c0d10101c3c24240709600c0f40041d4000050009480c0c50340e0740245050342e0418514 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 781738426 1250 781737176 781737181
    0xd0803060303090409030e18040b06010c020d060c021f0911010f0324052119030908100b0f01090302031e0703080c030a180302031c02010609060905100e040515060a121a 74
    0x444000d041254014402b01400b8001822548145000246131344007500d042903444081c1e6070b6405592102c03589600681c040b01710804003160054a050605602203010003039032405071958400040e00503126410f006007081c0000c0880c0c401e500c14038049000d02c004001131250558601e0002030203100349881500d0b1440201090b00c500304103110385104402c024644103011700750300d500341110294160300748031000e00001900103043c8588141c0c00c200d9600050120040010001d00001c040200ea04005202c0000d03c0180c80004001c0349004840c2c4446a089222940491810300643c100070980300c0d01044501c10400000003401c0c1c81042616110110164100407805100d41e40c40040c0d80f642c0a281c4286042c103105984052980300780c40007080c440c4d210001c64040d0b4400c1d6010303100140c1d8500400820700b0b445811607015110792404183c190030070f9210b02d0341d554048003412581c014450081241030f654071802c1030041904d98041c144515172401c0103a0b142c1a41802d207a14201076100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 781739676 1250 781738426 781738459
    0xe190e09070f06111501180e070803040501120e1906051b07060c0905090118110307090b030a0209030a0f06050702120a050d1e05060307060e0d0803060303090409030e 73
    0x446609607a00342da0108001d03071800310110380d126801c030f040d03c00c2d500828401c000a02d00c1c2c03460281c00b805640e241c802c00c0301c10840b010b900300d8080120284198000c29070510010b900842100c003142e07030901c0c040c00360500700082e007001802c0c1d1410300152840384080e22403140b00340c001004800c5004410801055980c599860f082c0180368140d510106c800304038690020f20141c4c098011481c0074031300304281c00c1c1c5a6010403403a0f00203821040c2c01e100c1c013002c0551454a1401200004402040c8a0b821410071120103031a03603200d80036560089002000040700400c081c1e06442c840d1030000c007207034400201c508140c2da40d0b110303808040e101141480700052480c0e0000070f40000c2c1c02801c0300840e01d49403541c0803c86042d041140e90800c1c040d1180050350720201294800d940200c40c00c01c00081a08104042610f040400ea10031018000d80b03460040590703a860380d0700090f894104110742e5a9a40c0ca400003800c5100302c1c0d898541c03013450000300c40e05155009640d41251103090300d0007200c121280a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 781740926 1250 781739676 781739683
    0x132d1716080a02090a05010f05011b02041509061409070e0105070c030803250e120109021f0201270605070c08070c0515070203060a0c0912111c020904030e010e190e09 73
    0x203232801d091807444d0200010351044010b00e88840d0a1440d400c42001030354001405c0e5020707542c2d00141600c3e810300c01c3c00401e07034501c100b100034011140a81076009030b4501151005800801001c06d0041d41081d030001079008004072880305500003800d030007050301d034130300151141c00036100300383c103080614240d00c0f10501200c0301c40c1811856850307460310800d94508102642070303041c0c1101303165521018113000503110134902c045003014102504200e540c0c0341314006d00315008060f405001c00600520f407000e4088007503043c0142604610041029500c00c0c0060300d290285041c01418040002114810310a22016860a94004942209000c0319050380038049015208000e585500f02101180303644046034080c078103003107503401d0502100c2d40c0c40824050344034401070244c407840396a2400b60381c18646041906110308000d642c13103d90440c01d8001c500e08900040006082c8202032000c400c0d103a0141a909424990080401d5180c0f00355042100541c241c510032000b20403041008078580d10b0010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 781742176 1250 781740926 781740929
    0x22060807050904090203010e15040b060913060c0203120405010905010e060c042102120a0c05180403030b280302090c18010c080708132d1716080a02090a0501 69
    0x7035441c02c1c1441615800c1100030401c8150032030b132540d611100e6655a48080c0800304081d00f000b54000490318090600d014211001010188584040000c01412000d0b009109441c4ca42211001402e1108440160301d580701c0c990380400381103800c1c8100020840150015410035104000901000702a17403410341e0340c2c8109580c15400c402c002d020602103150000074443c0942184402c0f21000c1120382c02082212600043c1103041e030304940c1c604400e10401c0c06031180241025503c244102110f001c0000c4080000340c401810541c41c6e034140651540c3d654500b00c2c0c0124a0213042c03103104c0c480d4203c0346102c062448228000c15001c4006140c2c4242c4005544c4000c1002d5030642c81c1e580e00700c004550300030040000b00e0342c501c0103010400c08914804090010300e00c043c02c09603e101d0030501281c08240180c1c0c044100f0301455007045140d0803c0c403034001304980030400c190521500b00c542e43c40c01c061243d0005848441c6503840024502c0000844c402028001d4443c121070791540704214090321800d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 781743426 1250 781742176 781742191
    0x1401020f07051c1a012907020303030a0c0c0c090c02011a0612071202190e2707050702030109080a0801150801030f0c030b0f090606040e0c0906060f220608 68
    0x1d0300440451194800c18200203144500184024000c142d0741070070a1600a800003201c4a00300c0c1c06d55800004041d034001145850b0820942c200070103640043d58900c0024079907015184c4890000079643d0186250001c5184c0c0010b00c048420780b6203000000421140815000546c24102c0d030303000d407201c00c140301410024041c141d1031501505448442003040060200803c100c0751240082039005d0602c082d02d1003882c0801904101102e102008042c107460418082c4070f012901e1442007080120b404002404001c1e510b100034a0340da224090380c07180208200650194244291601002104401003001c00724944030180703a1b0341c90f840a900e072003010843c040701060380c110042c008540c8540c0d410001c00e2040050702c00e034a4495448103150b80e4203960180f8001412000d1000c240c0d014008190301000c03d42d820440d9004203540282c3d10344460b410207014403603038008518076803517240c11901c150204006061b9240c0c2c960340c810a080000355800d483c149103641010508502c100d5503036015000d0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 781744676 1250 781743426 781743439
    0x6140307052808010b130506060d0903021c0201050603060106090e0a0f0612030f031a0d0803130c080607090b120a0f090203120717070c0605071109011401020f0705 72
    0x244030038800e00071490040002c050140b81400001d4030b640d0290707500034020500c0003041e202c00e15401c2c44021080b003101c0305007546c1008200030498440400b5a0000ca80b42c0e44c0124811296080c26418800c01075803031078038843e0040b00305000315015003146000d1b5a0a500f140e01c503a98600d01110000da041c0a0f440603030342c4520106d00100d4881d00010408401403600003819591185c2444401207400c40c21008221501150441650944508480901440d41c5820f500e964040018401d14590300001c00382c2002001180144c081c00310a403050551020007a859192503280c4559107640403a0400d000950801d408244074030400c0c01c0d036906074811b45a111f61500c440d840c00d0060441c80d9008030305640d8441c445805a0350070022015814010080075a41da41e060500c2d55030f0030029040340070110020084000004d0b2015801d504031122445d02a0f1a006585000340c04d0040c1c003100641e00004c100000300301d07091840c45941d4104826021602c24150ba6400d090b00c031411340c40791607403210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 781745926 1250 781744676 781744679
    0x200316150917030414160e07030504081e120c0705061e0f0705070f060c121401150903060c080604050708040f03053117030f030406090602191206140307 67
    0x70101c0700915049845000361446007034180c0301042c505054015510141e601001b41088a0a022400a43c03c40d010b07203800d200c03a20301502c45000707504c290f0383d007040c04c0401010301645422042d000c0d52608018207550f000700307051800c00e03948141c20004080d07509000344030104500e11f82414103113400011800101a803076a40c001a25803004d00100484180072003002040001150741e08200525445408000303a060700c0702c20010040007440d120182090705d001503d910b00408200d10b62b045901d0200200480c2d1002c0000b06e45044055000500c07075401d146400f040d00fa048403203148902c105840820191351849800c554066003907034060b029400d07001d40703030020034070900080115540100c2d180f104020441c10000c11306402150442401d5580074090212890741002d41e07190011800047d414001c040913481054030000e0401012150f880718110104030554064841e44041301114180c41e41c11001c0240000100100f84900c60b072a1800125514070403d0291221800140c010b1070040e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 781747176 1250 781745926 781745963
    0xc03030f08220309051008040c080a17030702010204050a030c06031a0618010201020910021c0903151e090501090212060c0f09040b0d03050c07080712032003161509 72
    0x741e501810f404024910202040c2a101d011400c0c68400d41c035500c0c4d403590310300350400c00c094001c3d98024411540000c11181c002c03888600911040f591401c1c02c1c6592521071500590092049074411034104144e48000000d020b111803a1500b1145191030030321a00c00d2050f4016611300d522307145aa44040203001e5a5190111002109441401800014a0144001c0000c1e0020010500d00801a440001c1c3e4840012600220030104105c50416201a0b4255615141448501500e44482c0d6076208003012000000c448032001402c20904100112012400c01d640a4010654240c1c011a610318141440b00800290380f48a900080c08243c28203903c14880c0310294030441000d40c1c01915525003070f66030f0f91401124010a8425110302d590703000c10010340341c10316400394441081900411810846c001c0010002c520403585071501010707410403010000840b507158139848100d4403011442510954a003d030b481c4102e405880d822400c11413040b450b038150344142d48010408001e194000000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 781748426 1250 781747176 781747231
    0x60f03050c0708090a09020f1e0c03070b09031e040602060601091a07110301020a05030105032808090d05060f010f09110a0806120a0f0c080d270806040c03030f08 71
    0x35440052110b880b440d0790354604400d9820034401c1c900840c0c0c0024020340c089d6100c2a81c120f01c4a151460b9508004006907440c0d200d0140c02e801403e000c98a10000c0c0366008144122007240c1e124602895000c90f10805100341a0054081c40002d8840d603c0031800343e42c01400004100c40c90782c5031011484070144581d000700d030000d08003210000364400c01405156070a002811103020b096907843c0d20f030b62412081501d0300a01e81141403c403580444903898035181004480d4403240c00001d07031542c8540b004003003540701117591b201503c0d0f80510420300403080802d45509040710091084099659100c01d500c10031030308141d841d06051101000003904440c000d080c0e066022000910305101c6070f0401c0d446074240780e4117003000c4404c0c907061152038040104040901e405441100020041400740381c90140502580040c0d00c1840b885980c0780841c81200c031441d11024001000944007075007803502d080d05880140340022000709800301104c1080c3d44c8560b0ba120b00c98000d601091103080d1000044411 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 781749676 1250 781748426 781748437
    0x7020a0608090a080c01230a060e0408161a1501020c040e071505090303070c0e10060c1106130e0405010e1f0e07090c0c110a080a0602091c0c060f03050c0708 69
    0x40035507c403e042074426001d51000c01d5442e0058446142500e08000705004580c810740009110f0346907102404080b6080105a50034184d2101504e6020360711030404018501ca0315103801c6a0351060410040c15810520000c01e840c0000c1c0c08951840c41001d04110070399483d41c0c015142035000110030018406c000415007854031050038501e01c1c0208881c0400d00319803010303601703880d01d840000081050302c142c2d040d62580403c03000241c412050a01d100100261108900076098007071075051003185036620340840ea0360b07007024800720f40010307992264070340714103400c86007a10316520b84945000a20404195900c207207065600c400306803404403192100500600c4003113001d5114040c0c011801800b44d00c03c07004442c0c4561101c0300c051142d841c000c2604841e00c2078641c0140e002280070444003500085480040b84d00039405600c40d8030318000310b4981001c030018110703401b104569280c00d003c1d4019001d000d40d21169907007074113205a0b8006400b650403c0c0c400c003110b070f1020030280740410000e402410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 781750926 1250 781749676 781749697
    0xf0303070c0215040b031f0f060e0d110901140103420e010b071b0302010e041d0706030207031b050a03141c0209010905090f01120305070f0807020a0608090a08 70
    0x11308081c0c5038004070110780c104442c49041c1c40002c24030010311483d41c202c0c500040c981d0380301f2101d01d6810000c0041c040c0915500050140f601c0b8032a0030304020810003000d25525001c0e00510b01507a4494a00d0700600314400c206010070300d00300c1110038161140084100c1c1554480380c0d5490503008a080100702c0c40c0d0b614007000000b0b111800807500842a80da00c03070003081c4d82c4a102c0e803030308041d080001e20340588181c0c40c207280d60070b0041000147d811110000c000042100d0000706600460050b203c001c240c0840040c032130250a2010034175a4142d400b80c0300b007d01030f07500d500e51840802e0640c04a80f208440c00b4015071f014550240c000380c8601511643c0400702d0348102e00345120890081c9400c4070180011070060380101d242841543c0c48038860340142004c60300d0f4181401c046c2e0000200e60018046c044003c3c00e800401c80030316001e10104c41c0c410354408409510b0300d0303081c10080a180c1088800301d00c101d000803400039600d4131580586000f0300c0314a001c2d040302c0007a5a50305c3d000b58800b80310702 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 781752176 1250 781750926 781750969
    0x1103010302090618040308010e070206041a0c130305030406140703080f07030204080d0c1b060c060b0d1203050402030c0402091c140f010e2b0f0e0a170f0303070c02 72
    0x40d40c03031000c0d001386180a640300751544040d550412103020b0401500030704036070031584802d0030030000c100100012440b030710340354050f0303800d9848905000303a0503c50134446505100c441d410000c20083c000004004a0b06244d44011880e16007410015840c8140003001d000a01e81c04e01161494500a0070103411481a08006140c20f03500c405140c20400d040c000c0350f000c20507036121002802029100030707800401c00307070440c0324a80c10481c001c1c0c40c0100846002c0c00c8142e4a03401c902e0356403a0f00c002214007940104501c1945002000002d0141104950881c000d0007080c001055600b0700d07000742d41515200138000081100880017058509050782c1c0700341c918044605401650300801d0224588000c04180082194140c400d40c09141030000c038003240158840d00104020500509103c601c0c4031414908150f102c2c10000c8101d4250004083c1b0ba82c4c842a03440e00002c1c00101c05d4211200c1c1d400140c25070300d603400351040b0681c50740800c0741c0c03250114004404c1840149860400c51078000c040ba03024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 781753426 1250 781752176 781752199
    0x3010f110f03071205010815090d140f040803120405010b0402161104060e010612050f0103320d050703020105060a060801091e18031403190e0a121206060311030103020906 75
    0x70b202034913000e03401f10352107411401c0d0b51718500f08200c9040c1e9101400100404070105154001003130104420001c0900c42c0c000306610004c111100108d034020100c0e201200d0320b840e07260326210340341c41080d2030869140d0700c0d1003c40084c07420036000340d5030060524004600c40c050607031240c81694064107880c1d40c0c030594500d804110f00f070718100c889020f49000d41c4e40c8202c0e400c20750840380840d00c010300005817a03441d210041001a0007502c0d5403444030309500b1501d05000c00340340071800e2681203031100b05040c001c010b0303915100b41d4401c001d8004140694028451520f401c018803d103440c590107103000003007074071006000c02b808a0700400c10020090f910018454102000e1760115581100c2e5207048090070144c8006041d440900d440001c05240f0b4414070b982001107502c10400503d5540038012500e86040f203403201c5003485000da850703801810103098070303c071280020131111180e034111080b1441c100000c55964441d100d403000611118044a10f03603420341d001c0000000e001001d4541c0841c07510b44 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 781754676 1250 781753426 781753457
    0x180d05032e0e0615030103080405062d0703120506030c0415050306181e0a06201c05160504050d050c120109030f05180f12030c0303010503010f110f0307 67
    0x541c24020800b0b0b00221505092410410610140780d9000c0d00a19900b1700040c00400c0b5a003040750700b100c0049802c103540301036485214012485c02104030400c442c02c0d59440c40c80510b24402008814843d560f00403a440401d20b80741c049401c10b503500d9405070312102c551806401c2c280c0c886003106101c07242103030006075190000f9190200880303019090499400585102c0d160801821150011a40e06420f018443e0100e240d5140100314000d4030050710354424500c000e6012200034072552500c11180d07602c40030845001184c1000d49400601302c4c3c90031000615040c0a2242c241041505584040ca840d1030316040100f00f00b074004050f00d0f140502d04110800b0396031603000603025081403002044505050402078511003c0001003814040f040000c0e04134030001d13404c40c20080f1021116503000d000e101010503143c04101100b40060f100018099000d103000202070b50488804800a02c94884001c5039442921005110420100f00c01c2c8110500d42500b04090341c0e00c80380324580000111038140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 781755926 1250 781754676 781754761
    0x1704030201021902072628150c020f07060507030507050313060207030b0907050a270c090f051503040b19020706140a0605090a110f040e180d0503 64
    0x2810300145e80102004c00c0001088036940a001c5000c0c00000c042d030805141094541c3c983c4c80400f05075a00003100700f1034179200204100561b40e000a120080043c007001944000d140001c0f458000d0710940200501c1000b0001d50340c0d0540c0d20607030b101802c0202568007030743d994100d80c40c200c03a640001d0000d4001c10425000c000010007180e40200740003465400c00f04181c210103000c81700c01d504407500a210a45803606411308076010b2071b64030b1b48500003100078192048043c08036082c0403800c0c80c0d910860594801800020385910100000c2400c1d620720400100154450084c44020802d100007000302e0135802c44c42d50b000800d108601c1004428081d41030482c0d0001d0411140706a848807020091a200030b1243c0d440714059004216050504000403808200202842041500c5a0a10102e180c10b0001e0b0303880040d00c4a5500c0d1680c0c0c907030312040c0800c281121821404504617402400c141d6000034100e111200c107403210740c0703540c0707423400c0803107410b0018004415000802c400c01980c104145 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 781757176 1250 781755926 781755967
    0xa05060709030209070207081c050c010c1d09010e1303110304030507030c050316031205070204050f0a0e0d0906030c0e09100f0b13121a04080a080c0703170403020102 73
    0x140c1d12115828254410031a00b01c0e4040d0030ba208561000d03506000e1854002120301d07103d00100b1403100c910800b01c10448840c0b050041e040d20341e50804140340e1080340c1240c0310401350b03000701d01c0c00c9050f03056200921680074001d21501200d032114102241020089202d5012168000d00e41001e40b080701054032407440d401980222010b601c4003100308140100b030741c030100c06864120042c1a44a80549085c00d00e8011400003038200782c00d0032900c1c11a00e02400c11180302a0f8042c0c07051000e458548407120140404851020420b801c0c500305104c041c40110354091204419260703005d000c6d04000044004100c0400442d09209610845a0465413200b2056201d54aa25145485d00d03040200313800e910380880c6c0c400c0001c00001d000708840450310f1000b030303426101c410f600700d1030f04078140c01c0009140682002000c1d40044120502042c00100002415412060788501406481e40e1042961502c50860090001030a001e01000c01054925051340c105002e440007600f0308441450205404118 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 781758426 1250 781757176 781757191
    0xa060f020f120c0f280c0b0f180106030302010902090a060e19111c0c02070602031210050a0f1d041716050106120201080112051c2106260c0f030a0506 66
    0x641e503949012100005d811900c452240361a000041e40d5139a40240c01202421a5280e110928001485022100300d8481903200600003400216501c1c2400b81c02000f4010086c0e0280f802c3c1c90008460302e1550040c001150b41981815020350f60f01c1c134002e1041c4091880b40310b2565220540350f802000042c02401185448082d036442c20080c00d401c60044400190844065400c1183e00f0041c6070340204c10f03241491340c4407803803035070710b903a0325010401151031500f05940c051030705100440d889003e002050143c40e09464a058400f0000311507900303664003214003c20747c00400b40925031403d41480174059145511010500f9444541e49040c20b48086802c80310769201046032204c2550780c040742c0140101082017001000741002d4841680319540c20340380440500001c40e11010b45842041d0100e001400c00392030342c0d00c40007800c5201000e0710003481a10809444001a000d40440c004501d000e040b58000050412905c2e50082c066440e15083c02140d140c003c0d070b0b049001249061111901c900030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 781759676 1250 781758426 781758457
    0x130203180601031203020c0a1a041a04210e0a0b03060f040209030c010c210e0405010b130501030f0905070b03042f0906061b0a060f020f120c0f 63
    0x41a44031000d10400080a9503010340c005401080410500301c20381d20f200d000e0b03140140c0c1d50700b01c0845070fa1800e00c050300010920800c0f83e0303550021002e4020a240200e1040c0c4007964025180d03103460010000a0714064040100e4100f91004002c24510440c8110403a0900c403003a03001650000d8110001e507400388144035000401c2111074904441700c03056100044400714244031000c0e0229039500c0003083c000b41407040c213202c060140600c10311548407425150100600309100400300030305e1280c214030030f0341c015400c0400101c2c2e108000780544140f5000c0469408a8501c3c200044014100302c42d002d0420550b00d42d2290041401072289101800d521804d0554030f0402d07281c669100e051450010383d5004801e400102080000003a16440301004c40741d512072070f10f43d5000130b49180300f441d0805100b1050a030031441341c0384011035200d20190240104000507449040d407002a803046480400724560100220502040e007030303d640741c019600e002d01a041800408140d24103a1180f480d400d071004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 781760926 1250 781759676 781759681
    0xd0218030d030e010c02070e0115020a080a0f0305010e01030209040b0a020f07081903110703080411060d1a010311120a0906021215030109021807022a04061707061b02130203 76
    0x180309005da600e400400340f0051207214607044082d921020180948036040c2841c15100d96002d04c20400d5800b00f50300003111603a1140300300f1000d82114143c030001c0021a080c0000000c04c03041507042d4504072900501310568690321640c84d401105801401e00743c4c0aa400c0c810a01904e42c6440070b803031864400c46000e50340d500300c0405c242c202e0300a80d0310703c410107050102d401d01d0800b40f08255034102da03150a0000c0181c80b18a045450070170b56803101d039045807000c2600c24803072650390860b01d80c80001c600e02d4480254840011425078072440030442401404100c039021495804511951012000307900146104031503480b03001381d1340030369968034a680001e03080c401e90b207004100c2c1f080111422402003000f17910950100d07036940003149060075040e488600040e03055000340b00d91048810403044410200f24201d45001c03c909a141956005628284010071482c801c5100e01030407098100003415500c1c940181199038071850740021046000c0702c15501c0042c2c813038040a02540b41c0101004d6140d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 781762176 1250 781760926 781760951
    0x70e06011403040f121722021e0904060605040e01091124040e16020c090c030402010e040c020f0d021b0d051c0c0204290f0402040b070f12090b0d0218030d03 69
    0x2040140c4140b46903240000f1603040e82191b254480d1f01258140d414103e44800b03002c02002c044a02d100481c0c011044600700410810035600c4902078510440c0d040018600b0b200002c3d0880702c010000901805ca044050035030703464007200c20742c51f54004081801107080002c0303a110040c3c1003540069443d954840a00078013848004c40d45864101c50300c02401c1e1414500700042000c00041c104c04400c1c10000085015a4455086204080c02c045e0082c880343c134641d00000d40d100e00c0d4265a03c2c06019948510003a0f074404510282805007810054082100036800c00c45145032589089074244245c07800c1c1d901c91a080c4d4001028542240c8410f41c0d031012600502c02920310380161240340c1445900c0365240040c42034034050215206841e41942d51480c000414024803454120210b461408220385080244001070000810b1050350008400360705086c0a803488142d901882c0301d83c4500b03003c120035928550307000d4143c15039685503801c84944401d0200b8203020080d40a80b000988850200303001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 781763426 1250 781762176 781762217
    0x301030302060c0a0f1422030c0504090b062e030e0607170a0b13150302041109010807030e07050a0b07060c140a03110705070f08070e06011403040f12 66
    0x40406950004d240024040004000340c81010701d0806101018140040303404c2075400303595400381c500e0300c5440750001c41f040055800f400c5200490f4000201c00001c552803e00c2d024020a00f940500c0d851920f13126801008650b080441c80020031504407054400078241003140300315851815240000c0008207506034078248200100042d0034040c0043c0d14150b00a8448061640007915000008010541c140000c8804400f4030380322080c2410103034202d100003440c101d00d000300e034802c450402c1120100c02d100c800070f0052a044c01d000c51544400070f40b415000c0d400141d1001202c0054640140d102c00c00100e0203d46501b14a0740100c000c11490100225031180e07600b03a07030103401c024082a031020b000342001d118411240e0304041d00d543c0030000b101001800c0c0c981352a0b21000792094140c8410810304044072600c0385088904c03034031a0004030b248a1040d400c1c0104011b83d2210000c001c0403140c14410b0388040c008035240c2e070340c401d13041c8082a8031404445440280740d5407925600c6c51030300701c500d9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 781764676 1250 781763426 781763431
    0x2040e0c0612040c0e04080a0f090302060f0a120b0303070308042604060206130209070f0c0503190f0f09030807020303090a03060b03240f100b041d07020a02010909150515030103030206 81
    0x50364011201800701260040c01650030402189c603103110003010154084806101d144d200039040200400c04c0c0702d010719480064642e000456841030301740002e1080b0203069805210794950950410000030000c04c0c45840d80603806401000800740d07440100d50b0450345150000010386141030080760030710959505022894000507000c041c000c110f80c0c541c0001d0b4040d8400307030280d030910140541000b040c6026110241590b500001a40d44492209070b81035421600c809150700054104c542d031100c036a0080044184450966803400380d8542166141162640074040680e071511080c810001d0954503c0008400f43d0b224000c0820b0b81c90510060601d824001201741100080100c10302c90100e0f410038905902924001c0c14000079220340103100070b80e00751500301040402c0000b8010542c82c1200c884070042180c00c0c2601c1c00395648408080741c980f20f18a0b00240041d2204604000b80c0d00a6007100312028403c0342240d03001035a4100107034101a07400c40a04c0400400f0004205154041c0403055 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 781765926 1250 781764676 781764689
    0x18090a08040603091a0f0c250f020a061e0e0f03032a010c050913091403070b07080f0412050d060e0a0c03020c100507020705060c06160e03030702040e0c0612040c 71
    0x389181007040c44098803d4000340791403402203001c100c0754404002d150640c084004c8c0054031020140c2c25091070001d1501855040e40a004100f40009900c2e119007203040c0915014000c0c00140c10030f50004039013444200520607031106440d4800d65203568144014012501444603c00d18041004408006401d103a03a180c141c40e4074140d85500c00329080821140c2c1154112041c02c040d07003003202c1c81e81c02007860038400f600c2d001c00708001c134500080000042444600800d004425580e0b42e0004452000c0d08890342e6601410f51340200e00011040188151406c0c481d0402c1070400810b0401a4101c800c0ea0b803045030030001e5981071003040e4010b40f1170000700101e03600e400d614281481249541e00d182d00400f81460556500008010a1080c40040040c040c001e20b601e59508401462036901d01003550140c0007000d00c1c039403085009010b000d0301c080c0c0c4c001c0030300650f081c5005a000c100003818008040b4105011382103c00203195144401809002e1814020980c10708060a141180b15441d80060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 781767176 1250 781765926 781765973
    0x30e0f0703030c0c0e01030807031722051f1a0d02091b1c09060c08070807050f0c16180c120209030a0f200a030218090a0804060309 58
    0x11a100440452054180ca070542446401d8103042e01d0301d04c451401c80d51100721070707a141c1d600210401c000700006002c2c8a010796501c6000c49010070b4a80294002034480750540d1041142c1c01015500d01d00d00204203d0140c0705440980a40041490151130003d00a00c2141d070f4a0040c1004450990081104280d00b9150441c074440c095021802000c8060f049a40c0002c40840302042c45241070100c0d04011280340080400300d02440d0740d600a0300325801c0440e40c450401c102200c1c0385100d00b1400e1310844495030b55185507265800e041e1043c0c1d00810445019880400c81420512410060400501007010304041039034503060714580800d244104602c003046c01d001c00b072290740d40d0001c0901502c0400000041e62907a0000009103040c0303500400030600c0d5806040113060010742090b80030308901070885811174000003010864242994040258007000d085403661880c100521074952000c08a022503152400e10384529405800c01d500c007000103070f110403444080100f901c14040e483c035410100c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 781768426 1250 781767176 781767193
    0x615070219290a0e12010207080a0306210201051b151609080309153606071e03020a0b01030606180203010b0a03090c051309050601050d020d060b03031c0c030e 70
    0xa6800328031a07820f00c20100048134410303546176620000a0280303602e0807070085684000d82d18016869401c06510034000c2850034600150340305074030510103204080c02020646900e051780c019074160b0003412401d4203401c0c001c05c0d81420340008000915a09001072024061031510341129181c84c51340c0c8180e2810003805990400c001c02000003510040c104c1160310300d1030351b220a0130044c4103000b0403298035000060301d0048011507440070002c01562003080182c1c0e5000d58013101348201441142802400100340c00c1090464910307124005007594407a2055076140f030f0305503c07101c01042083c0c20948000d40d950200f00141202c401071410b06820740001503045602d0300c03407403035910b0003041134100906803107104002c104800074003414040c040040c400d185100c0e9840d2000020030040004981d0352260700004031760391503e42e100311303100c0e94001c1601d10b21005d01e5031070901404d030345d0000039054807007484111500d5140540078900d07522001c500080d50340c082d0400800307558940040b0750068001008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 781769676 1250 781768426 781768499
    0xa0f15030b010e100f17161707060801052803170c0709091e15021b1207020609120f060712050708060102030f090604030606030501150b03010b030615070219 69
    0x8042c0466000307040782200c440845601c0b90412503c46a1070340581e440c21008255000e031b42328010342452445c011074540640702c42c42a2201c42c02805074176801035181c45034242c40c0700c2d1800034442009440d400500c440766030355070b814410220f41e081c801c01c000c07001c1802c00322103104001100090201c10824400c1c0e101540b210361994401000b0000400c11201c449004c0c450922407000c04800c50b86411035032a0000044140c004d0610402900d5500406851120000060050f2103005800a1999180041c0801001544241c2c2001200203005095080541782e01c10305c48684681c405450780c56114425502e070804450000709680c0500924009005407039038000144c5031079040810b0714a41c0d0301c0d04100011520f021319800182400e0070700c00d010082000c1034202182d0b41c0207006201198685801c1198501e0009001d13080e000c180520025445240100400210100c08030304903190041940100f107449048515a4041c5078074540200200d101000f010031807480760406205901e0300710007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 781770926 1250 781769676 781769699
    0xb0c030f04080307020a050601030c080706021c030c180308030402040b010206130308060f0a0f060e1e0f04180c060224010e04050f0a0302210705060a0f15030b010e10 73
    0x80020b022941c011000400440c020400c3e1200c60340c10908070703600c66960b4649241041c00500a03100c85002d88040060503500019585045040404002d14071205007035044000300722480304101082603108030000d02c00c01c41e00c01c8801940c019843c640da24034040c01071000740c5da210340b030890440d1f00180800c0460568014a454100c1d030615110700c043d25040c0000d1183c1c50264400ca511040f200000242c4440d00784094044071600c3c0c5408040788540800c11413000d1010b44035852503800f039200c81d0080c3c640802c0c4040e00003401040000c652540c400c1070000c402d6030f400d0481d07405081c041d051069a40401c8000d81940c044051600004100048003401c00b0b4184100444e81075001d000c5820000240304082116018074200c1d070789400703241070095407070b080d18804980b4400700390907180311031a801048800301034200000f0321154803a01d0860780102000f00303080400c02e5072a0b06d013403050f4003034425140096010300c0b40c21710554107028010780240c00c0504aa980841c00300400c015029881 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 781772176 1250 781770926 781770931
    0x319140402030d030f1506020a1101030e0a0b04060f110909010801052e03050312042001051b0c150a120603050d0f0e0402132c011406041d040b0c030f 66
    0x3e2602280c484410030380100607112459203105034201c2c91b807002c0b81d5154006501043d6a000707480541500c0346250041d4203c56103040100601d41107404000d001c11240c43d92990024413a0000140d40301d0f12403034450494070f0308448600b01001c00250b1404070f281c00c0c10034034013518520000300310f20b050822041008440e07520440c044044504007c1100074107110b0034030021500402078903035400ea4141c00403107000d01200c0480704102d60440b01251201d5038003031126400c806846a0785000d450b604c0203409008846030100c907904c40c01e955410240c4402c1c0c1c034082800c0d003003082d4039154840c3c800080c0003103802011a490413850b260080000c6072002400c15104089420200d032060007110b800c55103001c88984168006000041010411441c1c00d4060219055244c030f0a00c2c490110545d544505481d005410201d8040360051161942001040d0b10b025001080e8a1402d5611482c207d0880201294180d5105501c2c00700001d024811284d03540c0704c1c001d0718817180345281c080810380201201 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 781773426 1250 781772176 781772203
    0x5160203090d11090109020306030601060c121b150516020105041709032a04050606030709090e1e01050f100b030411040f1e0c030c020a0f17031914040203 68
    0xd420b40014886200c184101c0140041e00102581da10303440c8840103580151007d500074803a00c0c3c0005500391289400340291684991904540d00340d0020880f0591a020800300d500a040d45c00354001580b10313910110585880709002c00d183c540809011102031070080d04d0320659040ca0300f000001103202120a441b280480c400d242c03203117002400300786012540e11aa0000d80100c41d19010940d007101012040d54200311001d001ea0350b03450003070141030300044d42c0000110341240020f11150215030030a204480c0d00504030b403005110213240b2a8411031407000e08810307035501e90030b108007a0b0005406c958811044544015510300d48007080041d4032006001400d0700c00708996036030355940d450300000b0f066031840c0c00c00d0020443c4444000b460f032180c41a03196040713242c54010320f50f86000b4000c44c05603000da85c02400481503161241c4059034400941105c0d1200c0440c41d018500c18140f01030750084401d00ca51a134214804480c0d0b104680c926644914081200010040141c0e80003800710000c440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 781774676 1250 781773426 781773439
    0xa180e0f0c09240d1401050606090915040e030d02030f010e010605041802041505370e041407090e060301060e0106050c0109021003020a080615070f0c0510090503010516020309 77
    0x8516a04a064541c0b2121598001020f008100610107030341d017030500158404000f00300c90b48540003002150301c51425100e0300304680340d0000d0f65a0910651001040002030000701e880c0b0380c0e02c4101c7d405c551020784030401c6541d01000740b11110411a1040340500041c0381800d85c079504208000d001c50140348198564402c500c640010350ac0001e0301500d0080c0b10700358090690b0b000302d10010344541c02110043c00c200c0d00b002e41300c503191018501c01c0c0e0100101c100d101450301c03c02e1002140c5800c0940c02d030a030400d0311400c070b0341030b0900304030382042c0b05d0103c5546440c811800c00024910b00440540714030310903818400d081c00300b011003203941811102c05040280c1c4e20b03070841c00494090014000d001c0c0d413000b03070f0350654010250141c0082030030b080030769100c074155a02c54040080b0101803c101020040c0e044c4840400035450000141c00e207405002c000e14201c0d52500010803804e0f008445000040c00c60508002c5801d00b405400d070032102c028020395860300c1c0620029a00d00442044904c07800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 781775926 1250 781774676 781774711
    0x3030c07030c0c0605031905100b07060b0604030b06030f0f101805060a020d0608074704030b090a020d030807110f07081e03040308090a180e0f0c09 65
    0x6000d00c1c50800080c2d03102c001c00c00515504c0001521a400032614100703080000c103491030b42112181301c0c140c0b0030b1b40f005860152442c100300b40d01c011030300040f01c102c030000e80d01d18a483c52503030354074040c000551042d0390516885c5043c0040c182840100e1803090082d9000d01c101ca00c801e032012408001c10f1510500008840f01da0486042c2e22134001d40b0098403d00074401031140541c2c6a800904248962880500585569100340e55846502c0d20455500000460020420170309403084950070008140c0030400d243c05038903080d00c81c0808047d1810200a0001d42001000251500940c1c00754044c409013103040b00640201e4038440314004020204080400001c00880c01040d4105101100c402261040d80d19080219601e141d240100c01d0103100340211440402c0381007141100394044600a14201884d541d00d95800b5040040d000e0303400003c0d200d01260607155201c0c5110ac40380404004030750201d1841503603007401c03246420310485810800c10b24010b42c940c0c2a00039000b10103081c220b80d014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 781777176 1250 781775926 781775933
    0x90d05070602071203090509190504051b060403020607061a130905010c0504180e0316030309050c10050a0305060604030803070203090f04270f170307030f062d080618011104030503030c07 82
    0x8807d6420300410b242d00c2d2a02f80828440000342e088940e07032807106200a4000c00d04100036180c0200e2000030761040d400c1065000140080d0494010703c03051614050040040c20300080901c403400b0380c5106140c0e030302c00540017880000d00840789001c020381002d51800d410306544004c41d9840c800300e40050740c2c84610009421000700101c41c50030140780c4a445ca60003c038074006014000300c8400307550707a104018040844d072508402019210015444652421030f940c20309a000d00307002054140d108070140400404181410001c41c455000e80e40a0b540c1c6100e203000300540140720031901030055240000381019566007803121054441c886401065042c040d11745003050b084030040041c402000c00303440d0400c07016504003640c041d01c00c030748003400702c035940542c8d80c0d08a64041c804c0302ca5200064802c002070310421100850801806152085026280d14015117000c0b400e42d000f0300300c042c094080e0110428203120740b1040500b80101149494603517100c840c0c1d41c0c00042c084402e9400c00007007036800c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 781778426 1250 781777176 781777201
    0x305060a0506090f06181e0303300a1409010905100b04151202011202091c14060f06012604020f061306020604060e010b010804060507020102090d05070602071203090509 74
    0x4204c001040c042c3d076000f10550300303140a01d04101d0741c1d008408028164400d21a040807600e400000a00258140301e040f1400034142505000d03040e07200d201012100c1c4010144002d200d10178030306444003040850b0318010b0010981002080b4410a0b49040c800f100080c2000c5125000070385034110108041c0f91040008000304800908914000300c1e0440c00151010000391011046e8002d072160046103800c000030302d06a03c6140c00c1c4c00d501c58421000d400c014460709150120060054246005007603000b00c0c440c1c40d08809841b407000600c000400c1203200e680c000010640741644081078000c45c65442e000c89400140508000e02c186021310701d890081c0c075540142c3c0c03400d106140710152000e9039450043d444500544041d60b01d94102810040014014000d0340c10f0401c0603968600303a6940d81c2c4402000749405000390b02195001c1145849642d2000e802e0540540913101812140b45480c0b070103403400a807640070310b084612002002d804650040d03002c1003140e00c1900d15006959802e07900c450f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 781779676 1250 781778426 781778449
    0x40b2a130e060d150b130506030c0108040528020405091b0d03050405060a03150e07030b060304020609040506011101111b0c13150e011d0c091011010912020f010c0305060a050609 78
    0x811400c0f40403282c200c0c5807035402c6240507003415401e803000c81ca01742b001111030090454000d4041d900c0242049001400b219071007080750095040c11748130303015903070005080d120301f91581d4141c4d510040c5641000b0114031302001210100b1140306030414034940d000752a6000d5841014850300012411044aa002e504079002e000480ca0f4140d46075604c40a1070043e80d0020340d40d00002070300d0301c40d0801450501e00109c0b07000e01d400821160a004803181040081c020081416040000c55896951140800d00a6120b031503090561030307403a0081404030800080190f50908030580c005008090140c5641c3d074403003040c2008081c01b0030f0484a5080303509481103660f01c4a081a8a0718000251445110125548401228004020f50340f101c02200b0000d015401c5c1c11076000c40a284900b6402c0c1c041c104155400c403c010000c201c403201034403045419400d8110131800342e0081c118000400c0d41c00c1c442e100204580d420100024104440421580c8100d401030a005400c00500100240d856113071440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 781780926 1250 781779676 781779679
    0x20f0a03140607080903040e0a020a1808070305062203080405012901030e0705010f0513030609030305061c0b160512010326040e040b2a130e060d150b 66
    0x80c0d184214001a41c0b180d0855607a0001440c810204403070490100449040707810a0382024015125068014001c0d4003281c0a102489400d0101c10300508a8034074503c001c10324400a085070515506005040446c01055140300050140c01c1c1d507018031302504851410b5800d0718114096a80f24542140100003c1d42c1d204c0b082c0c0005058010f10b40081c500046405400785c0e0203108203001c00301900e61b2061240110782c04600000c10703490f00310703110354080c0c03c14880501c0c40b00074207541d945980742201e100c81c50680019441d030003002541d0510701001c2200e040390300042c848900403903c8580d0515406000380110820341c1941c0d040c928403070f405950b4402d1000b209a0186d5030745e0700e011180b2010703502d550010500c0425103603518000036410744045a00d03112020320b640d0307100d54401d8103c40d001807001c1d000000300c01d208071308500100c49507400704002c040c0042d9900a1210b69061640c01a446810001c8000c002c12510f500c480c944080d103241e00002a5151a240e480541d02600c0d8a07510a03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 781782176 1250 781780926 781780943
    0xb1305102405010305040b0604050601020307140120030c030a0513050f0a020114090f060903240a060905150f0102071d04120c1707060f050103150f0513020f0a03 71
    0x40c07410100c51000301c1186865601c900a2203075540c00541c00c3d244115409400d4120260000f503036400c0940003581d00110510507a0f2804d4070075a01e4110584440700803440c030303a540303490031201048000000b5050444141c41c80d070551820f40b02d0700000344801020042c02503120401b080c400f881c1d4400400c00c05600400b56100030014403070403551240d07100300c1a0700040d50002c8a41441c40020100c60303220387c4c00380c1960300d0040d9050a0014951203000c5403078061289846140034003400e100b540740320701c0d03d400311041c060406082d07104c20b0340c0442c2c1104403d9860078003401801450504400c84041094402c0d030f0322201142c1c0142c0c10900c0701e90092072050000310f0495103043c00403e08511562040c2d203038215902401d2000c4135080c00300b010040c0320143e01ca010030103501840c40a0030300d0304c1c850000030032000c2c01d0714282c20980380300b2f0348115240c4405020080d126652070081c800302226030b01c801c0113189401a5000d1a02e1641c20b0040e02650040c00e03004a1912625100009540c210925 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 781783426 1250 781782176 781782191
    0x721090e010b1c0b030703081b0f0a0309050103020f0301090b310e0114190b041107060c2a050c1c140a080406050a0201020c0106170d03090b130510 65
    0x3031a02d50711181d09103885800350320001e000f940c254458084080c5000e0001c2500350f040d9982c1d070049034048050100c154021408140c00b2950412580d404c98080801501c1e210500c2d04c0c010b0702c4401c035500114103150050048811502c1850705032411a40c1c62500072440c60100710200c0d010364860300d00000e546150012919010b400d10110041c580d0b80c0000030000e0910f071545c003a089070703542950819000304c0040803461381a07015611100540c2403880004103031202c10b00150032284d032500d55059440c0c01003a1041030000c58813502c0711080fc181800c035160200d003d0019070304500c03a00c12a1243d01c071070034424103100080000302c3c1607407005441690b15002c9410002031300b600500044a2078181040405081c60012035600041940107607007505090400500352a2500a40d810717000710741d401d0008003c402800d014080060807107040d40b00020340b899552138101100780300401e09040c00c3c2081800022501030020354401044005e100c40011a4641281420f24142e0342c1040343c0d040600 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 781784676 1250 781783426 781783439
    0x150302091206100611030304021c030203130e01180e060103080a110a0c1a040303020a0201080402280e09030a0518061b15160e21070e0603010507050721090e01 70
    0x100003042c4e0f50385442e0880c03c0c0300b80080c041d659101c100c42c025000310314103003402c50348103441e4801d403901c0b4440c0c0182c03030074410b82c8500c00c2c05002c2e20381e0000f804d00e40c403030340100b01c0d0720300e441c0b24a000368600d91001d110118008010a42d103d00620004007020000940072201a00c00d40200410650b80380503940d041071a07042c412011540303400380384085a400c20f0b19100c1092118216400c590303140c0c001d08014502c0360010342e18500010410f07a0048035080410b00a00006038080c3c1c4036080c18a82d07200c500e4208502c511184100508c594080c5d4410003000030300d19040b01c103035030061600b02c003500c602c1e0072104003089003401901010045411030b680590741c1d900c0003090507540003407568180d42c1c20b55a0f01c1a410f002c542c981c0250404602e0324841383c413043c1003980b002140110400f285400e04a031110300140791469550200c074500c91010148101860f080c0901c541010007858083d0800c6c000303803220f05c4140074014103203400700011410301c0319584c0103201c2b005c0140007003141940150307943d01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 781785926 1250 781784676 781784701
    0x11101023606030402090420090c03070f030e1002030405070e07111b1806010c2001031803090e091002120a050a05101514030108010c18150302091206 66
    0x101c080410180c0c032840640681404025284202d400424001d0319803500e44075400d0000458100c090b091504299200d00d0307484103e07040b40203c100d2800245c0c0c2e4070303100000030450b156103c80e1100f0582081c1407086104030014194400b19850040142e6a445e03d00d84603181a00320352190040c06a91810011050741008104041b8070421050300d00c8513568285403907011812000650748425100d02032803a0850100701740c0c2c2c0c03100d0181009840c03030710640c4910307081541000345030b62003041c0f4000c40111940c1c940200da911080248001c10b02d002141d0b0301404528040c01101001c3c1c0b04c650006020314400c0240c11725529120038115540c4c4c28000010711a25170480380d005200341410045009103001c0d10482e413203655981e4444104504101c1c41c40e0440708006056000c100c130041e461482611280300640c001c1c500c2d0800000c1040c801031000d080c84403131a6501c5012061407000704011034500b121984e82c040c0c0791400503503400e600c100007040e08030194540c2006105150400c03101318001e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 781787176 1250 781785926 781785997
    0x1241b050304050a060e06030c07060b09010b19030203090303040f170c031b030a021c12060801020903070506030f010e041703040c050102100606052502060d0b040b04050603060601110102 82
    0x1501c500b10045c0d210107040d540608008103050700120100700082c4924507043c05441c0c0f0b54420380c40842c140d040c040000d03540b4002a04486450f01e00080d4400c0d10322030300c0c0a0141c1b00c018909007541503117004241030741c4030b000080010b0300a40050782c0107400c00c2151908403100c414200d5000351201038882103150349e81c122240c00c0490707110543e4522040702e000400e480204005078010150703600c4103a00161644814486241800004211081c040c001c0340110405800642c00041c0c031030b0a14000c051915034540e11403400f6600400501004800000300300c1d0549030112440c0501380c0311880d0410006894880b10070035000c01009002c01c01c065180400300704c8000740e01300c43c410341402d51107000b21a0544036210100f00700304485c8a4480c50700624018400c41fa2400403c0c501d080c0e0003003030300c6900c002c8074804e41c3d5541b0500c010580ca028801d802108100340d03820011442e004c030110f60794403409802c50341405210406512595400d404035010b1a00009502d5a5035401c81d41111484440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 781788426 1250 781787176 781787179
    0x41205070e090d0309060e0d050903070509010f0e06060d09050a0203010e0708100b0f03070305031e030105090402011b081b071d07080727060e030601241b05030405 72
    0x100000094000c22010146024000c96000781011042c42e00041e40205080c00c001c40d40b01d902d03440519440c40040c04000b8075040230b912103654030300da02010035003040d000f904517621800b6040c005220303007040c0c491f0303800690700812412000f50700d549000548501030134040c0c401541c18104000208080415030824070b40c4203800031300900e47c0c24001141c0b100d09600070301c2c019910218440101d03c038160082145e001000d800d905a4049000109003007550a81090301c4683c80040e11051038950303040c042c684114950f200c0c500359418800000d4800720054030107410000601250074101d4030b1380c0c912079041a07014029946e03840a4002c4d07681c00107010003003102d00313028001c40010300325140130754507103107016a21005500340e0314400706584414000e89848100032104c0c0b0703009030300340c0140505140c1c0149070040c101000c0c130b0071000400b62003000c414640a13400141c01000700d5505071400c0181c45421806c0242030b4641024100e60950301c440002c56103a47e03010040084c4031001c0001c1055940 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 781789676 1250 781788426 781788433
    0x2d0d0b010201060315020a1103030916060f020d0806130e010c120908120c040909030306050f0f01020a1509020d11010206070f020c090a090b0a1a010e18090102090303041205 76
    0x11600103a080710528071014008a010344111070030741203280c1c0103010448440c2001c2d600d00c107400754668510b400c104d03045c03182603000300c480340011006069603100034065841c121491071042840252103085040420081c0440000407030f595036100003610724440701c0c6150400680405441c0a1301825414040e9404510705000141c900041801040314581d08010b8440ca0b005500314292030b081c038020603031072001400348008a0010b1003400345a00c0c46000f6640402c0107802e080401049200032120584500d22054400009903000304031941126080049400d0f40c05100a610b0090800caa10080d40592001c0f8003400f00462442070421044081e400c440c041e40d5494401d40700d00740b80342c0034800580e00c0156a241a0324005940799441007000d07101040d02d03a820313514030b0707208032003620244406a120b9034138004484880f480107400031f2003441c10344645488000400d0550080300560921180c2c006d0016070305590940451b03403030306800f508a1b44d6a41c0e44540c2d0245980c84c030401120b0600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 781790926 1250 781789676 781789691
    0x70e010809150c030405011e060305010b010905031e03090d05010f050f0408040b0313020612150928060b07050d0306091e05071806020709111801052d0d 67
    0x703800140b000c950080da41145540c40d11100b101500d00d40008000315140e42d210400d401c1144450720107048442501c00c03020035014214681a4291211348180d5070400040c80010801e550300007494201c000710f044c00e040410001002d2190443c8501451f450f040580707501000b081000545c0038a0480022103010021a2227071003540b88500e100391ba010708013003030a0105000070003003d00110f800c51981100400300002175401f0a082d50080343c60742110916000402541701a401007040240404407030301602d40c0307065400c0303601943c12190806940400c1820b000308102a43d48144040c00783c50700180e44070810382c13a0443c0d50354000c104c00c1000908000340002e0040072401801c1c1020100c40c00f01541c9402c4040b42c4001b0040144190b0405c8445070305003c2d4004a2800320010302220b90182180b241411200c03420b5440440003405214010001d241140102400500601c002417038a550340d098980165002004600021144160940c8070030400076000402012403a10010090104c1e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 781792176 1250 781790926 781790941
    0x807090203040c0317040f0b070209090f071a0d0e06180313210609080307030b06040305070608190501060e120307020108060f030313180623190806070e0108 69
    0x28003003942c0c010b1802e10040d0f0244000740d6101d2900c000d00800088090500303658074002c003501d0f0019400b0345005140002d42300d080d4104000c0143c0c1c0038881c240203080c024500040c0f01d54580040c03048010120f07519014003507001960084035050303401000280f20503a40003154031b80715042a103030303102d1011005810400141001c0140c0f4206403042c2d03402010035103440582e1042152059040c0d04210061001d40c00081c13041c40780200081c0030710f4207541c503850440000307012690180500c2e84921020b21013080083c0d0001020025074690381b40c04501a118403403c12200b003440310310a04014103000002c90002d42c40910604200011101651401d0302e08420a03141d2080310700c06070002d911540007540d80e080c643c40b078818000c0082c0459141125410442420814540202c4480111030040e0000348085005060250201c180b000345c0030a02c0807001004110729468035030046010148005490108000c000000d10111003502c801e8540007100410013582d2054040c00728032100c0109000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 781793426 1250 781792176 781792181
    0x204021201081507020a110d020d06060501080106091202060a02030c060703090b0a1b0e0f0330030c18060909091c0f0c0305090301090813080c030d05071e0b10080709 73
    0x51000d5170043d203001340304c40d01d491065600038842650070060346001040143c60711205080e80034010480018901d0500300014202d88041e4440410000c0c22a814410003442c2401007282d10f40c1150303100c2c0e42c4e810407242a070840c090021100310a009039420042e00580603000340d034001e44205c540954940c0c858000204881c499450181100e011500010300b42e405070150007031020000f00605550f401000000c1d142101c040c40700f007500d0034044140e10326820b05980c00c1d0030901500801c10b007145031039a5500824002d0300880041441c0050043d076068990400301c0310184005032844140e450007660560b40c0c1e6030816400a00d048400c280818541d1154492490481c0140e4460481c4041a1012a070380d401c4a88459031556807140204000381d9202c008017040140030a100303031654501003900b41000141c1040300e000cbd40120300c1d1070103082d6018003141c2003140c2c0500044005590f80c0d140800e020302c510401004a03c0d040180102040c80e200355408555900e412603c901da114060b4806 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 781794676 1250 781793426 781793431
    0x712020406030609140606011e0e3709141303050904020708030603191e0c091d070603050105010e090a0e010c021023010506031e13110303210a0902040212010815 71
    0x500c550800540308858450101403c6c0008001c03e840c104141795600c031302010010441c10521080a1552801c050300350b600440001c10012204100dd0350049440c41c910210081800c2114450383e20050b0806004000381d44600304040c108544a00092030040040d41c0240d90603031003441062540e00428181d018a108402d6004110340100358011002d0810100e80080c201c2d540c208554011511400b540b1680003403501d00314200c100c81003190340035420000c15411000400d400c000041c030550342c22601c440c51414044ea85468141c0d05c4c2c0115000911604d10280003e50a0210303100380980e001411400c014400b000c03c01000d1505034183d48580701e0040000c40305d0711702900400080c50040091070b44034241480c40700c1da1b0008a00c000c084540d08803044c020240042105005000740e4130300c01c0c0b132154030543c021840c0c80f407843c901e045012400701c400b00c00c0692260020f200028a9007241c0382455000c1c0c0b0541d00c60303540e2032118610341c0d8240038655052148010f00e406900d0441c111a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 781795926 1250 781794676 781794707
    0x7030b010317091f0203090622080313120c0e1303030b06070209160203090907080106180627050301090b0a11030c0708130e01080307030807020c03071202040603060914060601 77
    0x450b82109000c48501480ca111130a0158041405008071a40342d11009109503035206440810410244401005012203500018501d50081c030241e56034019000302c0d003080c1d404600c1c0d0700d201d01c146841c0080039490310342c0112400c0b08501c01070110404100c50103034842440f81d1002d1203002c0c1d030b0005010080c0241c104c047d60010481010810034030f05a41d0780d079100480303481502c0c5450403000c040b03800d00800b500c500002450181c0104030440e8400c00d607180401e00981912140c2e8600b14000b41a800151801d20600e003904031500381540c03c1340c6512000f00b030094004c0c000c110b03160401e996191740c1119240b4915041170b9052a8144905040fa885903003d034110a040011a40722551150080000c6906030300310b41501060344044062200d00906c07020004580c2c8045a01d4004d180f003901034041c505551010b40c8020b02076502081c1401924000d0114960040f0280000b4001c0c02c9142d201800e5545440600c1060214440b10004100d81400403184d482c0c5849004458004501d08001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 781797176 1250 781795926 781795939
    0x2010c0f05040b0d060314100b011d060d0e06190b0f2202042718051f0b060a02010b100207050f0904210504050109060e0603010b1b07030b01031709 65
    0x901c584100348000e0400400c1041c40001c03620b07100e0b0b807102d10300005a08900e4482d4012003208d48102e080740034401d40c588080c0b80c81c1004049207030380c40d40c406000346c0c6517901c5160085800c1c040c6d81140c0e0302c0041050150811549142403410109a230100d444006080b400d0401c0121491420035504007080200040e1080c408242545e10a4034010040d9401e8020301d5000c10002401000e41d041a1801c2d40408411043d24112614100c00321042d001c1106408003c1e20404070105c0ca0101d000010042030060600240d411103003420002c081059540307a0104010448112481e81540860308040054454421241000c401a40c1e41d401510802c0c0d484084180010303600d0030511a81030b00917114920b150480000200341c60000ea21800300c030301c0080d401040800c180d6a00c0b40d407810082c0100e040810303640d200785020440b5440305021700440000700007803445c5c640440321040f41c1c8600c48032094814554507840d191031642001c0c40150b41c072480c0e0403105104c00c0c01036001c58404080082c2003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 781798426 1250 781797176 781797179
    0x140f06010315090213020403050d09051008150a030c0b070c0602120d200304030e09070509031c0c02030303010b0c1632220507020a030512041e03030c02010c0f0504 72
    0x2401500c0140f004a03003040160403803104822042c0058000745108001074803400c0d60790000240140c20907404a841142c030040c10400c07594008242a80003c80b9404150b25003000c107000c034940030740c198002000c1103803000d400980ca501941c00340c00d0040c859a1030707903c02556410100d0b502c55001c0441a084802003084101705c2100d0762000511002400d0180c1002c1300f2008035100030b4100315015008150541440401171400c1901e044c0c2c01003003800c0003402c0682c2600400d03690280200c080c8010480e003c00203070b9460040d0344000d03c01782d0080440b035072076844030394040140d00b00c0501d4405070302c5a8411481e003001e078a481c0b10f0540d81d0002c19001c03600c2d40d461100d80c4007191208000b410060010140d0700c03d484024446e1884825840e42160072240303009058100e4000a08420854200460490001750b1002c21038408250301404850142c50750305018100c420700702ca030015100c0d8015000e504140e0550800200611103400802c8840414001a60080b003509100300015404020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 781799676 1250 781798426 781798463
    0x301050f10120c0f060305060a0b0a020d0c0f020a0612050a061a0d0b1302070507150801030807151d061501080703020f0f0d0509070b0f0306090c0c010504140f060103 73
    0x2c165a01d0b40192020300c0c0a0b940c0e01610954a4015009200040d071507404021240c10003a040d0001030801e1030456140805405000b901e03080c0c1c8941c4201048013013100700c010f000c401d0814281d826002040164050b545203005030080180941d4046071500f054000f40c0c260050344140d1007192460b91405030030320782c1311a40e044a070348840d84130f140c020798400346c4004c039032034466002e45e6410741c000300160b85072003a0510926081459002007144c02146551088055100c0307255070440b51f0120006484c0c00c928605500d1000b069807030380c2c1d54245020048031724044410801c11b1500840300503100035440f01d081c40704100426a070440c0c0440c41c2c25000c144020b11070b60040c8258090000314a00700540400c6000f0250703c1032400000c10398030752041c4903001c0c0c0b09000b900010003010005500c1c03e8200a401e40e8680801000b984c46541103000080c81c00b070b8003600311428020b08000030040340c50305d85041020040f080440454038402c40305025000000000d0243c1a03a03001203c00149444190307 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 781800926 1250 781799676 781799699
    0xf040203210d050103030206180106141017100f0b0910200f011d061603021e0c1f0e280f0309050102010b0a0513200a0e0301050f10 58
    0x25040304100720400004040042600c1054042c44c420f034090030081c1041108003152a4846c881d001c041e91408604002c4070b880c0101d440c51154050b242480a40c041080039210304041003118079551482c0c0303041014014009503400195400007108a20701c0c1e8844000125034000d0311000c681210744101d401c0700542c06a082c1e820811510802400360381c0404810a00300301181c003040701660b46584481d17062031201c1d42540c0c541340700040200200d15005a4148a4022400c034035014140c1c00100500d669403600f104403110b14030070000d40e503680d8298151664075140452521006000c18602c41c07840780045c010314448142e00c00c024148082240f003c1101c07600071200c1c1d011200e0a84a0781c20000d1100c00014000714003130b80318050b002c0d14060000e8203541c0c2c40d05100f44a1b130758081080c4603596810190603083c0710a140e00040f500b03000310003031047c03081c030030940f502d06075006c5862030f0502c3c1d0080004054100a4000344403c0d00d8561849450405c15500365003042c26040c8103125264610 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 781802176 1250 781800926 781800973
    0x507171009120810120f05010c110a0f060b040c020a0c05040b0a03080d0612050f250303080a0609060801021809010506070b13020a030b01060f080c180f1305040b0f040203 75
    0x13002031060301d07990381c9072030040315a0000885001e00b034a44c110092020070301c11a20b0f0792180742042c801203120054181d890354002c00000704800d036229070307103024800d155202000d82c0d000130344104055008010040d607200310002c401c0700c6900101e030380850035080c02d0044c510304c20030107005811400e0441d41e4507521600804001c4800a545410000c1d0110066501c0680c07240076002911492084d00c05030350401c0a21810b00803988101c01240400d00c0c0c03180039000480740c041ca00385010b03440c2c2900007006400540d000d0440941071070000300b04110706600800000380b02071070f4035a5603549041441202c1000340315543d0f1220061111034040790240741c00f070398080740c6c07800040b4000300250f0004921500716081915101c20000061000703542052074641c440c001c40c105603c280c50034032507c814600c100316210b19045800c80155006454008003d04281c400501f141d2004808240000c01481c00b141d0a27203081c1a002c0110f68520b48001c5164095030300171700500a0b0068003610321a010062 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 781803426 1250 781802176 781802191
    0x702011104090e030f03040809090114030616030e06040501150501020c0303040e060109180b0915030705120f030403142b030207022707081501090e060d05071710091208 74
    0xc00a00b42d45c00505401188528410700076240c944402d0014032804120503003116008842c0c0305101ca40c07554000414550011a0050031000c1d82c40c0413500300d0250645034280d58041c820202404108030040d080b004020200a0481050130782d80c0c0e004982c0c0c0d030340f01d040b0140c040d0010042404003142d4004480d512a0060510507145681c4202c200c0005c05008495000c840e540e070000c4901d8500803140320340003c42c1104002d070000c40780c8002610f40741c003441018807485c8124816140040e00744510407101104405803520340e030396410281030a448070014107903a070140d81c02d481203071507003443c1401200607050035401c11114160410f400a5005060990b441030503000c41c015101002c0461440708100d06008900c0340c14200380191002c20050704005102080d15004d0030966840012201102c0b070408510416407a000041451898a510040c09078080c00801040e44000c21a01d0020f01d5100000c586001000c800c01c50b04461440000402c0306031402c404e6100207100d2400603421048 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 781804676 1250 781803426 781803433
    0x2101a13060b160303060b040311040b120a0302060103053003091207140106090209030c0402030a1d0d08090a0c050d060e03210c07022223060301050702011104090e 72
    0x1210b4a050b8980c2c2c01050ba04000380082d00f801e0b03010580e16008400041421381030303803810a403d5984024030241500c04840c000c0d5070700e80030000c542e9a528808170000a0040648420302140d083c02900c80600340000c1d501c034459461102c0ca0b00610b58a0307088084002e030010300c0342e03d01682035400a0390014080040a1154030b000f000541e07403400051400b18400c0741081e001c0b42c44109580e0a41c0c8080e8012860544184a00351598030085450081c40600722401660b0b60750783d400c080024404040310b00c1a4000802c8403540c0c881e0700199410341c020481e2a512030580e54960134a40e60310315560010551303460707590104040d040410403110902d00ca10400302d01c14072400041c40c51600452542050903002404041040d100001000c2d0444030100c0b0551515401c0d07004107000e026840d07001100380450b28404d0108480c2c560051503010b00041940001210050400088413003cad601035101c1c4d407802c00401d00d2640140b00d42c00c4042c0c0c080d100942007a1038000948018800800d1214042c003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 781805926 1250 781804676 781804679
    0x6060f0b310603020d0b3003070b010803040503060a0504020a120809040f0c0f02010e0a12120903021506030109030f0f1214013b19140702101a1306 65
    0x8072100030040035145035603005071a840e6010380d000c00e44003441007842c00741c1e003000207800b0108080503c0c032a124041100f40603104400c440030300d1a511911402601c20440980089548540400107108540c0100c08a50683d00c50500c01c81c200c0e032007900c000b9441001c2000402110800d902f00211130760103145120304220100c2d0102e401c2c2c892205903103901079942c00c00d024040307030400890200b2a110f40300030040c81080d5130340c6640c0d4403c191000b402400a030310180701c0c030310310a2000070010140a28284102d5104e4503002c2e41d0740c10044400c800d5040b840300010500c1c1014418002a960165918400901000c1003511403511100e8000208100311151600359003840c020000d41001c913103141c068a41c0340044015615a854800c1d41000d103103080c1d0013003011242e40801580140204c0300314410340312085100002e62958070380151650034146041d4011048621242c07051446809403245041c0114030705044906042e11042a040f00c11100506802c2a100d0402c0d40c00020300b0000c0c045 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 781807176 1250 781805926 781806007
    0xf03030b060c06070906020f0a0b18030403050102073e040209060408060603060106051306030b27040b060a060f0e2704031403011a18190306060f0b 65
    0x1d40c081d42c0000038591101007440506588852010001c4c0f42c2d500c0030303068082c11801019141d0003142c0c0080e04000418012405400a0151003058256803108880d50b0b980c0d6032511038042d4000c1c43e01a5502d01c00350b03030141d40f035000c003d21689980980c6c44680c84458866007052402d0716401840a400c40e60a000a558130b850310b43c002c1c0007829242c00140510f00e0709071b080500d080c1d016001002040303828001c030032840752450126000c0d900d09007000b00d01141060f0100e060752807000132039100d00c079010407508604070b0b031818568041d90240080d901a87c1d250002e011954042d885003000107441010807d121600c1190f16901085000f4a03001901012014a04100050a994100801240041c0030402d5000355007105038109816442e8115071418203020960340c4190403181080d40c00040d01c0c00c0c1722500200745041c441000f0301e44903c0c1c1400941c070100840380f074042111407500e00780000c5200e8040b444004100c4044580c2c240c41c2144d030322001640340c41c03079400714030f40b0031801605090314 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 781808426 1250 781807176 781807189
    0x10f030f0f05102d05091302060f03060f150d021e120910150b0304051c020706020d0c0f240f14011202090a0c020709020d0e07150c0f03030b 62
    0x35100c00c1e04800d841411300c2886031480b1a541c900020301d000040c164548503800e40c0c03e0108a070001c49030714107280d583c540340080e042c6040600940c0300340c0004520440c00f1402d0095405940240c42d048182c5518400380280e807d100c010a8260910500c20303034203400c019400502e045000c2529858000120121a1560381c0200710909968000442040342d409002c1180105070112214180a1101c581c0848154044240030b0300c801000000002000c0c45810880c0511820718440b8411000d81008002910707060b10b409401c0043c005c0c444900c200903c200c603507405241d00b01006401da40104c0d41c5a00724460740c2184c040c01102e0a402400c00e6000310321803c01e82501041001c12490b450152907018180140c20038482c05491001c0340d000358840c2a503c40d030240c900c0d0350003d000d00c0201000d0380b40000740d5014002803400052644516102504650f148211650885140503124845941144440519200054000c0c0c000c08045403a0800b800445070207418001340c103000101c0450503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 781809676 1250 781808426 781808431
    0xc131403060c0f1c05010915300203100c09080a03020c1c0b15131b0c0503160c08100605061903090605010611160b09010302091206040309030b070c02010f030f0f05 72
    0x70b216540e08010400c22542380100e120301b9000ca502201400d0600000c949007103d1501c1d0b9222a120800e05984402c0461102c05080e0750001c044404501c1b40c0d04043d4050800420074800085060900051610000034818180b66041c0c01600200309617009000c1091f20f2401a01200c490b00d404071808075140011481c041c00300d07827401e200c40f45d8105050100c1000c0005008810500d0404281c0800003134031800440d06106242c50f41a5048034100207245016a20340303102060214080c490070403441004460440e190f440988110404142101003100c10b248070700d9412480420072140248000d806035612070b4100d080008a1034403d480e21070844a098101d000401c07881d103284904944204904001e088284490681d55400c14050703003c10302511460301d0606401082d09900b80c0e5440d460f100032821800d0456060345007030300f402491b0101c248400d89004110f0400b203071602e0f03c02c624500e603c1e80c0685500040010480381100240302c0d0300070010f40607031f861070f08000e4031946020341170 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 781810926 1250 781809676 781809727
    0x70803011806150c0201030b010e030f010e121e0a110105160e0405010f29070b06011b08120c0c07062a0c1412060c131403060c0f 57
    0x7503110300000d0241141c44540002c102040c1c44001c07083e0065000d0f0399001c08640c280f0300490f0308625440161605921800025854002d4000411403ca41580910120401e5104580d10b0201115010000d0301c50240c0c103c01400c4481c0f140410610340f480200f1040003e460459003481d41205030508440069440c0034110380c1101c024440f0541c06080c280c03100c03000300d03400c0242d03504d0100040d1203948948900a10030720f0240700030601c06c1202c407100f1355035031a000c500c940c0c601581c034198001190441d00d1703501142c1200310341c19070100003004280d4a580c0c85440740c0c0c9020000307408211070903001000d1440c090b100b04020348403401c040c00340388000c03d4a92a18008800c02403454604118180089114400441101404070b20300031861801c0b00c01d03003c100d10207800708801040d281c80303621003490340a21808040c025810b074454024075501103810000300c1007030780b254a4400140d001005481d410791084000c0307440c58441e40c00070509141502c80705880c1160441c404111480300d001d00c2c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 781812176 1250 781810926 781810949
    0x50a0602031e0601210b13020708121e13060b03150a0c17040f02010302070507140a06051908070912050303180105061c06150308070309140307061407080301 69
    0x4100c114030b15a42d0300030200b4280a94244d551101303100da01c480c08100307003502c140c58080d00c0000341c41e8600c902010407503182c815940e0350b400b0300340130740d290340007071a00819800f04000083c1e50081802120b20100303455a0392500b2512014000495018400c00541d01c2650703400301414240d4040003000314500b070403200341c0182e00d40701c840f00007264024400c1c1302c28081060404150361002e42001644075a010748454501d141c00d0004038000c0c0100e000043c400d204100000c61407529040044940840c1106d01021350307138580d002100c65015101d14404a45680d450340b02c01e0740d001e80c00d0aa8041251f00d040c01545a580c0181c0c0806107a400096602e5000041402a19511080c001d07030440d441d8002032215081c4040403941c141c105c540115060890003000e041040041d4221900c4100c0d0304c0c0c16081c002d03031642007074609540056800c90101e02c91003c0000c10055042c901c0c2000c06e001805048043d2801d001070f61605d128004000800c43c0420640001a180300d002d14040d0820b440013 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 781813426 1250 781812176 781812211
    0x6010302040b0c0a06050f130308042306100812030609151309020a0e010f1a0405091006030c021b060705150906091207081c090f050606010e0a0e0c0304050a060203 72
    0x218100c40025220144500100c0c04200440c03007100341d200d1059030309d45090052075444c2c0c01c117011078100c440200342a080340c52000c0091100002401802203030319006440204e40d86207106076a80743d11030300b18400b851042c03000400c189048524a0361010354500b01d120007901200c0000c0d9500361191007666a15a101000d0055050030301410010f0900c0301e18251247d41081c42600d0140b14503c504200803414800c40103c0e03440040c00d0760024880604105110b0828004440c621a00e42c09050000781c1341142840150707100041e0440304483e42e055525003030b42d14106100e083d0b03100e030b50150380302e11a00d8210158002c0490f5420301c21081d240c00b4100300c1c10302030314071400e04031410710411038044140103a00c00f19051000301c1d40d55206601404440000340c00c3e80c4409004603000140103031070000d550703006008010642c907200d804242c1e41e405403e110f440c100a01901c0368061110702d0a036400000e0440c07034400e00216003150061084401310541d60340d4110590f0700481d10703074110340443c281 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 781814676 1250 781813426 781813433
    0x20c0103020f1c1e0905030f0c030d23070206101707080316050d05030408030c130315090b0603010612060b010e0d150612031211041509290d0506010302040b0c0a 71
    0x1080b21300441020000e01c00e0700825103070f0070380c1c034001c4100c0201c04441c006040f000b050b03000c00c1110070300101c1c88401c3c0310104103160304c080700c807200001081c000c01441001500561004c12418400c208410060400f903041c000114500c0c5030b46120020385201e10000880e08100800c0a001440b00250103140c02c44401d1915a0420304ac3d0819003003270120900070b12000070f08400a80307510000082c40d29807240c105034413400e03485110381d001902001802c480280c0c03084c2541c1005103d140141d690b55070980b2010245030032644540300e001c0c640f12410402e60009100e50300003140c0e44105250443c50744000000148191703029400441d28920070071820a03044041e80211001096030582801e07442e60315031000b0b080d848060b13561140003991100d0001220444034107a5014003410441003100800c07205000d40003241c01d00901d10500e06010641c402e9000c0d2590300304e50000d0b07050f8610305001c020102d900c080c2c600034102d5170500d50240408548158180c4c01380c00b002022200401190300a0304 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 781815926 1250 781814676 781814711
    0x9060815150412410102070606060206060301051f0306050414011d0d02161401020a0501110703030501050306060a03120306051903020127150c0f0308010315050106020c0103020f1c 79
    0x4140440740035810b00c0e0b5058a01300003c04600c00485214802c180081c0b048586009205098000301401d281c89000300c0d0903640000c480f031290703c0960003005540c071401220f4180b09035818840da4415512041400081c540350030941d0028802d11000c3c10a0001c44130141c01c1d100ca0303007130813407a412410a1401001004012a840c00081c50028052407040e011900c0d1051000303020315200c01c1c0e00000c0500042e44200098090150000001c02c0955134a400d03850303003136124810503000a820b25002042c10b1901240b0b00340102002000302c1003203869941c881012840b0360700c2c0007017030556404002406440d0701c040c9100c1720315101d0348012140c1c21407001600c500c00205020b10300c52020a44d1040c42084c3c0c1d2402801c0d01c80e0100130b0b41c10145a04411258103007030600c010105404540c21108040d00321098905072072145401c40c00b22035009192a0442d00d0074403d040050b0b01001800d50154040d600408080710404030345d52404503160304818421040c1c04c0594851a90303000340d0307500c801c02039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 781817176 1250 781815926 781815953
    0x40305130b0421080d0f02091203211308030702370618020d29040503041202060412030818071406160b04050304140109060815150412 59
    0x1190464140b03401d10080985114a043c1410001c480441e20881442641030590701c942200b402d042c800e850b00042d42401a40240d0b003000d00582d8102040340c1840d038007206440b0108250501d4801c2c0d80e85041c07818140407009040384480c048101c0010700440e80880040d40315049a400500b0207403480c00401c00e55240346184012083c841010f0030304562445481c3c0640c454101c180440c5c03c0001c1030a0f90a50450f50100a610003122903442007084071204004086003022a1100c01404001d5035042562a0071100100306810400041c80500c0765400b98624450020b00400d040c01c1e180d403540e4500c00c11034401540400e09079402c201e09c1c1c3c00c1c1148001100c00400d0054180a8940040c0d0150040341c1c030303100c7e481550301203214441c070340151003020300042e000008803119003004d040141d10303075205004d05104000c04001c6144654011302148084408603a1048165503408985421445003036030501d600440782204005c01106400c0604060b000c104115162464a440c01090701e0050307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 781818426 1250 781817176 781817189
    0xf4303050c03061306050d200a03030503010911040e0c1206060c0d080c09060f07061104030b0105120f030a02160f0b0a0507060e10141806150406030b04030513 70
    0x4000800048455400c1643d401801c00c1d500d002503200c0015a000c040d20840d007149400600d1002c60f1070511a6244000881001c258061544c01c1d15841c140300702604107000c0a004200200010001c2c41942d600078400d01103103804003030900784ca4491440d202030041c4c641005211020a050500031410810b0729088101100c02c11b140c140e0b02c150352078030341043c07014480070700c12480001501030a03010b007111911403005281940d40d4000340500c5103103401c400c1040d01c00f0b500e400543c83d81924207404680540750442041701c0d00342e00c6c246c05c024060400e003201c03803890b0082c003024421039041040039015903042c603006080200000d030a4600f042481e5800340321403001858041041e00045002c035440364211349080365441090741000d07009060310610071041481207008100c404080d542c0500c8940070920600c1c83c59440f0350003111554680c600d1004503d4006a011407403011600340743d8054158058400709240c1d80e20f840340c01c44150221002e07070104100140706040400a8034200018254 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 781819676 1250 781818426 781818431
    0x110613020f010302090102120a0503040506100303020a0f0203030912030c0c0d0c0603230a05010609122f04090f03080f040302060402090c12180f0c03060f4303 70
    0x1803a000140160928445141403690004150b00240d1003032141082400b0070400345aa10407039034900600583c0121015292030107110301064042c2c144506d49030440780c01d80d00500800710540c8030b81c0d50380700c560602280c2c548000c00030117803180c6950b46036032980310b1036101a40d110051107002c02e0910000f0b010003403040c100d021040d00051196034207041610000e01c0c00003a0000d400a00810900003200900304201144081100010341500f001e4140c0305180d40d482c4e00301d0b43e10001e08004804074000180100d80305540d0050303030208061183d05291401110210044403400824216146860161412401509030406140c0c20841d41030700034540a602e09050318143d00c0007500e9900c042c00c02441000080e0100352500300260903900c401d500316500c2e11040c105030383c1c821420040485114844d00420701a8440210085503070246164042e014205076039500c0d40c8180070f0a0000c0030116031040a551154401c203081c9070029480d50071441d030815a50b03d003030b03e01c1d00d2a13502c200701d01c08050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 781820926 1250 781819676 781819711
    0x714030a080409020306010921120e1e19030312051f1403150a0b010905060307050f1606020c070306060f060f050310150c2603130c030c03031106 64
    0x350401d08680496094a60041c1c40351900e1004851141c440e40c020321003d041040000a19059401560300c0070b4883c406403a040002e003241540e4001c0300049140c1e220341031001203046012014102549604010802660480b01000c460f8080b16180c0003030340060a030818910030300800780700d010b40048440503e403012861f1315802d000c1000305400b82c1021103c0718810301006840c100200c820744001e8018401503440d18845080041450602c00340c000782581200042c9403e00c4800c5234014019651014500312503018030b0040c551001c0c14407544000f0400c1803501003099071000d002148000b00c041d01240740713503040c00015a58542c02001c45800480700800126800c064040f500341d00d01d00b80551aa070302c01420150801c0a40c0c8681001c240c800c5103c4901a030000b000c1e05c102d48106492054590381a8000841a09180203040400780410100e04c051a0704e103d00360205102e9070741105e00f240c03240c0d50785512841643c41280070030100c5807070700306258080c00f01540c00042c0301c000f03540d0700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 781822176 1250 781820926 781820933
    0x3010603051f02070609151b020c0f01020c0d05010c0f0513050409110a06080108010c0c0c03021c060f0911041a060c030f030c070302060906130305030a0b120714030a 73
    0x80012a40004201042002c8500300e940707a6015244125001101000f40c1c5074142000f812a050103001c070391500c3d140100c15144c60600e0090324410b55003550007400b29208020030b00030903561075000c060545c0305404c454030f800e56450b121840640d00c50800410031003004072010f40028526200d81c414003506221904409582d92003100407604102c2e030210f0f030414141050541080f0800029410100c0801d000c207089401081c1113040b19030400082102a44169003203403020050040100550000344c81080503142a07001d5101500310307441c1010986082c0e035503580443c0c400e89413075005140c4803076061007400840e400f00340c1001d8050b1001e1020103515030701c8203112500d402984d0f119070300c0031a096680c100104292095840880d8070300340d59003846100490241c0156004500500c00c0000090f008600420f85901418070030b4110400e0140c266802d8455400c01461600015507070320051a00359541c2e41810300d0307001c290300545030560400d03285001e8401140070711402580300880c02c4000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 781823426 1250 781822176 781822183
    0xf010804030c0308060d060e070e010b04080615040219171605030a1a13020d060b040b0304080a02012a09620f0601030b04060507110609010e0c0301060305 68
    0xb07095052612000e55511507001811003c0d00640c00f810071460100000445400002d6042c10f131a02d88100340c900740c0e41c0d13648190003880340c0d010b4000c0076007001003c0340c02040d2070311310303d51044030040015042541d841c0840b1080d450003a000c400150140c3c814540c0c1c81220480340360400740d608070034407400d0000c10003d080c910001d404108900d58138451035010045403844405e402d0f41c000d02813103038140f41885110203504101c880c00100c9103414000100f01480008a504480c040d240603815540c541c1c40303c00385900b2a441842c1076540702c14450504020b16540c00c01d00440400c506d00c601111030600a051851a820801c44417585003c0d0a03154a0101c40500300020000004400d0001c03000004240c8a462400301107041441d600403980c45400a61100101107220304031025005010f50007030740d481c2c0a20002e04400c0e1010082008a05281c11256114440e0300307000000718101c000c4146400001c550101c0c3c243d560f6403408038198070034000e4001212049000380203c50440e2600341d00d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 781824676 1250 781823426 781823447
    0x40510050901050727034803081b0d0c06150f26030a050712090303090e09160b0d060509040809061e04030302011407020d1d03150a0b0f01080403 64
    0x150440c08050410351980c17040030102640c1d1024080c0c012584a080c0406480750041e1503000740701180322151101c3c80351101968218100c0382180780300d24a161034800040e84090684910304090a14030040c0c00d200700405c1300d4400007556100c07840358940c1007141c111084005020584e02d055102005100c2620303440342e05969003030400d01c03420f0a02c0c00b5640b4000c916424407944500000c41c40d104220f8210020f0714169000d0310300390000940d1540112036a111740d002c0140410024501441841a0f01c08811342c03047c148412070340c1c0b142490301700307008a642585c804001c0540000f0b811910407084d014240062a06480e00c40307103820190703210a0309019100c90b860241d0004100580000c41d454203038804002c05210190b91140c0b2410300a01034141d8130140c1d03c1075054807001c2440244006203000900010355610110156810060510142c2200381c2e540d1500c110040d10048111500c8598080d0200d010001200400c00050000501400c0c00240c1407140d40d4081001181d08031501c01e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 781825926 1250 781824676 781824707
    0x806040e1c0e0d0c0611060106080f0a0b06120a0f09110607020406030c0e0103060507110c0d030201020904061212020d0507110103061205030d050141090405100509010507 75
    0x180c0e04610488226940c00708040499800740c203d8802d0b1040c0b05800440c04241c8041e0f40da180e110200441d030b01a5202c0c401c1c41820700040311000040c20391b8041200c0241c0069200b074000c03600709000d50004d546500a400481e03081c600ca401480015415445003800d244481c02d803d000d1400540c17146510b030311521408900a440001e0058219030700c03540000040c640c454480d90b0031076141d4100500f260024082100d003e480c060200758030501075420881c803900744200510360081c05000b40201c0e620000c0d4200d042d99002c0c00241165034490094001504a662050071108005d04284003002c0d0034100400954120b01c5100070740d10750010403a15102c1c1c2090b010410052614012002840c855000079558006450341c0020800d01000501c0c41200003d030078003659884030050402c0e4420007524800c035071005d10207102c0c4840420344e1148003aa03810308040c0c0c203000c418081a4401002c4600b00d40710741041d0001d400440c3c0f1032007082e07080711011008003c01d142074100a00340c4200303400070b00c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 781827176 1250 781825926 781825963
    0x302010c020604080706020718050f420a090e280b0a051f0b041208040801050408120a02030c09120c040e010605031203100b0c190f030806040e 63
    0x40c015501c6420032503000f44081c0045a40315551508000c1d00c415090280f0307051035203492030b085c805086500959019032071000346560745454110008114101d402d09180c0c0100380500180d00a5030921040300350200a4601482020038000400050f032145030019080e1519009030190414400598003031022107800c03c1d107026500352000c60b10351030344070100201500001010490309800c4c6411240c02102c1000d0348080314004115440c1490342503018100103040d0610041107960701c0761064044035409942c800340380031b803907e03003260a68100315002c2c0c1d02004c1c0025440074002005c441241c0c0007500007011402e41c10300345c500a0442c440e00246512428580841c06012a0144561a0202c90041c800c2000c550403000c0350740601801d2241521030300941000e9081c1240c01403c40380b294a06800d0544020300344100c1603019003144949904501c40e0280c20341200d5100803800001a0154950940d0050640350003455008005d02960045080100103050341c107000071024502002c1e03400c0b9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 781828426 1250 781827176 781827197
    0x314010e1e0a1a092703070501060303030c1205090d0503060a08060f04050d050c0c0402091c110f0402040b07022b0624181e0f02070606080c011719020a03020912070b04030201 77
    0x1503521b14001c2c0e01002d4402c0d440c0210000030940c040d401075000012030703286c0385520640081048101d650484882440f03821100020f52200d10400003903034001c4000f05002086621011203500d401411070310b0210760442c081c240420312400700316101d002150381c80d0207407808429000c0203442e0100320704000d02a80d00400e240d0019075030491002650007101850070f0310f116840c104403003141c000e1b1401358011020340c801084241005d0089030141ea8000c0f144500d0f0801543c20b0145c0721082c0441502041010020382402d01148010007403418001c560101c0e043c080141c40b00042524901d1074500c0b005035940c02c0050b0100116100d005030a4004002803423001510f200c8544540d0400c002410f91a10a0414011585034040c00141c3c0c01410108070007038403148217039a12564210410b01041c502c0c20a03030130a1100700d01c4540e000d00c42000d540c81c0c0c6408000c111050740c1054140c00b000c2034010943c030015040c034150709011080110000d000b01c40c42c04030300740d805101d00c0c007020b410485035284 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 781829676 1250 781828426 781828501
    0x50a0903021c211b031104180b2d0a0303120510052107080d1b0305092214010321030b0a091b0314010e1e0a1a09 50
    0x1401c815030440e1041c3c10004080c104a6603005002070f81c00d4013111860303000c0198041c5e20a120b54080c480302c0d10900362400c2c0c2464051034211000c0c0c1408040180c0714079840043d6100c00010702100190380810380070440341d101b49041440400b0545600485070f28000b0000b1940c06442820020043c4800080c15160310380c8803d4107806c1d03034000c075401c1810b0085107030300b13801d01c00c1c0400f60303460f000025611030035201c042403a00c4510f0709001d0700000300e1082920350760002c6030800c070b1500c0b84641456444c10800c030001c591180c2094129040088075816201c03501c5d03420b802079464065514000c20000c2d0306580c0d4040fa00c00c40ca69286180c23840c03041c0c000c81381c81e0084d0f1040b020368070014902030006e034cc2c50400d03d002e021002d010b482c40c55800d502180a00780030703009403903141d0040001d00301d4981c2003c011002010008084c0807500c8009840d40c00e03001c03428002c01c0d000750000c030804136070340c11940d003a14112002808850b01991165041090660711804c0d0340001d58000040e050540104c0701 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 781830926 1250 781829676 781829687
    0x7031a0a060801060f0201020301261f05060906040b01200c0a0b130602030a0e0103020901030f02070605220f06090c050a06090509070c0305030a050a1104080c04050a0903021c 77
    0x80a00d82146200c0c201140441d0040c404504032041c99891421030070080e40300300c0c00e0340005e1044000b40b5048818404155045104c01301b094003c980440c0d04a000d07040031003044052005c8040c01c5981e481c418015075040900b40c0300d5102206a030144070481c01c50000030400030300241b2a14a0141d0740c003807440c8801c001d2202000d00c3d000289074907011500c07619410502e0b0302244001002c1001050001034560000c400c0d900c480d65161100c07888200301c80c0054001e03600580e420350415648200b070310000c2207944003a184181c0915400035007890140c64552422000c603100c00000c41107a1012070005c0c0c02e1030210b005281e40507030085007202c0c152030403101008540d08074a512008051000c19143ea00c0b0b501c0b034040741c00481c0d09500e9510b07681c0b4103865121a401c0d02a001034800c0002900c0c2e03a034a0740280d90002c1c0a800e001801d0000446017054680086e0040140340c2c01018400655141900456070440d062078001c000300720300d5590281d43c81c0c29558010b0614006614030900f0f841c02903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 781832176 1250 781830926 781830971
    0x150302030106080a15150503091e0d2f03070c050a050d11030a02031f0c051c0506152209050610200a06050919150b0301020c07080a0209010b030c030703 67
    0x20010380908106c3c00010342207820443d100c0c15240b14002581c8030540b41542d4407400762110901404c640030944100300c6200418107203030a4417a484204443c6c0100f154070303146001c10003841c0555210009031604803004407d9901040c40f0301c000c20b800384001d0b0b680481c030490040d23000810220700c2108501007410030700d081c140a581030050150868004040030b044c011322a0000c041040088078046094a49019407c070952600c0d1651140105142007a0310043e0040b000411210501c503c19101d881d240d0320942c0c0f14100200d8010801280e03040001d0107901910300010244024a0410b01050b0104140c0d217006c0c0070080841a0320004070715200c07030f182801c40007800740c0b400880c850800e88058242580c01d030314540700710140d001c0404061400050f800d6400b2650500000302d4581c0c1c00040c1915031002941950700300b0001401c0d00c810096917004081d15005410040c0140c01080340d02c03001640325001c203038402c000300801004044116540031000303013000201140c07000d104480e202001c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 781833426 1250 781832176 781832189
    0x2205090f0c0904021b0d051c06030512160b07180602071208070c0b03011217130501031a0a140118060203030c130b07051b030a030c1101020a0516150302030106080a15 73
    0x481b00f00c09042076002c0300610202e0100f10749514900140c3c01d1580882d03002d440040c240760000004000c100010300010281d0045880243d0030902603615403001104040c2c580801003100c10b8009a2400c60501e880340c01002180041c1c10510b142140c401c15800813400c1c000d02c0302d5000216402004039414500025100100c0e20030b880b5a15804881801d9203a00d40a44522011110104001d40b0460032100c030005005040c2d8181d40c51b150054001e02800c40c004441d407500794000745030300d03280c03036403c0030060540082480c8115141030000d41080700818112900005005007400f80c9034000003141d801c054004140c40d07686000711700b081503c4081b6040107903825000101d04062010008851204000000b464a0341c54204010103a40c0d410360f202c02008620043c42680208000d002a04100c2c1d02c180161408001d0659819090079480c000848000035190b5050241500c003410b410345824a5003011032035541800c201501ca1680208101c2499840740c00004110a01c04012001440c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 781834532 1106 781833426 781833433
    0xa0e12180d0302010209130504060507090b072d0f0b0a0225050a060203090f060c04030825050d03061d010f12082205090f0c0904021b 59
    0x210751100340c00b0365500b0b1012595a45071340e0b02e085103c1120b010700140c1854145480007c8940c0903280e2030411005480a0048070001412600207039040989408100c86004030145d810064029484000d03082c828114200480342c4c0402d2415032080b8407555150b682c03081d1800480c020070088265007980c100301450200340d4410381c1c021f12801501a94800c20503600e81006aa1003079400302102d9106000c0011441c1060102c00d0b000112035446610f010b14640300e00005000d00a4200c1d244040401001166400c821041c0c00444d4404c080d101c0c42041c00340040c00a14103407007503007810744e089800d0700104840010b0060680d4044842581d00d5800c00305002c2117042e401000302d43c6c0d09010400900311740001808103032107003040a840111581001c09000443c1d1001c0d0030003030a501c800060008401814061320100041035a00507121380d0750b2403c2403070b8460003810340b520038007 = true := by decide +kernel

theorem cover : BRFrame.Cov 781654676 781834532 := by
  have h0 := BRFrame.cov_init 781654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 781654676 ≤ n) (h2 : n < 781834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
