-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5517
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:07:24.744825+00:00
-- url     : https://prove2.me/submissions/6a4d84ca-09d4-4205-8ec2-6d87734e7c19

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 992086330 ≤ n < 992266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 992087580 1250 992086330 992086369
    0xb0a0b121b01050a02030c010c0c110405010f06110708120c1615030b0609030a060605040c030b210f060702010c0f030504050d050a0e180a060e160c1425050d02 70
    0x900e8910540241b043d6601014048020000100300701c40051225601000603500c0e1000c08a01c190a814140229810f07608224199460b0a00d401c908032000310030502444c5280c0541000800c4100c4240b04000841e10f42042940d190b00703034030010600b001c00c0302c002c2140e118864902005010007103880104460882d00f00010100160320100f0340d40d21540c0d400c6a40350062048140402010740d100360141d84040d2410400442c0c807000a41c11a0003c5041071790050707440744541a11192410f020600740384070019030f00f9641012030240c0c50300b04240c0328400984d44070664a40200da120394420685862468148928142074540c1030b2506070b0749541c40100800083c0701c2c00da20740580c42c1481103030005090346919a01c91300d1005046034007a41d1180c0101c2c1071040c00642c0207500703030016009460b000240000401d104800340d40c09440103200f25115401074891080c4501c1c107226002c1113900280b1b000c14014a215a0b40441303115a40050344030766903040071000940ca070003202400b81c514454 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 992088830 1250 992087580 992087587
    0x40527060904030c080c070f05060a020a0f06090507090203070221161403340804140109120b0604060608090d03020d0207140304181806180b0a0b121b0105 68
    0xf82200c1310400c038030b00034194000000d01c02d41000e600040c0c10b03040341e01c00d104540c0d030140c403242000070510540c80d8510069010411040110301c505403181078892280740000f91100060380d038181440c209074005030015501200b0809a15011302c803009440c80e500c0310701140d10768400d0090382c15005d0b280019a0041c19940017408100710080d050a006034100200e0ba101d0316440414107070310395400c6000d9940410204945e02201191111440340b940c04002c942c03c9c81d0406004a44c000c0b03001c09024100300512000140003180d5041c0c03039074031500501202c105c518041d070610050350341640c040030402881000700003c11002117901c0e0440056480c1c00740c1c1d02e40704404220080c0c0244480540308080d0b14045043c03080c000001801102c0d00d5004101000e6080c0c6000350403144005040b069228000d251900003480540c0045680c0801d0079041130308228648502e100044111003200196a40307036109040f51800724140800c0d0351400008000d01c1d200c0002c0300c50545c103801105810b00c034010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 992090080 1250 992088830 992088833
    0xa0f0603051012240626030c1c0201140403030902120a2a080706081f03030207030803041a0103050705030c09090c040504051e0601091b081b0c03070503040527060904 73
    0x401c80c102e44200c2c1010521417203445c0c94101090280d4a090308003e8080e8100443c0090808000d850384803440c240608051505203040361800021104d010045558030f040302185150f40d07a401d2800356001ea81c002541c2c0350030740b050040710b20f00254103008903841006441d00140107032200e00020004c01c44d08440f078a10305580401140001e410040e600d004075140403401c0c540c4034081c244504855954499104107040d66100402120300014005030403901d002c0c4003088000c002960807600c41d009480644c084200c10340c40741e1501780c0007190345820005003003203c0d25040015030343c0c442085a8180b05401c04504040d030300c0a0400e1041d000f03070b842d580000c00f07018003805402d1849103c0c3d1001110701180c00e1007591100e409014a6603021310f044001103424880d00121802d54029459521072922810a000c840c6a21039401c0050704004118200002c4003d20203424501c0c46000196101c600f40001c01c1510400350034006181285138041528030105041002d030002000d542c590b0581e1985d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 992091330 1250 992090080 992090123
    0x1c0305090303160f0c050d050a0204090836150304170c150708071125050d0f151b03050a020702100e09090f030a0302090307050a0f0603051012 63
    0xa0710086019010243c0703e1200b80300814000c0c003682c1d0b1041c80700031006030310390003008101c102c00c01e009001503010b41d1489006081903446440f0312402203e00030b05202c1041c9140e00f06064202803071440f903c540380a08001322210780b2141a2040c02c90b400f008c44c1203003c003549258000100050858910111640450500307041142c52502120040d50321280f981030071500362041c1982c2003400150002d0020b200303540700e625401445c1c0100340c0039010f02c0007000340d8a148a8a0100d03c06500d1994200025240d074401c0741020388180715a500c0c04820310142800e16203000c1c0b0b0500542e4141c1402c4a880f007a00c1c21403842d4002c03207458100056651120050395000b800383c10002900200701c0f52014059036040ba034984229001201c0e9540385603038411071a6103998903000c1c00c01c001d6200703200342422903009801a141e541005811150450f0380c80300014500e9100f0313030090b0f92241001c2418400141c0c14001c0302d80c89401c0259509a0078904800717a00c000c0e034071a2014140520515080401014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 992092580 1250 992091330 992091337
    0x6050127030501021314030109151d030318070909080405060c100203194d0406030b0108070311040b030c121501030f092d120f030b1c0305090303 64
    0x2c00c01c00031074035102100740b460b00d1524603000308410749441001a2034a49014003c100312690b010182030f82c14808a8213150280c00c0244500d1804580c181a030340b0245000c00185108030140306004c580d41103a03e414501b02103180d00545490b904100b46c4d103001c40e04900c104c2c2c0440e1815520b0965500038240c0b01400c240d4051600f001c20340c000000c0c00401c42c0580781045210300700400c01c1107150300079222941c0340804050400c60280480c0c00c030403000100303401081c099035004c114200d00c00c103922001d44010b130305c60b03003003440426070354207080309507583c0f19030707411340c419042c1c1000c00c808141c1300440c4e0141c0c0181d10551459040010000d03050090203c25a5090545600d007202d20b428401c903045428034181d4100c03400249003030140201c05c1c565000304a5240d800c018000c1101c103155918011052001c40c0c2c28000703414a900c80d01c00205003101142d06010560f6482000b952007100060940e4071500c0010320642416011490400010700103000d51580b42c10015901c100c81e50107c0e04601 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 992093830 1250 992092580 992092583
    0x120a030503100f14010e0303031b0c07050d150506090403020604081602040c0201050a23130302120a030605131e0509100e0309040b0303070c090b240c07090605012703 73
    0x1a450100026001c4c3c0c034111412a00c1e4090700c0381600480326805150b9280000c507101103102c400404068007900d000f400509900c061001039542c0079480f0408101018003078401150480c1100c81c50f90110400c611626070445d00840390b032111818241c03030095171030001420240c4400c20000340c1409104410100381c000700e0707000d07105128150246c90080c0c02000e0449140580f541030114282038006202c03d0401e05140352a0002000d444844011001d000c090100714254400e0051511647c07030804064130346c15601d80e40c0400c0850408040c03203201041041544000c0b0f0808500440310740e000d00d000c86044801250016143e501c01c000d2500d000f4801070030303400c514941204070141c81c44c04401407920940c281c1d414440c0d000004141a942d20400c231010700f1140150509000c0900d4581219081c58001030101040310081211410b0100f031411121900f03800000e0380606c4480c017401a81e0042607003260400000d854000081c001d44103490032580144000240c42042d906e01511250245 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 992095080 1250 992093830 992093849
    0xf0c0106151205060109050105120c09041410060e090402010f0918060f0b0909040b0a060317070312090b0c07150509030a14040602031606021c0b0a05120a03050310 72
    0x3920345a1010b0400002c5184800c5010f040400041d011350280241a0844030180c0d01c880c90001d000403c8404120041c1000b2423861081242c00010368480c0100c2c0a00c2805c07007031710b980609020850043c0100e291344200140046200e00c0c21351580c45c01d080507802502804c0012040240100840748101c040d041001402d03114110352518900940c0480300355034804085c48007058030790b200420f840c00b4101040380c0c000e54440020b00041c80410700b15401031000200443d0b1561070340e480300c441000307009580e1003596005c9081c50925500c005809600b40044204000c60750042d241c1404041c8001c0a403030181e48002001c0302000100d880087c4040341d101c104115500f08404802d459078003a17400c000001d41e18004c084d492641803401c81e8100c9091b600194600001c0d140300560f03e40c0d1060702642c41c19030034001400d0901a1000c3c11000c054940000140070303120b481008030414080d0069409041100c03406a04540001000202d654260800581b2603880c40c00310201c5261716004003041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 992096330 1250 992095080 992095109
    0x6120203060f0d1209120209011403071502060402131407030c0e06040e0f18030301260a2f0307120507080a0302330402040c0e0a26070501050f0c0106 66
    0x180203103130409035200000c03584e89816056464070b0131032107850707001000f0394480c0c00710004200c04400106c42204c130300301c050203480c029540c4505900d05030104d0509800075801100c100700c114a091068ad07400303055814000c202d050781c141401031400000a01840c00c1c1540c640000d0a454084c2103040000c010003081140d8558076072005000c0d100c0155581058010410085a02d90110086140d10f11142400860031686040883e4501042214102c00300701d25400e0680396441080c000044040d020f281882e070b200b22580781c06d00c25281c40a060441c0100070003031013021542c010030b440b41210607004190780d151015003840d5040000584c0072810512481d9403c0017003507000f041c1c1c00e5801004424080d0101c00341410308034440103500c08415580a00d200040041c80c0a6000112030046407401c90343c144003800124100c0841500001100380700c42c5034401c0800d002d44840a941105c00d005803101030b14150020b440c900500f2071a03245c0100c0441d1000030017809511001c010491442074502 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 992097580 1250 992096330 992096333
    0x201061214010b01020f03120c091503091002090a091a100c1709010c1401090b07020a0516050f150717090415141e03070f1d0106120203060f0d 63
    0x7a505402507214080c0e50800c1c090040641c00840e50307150075802034026610301600b020b892480e0200042040e022103000740100200c3d0744401e00d0700d01510400180c00e940d20705184904a00d000c0c0c00c14010881c060042021030a02e840701c0290310101c4034020404110b0717048000f031360580c0b04060a2003540154006880a000036840500c44a5a0b40154030841d40040c1c0c01d01030000b944031760740c040c501051000d030b1403c0009850424054008041100010f039445a95607508250f81c0c096400c000140e1061040c5014848103021101001300001c0151401c070785001c0200b01c0d018280c1110500c10940d5280030700341101084111580203920007482d00820584201c030f22802d40102150502403450002c074600100c1800c03560b2030549a2900144580411000801011402c00e45052101c4041943d000e009034804020705005404842140c8210f642060811000c5104e4100c407408117051000042000300d4000c50b11141c1e844003407001603540da8510f03001c118082e00806c04c20303400800c001d85080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 992098830 1250 992097580 992097593
    0xc0a2301031d212104320d09140d08040305030c070914060f060c1e060703050912030415060b13080d030b030c1c0213092d0605040302010612 62
    0x24000c602e00d040c940d1500758810361042c0c001d03000707280101c800c2801c4030140814840f00391980284502200904000020b14910010b02e440b0b0551b8410060090030b000d080c8000d00a020a00045183c41d200035840c01c80c0314400640c00031300d654010004851050305000182049802841c1c02004070b035600c1e844400e24a80e903428620510b440c0c2841d00d281003d000e075400103042d0081c04024202d03242450501c04012242e440132110030903911440031b60b81d074080046140c480f0351400c40380181010340b400b003a020b019074000030500325080d08141c00345ca0b161902407055171381040c3c12402c4e030b10034921440204401024282c2201020000100d44450002c114800c80c00589142e0320a441c4038280d01c44d0258141c80ca41d100966054124201d01199410010886c841145089030090880b01d815000301d00d1040c0c0c2402100030554031201d028060203420010350044042c0f507512000c3d401000440c2d0140c141403400c008283d10340301c0002c0323814903100750412405440c2481400d046012286490f1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 992100080 1250 992098830 992098843
    0x30e0a080304091d030a08101503060302030115060f05030606040e010e10050109180b0d12080a0513030504150e090c1b0a020f060c2803020c0a2301031d 67
    0x40400d02e04210b5213901d00214941c00c0d24001205030b00070350500c0c6c6020410b90f82c00e44000e00c0074003620040c82000803840400d1880304001c003142d0324005400c5043d801410309603041a0305060a62801610402c00b2690041c540d4001c2c0b0403e25001d512a121000040c406104951102c07824500701d01c004110640203900c3d160107402450010740050395030344015100d40030544a61030b100c11042000b0f4003011841d40140c0c142a00c0205030300900c200e260b4803a445440c822210a0010b0140805c04c004c510356032080c207410040280d05018818016600105240300300d00a40840d1016441c42c10320481c0281c44101050300700400c510001d01d010780b0241d01c55000442414451108400d8069041002003600010343c0d40103482c4c07102030a40c0e101808660b50091031100124400e0300000325031907000030a4180881c00c101c1e00311203501d0f6079003402450102600c01140c483c02e64900c00700407040503c09045100c0c0c00d05140f0100c143d40140040e030040c10b0095001c140031100403145d440c00c14012804 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 992101330 1250 992100080 992100089
    0x3010504030f0e0111120901020a15061d04020618010c050d050a2a0f0c0b040b09100e0906040b030c09010e0403030612031727010509061605030a09030e0a080304 71
    0x1a160043c40200c01102c0c07643c8010300403c0650000780007a13440601d0140144a0080180104c41d1070512960300c40100300e40c1c40c50280314150340c0c0d01052107400210800742c148918038200c4813485050507000158144161440e01c030302910b0302d000c3c880480e4050a4818045038001e010b030359040c8003604003c3c005520810041c00060100111a801c880a0000035641600884071490032603c4a54800d2600300c0d8900068400181170600050451045c47c020005440f00258580d2a000f403081407048540302c00500105001242e14544c0c000d46a0046040d403110b0219404030b030710030b030300c07030101e0300305054005c10541050b0000004030b09070741d1442940b800342d0700c0703035074100704042d0b660112110500154000400142400d1031810406003281c5d622600000031007250320180420b03034881c601141120403400010394459003040380100f0700303004e107a41c407080800580800201d81d0b24000e1030342c0700081c40c210145541c1d080203020302d4880d04d5840e40d45071b00a4000800300c0e803180191030752900305214 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 992102580 1250 992101330 992101337
    0x504180e0d030f0f15030f0309030804060914010c080d050a02090a0b12090604050319090e01080a0c051c080d090203010c08160507020a1511120723060f040602070203010504030f 78
    0x4e40100b419070f40c4118a0f0446040c07550340306884c210341d80c2650032242404107404200c0701c0b49000c000302d203520340144010112500c85a41c45032030031150901403c031610455041c0510b64140070f01084440045461310800b0910010361691540c103914004e02a000d40950000303030541c40400d41001c00c0c3c0042608807070465400c0c2069850308400350b41e41d581158000d0568009001c0c051700320501184404d220a810b041c800101a00e030307088181800ca00341d0203078445074418075002003440040780300d04000d00b03025a840ca0306103042c907200e040508100c25001384988030009402005490700c2d0301114205600070002d2200703908000d401071030b022080c5c6081d079041c000c12a40d0410a8060400c90320a283e024103561040c41c0ba000d000d601c0101001d20368070510a0140441c0040d500c14050040c1159005006644502c1c071824101110180b06005505c00d40802003c0c1c0c014500020790180d00c41d141100000c42c603030f20351520030040e0080c8003009401d1b608040910003016088034035402c2590044d603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 992103830 1250 992102580 992102591
    0x3070c170a080f07091e091a010305070f051c020d050a0e0f211b0601060503070f030b0d08090616050705100e0d02040e0a14010507030e0d0504180e0d030f 68
    0x880c000c1c0121425183c1070007189022004000c4110260040414030f450902811044c1c0e40d030b11281c80540b00b40000114001080d6014015103682610801c2c4d04443c14dc45d008403070700445d8201074141d04c6900070341048031600b051410790b0412140c04503113010407403505c20310040c00d080c48030201810045450341101d00503c4103007070801c4000903900086076070302c101c100e1410106113560045940300000d200b50013000d2550325201100b04114082c020a41a038402d0341d83d14101c1001000b82c40465601001c150615501011369507518111501140e008202c0302e03581c0340c00000061052080842d81a03240b5521148042401000324814086920a44528103640d090030400c4035200351201e070140d400911100844054142035104441a0710042c0444580d80d01e5511454408581c3d104001d00d10381d102c03400c02c80d13282e516009900808101c40d00501c81d44c44800000f41072070046004100c0042c4580c000c44116007940e030002440e6440c2e810a0391490001000014050800740031048000760411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 992105080 1250 992103830 992103841
    0x7090e10060e0f0a0f14070f0206160203040b0a02010b030a1103010b01030b0d0609080f0708070c05031f0b1c0303090b060f0d02011202120106180b070c0b03070c170a08 74
    0x580082d4070600c0e285000711480d56610194600604141402035040c41d5298640642128140035241c080e415031748420028030758615000f031a207031008004214214440c0e50701c0c1c50f030700c1e000000d8809680d001641c03103441c1d4203400d038220b00500790700d29100d0b03062040c500070100f403294041d42c5000e1410164000d0050260401c019020ba4182c817403120b400c81d1030780d8a4000402c10329407002c00003e1080b4405854269400700000c0d898000d210240c600841c0019000c0030008c81d980d05e107000b00300540c05802001100c440d00d01c50941410150120142c40b0f2110f0003c2d50750b900a07110f204c0c003006042145078910b50070002c0003030a00460481d10403060340c011810601e8840b901041c041c800408105580c00582e004450203c1041c07503000d2490340071300c0080f41c4210080c0c900c40c00380c0b1450355640c1c1d05040340780c40506410743c0c0d030b0300408048070100584004100c11040310010340f02c424030396a5407901c4030b0030300301c90148020703602a090744401070400c062070641100a1035032421540c1c0d150000e4840 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 992106330 1250 992105080 992105099
    0x3032803140c0315191413050c0f0307090f090905010b0a080706110109020a1d0a11030f070c15150506090609010c1a0903070611270307090e1006 64
    0x35100010b1010007400080d0151218140350502e0300000307040001c0503003074903484d0784400a00390009407203006001c4401030b003070a02c0300c09059030500c0244180018101142c1b95841c610529240c8211040000000f450b254012010311000342420481064419620100c100090030301c0c0000311140d5007480d1003d000380c5440c000c48410b880c00c507806000c2c01132411500f6212846000095101075482d00304107800340e580e02c110a00106101c800302030504074280390401c103410f001040411418900840a00071502c0982030b6603108490190744603503615080015101007400300c500a00c8540303020402d40e44511140c003d0406904100000301140351504e0803c509405803600c040d821a10a11604220390304c01c000280406008130324003174941018241d0070140c04c400b218a0550365100007603084c10018a40b1488043d540b401001c2410040c0c086514034005400c4031104101d1003036010358081c00c2d5402c2c070800004000d600c07020000040c0045501d519104d10304041c241d210b2400c20700144500d0b8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 992107580 1250 992106330 992106371
    0x206070503072f210106050a090219020a17180904110f0303121504150603020c120403021f050d0207030201050103211407050c12010b040515130b03032803 68
    0x4005203840251003c0b120101c080d280800c44da001203640341c0c1e400041350780390003500c0e4024112000c0003507030b242d500c0048101184a100254805c552000f0000d001080000ca800d070300340b0303003034541071a0340c3c42070331511340c0600303685003055030b8004501c60501c41080303e240c4120054210680d42c654060411604243d100d0050300c0860f038510f4410000600d0b6609007032049400568018800a441c44000450b802188001d0304550301103680000e00d022440820801014882000f00744140f4260031a030100f554040c801e02613190790690136080c206c400b40a48160340c4103912103402151192003904000340601001e110580c1d0002901d03281c0f031705040203400c0f03000d00080301c0d44914210802221403924640c0c4280780540b564091582c000c2c48070760b01d0030801e40190340c4007070000c5101d40d035200810040303400203462240760003108048021903448030280100314080d02040000d9100700140401d080d03100f01c40c00780c0c0328000c50604005412011500c03902d66038459a5041005130360100c103d480030302c1e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 992108830 1250 992107580 992107673
    0x1503032a0d0e03030d32070201050a150e0406060509130b090115030f05070b03010e25090614040902040b19020a020307050d020415060f14090d020607020607050307 72
    0x402c100051030001007190001499001455071034802c1ca01309841004081c2107031803412803140b46ea0028040c42a0782409100d802040202c02000b00018501c051080d089041c80303200700c801c0c4c0d1440050140546e503480728004040207840c28010b464040d2550701c035014565411112281c458021034654207051184e80319031007030444510400780c19910390107035000300464121490706c00e00401284110840300614000d0800a43e851140e040101c0010480c03500c0010078003801030f50238003050040d40e00140300011150103050110344440c0281490084e846680c2100ca0914000100000c40c10035440c020605558000b0000c0192044401c080380ca4a09074180694103911560042c4064509002e4214045200820010b07150700c40d1500300000584980c000c83c04a03240082410909400a924030400030b250a0107514140d0200006007081d04051030181c011403000c0388020441d03c484044600e80703908030084a8031000c140c641642d505216100740700c90358001071111714034544074148406002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 992110080 1250 992108830 992108833
    0x2030d11040f1a211b0313150f1406010201200403060b0f0d052503030206011502150f1005090108030d05040302010f0930081503032a0d0e03 62
    0xa0345445050030803c0e50701100d280d1820f00c10000c1c0e04a10045420003803091000400308600740c9007661840c0c402138401d075002d0013101010820800e1448843d0070b82d000c181c1e170000b9410070882070861003200901100c82c4104a69180840b45024105a0700d0401d110300000d90080c003021b060340c034a801094811020003510410b0600041c40000e80300c1d0400c4290319006810b2944000981c1c0003e07803003200668059540d03401001d10241d100400101c0803425603076481403a1285031556a009541c6d00d4144a02800c6580030341900c2d81d01482406814281004a104950726052a02c0c02624010301a503194500003e003250000703003070038030380f0384541210201409942041d00c944601d80260900078170441c115581d83d284800108014410051082d0182102e8040b00c1342105050702c0c01c0d050a90803003903500142e965540300c141c1c010708447c0d01c40140e5005030011326581c5c002c44e15600a11b1008001e0707080c0e92001c140201d1030701c01010004400c5104851070780150210903500301d44c125541c642c15 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 992111330 1250 992110080 992110109
    0xb100302010c0b0a020702180709090b0a1e09020f1c090f231617010e07050d170d0222081b0a080304060f020615010e1002010b0a0602030d1104 63
    0x3ca010360320303d0350b40f100103544050b18152047d400250b840a0101302540c110201b030341800035156000c04501c001d085105000c1048100110014a803c41c841c400c81c6c03003088034108040030706104090003500030103803c1405c0d501c61a621013190000d40003000b42003641100c10148151000243c0502e000080d0000c1c100341c007071a02500e540c0a50844945d21b004910040d031010090502c040009800e15041004034030b0840381000c20f141203e02164201c140b1980c10801e641c1d550b0180411010203c03030080350034962119582c9456021058180340c88001c00308007107001001d244098000b0000ad140b00a11564411100611000440d100e40258840b95010060801210b05007080580d010080140003071381159070f0300c00703161446c0c1c443d0b040f04001900c1c0d0390703464000340c4d0100310f01c41d041241190490800501e010008081d040c501d0f01071845200700e6a00c910907c1c1c000e622054112002800001800f070300c40e41c0203503880d40301800384c111851508010f513080051100a4070281e80e4100ea84481 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 992112580 1250 992111330 992111333
    0xb100810030303022b0f0605060c060a2703020606540a090c0806070f0c06020c15010302030f030c1e030f040e010503101e050a1d0a0b100302010c 64
    0x2500101740504e40081000c0e00d4000000d55102c4a22544400c3d50000c0740000c4c51170007880507030b0441d03404a401000c0030f103c0b200c420300e0040f401603808400110009400f08103200801e51240100c40e205251820060b00340c000c0c554082880d51099000340c1d070b54404a0148030f00000da200c040300000c091642c0520701140c09504900079500b18101d90780c2c075880032035510751000b2046202560040811562524208200126151504020070003400a440c05280220020700941c484a424070100260080d0039410480154180c45001200c80100d401a503044105481c8039002808207030b00c07912404012070460a070000c00c881000b1520001351030703200c1010742148000d0600c00904500780c041801351440425a900c0070340000c007985000c030f41865240071b05060030710023400c00480c3d03c0703810450900400c024520040d00402c1c29003a00003070301e81d509440d42c2c0040c10b00464040c18210491039a0110903400610b0320380742401620340710840d44610030303030203c80081031000030b0220301241503510 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 992113830 1250 992112580 992112587
    0x70e01030e0705040c020f0616080103060b0a030602032703030907060e180c1902030a0c1b0b030c07060b04050411010c051002071211070e0a020f070f060b1008100303 73
    0x11881d05404441c2e030603848000041c03e4400c500d1040c00168408481200745c80c03020440603401c49025114488592404c0c080200000c805004c00380940b074540b04d4140d16520f981210500942d00030100315101e04100343c06403841f00c82c110301c1c150000f14030b000c182c800b0a0040216070181e0041c078014408980f034414180c1e0415a04860a980300c0d14000a110041054200180c401c1c00440308240e921200d01d075400d00e902e40c1c04100c9000b194800c0c0040030009400c01020900301e50882c0d00c0f2044882c3d210380c0000c00c9125030b00300c9070301c3c4000030041c0004480740b00c0c05000e0491145070f09000c0d12542c4810300c000c5850840300a407590310701c52190040e039401900c0c0381803070500910903100200c40106000301a07a120304821070b801d031510360a480c1c003a07510002200347c010b4441c0191205130315100c8440c901c10405400000312550010b41c4024040900045030041c65001d20710004200d01800d1200c02005142440c0c1d00551404a110008501c10f0702d035113108001701e640c00d0005605503201103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 992115080 1250 992113830 992113841
    0x3020f120d0c02030319090e0f070927091b090b0f09070203040f0e070305070315090b030c03100615140a230d2c030715140a0b0306010608070e0103 65
    0x3c0e600740c007040165582c4004001c0e00c4039103100c0c1c0c0d505d400c0c00c520b161295900c01110010000c10171600c9080911100d10b41c44000002111030300103e4440800d021111054210b0307985010341400e0307140c8030001080003900c003c40c0c0140480c0340207404441d0398541f400310958201c10340c4194080760360085c1d5070441c64085110758008549204590405848101781707042c0380020741125469640034010807030f030580c0c50b00411764045503034076050044450a103855145210280580c81c410f44d2a9030240c1c000f034808001a404a060080464440303841e1250b80800610150152074900d03034821900000c49030244d03040039400ca5175407038030380d142003410003080700c041d0440071300c2ca000714085102081c1c000d0344042c06080e29007101000010102c0040314100d41090715020307640211607014006180400c404015101c2090700103c1c201c0c00041b40341c5a880c014035001c003040c4101d0303120300b06000c5a103141c0c4d07110b6040b502068085500b00c2e40c0318041a24114411640f40700000c80481810001d5407103034220 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 992116330 1250 992115080 992115083
    0x90c010203090102032502060705030904150302030a020d05011104060507110301090201090303030b062b0f06050303040b0c100e0d030c0203040b03160e031b03070509060604210602040f03020f120d0c 87
    0x181100808560005822741e1103c04191005e0b8400719240285203850b200d46294091602c060234151461540484d8407001729941c081e12800380703492408207100b02034000101403800d6807802a1707101c1e1288800341454000640c00c3c0d90b404242051140c0b40c0c1014446c280409405840b00c9012500d107503002c401070700d80b06071002d4000506210043c8000781d680c1c00038850b1a4000b02c041041400701c0c1401c0300300c0b400b03005144145c6003480400c2050340c0b030200c04c4a00b580c40307030b9800e2552401c000d4149840c00d00c0b07405090031018645201d898484401288041903d030003540d0600004490740c0040b0390b203005c7c501030034050101c1040071a0103100d1800e84d070700324600c2c503051850303540c44260006420302620244041c03040c96540101c410a1400f0300c54180a81011a400c1d40142000400301e44540224020780f48060580e5058410103c0544002e1261507400681556165140c0010140340c50749480308030b0207100c8a6070f00310030501e040e50344030307504042d00401026481500d1004540c40d03559000c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 992117580 1250 992116330 992116387
    0xc0a03020d020a030c0806031204050f0a0e0405030301050a0f05060d2a09180221060a033507150b01030f2c0d0f030c1b0b090c01020309010203 63
    0x920791040960028040030a00d03034030001250a011a00503112800c01846a4800c1d00040282a50174510314140e40c01c3c0c95080d1040d00700541681d0110b40700a0994203d41d0700300b2502c0040004000f0b00100550590704140c6000d00109d6454402030281d0800d4021241d01020a000381300140d20140d103e12483c0101c0c924585038104000e100c500c28241101200340012800d02040c4070504000d810041c408201500851921480c10700c0000e001140c112010310052400c0d02280241d5102e50310200a1900041c24a22903080ca840b440140c5d61020403d01074183d071045900c0500d80c102d4107449005801041414005c0b8283c0712150017450501100d45c14150703a141480385500c024895210107030700c0d4481c075800551410f600d04110900158900d14540c0c0001e02c980c0c403280d40110000c03c0d40c0004d007008250740181c07020641d44094017060342e0b400128031020000c1800131070030704180240052402c1c0c0b8000c081d01801240c991040c8801a40960f00412091081d4a408691418031064628 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 992118830 1250 992117580 992117587
    0x509040317151002032b15090902030d0c1211100e070504200d020903120c01020706052203111c02030304110a031109060f04020a090303080c0703080c0a0302 69
    0x101010400700c0550719440b03004500c03040446207091580110240e25454001107042000d900380e2000b40c40380340c03600c890741d0043e03040030b5944160341c43e04841084100e03580e00303c80958031880c8800041111000691181c0300312040306045034040c24040c280740360049001c42120480681c2075503042c0c0042030459071fa108491008240324190b11034502458462800b40c80c02c2d51410003040107413500700c440000f0100c034200a4031786449806044a00b40010508050b84500c0400b00003418651100d41440750036000051180487c10190b00a080c01445800204619110355400300901804220018180c19040d071240300401e02680410109107000411100d41c15a40343c1c5480c481d02840e0504405a48044184020060317405514820003000f40d0701c46000603d151900741500302034040c481d010f4139190700410364540310034940800391000600155a2645403c0d401040258188800e60010300f14a02241340507884804903000d158143c2d5420b07d0302e840307045418546601049040c402d256080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 992120080 1250 992118830 992118857
    0x20a12060605070209151c1a1312080c0313020d02061201080f12090f010314310809011107031202031b1911060f07060b012705090403 59
    0x9000303a0016200c155540398445a0501c1030007800d5401909280c0000880e41260000382c132600100005000d1410514a1240003400c101702c1010300170140316224441031042206001d070013039407095114421440700070031115945040307030351240c19920150212010000302d02500c0f81220145099070000f800c240c0c1c181171036270008240394040c00045000340f88038401001006400c4c440301c0940449440a4500c450a41c0c0615045110755881c46214440622030f40440364842d501025807404502c1038803265040840d545d080f0203101c2038407205550362451215007201d1001008000ba55071000f0314904044150b0b00556001043c4184440c0510031441e002011500d031100807040c09503150013455503038100c4a0042c07110400312072480042d600c0401d090b110b41e0300004111010301e030407205102c20200e038400043d409202e071604540e03040c0d41c08500e03401404250750103e01c1446090700e80706401c224001c240005030140c0401941070111070f01003003169007010805250301900ca40340514107150b40c0e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 992121330 1250 992120080 992120117
    0x10f020304120e150f1b0109030201090b070f0905040203090a1e05010b0a081506060c0706031418060c03040f0b0106030504021203040803040b07020f09090604060615090504020a 78
    0x499080e111000c2c41a800324030740741c000b16441142c540585220884442507160b001d402c1c461a05140c03000f140c0000d55a980002c03001904500a104e035000f071104003c0f6040c02400380c282c142e001da981c10030000104e0b0300d903030042858a962000517165501c88030f2501c42048001c0d04001d041e0822801840401e200043c448030204601c5202c1a4410050104505165007152102c10000d1b0040c45040014407c061001501000004280303401a48955603038010800074028218445014031a152020a0050b0141c02c16080007100d85e2580481d030741c441140428000e000040c0b02c076990459404030702ca030400c1400855101d8040d08400025181d581c3d1400800c02c404d07401070000941e2102800300318a442080000c480740c04000850505091020580c1c036071280e480b4a0030202030010300350007151034811075403828100041607a25545401e4584c1c0f6100c0904860444070585440b90104001c528001c140e003440030381e82d441c032000b50304120a200095000c1050181400080081e86460000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 992122580 1250 992121330 992121337
    0x6060308030f0103171e03040c15120b04050c07080307090f09060302030c10020d0e03100203040302030c21040501120905300c0604030c0f120801031703070e04020309010f02 76
    0x20162020b46040d031441c10b0548100900c056160405038040000c5881d0f4403a602048000340d60180c5055a00d441c0e07450130319483c000303940c090050303c40d014113586110340e00f00468070800041b600303040c448440400204011103e04440314222100c060018002058800014588c050803508000c03c03016102c03400c19600040130740c81902c0d4251582e4007801182014040c803180c10000b44d0708404903075007055000c0d40f50200e811411040011560f01c907195a49d00b04215660703400408401c46d41c90600707050003912648008101c0b40c161040507900c44400314a020810200c04d00b1206590520b0300382001119000510700c4000d2416449014040c00300d282401180d0303490801d801409480d80b014a00c900180d28030f0000040602814041000c0a0303c02068459200f44e00d4500000026001c1c9092034044800045c00340585503050320003075005400c01e0340281680c3c05101e01402c0d50101c0703000300d4058071044604800284070a003d00c54a803c0c80d03000f41d50054074510000c5590f13014010340c0401c0740c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 992123830 1250 992122580 992122591
    0x409060801061703090a0504050a110c100c050403030206281415010302040f120204140a05011a0a210b0301020d0b150c030a21091115040f120606030803 67
    0x1d40d11502044485607424499840f44607800c050350074102c5035000118040854440c1034002d5483e40001480181c00f40d00c00310000240b120025124255100301d6136403a4500010107000d10700c0d05a02019290060050700c084a6055000b885169590700705800401b00480b040403050306503c1282580d00074601402d00480d40e9007000c00d841d032801042d002100450494030798181481040180704010031100c422056550580d13034100d8610884c40480d00510426041e400d118020000b40080c5081e0742c1c01446c100c035000005100d1f030486103031007401d0034882c480c5403101080c041b48140301103107450210200032030002500000c440028002003030136644103980500c2d003917640f4000080c061800880c07120b004000c1c101164200820b401c8415130301d1003001031407000d115417840303260451074810000b1440a02844014480103420380b408001d41816809a10b01c00e0b49425240341d080e9080d9001c0d117040718044810705001c14503007030b07200c240c481843e00700707a95040d110348020000c00c00c1300c801580110f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 992125080 1250 992123830 992123833
    0x3090c0302151801030204050109031121070e1e04020405100f0f170d091a0f070b0f071727010c050307140a020c121608100f0504050a06090804090608 66
    0x100d5810034a00f68164881003800c0c1414030502083c00143d91000340c90381501c0d4480517100781c499480c4000741d680381114514211100090701090074824001c240f80045440300c4090304a40d480c0c06500034240644c00700c440c020709802c0e0300020301501d0150081a000300003040ca12499507160000f0000c40003080d0015802801c40a01c200701024130034096814150b01c01001e0103205008800c0148001103034891500318018100764a60203000e41c104031540703e03001e00c25050b03072903c4a14100343c00a000321011000c519150001403c0640102c000ca404510488010003295440a0381c4420100304c0c041c6040241b00c50039800d81c0840000d1150304800e9200b40c07522500c074545820028802c00785203514120440c01404100c4000d500000d003410854030450f20303500072070360342c0c0d288038900810407114401100c10100001080400481d00482003880c0d100b00f48151140607a00400f503c0c0242c40051007a0f21030b0010304c000c220594000200e03e0b11441c0304520b05039031280454240c0304070707400c44440e0307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 992126330 1250 992125080 992125087
    0xa030e060705090f150d0e12070c0f0e040f120e030601140f1005090906010e0303030f180313030204020c0f15010807140d170409060303030b15030c03040303090c030215 74
    0x102e26004841302c0006408807080300300c030340134103d0500702c41c0071300a400d81855403152041300c00d800d001c2c0f207002c09030074610700c10070340300c010900784140840c02c2c070300c200c0904012004010880c004d2668074248203039088400000007890603905c988048512810880400020741180328050360180a0f540c0204054400600e00c1e420900802c500301c5024007640d8403030390301803550030b10081e040343c02d4810811003100c900e00180c1d2180010b84410351342c41415685400300004000ea10b1b041441e40740d024081038400d09100c2d0020140e070070394134812080107486032080d003002080140ba044d001400e4100c180019107805002000c0345038a44054181030900c00d03842c040c0144480d1004109000043c41e0300e41e20100380c2800d08000c10500c0c90034503400307403100d0711800501e469480200101d400a20795200e041155554030b090040007800030481c2e42e4401c0078014002d4881020000c2a03c3c0600c041c1c0c1213152444d01c4030755092b001041c2500382114900c55584001000da85d61400d211890f05d004096140d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 992127580 1250 992126330 992126347
    0x20c040207061e0209011704031809021c060524040e0408030403020613030c0f0501060f0b07031701080304170a0c0e0703050a0e030301060c050705060307020106080708030f0d020a030e060705 84
    0x669a08944450f103024418412190075aa018103410f40d0410440c0c0c0d03a03c50303031300da50804031007a03003034081c0c1c044410604040020f11940e543c0e00412186180e00341a880c00240524031a0544265200c2c01354050400e2203071540070307948000c1161100724a081243d1402c0d46c1d40303105c028201811101561040004000c01c01415010311a15034448070380c000303981c4078210507900a07111480c49900900900610721800c07041001c2540508007074403140008072006c40da507148603081c0d03034000341085000807d16480648103040446900e81aa903507940034604250503c505100c16101004640c5214032443e40800301090110060401904240c03806100514050001509aa44c06818898110b14000c40e03010081c0f004000d4070b06441d594980034159501e20f041042ca41049900481e510241c00004d0100946e01540f11408441c4110140c030074160f40c40c0ca446840b0300414445c000103020030040310070103156945c02482158823909000440d0020611070070310b0810b04440c2e85010440c0000c803000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 992128830 1250 992127580 992127611
    0x80d201806042d0b04030b0a09021c050106080c030303010f27140a06081906050903070b0c040302090907060816030204080d030504020922080310051302041a1602010e01020c04020706 80
    0x405000c00d9088541751518613550880344c440d004000504040ea20b03036010f021941d4060014203550000340401c1078161090619074000c040b54813854403144509080e9148030308002c0140c0e8101c50402c100b807504d04e41381c00c1c54100c400072810702d6500c01000140c0700b001190700c03c0c070400c0d490764040841ca480798580007040310202d601c1900b0442940d48005102c8141d81516804000c3c9941d2007100401d0640710249024910b0103801c01c000e11800c00c41c4108250380a40d0740180c412030740202d1b00c000d400d8441603403403521412580207160000b0b40240004074038003805c01c90046001e00901e8018501070b914444241010003010641c00080d80320307400c2c0010751420181c040d030480b0750700065041e8070b010801d5101c003041030184c0040204501000240d620492511004005d003170180115000700000414800250701c94054600d0031101c090801090b1207032801640d640d010200d02194803034800b130300151a400050450340e8114807400100c1240c0d81c940c0c5c0003038090340380704d50004100c1144852105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 992130080 1250 992128830 992128919
    0x303020c01060b0c1c18270b010207031101020a140a12030e030421020a0314010608120403020103200c030705010614150a030b0607080d20180604 64
    0x4004440502854560150129050094112014107810400600c02069404d0700b40400e0a80000d41c48a10010312014a20b01c1c0707d20003da0030569140a400e5415000100e528140704140180e00800b02400040c5803e00d035100b803280c0500440b01c41918aa42d45074041d802c07032142e035859410001602e070400c0700605440d0031400c0b0174203080c0010346c101c0302c4030396a178000c500c41c0613040c505003004800c5001c1c81c4a40c01e08001d4016110318182c60301c900b0910f0180005c00e404102644ca01000040c1282c0040352903120025501d103010300d81032940d001103014007590141410341c1070241c000041d54448003401001c10314540300266890f0b41150400c9400c448080d40301c5207580c1d004a031004801e0703952032201c51300a6011850252510400c0307104400a040103001c007500140c0c0003070850140101c11014100c503c10504040c09900a41c0011901c00b4501b11b00d45101ea0a062104c902c411450304000051050082c00302c6003442c2c0d84040c1c420540c2810144140c18054140d9490120410302002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 992131330 1250 992130080 992130089
    0x60b010f02010504080a0e0f030105090a02090f0f0c0702061612031104050901151b08040509010b0703020a02090901090503130603050106021621140f010c02150f0907120303020c0106 80
    0x810044c42c0989540d0b52501c02c5110340c108008490505000c0c13070760359454400380844083c00800482c40c000a4065541c0d040c208164401e405034000159003540c0c103600184501c19281542d00c4a13120310180d403046420106049038008424458284103c80b200046004640126400e001180301c90701f010781100d682082d10a00303401c081100384240d4550b11407150440d81102840380c08031050b00802c0303804851b407800c03880170044c69001107001e004041025109651b030455110441e41d0f03903144100c031240318a000081c00340e00070b12004000b6281030103031154040742540c0041090a10f0342c1c2c6441c216400309c1903045d80c0d01a07403031040c40b01550500c2800e000d1701c0d440c001440b080041000e14400004241300d1109036500c406110ba82c40c0c600e8040000c0401e60208001c09003c00350300240c0e4480385070001c03d850b65803130a2010f0740344903c0002c0012440c2c1c3d0190785d40c490341d1030b00444c0c900404c400178000d0100e84960640002c02d02d0351950306245160281d9001629010708200031350a46541341d02 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 992132580 1250 992131330 992131333
    0x6320d05190c0801050d0f170901020114070c030309051c020a060e0c150d0f1107031409150d020708070c03260301060f03110c0a051621081204060b010f02 68
    0xb150881c50f070000006410744030100c03581e86000d5001d281c12620191003d500821080c0c19070114811000381d0701c0500b040e180260000e00c141409080c485009120495071000021400c55010340880d010f0391048010b24040c10a0340d54450700d141400e003614407446001e1006a03c50080c810034080e80b80704107080c8403840b5018003d8000050300180d0410880303400c88400440004983c000507002c4d0344409030003d000d190034000105c0e0f191070880541c02180c025000309407810f044039100e0310010121754107010001d009580031000400764018540042c0020f10100791700f0001000810506000703009441c1c8900550402a0700718079010721920300c21200b0300c070113183c900c003d200b03a18030010540c4d054810505d8040569011034108501921040320ba9444034040050644045907021400000301406a8204c844020a00c2d080500000b9544075640f0301200704807204149c000e015038242d11030360080c2d0203a4101070b13000404620503141a00c04072095a078800a1100c1d039600600311880c401c0e002d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 992133830 1250 992132580 992132591
    0x605060301080312131b0504050f36060126030301120609020f0907021c02030f0f0703170a0f1a031e070b220f06320d0519 54
    0x52400d95039002d0300340e08100303048203000080c03100c0e0b80f549030703114a150300110706540c03246c0b88140b03099030020140155401141420001002c1c03c003d41420b0b402840c41201e268841c1c510a0445040c855141d1100c607100e420944000d103145100f04015800707050412490f5000c1d11b41c20201007000e04101d46046050f400a000401600c0c10840b110010b007038100c0d2001c16101540d1002400030750700742c02c819501c005c2150a101070654001440d241e03505009501c03c0750201c40c51810381c1e50307000303222a070000560104050003050034114040c00b10b0620a060601c030164103684d076010540340440340800c200340e0318511010781c01160f01920307000240340007203003c0070441c01340403c0d03c031001c05401c0b043c01800d0f1101e03807008240c01c001040083c01c403151420b441c0c408455583c110800d51000350500401041c0740451917030701d19003072542143c0131303915040c001c820801503c1c1040d416550740011210f00403018405090305042c001d0880ca8504100040c00c0c1c80c01001061171954a48101d5030213a02c4c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 992135080 1250 992133830 992133839
    0x11509080c090a0b040e1c020a0f26031e0703090f020910050d03110c0109080d0f12020406081021030507060207060e0d0801050d031d0301060b0406120605060301 71
    0x4100195034241c1924003500315624000c0300c0c400b400b0120b60051300245400d88441000340007080706040c02d0703850201c0b98090801e2a00813a0768481c050405030040c1c02e81031440c030018440b0001110306d64031403003003c3c000e400301402c0c0408580040718107a49441c541c29102d03041c0f94203070710050351091290608000b03421898450801700054018002d008104d40e40100d10610b40711203805c4001d0a004118a0300718040e844d000f0f14409000d10445810301c20540302083d950301503087e003800ea400b00c500030485241d81c1e5008031100d4041a145105109180340000621085c0340001c0010b0002234494501c1070030100c249002d054850360007032100b01d0806505031000020503160042083c0c0500d40b030350721000e007410039000a02c04e07608024425484e201d02140580310114071107151221540710812181e81e62001e008419140f100024002040c10050391000300000011040103100900000750603a1952008100303031740643c102002152071500d0410107482e480c0100009030100769445c6086500d403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 992136330 1250 992135080 992135083
    0xc0305010e06070c0f030c0c0603021206041b0f030e100515031b060a051b070e0a140112050309041401050f0a0503071518060806010806030607140a0504031a01150908 73
    0x1090003003214045d0710091040c18419100116a00d4002c0f840c0c1d4651562010054000d510110514041c02030f023100042080ca003a104280300f03c241d0741d050511903052000c0440b030200c0d1414000c0300741a9600c04105003180204203550840ca4844000500d90500c1c40c0101601503507004068841e510080e420119416001e4081511200030303501c40f500e483c008441500c9030701901022050b1802180510056070400040740c108a6421024425581d210341c2074078020750303010300311030f8001ea054a4010000302c0c3c903c142140f070f03050080b0103903414042c032040001d00fa107d00c803501080503502200140300c0c500c3d03c8041110780103000c42d4080c54070352408001c0303911194584507e01d0042c5c0488400041d17a40500515813480e00012150111142c40f020081c1003008107035956400a81003000150181c00c00050081c00b864043e1900c07140c0d05210001070885d641f02c07904950404c10240400000a504040c2c03a00c80c8841c0e103040c1c0c40c8190704040001c0b8400030192405000c008241000704000c190 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 992137580 1250 992136330 992136347
    0x7030f0209090a11011107210c0b0f160206070f0b04030e0f090103150e1207030f14070f020411070b15030102030708011202010302040f0603051b040f141306030c0305010e0607 77
    0x1406c0c03d10b05540c0303580381070041c2051a6544004030020f9015401021000b40141d00b07441c49101d00c020b40305103034451189038001e000e000e00c03002d9408000c00c5904441c6030309403500c150750340c40105140e02c1d0400940c2da0442c640340c07500044801110407400e002c00c250f00700c1040302250105655082e141200d000c0020101d030010321026040c1902d1f20703c13034504184203412000e0701c48000c204560140c40b020303c042441c0d9008003425400141c0001d0340342842032240b41c80011210b81144400c0c200036142d1509003c1001010003242e019584046690030403400c080901039540c01010003211500c3d0040d020f01d00f140c1a41c280314400c0e4030401c2045203841d0080b034003d0540b03038100255200c5498620040c0c1c0288520b4100000c03c1b250304c400002c1c8a58144c1040b4030502001208004480302480c0030010b0b1300440c019444140e105034803d0040c0380d1600e410010074880101040d14048081c0e041f50101c44554009591522221500f8418480240184051081c0c0280201344074507020500410141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 992138830 1250 992137580 992137613
    0x270b1305031c081b040806010315020f0409051f080c010306091b0c0f02130b01021905100209041503030e030d09030c1a0d0c020313141014040807030f0209090a 70
    0x500f4501003841e00406000341800c0c00005a50b842e41d4075100c03d6400d680304800d10084500030580541078021104a000740c8800b03102c0f5480041c1400d080091150250000800341403d84070050800060300e07000075421002481402d01820010b200a800103090710030a41081c03281a0426040b502c0d003000380c2071071601c4c1041c0307403034031031440100c601e0700f0752070000315640103540000c00074411445000564021003080b80d00b6000c40302c45941405903640300e40000032000d40103400c01d45c129064181d071500101041d13040100001542e29400c0c8540c003207150540c00907000204010481e00c140e04041000d2180d45849080c4495014a165a0302d0200c0b035481c01000c2400458600103490b00072110242c602120155400f031000300c401000081d941c1d003003c03200025965024000242148401c286044644005040202c004111140c16610b140c980b09890342d8900041000240c410001d000c0b00001d14801d1030740f00000315071401046600400a08041425003040e034019000924980c0c030140c170003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 992140080 1250 992138830 992138837
    0x12060603240f030f05100e0102091008040b0a110702030109080309060c030c0d0b061c0c0207050105040815060d0b01090903080c04180e03090a0303020a0507090b10270b1305031c 78
    0x5c2c0fa000f13007005100a46902c01c1420304003d040008019005080e82d010192a8811820302c0070030112011201941e010f8044110a8041020099107402000664811507030742490310304907901007800c403000c2e180c0c26950040040b080c800c0140d42400840e40000c041c0440b5411401d2440d00b65550b032080115100d05036550f02c03140c1e40f56032681c03003e643e124150140d48030340f0001450b400300b01404840e07400c0c80040c02104001301d07a542c0243d003502d0694480c60010000240300aa03c1010500b01a01041d401100781415800150840084502030007085002003400b40582c03030040c00c070082c0a0140c0306802400d11060000061042c490617001061207000306140c01c0b0201e07201e04510a160046811140101001c4181500001c6500002d88a08110707542581d48800d07032411a0601000b8170742c02110f240403800500e128090700011042c420040000c401043c409400020f070302c0340d1000360703103150200300c074071a00c001d00d5884001441309501400c000c0300081d10340c48900c070041d024401030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 992141330 1250 992140080 992140103
    0x60609130c021e030d0b030609030d0b0d0210111605090f1024080c0405030a0f0827040e06010f18270c0801110304030f12060603240f03 60
    0x50b882003103403002c01402407181900f4414003160f225100d42c8108080d00c0000d00701840306509040003d013051013109808003443c103254074450782c4800b40000161459002c030342c0d1000e00015a89100352400041840d0f00c406260303011256903a030500358045c50030300340c04194040401c1107490b0b410a6681c49000e0300440004c0d0380c1c90800340344803181c0030f4004545101202d035204030003a0740140e40c403a020a4980741c443c10b0740c0d501d10444400348214055160560040c03564079001811b03112403070040903c03800c903490514001c402460f00150000141310255007040342c5010250a05104421070900c260014040e07940c186403c5500e41031151240c0c003403940422001c40b05440c2d00d54800012901c3d00030700d2282c0c854401071b580c102d40c6040c150944980c0c414030340020f041b02c0144210103c0005203e8424216170351500c0031f58403001e10303000441c11310019000007600c801040c8035030406000540c130001074400301c004070300303140304c43d1042000c6004c442e410052044d060243c403100100c1e54400030034005c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 992142580 1250 992141330 992141351
    0x30901170a0e070e1e040c09050c070602030f011d1b1c050a050f0c070c0b0a0309050d0c060e0313050f120d0c172b1b0809010506060913 60
    0x10a21500b40200c28081e0035408182c0080040d01e0718001d0b0a10ba00454948024203c0b0403007900c0240c0b402044100411420400c44103243c0106521501c03d55034103080048984070a810390f802101c580c05910309080040c40803002041340324024000b01a02c6801c14a0400c0444014090160504103421701c04940744050450780c0e0700d80001c1203030404003444542060741045002c1d001c02c0c3d8429200d41e141d030001500030005441aa1459600009204155403404c1d88031901da90000141300e0030941c94135072010210700d0170810f001c0003240d503a1b994849001c0f02c0c1090411038506880752002500300300608a106624484510282c0d00101c4110240950040c0003031050310810b94183c006008440071b481110740c101c44480c00c028016209491004114000c0c4407080c031400d41751011284980796000e8903100d800f1024004402482d800140302408096141c0c03030b804801900c0030004084808020600c0820b02516401200c15501079003041d5001c0001480442c107600c1705070340f5a0351a0b9404e803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 992143830 1250 992142580 992142601
    0x6070308061207030803010e0a0e1504020402160f20010e01110a061b090f030b0a050a0e12210c072a030804060318080d18021302070201090803090117 66
    0x500b821103044500c00c907500e241034807207504248030f4413090351070040c0028540c04140c000d200c0c003030700c442001e40003104104592403003c040261080e1382003a800d10101c410728a060071321181d19801400d896840305600c0c0307000824040c00c41814000900407108000d0503076003042210765040e10900f014030221a103116650b113008000ca40152280d41000440035644000541004003210241d41f54001e545c1c48000105402c545488014601c9144071b00044652111744d01c00c036040040c103100401c140d401e40319550f2030301281c0da181031f03404140043c0032075013150303052410092180c2c5090102100d260124000029010319030010700304a81241c0c8044804003502e4060f14000c001e180c852070540d0307d0381000301d40ba42090141d0f1003c42d181c240a560700034050040c130355180b640720058500c7d003661700d01d07210080d00d0041034030b0700c4000448842100690702c2050088030300d0181c8800603141d0b0b5207030000403e406902e50111800d034008010603005e6076406041c601030709210907a8440951a240041c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 992145080 1250 992143830 992143849
    0xc07050a081306180806180a0605040c060e0a05030303010902090a031a0f09150714090d0609020315091c091203093f110613081005060607030806 64
    0x188008000074400b44a241c80b140e0b0001600d0716640ca55240080300e03610072482609501580c0c00c01e500200004100c1505104c204048181c2e200690b03402503d1b81d0f58140c2030f01c1050780c00f255071420000c4144561039103d83c5800d103581048a080c07c6640c582404aa102d2006020b00440d8540004030170f211911417240786001180d0003103480d4441c030300542c400070144a0540e055150080d0310008100101c10000c0c05220340c02d4040c3c54400c15451b0407606a981c0d40701188601403000c030600c28680b03265198182600145d0103440d0100300001e0a1040600b01442007404041c43c50740903003032000c0440002009170b16101c4028075205102100d00d002d503000c82079a030010008809031074000c01010f6006590b001140c10b9802c489200c903002c2c050110515050307135054864401c0780402c411080c112015100921400703804c4001060020a011800a40c4503400c00081c1c0c441c0c040c0304112524042001d00030102115104000c9130500c4000103040d0701c1040c2e006001c0211860210f07155030342d840d240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 992146330 1250 992145080 992145083
    0x6060d02060301050f0604050631080615190602010203040c05090c120c040f060302120708060d061104150f0f0206010509060609150318011808071205070213052406030c07050a 77
    0x61a86074110300c1c06100c2017200506c1c40e4420070210004d4401c0c2b4140100d00c10080d02c0001d4042c0000ea03842e510a40140d042c2c44c83d20541c0291342c2c8000203a152060518240582950341c005641ea240904241c1c015109540c08640100102c00c10030241040040079141d0082503d15522080d0300d41100c0400c03540a5034000302104004400e0000340d85406600401e190446039103191503d5603030f542d05441603082100d6064201c862000f040c400140300341e00000d0040075844041e030406480d200c000b6202049812007101095007000204040b40d0004a0075643c05034a200030101581000082811200044d10b09800b601c80851040c1c0c03a40e94243e52a4002051580c000b516440c0c012190340c401e6a9289881c400d80d460301c1d41e026054a81e112541c10056000320166240140c00e558075042004c0d100303446130070090180f01c441c0060f44d6540491020030f64200d4081503c0c104440c4120582058045444060b81e40c038040c00126190707802030301d078040a075080903071301c1d04d103581400da0400c18500780 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 992147580 1250 992146330 992146339
    0x601120c08071d090a03020706030b0415151206050f1002010b031005102309040203250f0503010203060f010e0d0213051b13050d0807021305070206060d02060301050f060405 76
    0x314000407410a800c1003091041803c41c1242c9441d80d5140d1a0011042d0280051304520000c1c00342c1402508a17000c00362026200082e20039a0029000400400b87c00280c0340800744401c964200741d000f511800000b041c601c0c200310481c07401000449003000c02074014015180f103d14904094000e6012400c803800180075034071200c07844000d800040604030b40c0384074120b4020303201050360417141134100440e02c0c0340c491034031540300a84104242c0c41c0340140101da1610031100d84640d4900401030300c0106c40014440c040b452030401c0c070810041c03241608124000ea105008000301c1e940e4a4842c6a00030344282014150b040d88117006c18400304d401031010f5080080c0d003c03d07200103002c583c8168821340c640490007500c0c4030744040c185200e01c510380c4014680f182c040c01c18000ca1501080c3d440e9058452104285450400d40c082140d80c5c4520140c40a202c6d80d0710104087c0540610011360b204c00d007254007400300d40c1e46600203070007804180201380c00341c82021400342058807802d00b00d0f0044d010090 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 992148830 1250 992147580 992147593
    0xc130204090e07080f0a020105220302030307030203030717090d080703020409091109160c080f190507060506090c0426011e0c030207020a0302010503130c08010606200601120c08 78
    0x5030340baa65440d14403c029182c468000341035801032000c11101c2200303905079203c40c0750034500c07242407040200740034043c986040100400401a54108001d0071018800d4029507160300d03020001402c8600b130380084105402450301040848180402d4914503c2501d0815000a40700d0302003c07030003030245400690255240801160612100c0c401445450404459240803560317450400010a120320364500c01081305001e4890000e503542e0080c0081036181d03032000313061000c0c1406a506030b0391303081c41300300201d2000903020b4140304190241d140e200070141c03000c50680c140280c0d144aa0711035403141600b0390420070740d901d03022760002e1000c03410420240000c1c0184030209402c1103002c50981e0f40b00004a19129906001d00d001c1d0090f42c400640082881d103038146150010f640c160b01c003e110b420505480d240d8580010070b501a92400780401400000f2414104400581108015600c82c0783c24030030000040b91104001a0542c155900c0c11515504901035140038400d014817500a444a0702495 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 992150080 1250 992148830 992148851
    0xb0d020c0709150806180604080f0d02070c05030f070b0d0b19030327050d0209070c0b0f09190f060905031e0d0c180e060f0405130303110307020c13020409 68
    0x6011807810368241800352011502c5130036106c440041360060740e070381c00d801200000d4003046400d4003611015501c80540c9240c1101104040101e0384011011284406100c1041c0403a0504204810800e03a40c280103110b800c0c1010780d840b115000d82c1da00c07088403e4503040c0318451501c4c4d6058600241c416030f0f0408109585a24000d04094140101c0f10441044e01c3c0100300c1ca0741400f0040300840700003606446011107644c007402800e00e03005221400b0b1140000311080058007003248584220b20a0030820424141501d000d410700361910416000241d100302e8030b40c08118208000461142e000d07200003803010007468042d082d800f43c400c40d0107200c41d07000502030940072000002c2141d01c00794a0200802c100d103c1c0c0c01d8820304d12a5131b035120740010002c003e0100c1d921040e038641d007010000b000408401e90001c0060180e07801101c180e64003c200b00342d4442003640601030902400d401441860552401d0300d8020f594070100c50340f0610030641003071000c014860b10f90485004e85041d80060040301d036a03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 992151330 1250 992150080 992150111
    0xe0d1a1906170d08010f33030605010806010c020f04020702030c031c03060501050c1509030f0a030b040c05121b0f0c01050603060a0213060e060d020a020a0605010504060b0d020c0709 80
    0x1000400c81503000d04250120f8003403140c210181651542c400315440607080501400c4100c50071800c800320201038040f0000e2041d41c4503a050f260880c15035000c1201c506102c001051807502170715072814490080c001200607034810b031404101d81e41c180da0058954040d400040c0c542411a112182c06004540b01c004811366200c1d10740e80d111368180c8043c090303566281c1c011500c601c1030511100164029200701c00b0014036040b0341d030fa04042c1030310881e070405880500c8514940c1c0001d20380400311740e44003c000d060b41410b00035a16440490b04080f414080c0b202c482c032008201c001c02070856402d6010403c13a140c02c844042e10030010b00301d42103d840e4980525094003d28082e180e9610a10500300000d510035000d0003211000030a20700c41c403500d0391520800765491210700b040399600c8070080c45002c81050091014001c0d282069000300300346045800c04000b243c1c41a0020303800f907414400140216018442141d030281180c0400590318280c0c5940e1605200e420340280380c1c014202403001c01076000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 992152580 1250 992151330 992151359
    0x213060b0a11060c0307080c1308120c01060503030708041203020a0f0b060909010c120e071d0115030c020307021c0c090c02010f020408070e090a0b090109030e0d1a1906 74
    0xb620000c507400e6481d51900c55146000c01c4540d81c000410300d00004d8a29403003071001e0400300341c900c1d410008250b101c5840b41d00b40000e091481d500d200e004110500e23200001d000d03140c020002a4042c2d1f2404103951242c085611403401000309900340e842c084070405200b040880820b58000d1010f960200181c50040030069040c0e9030148160f6948000c01c51000d810720400101403610f131600c0440141c1501050054910301c01c2480031030090340b40c00210340c0c00c80c8040d400010b5070340c104040a9030514803c5071034100b4401849080600c0c181050f440e464000084552654040754115040032800c2000d0482d030900100c010309909803140300045401468000303c421180c1600207000c1c00c0b03000f120410481c004c07441401c40c1c41e400750030300f04014031441241e180c20841100130348400070560b4031101c1c07007028240e4103040c440e950741c01007006141c3c0c040d40840b813440702140c28142018003625140c9081c0540c00c2e01020140240c804280b40b0f06042c03030700c01380000e4180002d22199aa50380301840c5080c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 992153830 1250 992152580 992152607
    0x30909050a021612050c01050a060e130b01140609130507021b090402090705070f030e0307060801080d0806010e1207050406090c020303150103090b041118090a0213060b0a 75
    0x90900020400041c21802a10008060011500b01c80b15854807901018641c0910640501c2420081050051020f000c0c89101d40b02401300810014034104c04d40c0b81990005041c100030b8412001071b14000381c0184499030440e0012001080e803a040c00c000248540304000702c40e5403152050081c4002c811150f0003803481800b06400761100004451341d1205060b10010029501503081e030009801441d0207081290400d1580c544203003060010780e201902500100d40035000b007102039101003072034a001c10055010744040e2a10070f03078039407428074015950f40550034400140310001e0002201640b00d405403070042c040081ca4603d60025011889856850724002d41d4000ea04001c80818051818095060ba9001c0c9034000c1d46165a603107450041e208138803464504241d101e085c0840440c40145049000c1c0f402210b5601c001080074003080000502c5110071614a03001c1010040c5001d0f012404c0400d00e9015a20104680402c50358003008049075005101e481c0c001068554410342e0000c198050f84 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 992155080 1250 992153830 992153849
    0x14041b050103060b121f18060816170c060a0906030b1e010c08090d060605030c0901030507052112030105010f111e01090f030f023003090304120309 65
    0x151580c004500341d48540c0200988080c040000c2e980c034010b42062241d01809950080c2c0c0c1080d0411510b13035607001c2c1a0b000761513080900036040200f41c0350784a58402032403d0b030010f007800d0200c0c00e03128000031700b141304480c0e40b01c410301060306400034240318078640000c00402890795070031840b401803c610b6890243c0030019207080c001030207d050503220041e682e092229207004030b010308001150003014604040700c1c1c1d80414000c9020a4440c504240d08423485980b0210308a42041c00f4540741590880c00e40d0310848030040100081030001c01c030401610000e0b40c54080c00a60065140c1c10041400301c0f00d0118400c034500740c100c1c080000055410b0700c03c01d030b0321051a0030380c24000b194640c40307201210b00160032100a10401c0c0f10a007070900810030504001054991060f101c244010281071000d80200f0451b041700c07004103605100c43d05c010700200c032120401d004465040040d84070351940480c0b00400c0000801c400700403c00684004150300d501c0400001c00501e001404000320744181c1c0b0341d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 992156330 1250 992155080 992155133
    0x50c0a030c0c02060f22030308150409150b060c0303010e0103020f0105071a07090806040f0c230d02012304230f010f121107050607020c01170a1404 65
    0x8503841184419282c50b0001c2126040000c2d0303011681255020465409860036042c2040140c43e81d01000400154042e44991146103055109907a0800c0c0300d1154034451480e0030300d0000003c440000400100304440c80c00100ca4041d080454a18810945280b07014480840000307000c941854809040c1ca100341d4110404003100c100558090103860030003005003042e10204c1d105815100f11065000015181c001585565004114104001074034141d03003c2c01c900c0c4043e0140070700d07d002d9800404070751801109004014041c0c244060500b0379952245505074000e0f400e585c4079003e61200c04420a440c05140c40741c0460414040e44903205040a040b140c502030884480000d488000314200030300b403201c112210a00440e4001c128440e08010f004000c0480b04c07148241d4428000303043c48582e0296651017070742c24a94a4901c0c001c182d02d0440d4003c0c0c5020703400340da1200f424036a0079860461188140c1f80c0301c003e50058606403602d000c990f00501c040209000381d10547d8003102045021b111503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 992157580 1250 992156330 992156351
    0x6120a0b0303070206042304020a02010203160f1403100e0c0712020106120813210201021b030312090106030501180201110615060a0e060c070f090911040c030e01050c0a03 75
    0x4403070052401c0070b0360107102440108850b03050800c0c0401044103900032400e81f012041e000408030303000480f481006030360100030090b01008043e14001980c840b414105030350103003001c004040e09104828400722000c040040f0701001107000d40b000141c0b200942251007490034001554107a00502c1098540018400030a1012b44c01885100251500c0c0d0860a542d403009440e584e015900c101e041da108403082c0030b400241a828100381b1940041d07150361400f03070083c95000080c600915801300000e4001744500c0c180c010342d000802c40301c0034042060b00b214581e881e08a8140109102e5101401c55420a0350b0b038041a181514110600c0d8803d0302c499440c0240b240d40107540e214202c544200060508511030114900344014180c14010740c60503101441c0c4ca40017240050f042414044001c1d4804801441910300403546140075050708c8604004900c4651180034000c98200900390203565a00100d0604502c20b030030207084240380400078401030500703010380d45455100c005540700091070b001c100c50 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 992158830 1250 992157580 992157583
    0x20307170f030103140a050105040302070f050a080d030e030f0a030b120c0d060b0307031406090d02060f060d020105070204020703080a05012c0a1b02010504051204060c120e06120a0b03 81
    0x602032400c4501c0d080c116821030ba24500030040791403100b4800e20410201500041023409414440c0d8807d41c00303452050b240c02082c00c0c0d4810f9540016200b44801d11042c000141c001500c0503040101c4e14002c1030300c01c8054206419485510256221207800054000c81e05030503400c050401401615035080260030038600507280c4140080f86544034514418490100c3c1045e04482483c0b44000d00303880300c4035941c1d618860351340d0941901c41c865400100070002001000d001025060459002a10f028541082840c90341c0300300820080c4a00260503140040d6441002581c0d000c40d1301410841d555010750901600030300c000c8038003139505418000040380c3c0e41e514a04d0134030240101e0892000b01d003420f60310b910b05610010032800a607075403030110031040400c8e408001c81c1e0300d9150300000b6090805007405810020480c0d0300ca0f022000c1000100482d5501c0b140d550307405a0400f102825a00010000700d5100184031001c0d680550041520107101c0440c4641c240540850642080300342100e90a06 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 992160080 1250 992158830 992158837
    0xa0305340321060806070e0a090e012012040b13080409050628030b06060705120d0b0409030909050a200a0e0405060607080c010609050a05061905101b060c02030717 72
    0x60544e07802c9800482d0001d40a585009841c04004010500043e103030400d020071a080d45103440501d079142ca0801c000883d218020300c1c0310074403520903546400c0b117000909034040f102a0000f0180540d060001c2e1060901400502ea52a409201c5595540c0d0302c0040b0300190800340c1e2a0303031180c100250300110000c4030990030000e40f0100c814a502c820b2442d2160040010700410454110034204220400514144102283e40b100500441c1d00d402c005881030302211405402180910f00e084803c01c00310340c1000a210848450704000304080d611b0b0101c1402a1802c0c000d003034403034401407101c40d6900c102840030704001040c40d034424000e40c2507402040140c84040d200d01d43c0000c01000700202142d030321002000e0320007940c0004502e159071480a0012504100d07541081b05a071441032103802e03c0c040f45003002544c0800240c3c0402403c0c40006aa155010a2004240000b411091013040300702d1100c11136103608800108801840504081d4030b95002150031102c075050018580007504036441503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 992161330 1250 992160080 992160089
    0x60a050717190906020d1107140d0804020f0301090f0c090c1b020402070c080a0b010312052703250e18072108031501110a030534032106 60
    0x4100c00c40c54455141d90040c10f44450a6958035000c228070a14030080d402981e002c00d481c2589999140110704000a10040c044c0448100380c010044641d51282c2c00701070301750130680403603107203c0c0402d2540021b801003041030720007807000f1090101c481c02d221070280200101d5a03074107824000c94122050490b032007602c0c1065003c00008460040c070142c02c0c40d03070280000318444d6044c072004640b1b4100700c0d40b500c12003000c11609080e011005104000e213859203840030b18020700b800c908001d0b0815150b02d09419044002c0d541c02a1001350803090b80c1d0030800c62890080d000030301c04070f0a03013804e000f130340d81c0a03c0c0c028400d600c100b1302c0c08181d2514840c13140000160118000c0d100d13040c102181c0f0540c150150a1611041000010b0392020981c10002103015400c00f40c91410540503460000d070aa5100860004407504200d8402c1f003c80d8002d0304464182ea00c031084230505241c1c240b40c5188150301000721816210702c8400240425030004100c0e280c2006043c00b4241d5a5044070f920411b85110f07005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 992162580 1250 992161330 992161351
    0x114030f070308130f08060a0c0903050606190b0a051201051f050307050906041e1a1b030c0f0a1707150e0c100c02090a2a050c060a050717 61
    0x102007010901010191000060343c0340d84c15140c43c0c0d00c00c2420001e020f503810209071500725101f0b1220700c0b8424420050340394801e084c4007901c0752950b02d4541e150b00c80200b04038080c5410700c005100a180380034800c800340c40000e40890326540111300003406c0344c0001801c001c003070019000124003413078a004900f0005081e204550300460404508450035080a002072003444000d0103040c2244e078903940540003400e020885003000006129442030b16540952224424244183c01103154000d02401c0b210560482149030490b42080c1440a00c0c40c461041c0d408007074010701d04448441c0202041100d84140a04080310260150304407009680c4140b004c0203280311f60034480c2011210041d0007261340710410b141a11081002d030004038010710050321242002604120b104401c619044820300e400084103038003000703401c40450a0800b041c16003040500e5201d003800c4540d110900c15400c49026a2450003510a2400c02411b460054181642d883d00444ca000080030304403d012000e03140308514106 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 992163830 1250 992162580 992162593
    0x306050a0e160c0c1203080a0c14090f03070f0f0503060a0c08060d02040e0a0302030d1103060d08071b090b0f190e19020417010c110303191d01050114030f 68
    0x70081d02c01001508080350100140207000401c5d40d0707103400034100b45000340c562071030b2454000222011105504091400d10001400039983c034000c1809640c040d09040c3c4004121216503000681792409940c8098120501411302140d00c261940050045803000e400305c4415031214599481a00d8101a01c4400902c03000c00240031480c0c1860b1000441d80050400600000900c000c6424169415003e6001d41c0c800505404401051b05c1175104d4903104040142c19810321300b00284030fa002c1040d01511820010928030144100c0043c0a07150448817200b50000d07603994103040014140b81c481e030360700c0340c030112044950034100300540b0880d08115000403440c1c28180010141d20100180000080c08004603105141c4421880200040c01043c1800004104140c19407402d46840d020300c08100b0001141c2c031180307074000100383c035000041c2e030304078200e0314200b214020014207003009a5460300d03008104808441a066010318141da954031801c00e0818144002c1c50b64400d10141284465800764 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 992165080 1250 992163830 992163871
    0x10b0702090a06120b0702070f030215071718030105010e1e0a0608120d0501051906050919030807031403061008150d030815100518010210020a0306050a0e 68
    0x4404160700041c961030018030b681e140c8001c0740500c007007034504684000e5205d05008949404101c450002c0c144040c3c0c030320307100f415540170940d82c840218422504540100f224410048250070000b5072581d1740403a81d840b80141050303842442da1141d4818000c0d441e0a0000c0b461106556405204410703416a910307140d551400c01c0203e200b0010450f0082c180e640002244410092022000d40091001d002d0b44400901144008456043e4059440b46210018032400031070000711090444119061898581c10030b54041440e2070120320006024290380d16020040100c4000a0306c1344c81d00a230380e070700500409500412254401615195800028003c1c4001300da4400c00e101c0c0e034805c100500301c074028040000070030061110600cac214040362403001000241c0c0110701e4241c2c4104412292603070b4980c0080310141c4244903a4400c04015500c11500d04166402000416480351010000719a0707110504801401009a4010703035205217507c2d100028404454040d0900500640c050002e13142080c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 992166330 1250 992165080 992165089
    0x6030f1803050a0311030c0d060e0105030606280e0108061003081c2003060306090a0c0e06180117010e01111207111501060f18060f020a05012909010b0702 68
    0x64500301c0b01301030300c5001545202c3c6182010f5401100c0c0d540040e612900081083c001b03031081900510805031540004002940d00001c04682044c1c00352501e40c0340c3c0e400c1c2c101200440740c01c19041120301c0c910160015514803818a198101c0d2500e005581003134032124003100d00e03201940720203000c01009000e949c03c40c2201450440d114140ea110000302e041c141c1c40e40f004401c491101002007104013000308400c90600340f1581c2d031301107108000b921000c2d002d551030318174400c0a030140c0f05e01000c0c41c00009809450322015150035103c0b125040906603510100c1c030031040d03076000f802c22403035003403c1c9110700920050051810b45c0d18070b10a042d00b041c0c01000320600528001305908100001c048078120a10780520601c41036044600052180d1760600602600d51060b40540e60100003501d511601d140484591a4040d81c1d2646800910004074490480c0b070000140405003c951038076070542000c4140c44507020700c241c10701c0604405020302804101c005002481002d001c40c03001c010040041c0707070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 992167580 1250 992166330 992166337
    0x91f090b0a020102040e01030c050321030109050a2c0c100801030602030c04050604060807080c0909040209041b1e080f03120714030a050415050c0901030203040c0e09030406030f180305 81
    0x1c070340700050038540e030b0b00038681101d00c003a48141d500540f8000700b40700c2c82c01c0501040d00b082a40480c0d45620405060b00081c40b444144211025943c0d5480031820088480d00302c0e256005254050850286012980803002c041c503184c000c2691154605032541d609106950441313071491526441003d0b03186856a90113540300400100c2d8030242008003203250340d00c200140000e4000c0d607984041602d0080c85c0135105000180080d20700c24800d00058070b09a80380d9004a80c0309605490050640e1603a1501e180000006030440d0921280d001c0041055003401c003546e0300507400b203010072080650720102c9503107410110904211507082004180141d403407002d4029005055450040c421a44001c40900386400a035600a0b0f5161100c080c0b0050081160b086c095130710542c01c00300b040d82841100c203a094440c440c00d640c1415004400141440304440c010302c01444050002d010034942124007948030350050240c0400309203071541041e540303145440b83e03426482d010110b03c0c0c410005918207403407541 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 992168830 1250 992167580 992167597
    0x40e0703081c150302150d0f1b03141303140c1501180b0625020409061e020304050606061b1507030c03050603060127060605091f090b 59
    0x22680400000088420004180700c0040c034150780e114100003581081500d25804484603e49605501440543c1d0b85018034140300c81308465466030743c7c084191440144c40711400c050b02c90f9140c145543c580e94190786a41c101c0b65440e9408204d82c1f2003103040b21246e040103840710360305210250080e0001900034003061404020490056051030f00600343c007440c0c1200421608100044100100490b1071056400411328400040c103000c803603040c202107440d500070000504400c0b0551070503101c2c100061100c850f03180d5000b4006200e00c4d9618104000900f100444038200903d8130307400351401c07500500c20b40c0c1c010ba6004003e001141c4034401001001d402000281d069120500b5581044440400c4699440001c1a40b584007500d0900c2010b022184141c660105040c1454100305c05641d010034036131306403082c602e6807400e000c2c0080e03240d500101001c0344000b4644d181c4880415800e1300b00016141c140317400c440310b5401100840e505002d0703d042841180100388410818481501c25001401414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 992170080 1250 992168830 992168833
    0x4140d271811191e17150402040317220803071101171006080603010c051606060317070b060a0305030901030b060c0d181d0109020930060106030b03030702040e 70
    0x1003c0310034102069281e085083c004180f003801d21500c3c002800e11549505806810b01110150110201c821160001003240c44900140d0350100c00c0ca075201d506540c0a190008000401400003a80c0e40d038040d0f02a501080340c680b081349802c8041c1e480300c0c094809454004021714100000b03940d40680305800c02d01624140403200c0100344444018007200b5114241c0e00c5440c81e8041e1414401815585014010768040d9041010801d034842c4c201d030446101071591f000c0c0174a454070500706400200110f810003002e00812400000c1d811a42c0750250003101c0c00f80c0040d1216445000400054400d1484028140c0d0024055540c2a40c003950200c8201c0c0301c050f04651a0801154205080003031800c82231011402207444540c02074006014078003d00380080c0301042291803055800c01400051080100d0300e600041c0d00000c60302d800d8803840c5222902100c01902100c038910341e002c00140002e0100880c070800d000081c26a01c28005e04100f0a03020f400756240550a4091001030180a81405000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 992171330 1250 992170080 992170087
    0x318040605090a0504030e03030f0417031204201801031e0204020a0309110402070b270715180302061b0a0203030c0115170601050904140d271811 64
    0x11a102c8000c4948280c4940d0f80005445ca0107150107000340b400c10741c42901035401400340540c0c0034450030455041c0c1c1d003848a4422454203408096265100342003c18240d0303074110090101304126414410512400f4000c1c20655811202c00c0c170803103a40b031101503014215880010008612644883c000351a03801d05c0b014036003207654000c40e0580e84055600d50000350703203d0703030102400381140e100d9028403000c07030b820b519000c099140e010111001420240c505e20640c0041c100141c4000008040c0504100503500c001e03a4596054604020708003203440410711124410490100c440d103924183e81c0c0c0240000e042021149401034901c0300c0003175580640c41425266405641e04002510419a143c1d001081c416112101401d000ca115444201020381806240418100c0400c98a05460040c0c1da00d40c81c950303640c10020320110401500003002c0c0610002c00c684594404000e1000ca0b03016180c600e2034005244106000050344c0c81f80290240007010808680803c0f508010204c0989003141400c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 992172580 1250 992171330 992171339
    0x90e010e0f0f270601061d09280f0b09090607170916141207080a20120d140901120213080706081e01030f030e03390a060203180406 58
    0x101c2006815a009a54026001003080607072000c9031100c10300b04034480c00c00301d6086d1f001250000502130400f0300940203902c4000100600405810320001c0d44600612041c044451618014005c00d81c0d11800745402c0d40001320302c210300092480c011005035a035401d4080b85010080c14010014006140a000726110310700031036103d941480c06021949105140e100e0b4500c200030650074072300703000f070581d41001600b0000c440e008a05a8070083d04a0014140026031030a9251a4090985540e6208904e00f03004c0d51110030001d40540c160a0070380b01e07544c000707005850100180c020901c00a0000384005003411a0341001c2d0050b00e40d20303045802003201240c031005804c0c10107a05070018070005800e40c040140c001d4076154565141c41d20220110340550441e102d00c00c0d101410a40a0140030061207444040e45041015020b558080040003180d1600d44180e00c2c004542d15a0303e030994510401d05ca241c928046449600b00d418940007185045001c4800e2040c00c0840c03c0320baa845641c8410028 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 992173830 1250 992172580 992172631
    0x5040c08280905011e0605060a080a0b0d0f020111011b0513080111250c120212030406020109050705041406011d041d1908090f03070312090e010e0f0f 66
    0x2000b90f40f1071000401c030384080c00000006111060218050541001d40c00c200b01d0300e5841c2100c80c03c0c84140f41402c9036035a02c48014018000c00700c50340d900442c1c003040d5002406011200c4c2113005200341c2e1a580c843e003607411450b003603c4011030041c0250a0641440c000c0502032001891140118003410407103e945289060850f0030150b200c03d403c1800280c4404110540640d0000e601c1c00652f11440d02040c544441311501b080b80548c80b40240481100000e6540f0300000702c000042c4c07031045a40e256100c0710000d001c0c1a49550840c0c0900c070300000840d0900e0300c2d00451b60b54082445103201d0560380c031401140d030b044640141c10f05291812211000c07a489074003903044c004c00681c1d45000d40350001c854140c542008680e90400c00c44400d20361900180e0160200c90b10620215480c00c9540701c0e00c4000380c2401000d074401450303807031010040c11200743c0001c1d10300106e62602d5032220300b60303030b0b43e21810a0405080716140003440024000414031040341c884507402c00c01c000e4098009078030144003003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 992175080 1250 992173830 992173841
    0x30912031e061202030f011b030209031e0c0103230f07110a0b251e03021309060905101401080a060302030f010f05090703030e10030b090a02090a05040c0828 69
    0x2a140c0c61a0003400314213500b020041440d485031060f0082140c100044018a41031001d810300000f0581c0001c0e0826440c1c0c5e040048030b000d80017040b005015405c8142d480750b07503041c3c00f2010502107400c003e5580801410141104000014900915019075500704001068070f0000c1080b024010028400c401000c01000400e8101d4030035000305c1c00c641004010701001951546004e05e486005901181d140c540c17000c1070794207007130340c00129031000080c045040d006030190a41c0880c22501030100061800d0440c0c10120440f181050100416103d01603507850880c443d00864440c296044020303941035101c0c182d615485515080000780305038803a4002801d1a01200a00b03d4607910b078246c0c0e0406c0f14403489580e800c0b448500c000c2490500e103903006803082c1c0020215a10031091140320008090107038000208070140100400d50500d01640c1c2c501c000e422003424940250b240e10004511801c080c0324072105902185c888560329500e0005003501e04030304d410b09443d199511400c004146480b4040c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 992176330 1250 992175080 992175089
    0x21f050705190b10210201050417010f200703050c0304050a060806010806010206060a0302190e040305220f0509043806030c01050a110a12030b040c030912031e06 71
    0x140d4200082c94140104604006021003038800b1000000f00100e00f403100c40c00a16100040c0c2c0d0035030020b864001a1550300880c0c1c8151b0701681c0a190001002c441940103004000400e0b0b010400a031208041040300e007081003a0801e20302042041c0400f01e4080c0000e40700d40142801160b2805407a00c0206407507000c2607114901160810b0140061507800c50202544240c081c40288800d00d000c4000800c811070300d1002034004d02d54040c5043ea109035031500c1c3c5010701211500da1a0b21704082c50f004016910030701840303881c3c28840030030701416040300c001c281c2203e80c2588060101c40c10002042185000a0011101c00c001c0076441810184d00410900b140210b001185016111105100c0030224000304843e12036041650b01d0302c1140c4e0051704ad5220681103141c42d5008500c9030f0072507440d21440250151442e00311880e141642c0390705070400c420300c00041c0d40a0200b400000801d4096600b42440144410515022601880d2107a4054540c1e1021030304e800e0b0a20843e50742ea9800c4890380d400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 992177580 1250 992176330 992176363
    0xe0c0f0d1107032d02030d0b0d02040c08180c0102060c0c0c04060b03160201020c0a06090c0b070606091116020103020d020d021b070b0c03090f0d150b010f030603021f050705 76
    0x603240325070051000812003511010700300c03146401300b44070001d40317a00c1000b8500c0203040c0d50788034080441d202c1962507162580d015000700b20351480b044014002c800e08075010456200e8100700d114208002007040b030790400d010303001001c00b5220980700c0e10040d0002c0a07414450310880810121582d100d004100040001941c03031035482c2000d10f0b90903010044400c1c00025603004001e1203411103c00104403a0140d00300d00f000407100111f1504040d101c0c4954400783c0104408144001409400d9001c1c03821100320500c20071040300306840d489200d00680c0d41819400c1c804071000710165000380c0040a410400440040c642100251040101c1c1c110020601c001d810240010421030b1b82005413101800b41c00200380e01303004500751029543d2203110001401000b4441c010074503503d034030882205060b406000c00c025541e00e000e070710005041440a00340040d00500514a05900910452043d00e40103810b08a40818801d502501000303a99911000c000d0200166030101390140322081c40c80c1030051 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 992178830 1250 992177580 992177597
    0x12090307110607241a0d081b4209030d110f0c03040f080316110d0b0702012a141815041d0c0307080711010e0f070e0c0f0d110703 57
    0x140341c5d48680051001c0750040c82c0e5481d0782008030345000300342e8006c0380004819000c2030003096503150520750410300071241d100c030304901d080840c003c0d00c52602903004003000380d1805800c08042c49a03554070503228009140c02c00c1281484000fa16001249801000c40c280341c94039000c0e40042e205584000301d8819990000305090082c00140003130100180103100003142080700c1440c140c640b90301d800300004d0042d406d0603484401c9444412250080725000245400d0b01e00d890b05001c5c0c064140a42003030040c0400e040d041c2e018400d00a0300801103c1d06079207600c0c0f60309142e038640e1415800910b10500e2042c03500c0c0c00280c20342c2c44242d11062400090100c0c0d407514034040150500840342c65410420710351500410540780c2c00341003500c1d40804075190030303041d6480d100720075985584100d00504640d42086501c1c3c903095800070354050364802d9a0115412140e1710610304a001005030344072a00d0b460200312890010324000701400024031501e0b40002c0ca0a40341c1018444c0350b2005108038003048401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 992180080 1250 992178830 992178851
    0x203060108031312060e07060507050f0d1b0f08030103050a0b13170703050d090c081b180402030f07032117040209071b06021209030711060724 63
    0x9000050060070840001c5083c003011050a000850450181e0b07205182003045040134400b4a81214101c0c6800c041503618940c1c0321200206544d101010550b41d0340306501d00700641440c0055402802286561001c25122059110152100900c002a520114000100f1000c07501a0004500861164008129201c402c1c640b0410710300004000003031a411840203840801e00803280c9007007007064084420f6886a0916040d02c072070084e9aa00041286071030b81a40412140ba070040055480d180100e5001100041e04115440d00500320290044203403410343e902d540d4080c4046400510044c00d5440c0b01c0301f0010318518046503580151004c0f0714111004031901d2002002240f040d44514003c0084a180454a04000720250000340070f000c131180003801c450701c215410f81d0360390103001c207006e850300f25400c01c400070b5001400303a29008103007540403500c05400002240c0105521400f0000c200e81403030100700c40d42d08000800c0d6a10090007003541a101c04102d803518483e9480040040ea24101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 992181330 1250 992180080 992180083
    0x11d01020c06070206010e0610030f18030e0f0a031b0b0309061e010e160201020c070608010e15130504030e0406031b0501020303101a07060227030a0b0411030c0306130203 75
    0xc0e0082c404d40d041200140a500319442626a1080d020b40d40c5200c0c2c071066900480082400382503091189151040c0024135600340c120020404e4000e50f035100810108004000d00c01000c00102e50303000700880310130000507040081c21002c00d1343c50410103411540e46e40d02a0011340c003c540f00708a07034000d407042000c01e42001340d040c88401e07490550b24603150705086600c52841c60207400f0603450b10385101c210481e20300c00d40451322900144415903900c151303070303102c080c080302c9003070185c004681610000103041090084900b1082580144042e100c900709107103031401807401400c26420880070344407611050312240186c5000318415480d9500059441c200240391a58503000641190001c10a01c01c00da0200c005400680b0034401814034400400800800584038802006107090300104400b020f020010300c01d14003501049c000340700b07106884020162100d920030300c01411255084081401728203c1c0700b45100814024080302c21503082240080d1402e90100e458829908000c6a5481103080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 992182580 1250 992181330 992181343
    0x50c1308060f0403110a080a0f030605060c03090d03020a0605010f08010c02010c0206070e1c03050301060f09150e0112060e060f0109140609180106030b18070c03050c011d01020c 78
    0x10000103455a801e208420540040c400742c0003038200104007000800c0c00001b840769505559021100f5580da002c3c0c2d42d00601100b8020f07091201007450401c000a00741081c108072170b00405100043c1d80b44c185544108009143d1030303a001ea045116611003500001c8451140501038420443d400085e40e250040170340c00e554802c0800811139041c410420280307500029100d82280d86d900744a00c40f9041200402c500d001c950510b5207c405008207010f0034103401100450507a0720710794071110a21700c0c4000580d00f840180c8501d0740d0135101000107140141c411072400c9540e05051520308803401a514504082d2038590b0042495500311000303000e0030385040355003c0c6c4015804c0c2400c40c1c001d4a86144504d48280160100c1d0250ba00000c04107070590705c0441c20101215900410301680d40c5074a00140101500000307507000e609004040c03840030810b014410302c42d080780d81c3c80080d0042c0726036040703560780c000744145440c56488a10007000c2c03034211200c000a40361040c00040e11a02a112060300c0d018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 992183830 1250 992182580 992182589
    0xc0c09020c07140f09063a03090602161404061e0504230f0601051c0903021915110910032003060d0308102102120c0319080d050c13 58
    0x201068184041c035218040141d5100d0001c403000c0c0342d9565807017056018862541405034441f102ca14410100407100b403183c1c600640a90380b003040c0c139516490281e9072500210050880340e020702c4003c00500820b0541002c4101c030140010614030f641e032116210203968980282e01d4100980c2c01400182170034810b2016200c4400004062190520089a5009809000490b030356046500103055a4025021640d000c200200400c03000303c405514030004010550045005010382c2d6425031145603e00c5003039012075000101010101c4400403a100240180c034801109548107001101c2c03580d8803d6150000c03c0b4054501145100c01c0103851408010300c9200e0f07840600c4248180070701d80d200c140041082503450304140745903455100344000c407545568420451640b42c501006284031400f41000c0750180700303640180348012110012074483c03891920352074041c2d2120460034240220103d5245038580594646841d104c0380802c1c0c0402d13a18100c6510140f01c0300081d100c80c262000886480c002e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 992185080 1250 992183830 992183839
    0x703050412140403030e030c12151b030f190e100501050301090b06061803030d0b03010c09030b1609030b1003032a0305031905040605060a090509030304030c0c09020c0714 75
    0x203a41c608011030b900503404042c0c00c00c00320040181640e141007000030402072000b04400e03e01140c00040070f0b640c0c113401450203900f12030440030403200015021250b468180b0019aa400d543da159000c5002c00f0f03000700100a801d0401300c40202044003441041d10240105015000501d030314504e00050b5001030b8041ca019070302d400300c10310100c3d54850000350020402c41d80e083c0d0b200108190740c44c00e4410b121010754036010004038400700e020b103035000031445802a8024068415121415290911244005000080c0c503a0008104810100700d80401030117600f408134001e0b07201c2d141c1031881801203c03143c10b40c1c03110080034014181c00840540b4101080f01d0103290ba5a442c80d099002d8140c2814001c042c00404808202c807220442101c8031010b0b000b250801442c90a410210040c044c10758031603000786000400810b81442d140156031060f1a00700c002e510f9500c855800702c03186021481e041c1c403040c5081f00080745214803400102804402c01000709541c504000d180c00c0038068995007a4840c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 992186330 1250 992185080 992185097
    0x7030216030e011b12030c0c0c080c2d1c0807050708210a0f090302030a0c05150c0c06090301060f080a510c0302070507060903020121140703050412 65
    0x40045070030080b994003a180204901d00c7e1650203540348000c0c00c1c0d00a1050b203c450001c20400750000b03d18407c194202e6a54803648683c06030001d40c400c102c1500700c080c40640301803414070304020080c048100900c000c0c084280384c0680750b0003034a4000d06000c41c0c00c1d42103d1410021294100030030812010b20854615014440340301c41d8489204c0c01c000c0c0807c2c000c001f5040c682560003855142c00854000d02a100841a00e18107005401d299014440c4546103070000754150042800c150b540c070341c1140001f8034103a90100c0c10401c3c1c640284c0703800d40e4159207801e008505042d806c90550010007039a00141030400e202d01d043c8001c5402c02c0a00700b018201125040405a40c0b94111041003401696052010250643c10340116185056401815041514100301c0680c11307801001907a004106941c6a59140c0c41c084031104030314032010707002030004c422854100c60000c07014529180c00c05000500d4508010307407200300400440c0ca21000c03170b60301e100b007105000c225001c03000394503c503140c00c505 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 992187580 1250 992186330 992186333
    0x180412030b010f1409121c020c0109051c050d020a05010f0504021c0507080706051b010501050108070525120201050a0c20120409091a150907030216030e011b 69
    0x10040043d001d1408000fa86401c0001a4019904a030040390014190b00c0c0d5610486140680d120210141c1c2d0000c105824090b04090741b001c250840c9040301651002c400c10b02d0282000180d04004540c501d40d40c00440b103a0b00020403c0002100210b81500903101c0c0a036141801801c5074411950310030365506000c20007006a80d141c100903c03140e2088011703113a6100700e04055107400056045400c16204105021a0a58106000e016a1691000e9001030b07079241c5014242625428401c03940130503078590100d40e08901880c094003219040c807015015002000113200c4480660f048241ca00f0341188180c0c00b685982801142e61006400405201d503984c1204024258519410164258120f9207901d2003e0036040c060340700d1407211160701c0c68072641c80b864482c000308101c40044030304540b81180c1d01c3e03604900e0643c81e4072450001e07045400c210031400c24411030841c0240354104059081044907101c2d05156090380d078503806a61541c00010f9410009032400e002d406d450900030105800510 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 992188830 1250 992187580 992187587
    0x4120c050616180f050a0518010509130501110406030608061e060a030c0b0904050106080702070b0a0e04050a0f15180c09050907020a0b280b010e180412030b01 70
    0x2a003054a6241180d0b0000d000c580485450300d542110411540d1500000149100f020000c1016180c00315220501031780e4032810800c082e44142518800b808450b8010803c44c0b6101d44526809141c1d003108c0302008000d527403440d00316015088006040000400c044c044240c0c140b103410301901001c001800d50b0308001901414801d07040c00960071031404500001e146860b86030449000715030100e10740b109141c5036070707020490b0340140b151240146d1900d0000510f552040031710300d000f102c4940152014504140c00a1800d52001d0f40354414050341c400303140354545480c0304403480b40c03190290019903440d85a405030260741081000240300e12030600240100c0e08240d511a00c8010032080006802401c034900313541e03910060b40806d41c0000381504100070140c01003049102144200c1340510f890760341e204010485004411072001d0094500d100c1122100207034418040081e050502c100718120b002c001960480d6501041d03d030300c040310700038401000100f0809800403002030074240540004180000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 992190080 1250 992188830 992188843
    0x302032e0e0a12140f0405030c0108100e07140a0c0c15170604110a020a03030c080705090603150a12051504110d0c0b0a052701120e0709020d0504120c05 67
    0x60305900f000155800078501606512405201a251044d114155000c3c82011070b00248a542d020740101e0b6551001513120740d0b0304501c501c0210a40c0a1203d0510380240c3d10b4007001041c010902004941d00d1840012060280c0350100c42aa0707550713024000c0d40761400307004005a10250403214108881c0c81c2840c1c00c101016990784103a0500c0c15103954090020f8090800e4540384072170cc80001502003042680460528002802910140030110b00c0900803100f1038002c80e8048005481407100c40312519040f0021038000300d1200b10720a0390f1885000050541580b50b00401139941c1d40014034040000a100e5941d130181100c410703035458505904da0344481e0380ca900c8038920801803143c10004004407005500040c001e002015a1989540503016045500115508400d801c5101c4181d8130140c00401c1c1d541d00c00c0041e1b42e5139070040c0425058001811410640051601480c8000301e50302c0120310140c0700502e000680800c0e2170805040901000101495034002c10031940d0585000c2100014071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 992191330 1250 992190080 992190083
    0x2011406010f0903060e010209090f0c0d0c1106070203131d04020f03071e05090a0513020f150705071a1303030c060216060605030f0a0515060a0302032e0e0a 69
    0x2000c948148054100c40400c019013004212030714202c19403080540543c054103009005540c20410b944031a00c611031021001c4580c5194104200101d2a0f82c641a8121801d00c00302410100404c81d07500c40582d04080046801800603030005c0365078418034078580310700c0006007080741130410028034455a00d2000b81000340064042c4000040e50781e041c0c1c404201410040c88843c5101e0003000400022203900041d511800c2d00c549108400701d181e40c0e0041c46424092440c401901440d1341c40d59090101181d8203170002548a9844c0f5640c150455580004000d20341c4204050320b9a00d040540104125141000315601c007101031104810707403105450704c2400d032a0182030031032000d41c59142c00e2000c1d114144078520080901e010000070440b0a0b0010015900102c0940d04032a01c081e00903030750303203804031409401381d80700b901c83d2410380f064031f0202c2d42c1050f405007645514030b03102c4c0c005c80d00d00000e4240c001c0000064614040c45401c00401c181500e52590401b440341020a91410f99104101c860 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 992192580 1250 992191330 992191337
    0xe161e090e060a0b0408010c120e1b0f030a0605100f1d04051e0312010b090105040b180d1a010b1303060b010905120705040f1b1d03150106020d0201140601 68
    0x102d00c1c655a0888000f0082c01004d04c00d40c0d4460703c0340205806002901080000b046042400541e103029902580c191009035200424041407000c04540300d5183ca4400c07107400840c450070a44680d1418031864130358078010034020500d801c12a030344480307080c0c1d254881807602000071010b004405801c683d004101402d010405940d4450341030603800c0450282c070b00c0e2905810300c0e85414441002201400303039160341100c044040da98070242d100d00c81c401c41d0307035203070014801700700c14040040d150000d400f80c00c0009465441085040c800700b000b5801809060b60041c07060300742021086451550103024105000306d0034203080c40c07030000301a2030070140401011241c503803810301c62907481034152a000700380082c500e10000000140c1d071501c51700d5074000d090103a0300708000103410101d54052021002000002100c9031942404100c45081300e896080801c811072001300c240741e641c10031254141502e1540e80e03140c203515011002e8540240100b0010540e4105041d03203611203000c1034515030201003800e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 992193830 1250 992192580 992192609
    0x40b090309030d082e05221d0d0215060402030702150a051b0f09060a0507141b1c0b1003050a0c060201050709030804030f0206040e161e09 61
    0x2122038214014200361941501c41c0b042c2d4152100d40c4040a2801045034001d4a050101400d1a41840e1000e003800d160f40c401404504201e5030504040d99482c110141500e000c10300044d5804209840340c010140b40400b03030040b941190300405104090140d40a40010400c00c00320702d01b030710580300c0f00402c02c910560740840040d410a000b032017481011034a001c812855850240410001004141c4500701030440031880141d030b08019800316516202d07060249801c100c120b1007000f1441c1d11044a0400b0030000b4010362002a000160b0269a0091000a000181b103000ca0042c070300100c50712024410158802e070b143c09002c040422060058018001030401da640c402e402a01c0c1500f94002000f41c440c2c00300503c1440b212103080b0007514003503030007880a074640356400c030350700c4d451030001030015101084200300046c081c0451844047c405851039041a5460b141c001e0044e100301c0c0c90044102c21002c14058207a48201550702400034841e02d042c1c501d00c0040018036400300e5001e035204054000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 992195080 1250 992193830 992193841
    0x414040f02090303120411040b0d020d06021605101109010c110f100512010b03040c150903150212071107120204020c0d2120090a03021f2006040b 64
    0x54040b00c02c0000b010f0100e03591254524880f0503007a130304581c182c0d12081000280c410f40c2c9014003900c0c184842c0202041119003003a001c00c1100411024225a425802c01c0000b10694003002078500341c50050010f0180001491140b01c262901111b101142c28400c04c6410560f80c0c004401c0700025822400403d10000924042008100c804170700c581d1020018001200d1141c0c44402003150a19a00440b4100d036602e40003112503000c2034500416042c69210144a01c1041441d0f0302d03401400380c5070124425640f51243c00340000303e030740c141208980005050510201b000107803500310b5054903010004e000c4502c2c5082d142d45060082000c202000a1020155600c54040d14101803112043d81c00404075110040c201640286c860390314540d2000ca01c903100c1c002c600c9101003c03841c00c220007074005203200c000c0000743d1100d40c8c0c50394001c0e96620080007607102c9020000f2018240d1182c190100501680030700b140442e640e000943c25440c081640100c1c0000c550035804c16070082401c40e094584 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 992196330 1250 992195080 992195111
    0x240804030e150301090b0f0d0f0803090a0c30051213170a150e07050d08070b0702010c03240303181d040b070201020c150a091406061005041404 63
    0xd0b40e81d04070301440200001c200500305070700c60001340301e04a13658801d8200a6081c41401100c07400e011302684803c1c0030034004a0f418100a50707106c070482c0299030002280341c3c1e600c0c2c2c0d059000d030440d000c00400d41c20071102c82d90f8044030182ca40e01d0011021079904c035060b542c2c07990300c074114807030307034991800c003007003da00b07a510300d80c0c0500141130500500c80c0301048041079203540d1075082c4010344c0d140040c088101c0001c2928803c0c1c5251518510151500e41e0916040c41442212640210b5402d581009510003145140d2400c40c014403084d80007150f2403540c01030040039203505030341c0024404130440e40c03c21441a545050003c072640b50424458440e00000b0309050a507041c0c0c010341c504001d24000300021018188410300c1284a5007001d0001d4a8a600403400c07805501c0403200164012094190003e04110f04641c1c800c407030702c1000c0351320201580d4072012070705401040f110b039520030f5050000c6458101601c422420040ca070041c1441e02d00060381030424201c1e2605030183c2d6a5012b00c2502c2520f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 992197580 1250 992196330 992196349
    0xc0f101b0e240f0d20281101020a03050108012409050907120803061827010b061204050c1009150210020406050715020a0c140f0f0601240804030e 64
    0x40c3c00a420b0f40701c080c584012009441007441220603210703100c4507a44c81407065070a0740c460f010f500424024410004088883d100e4240c01d0389014006401281c2602c480c3c00d00040c800004150f502041035450b01c0000c45c01c0da5148152148034034071000c040c420841e1002202001c440c40080049001d868801900c0c4c11303e2450341080c0d11801083c04030310b00b840f070144002c5000d03410540318111101c0041e960004501c00645990043d000388000d14010303d6002020300290003c40c01c000a0303400882000a0741641c0001d112242d151400d104002c04d0240501c860040040151103104002e00003031002400c50f0003030b004007092070300e41000348078242c0d100304840304507405001800c640d80d40d191704016000340c12000c01110002188030300074842d80c0d00c1e40240c5080c2840c94a034206041d80c0d580d204134041b404002c0405152007501402c88100808228a403060401080030f40907030b504200c923001000b0700c24108501c260041070280d030300700c6078081540e56003d41c0602e089500c800c62140002c100740c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 992198830 1250 992197580 992197597
    0xc0d050c0a080d1119020c0603190c020c04180201140a02030a08040503040f03111908031e0c0706050c10060302010804030c020102011415030d090f05060c0f101b0e24 73
    0x35000300d003110784115807856180029841b42c08444e16440b0707810400465120840c2c50000205001c0000641005107801101d140d00b014016507a0046811010030100d89070390b9103202104915000711270540d40c1090f544141540e01c0d01c2b020340303000c1c05c03041c2c00f035602d201e19040c8008100a8030006000e1004c14402d44010300070031014500c200350769092110780b06850b0b41056200303c20803040401842d09035060300b404c4545200280d07003481402100d0354224184c80c4000c050144040200484400045c02010301030000c0c0d881c2c09403200301c0c2007010781c0b0b0301075411015503043d45092000c1c030250307070007402d140e601a5040c80d1800200c0d4440c40101d026001c6682e1441c0108151001c0c8220400c070701c1074a91140209604458030249404d000300c4e030f14481881816100e40c2c4011041c00103080000080021b00303088800c0f034481d07100501c14145803070141c480c180c21581c0d840c141c40c0074040611031403250717544203494400d508030b40d2000000d0040103c0c59252900802289030b03101c41c0c8551900703890000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 992200080 1250 992198830 992198861
    0x21e03061215010501300e0304170304141507062a0e03061021081626070b161101060b030603012412030e060307050c0d050c0a080d 58
    0x810342c041c0c06020340d0b03003e01801d0302003100416902d144c092034190081151444045404c0421a07685007803008008802e07a074a00f03800108800f0500710480c4803102c601001410040da9201e15119443c0e1040c8140c002180c07094506c9940305080085260a9a0250360002000503c1c1d0312402195440d82000003c00602502e07a01900500f40fa044568002c02c02d4080d0700f40c034515503682d6985078441c445409240301c058000c00455040181d06500d80410900c0345480c140b90a001801802503903008440c00c030707264146148a03c0c0c1c03080808251102c510f92000d951070400a840d5611505058000c001580c031040802a04000600c121110740e0a62640c1000b0420183c80300740801c02540304848150081d82000951604046c1170300c0602010b115a82c0d803002400d0a00d0850001c10b09911001e070b0030414100341c410314540c0c80c40300030340c054211921100d640e01600b1040c10308002d149400c20007880b4041c466080782c8100803d1818801e5441400c00d5940d4403100c80b00001080c1503034410182 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 992201330 1250 992200080 992200093
    0xd0504050307050d0806030d1d0619031a0a030201120b060f0c12070221071a07060b011812020301020706020705010b12061308030a0b0d03050405040b04021e030612 72
    0x24060007000074000540180c00355402541c00840c1a242440152030464040d40041c51026030700380b155202085030984049200e19018003a0000390068204e100da8165020004c94003c1c4a1609403007182420503081503050005000400020400c030060712010781480164104002d501e101640b08407900c0c20000d10036a210302110725402500e400400e2183c0c001d215515003a103201030142c0c152241180e00030038060018203a00300c040981c10f081024021244102c0c030021a130100c040a000750402c00b041d100a03240d150031305000382660b042d00d24480c14010740190090350071400480f01019500c95042083c100846032021a0081c0300e40e0001406230361002c181c2c1c07002c00106404c2095070362411500054104403e0711200e8036802d05455400b04c2c0410394802e2800513039184041c40e4840980000050164140c9011464a200c4008110300148000609016618161240001c40101500d0031418070140440c811000a83c50b000f0440e00c820210000d0750305c1e560b40c03c06103a0b039204141601c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 992202580 1250 992201330 992201333
    0x303150d0f060c0306090b1c1b0602012c1e0309060316030506120a02040903030b04090b0103060c0201020a0e0609040608102007050309241309050a091a0703020d0504 73
    0x3003540550060010f405c0400005101d10700d0301a08420348030081c40451500712218050381402e1049204607014606c2902000740c1c50090b40c1010018499a00046040030400300b85e181d40012103420720b8907030f03017011030041100140002c0d02c1d02c030101c44140340e10001c491420301500d10300560610382c0e40000f0001c02c1144e0907a98600d00802c010141c1c0f0184000d440d880e0400c2040498041c03100500d90100da00600035292603086594a28001d0900213801c01c2c000d8042404c3d40c07494070f8217403a4016441c00400401a15100740e0aa035410351008506240b05880003c1c643d03042c490181c1c1c17181c41e011410240960700c0d035024400411814080ba81502445c3c00d44001a001e03007012091040c90342894403406d0005803045440e0b8583c040b001d5450801d01c8410480e203201c544145100328554490015450702e07070390006124042400101c03100b16450f188600c400e661008102e118200d040c0342d402c3e0300080c1e0905103420505c000b0a070012640d0b8076450304500038050343c0184103009003080248030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 992203830 1250 992202580 992202593
    0xf030a05100c03021c050c0415020606130b0a0e0405161e080c010509120120070c050d03090302060714060703020c1501030b01050d150903020708060702070303020303150d0f 76
    0x500052580000e000d2050345220540c04c9001d1158181001000261200080c041a078011a0b000002101140c1419212045004051004216080540e10001c1404024508a0b038401c150784540601404048104c8020440190452003a281c040c0000004203003000320910400b108540b20044030075005031380c0c1920b503200c0c000a68071164500350143c130110700310710301060070b0200c80303c1a1501864400e1400600c1900544050801519560f5030001d01c020100d07854003150f54146903010302d4403004a800c0c042c1c3c4e40c1e001540107510070004240321800094010140b08100c80c1c04540b80b036107841060038445030070ad21040d40f051042c001d03078041000c40c9400d6805040384940761401c541c1d031040e1400303a20603028000e010141030603148200400640c54100e98402e0860f00c2030030b21211880c040c40140060f10842c00045001d80c0000301c05014141080204681c00070045c8000c04a451968601949034030024102c3c44502c09440059403003130315030744002c91496900510341280c10000d030a00c107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 992205080 1250 992203830 992203843
    0x5041d0420031018021302030c030114011b03050d060f0807060513171507030c081b040b18030c010207120f020f031504030206060a05011d01021612030207091a040b0f030a05 76
    0x403841b41e42040c070400d207803610030300c2568410409003403840e14503400c05000307882250505844904014404020300d00255496141c402418440c1d26840d444010700c8900b0410b0720320580240820224901080240081c0003d00780100c4a05041c80c907680d24104060b92244107685e046141c000020306241d000703035640051040c61540070f0409020301a1181c0b14110140c603241840b00f8001008080415a210f8519014000700008180310528265962118071100d40000601c840f0300d0324520452a5242024410070440e0802403000c0e040a03810290b981520030100303000603100c00341004d0104115113036034a107039503950001012109021048000045403200072034003207006003d058049a00740c00e10002ea01c0958070140c55810541c0c22981002d148a0f1001c0c100d64110700c106828900c0501008041d4400740000c102e070303010700ca1f15a05029103850700961054010900c1e048409003a9a0b00e10310241c1c1540007203801040b0a030340c1c280000d8100b500d1800c1c10382c0c1030180c3c0503018100140016130 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 992206330 1250 992205080 992205083
    0x50406111908151f030615080a0b0d0213050a0902090a020d0b031b0607061d0a060b10050d0b01020c04051608060603060321071205041d0420031018 65
    0x3100983d42e11100c8140c942c0d07807464500e9070818800140e40c041d50b45651102c00000d0064036001070415a034500079001c03010410703880408a000c007800d200c011440b5015040494034255562602c00f541381c0d01040c0f40848032018003a240c3d03500c5011818420198008007205030300107184100d142000643c00d0000e5014640c80c40310645452484400c5080202d00c040c607140c000444c085606d01c1d42001d02c40c269102c0041140c019039680e860704034542402500c46803940140d8001c0101b000c5038a0000110344203660800e200350011041076050a510508940425999800115400d0f6040005030310b028012480303980d2050402e0108840d8114030300c140c2540d950380356210720203529008103002062100303548003a00f41d00701465040e4001070402000c100781e140091000e18020303040c2c4406181d5119802c0c2440010800542040444944000034240c010460780c4240c4c1810280e442c10790900410300481c03802d105031105d09a01755014000150b084c601e1279018460200c00310000e4074a01c0503400c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 992207580 1250 992206330 992206337
    0xa1b0905091b03070f020c0409140706110615220f1a0609041517070e091903110703080d0c1106070801050d081b06060a06030b060d0504061119 63
    0x4100e06802c003001024442d200e400c0903d162180ca90440f034071454500c41d40298400c0001c0c02c403003a1514410654004d0096031401048d10107100d040d41800183d61020081110324045051400710106089030001231800134443c416070310320003241601d072041c04a40b404042c280164055010300c0d400506a0600060040000300e01c21820a0514911a408950007070030900c810f80090626900840040340b81115034078400d942c5000c41d8007550341002c4107005035081b6410801044851061542d04030f08180701922204900d201d104450040080001c1c081140c4100300d0100202d05200b52406590840f907255a50b410b42080346005c0c00c40c000b15000000c0c0c411000d9101d00b14003181c003c1c000d508644d40c5100310b910f0701d030030082500604881524419420480380c10b10081c0098030030440c0031000080c0085140c008104601d0010540c001e00c01c1c9410706100310f41b03695800080f0f88030020f1b0000001481d480700d040c240f004115000b4081d800b00c10024000c800300800011504003800581c1c3d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 992208830 1250 992207580 992207599
    0x270f09051e0303013005030702010305060d02030307150b1207050901050f010c08030c16031d01140d050c0c031c15030f030c0515162c090a1b0905 64
    0x5420701034121003040000c40c01d070070a0005000040210803a0849007404070507604640c0095000c1c402441d1700d0000403a40c1d980001600c00440d40c15025071940001c0460385c2c080c0404054022a8a80c41001d500400460384000941500030702584955407801c0d024200c00300c6640b22054495507a000c0f8060244180c03000000007c2a180050028801c00340680d1202d034643c0346e594030340b2000d400103042050020f8084c09541005411461807294250180d40c0b04068401c3c0600f82406144015011a04001207043c4120004010400b1034280c00c545010005945d85c4060703c25980c0d00618a00341d02d980000581480c8144151790000001c112282c0c04001c00364608201488600032840f0007440a210b0703070388074000300740503100e483e808502a000740c96503443c03081c5100c56410303000c488a0f0350519400c0c140741d501c540e21450300315405504101c400c0c00f01d86903000391354078048203e8403d480f40f11000c001a13500034264020822961200c40141c0030444c03c0e01c1c0140141c6918001d5500400e60321 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 992210080 1250 992208830 992208853
    0x306060807050a0905152e0302041e06050306010509010323041406040c15200d0201141e071205100e1e04031d03030d0902011403010807270f0905 64
    0x1440b905c0d00a00e10f1011409500000b48280040b00000103580c0c00820b900f10620200004140002412004070307580060791542440000d900c0280d42140135039a22403414024400e494014003100d400c42003d00345207440c2d0207102d00480113030960f0262120340001c0101200d80c00a090001d0600a51141c018940c3e240554030105642d00300c1280e000c0d00c0c4a080404c10030070429080e00c09907a6140600d002800d01a541042c20a95102d202c403044043d40074070b40322906964284118400090a245072101605003031855200c00309420581d14444a01c1c0d40200d420b6a0040c4800c50419034200000c1c0850b1800040e101c40e4454a4403444915052840009100c1102c0e030441e40650092004088425200d5071001c4929007505407860000080000c00c00034642d60810141c0410341130808080790104081c400109030203000c004140c08500240b006101d0300300080f8400d801c0e00c2d0f481a8050b0f0381549140c0da01c407410480008a41445c1c17818a881c80410030540001c600203020320300700e41484410303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 992211330 1250 992210080 992210099
    0xb0a08090d2f011a01020601090204030803010b0307020a0f0309150503070507030315051c0510060b0714010902042a0914120a05030c03070b01140a03060c02070306060807050a 77
    0xc400140004180c002011000c031054020001c80744102d00761051003625a100d01030031299151440c201c4046800401e107015030741000340c940548000081581014955640c1c5c3c0a10300041c001c8503080d000c0800002c05041c801c20805850302d8105c5003181c0d404516040c090f00100b618011800400d144044003807038540070300300b16400b41042d41d403620301d40002503d0440c002e00460381ca0b019003030f0010200085607035820510403040994540c16010030816072400501c1d0076091000c032600181000d50401c0f070f0b01c0e02c20040c0c4080ca9046404a00501d544100f1a401081070300c0d0004d40c85498805203005078141340345039101c1003042e0040800e070044594001e94410080707110304404440c070381100550701e042c18080c1c0c0000e45c1c00c07a400c40c1c4500300b4a603030b01811078000c0620010035030304c003280b01000d10030500d14090040c00c0c2d440c080d41c030b0f48210384003051000c03840d404043c1ca05502c1c3c2c9525510940708000a00c000c582214042103a2600c54400035280d41880c480c19100b0000c00d00b001c038140c503c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 992212580 1250 992211330 992211343
    0x40c0803040e0c1803030c151302030a1401060302091602060f2a04030c0602250b0708250309081e07060e400c120b060408070b0a0809 59
    0xd0440c03a0140d83d9246500c00b800b6520504060b8075075450b004405500752010805480e4141408005d04524160841600224400204030302c0c1c994030014080c0000d078801041c1b18051344c0d0440502b0750303031002d040d040350301514203680029003108444080001101600051219508559003511501e4854428101d030305081510941000c40046c0c2c0100ba003003661807060613140074403965140c01c10f956620750300a0704009a01140268100c0e0441ea52208089110030181c04030704030f203103a40281040c0060825008410004210303550000c1c00c0d420300012405015018000203c0d84204c0035070320300e0000d08003000c03880340340b5161240483c0c16440c6001a0011001c041c014001002c0e0300e071520750b040310800640e000319508142c040c0c4910411400141907100310341051034900e540701c1c402c0c081c1100210394454002041d64a48584600016441350340005018035112012400c8800781d00010083d100e194025040307881140c50029034050034038090100c01400b9210b030212556006031040e00c0b00d0307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 992213830 1250 992212580 992212589
    0x207060915170603012004090501061b0b15040c02010b1e09041101030b1011240a200a020601050a0902030910021303061d070906060212090d05060f040c080304 70
    0x140b440d41907001c510502c052482e0b1040c402000401c0c4030780d003005105030620a1880407001c1c0400000e00740301d140348600a00e4014085c528040b08119404091b04500b4030402100510f4400d445001c90743c0b406682290207801840100304024803103500f00701070700803c8094900b60294407107100d200d500380100303c0102042c81005c0c1546040c0d41d00d5503210843c4440c910b8000d41410307130b00d00000348162142460b80c80303a41c000742c50f00030f8003244042580303251501c0c00314110240b0ba80d2265080380c01003985401078110040c06404140e2001d00d400c408086807552070070a0610402088000310140d001403400c0c100d40040c0c440c0070700c81c0d0703e80203180f0584c8070441d1400c075a40d00644a8458000042d40102011445a44400f10481e140c0e500c91050b50286c803001800a500f0100180079031794103001d032400802ca00303442006184d14106020392103c0d0580020220150041030586150f1107010400d02030b80d40c000155001c03442d05030f00d0092000c1c0141c4042c0c1b2510720351503000c0b0b5a810004111000c2d038 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 992215080 1250 992213830 992213837
    0x2120a110d1e050915090a120305090f0607022a060301150e0411090111060906070f0203070b2815090513170a030c02070b0304020411040b0403030207060915 69
    0x2961066500000e0981982910902c0311011803040400c0d0107807084074014405007001e00881031382e207000b0309620103000c3c0c4012241d4102c0d01c10b8100145124081e01881c904c80c0c100850fa680c0c4201406041000006c41c074002c070b010740c0080090403940860040802c0503610044800c803804915a0504000c001581c9600b0400400040c0007110485408039000821440d242c143d201511001c00c055900c1c8e000a910f404801003142e842130341e041004a1682c2d81160010503041c40c040000710b6855602405150034010034460040b503c0384288121104550860010395090600c4981481c60000603202500645070f82469031110386450b00880404e8071091510418039414200c00000428010340301c41d24501c034000101c8000756616000c948420355032840f00752100804800641522400f19038401150401c040c24400f140068090f0380d0403071f4064400080c10400c8010410591046d60024500d0150110b4004100343d80001c0d02016111136980c2e45000540e14905880f1a030301c20020003011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 992216330 1250 992215080 992215087
    0x1a011404030b2206021612051303060e0c041404031106090d030b0406150c0c0915121e14070b1213020301060b040314010b10080703020901030902090a02120a11 70
    0x41d07010002e80c50581400f6010021403d030440c0d914001240d00c00c070309100101c02ea142c46841440001080c0103400100b6040052a084203246000303590310140c00700900450781d440c4041842c036420422a036007440050410810700300d08030f800f1240b030030044a046000a0414890001214000c0798090140f0b070b41800a01d203000e1880b02c280c001e0010002c000b40c215907200400075044480b81c0410740204080d0315000d07268256402c1040c2e10400541000100c203080211108140303001e400281e0840f4111a40740030055031525011441803000a241d41c1141c29203003060f818051384104500e018540d900880c1d124075500e1002d5009405a9490508000144000224044800788014003040d02c014000142e4075101c0b000d58034035030000d0f00207480903c034003403038a91565824402c800404508840c42d14948011400040001c18010160300406401250324a02039001c0c0c0c2012401030744c001c104541c0391500c401c10b10b0083d00108004801c0d1648000850420bd090348244000b2a01843c0e2182c81d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 992217580 1250 992216330 992216341
    0x4120c150c1712010303080609090c010e0402070f120914090f130f051002040f0803031618050411070203010506041a0d03050c03040b0c0f010c09050d03050d1a011404030b 75
    0x102c1403100507411041c0d801c2002a00f8000e0861040b0702d0207144030351140210b50801e1824065a803900600c080d1a071303401034120300803c1e032b040008c44140d035008650240c1c1d649003504e032041e2101c2000500405084164041c111040d4120002c08159503c40310380550311003a80041112055081c0c80f0100c10f00e0f212408241c5240c998a00c0e402c02a0040388141d105141c1d41d81c6071880c040508184240c250ba000c40c080c845c0361980c2481c00b001b803000b0002941182031002d910100142041035800a00c10700c0340e00003400c061000c00030340041c04001d004024000344020b00c45c0140c1d0001000324802e51920002581ea0300d05403040d80e00040000c20305840c2c04000303205000c0156402c841c1034090090905c410000040100000d20140030062509a107039035100700010b18041d00d000881c191a4104013910304084c0d4424100f000700d800c22a202610302a46040980b07ca03c038219002c800f09050039410b0018020400b00c10104d00ca0a0340c1307101d25403005007140a850302681c0001081a00c00380f01040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 992218830 1250 992217580 992217593
    0xd12080103020324011a070b2403010e0309010c15050a02070b06030a0c0e0c071e260711041b03050402120d1b11090a14060d03200c0604120c150c 64
    0x6e010b8100300b0011450700740740d52664400c2c83c04c11104a0180010441200c111548104140b00d421a043d0021f10103035030003c150725100c0c068032140c6410054500011420321103d800c01c000c8441c1c030300404014a0400c030504802952018800b900c0d44920400810503074240003510128594100d44034101c81403c121107040f0390f00e0054407400c0641c1c42400040b001c9416a030320014807442900c00f610301c0d950a494015540400c001c40050500c03903546501042c501401d0454034505c1d8003503400308017001000b0006006101c2d030420701d804140c0309180c455a103601a0300090285000b00c540040c41c2c02500242d03a520030003000500005021901a00078030060009582c0f1880d01c60541c0b28040c000e100041010380c4000c9a03191559519504940e0014960b0400c007130300208192021040d240c01038a001e010321030031418224101d145214800780304a400d0007821b11403000142110394a0340e50369001e00207240b45181c16103644541d15800224021200603020308649039440e050000d14039501d030b98 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 992220080 1250 992218830 992218859
    0x120908040e0c0d06122a090c0e12070501020a14070f09091103010b061e0702040509060a0c030513030f03060504051812090a0b0304050319120c17150d1208010302032401 74
    0x1310140c85c1c080c0e2000c110400d42d8002d00c803030508c4c0740d660a04070506040802c80d0601d8001c0300e002054010b60030034406660b0102e0b102c2151a04984031002003030790410a00e241a210f0382c000e11031640e4140000c682c96032150449400c0c2801044c276034080303140c07000c2058200c1301e40b00b00c1160320581c2000120300400d03918960301405a0425115806d1400c550085015200300b01e0b0a000286c0103042003041c12810742c455400c0c0031100e440c0400180ca401030051401440724900078080c04400902001c1e1036120303401c40d400ae0b01002d8010301541c14101503e040707170b8542541d1428203000300d5504200301c40d0240243c409040b802085100d840e441e009103001c02d61b01c094403c2c1d8044c0400c0003040f489400c6402d00c0b1207850096941c512054440c0196901102e181d80554020021118400c10780307989403829003500702a8100c46045015402800141074400717850006150504134000200e6854200241038100c80c001c3e000e41c1d43c04807110780c1840c2000138004140100d081c04c0d1005111503051003880 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 992221330 1250 992220080 992220143
    0x52119050304090f150f050607023003041d091015031703010f0611120912060103050304170a0c03080d111902011b120908040e0c0d0612 60
    0x3542e1406849034510800d0722403a14038544d4554a5030300007440b50700d54102c3c0000410310311161460075070804000401074843c00c800684600c80d050602d40b01e03c001040d09178030030561101060301501d2690000c1da100c1d0014400c5080b01c110f81b202c3c5040d0480e0f503104152103211002c020b454662280744080b0001d00040d10040c080803248103001c00001c60b00c2d00c0d20500c5400303014440341c41e1743c0740408140c0f40040c107070403030710030000a510140420080010902e010b0203400303c82c03d46424145010840804030582d41519500c145000042800703c04030041041d1071a442d21007400010321b001c51980d4000240e0300030004c5260600401c00301d001d030702c050103501c5a5500d020036482d0354540c01881c0e5030040d0b00843c0002d4014828882c040e174092154006045040d00c07050ba50411a08004e0030a00011862803c0c0315200c44843c000c010307100003101c010b00301070180c0019500b450200301d00c113600000c4030074540c2450241e000c0744900b4140403100701e0303c1c3e000704c08103c4c08a8401c0c6100194110980 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 992222580 1250 992221330 992221333
    0x1080a02040536070914010c030507030c1b03060b09180304030b040503121f0e0112020603040f120503040614010e01060509030f10020706051308070201140903070306050105211905 79
    0x1400e000c0118004810b03400341c8460745d41e44000904000c507950f00702d144540c200d070602204000b0000000d030402d003510389890701420071100750b0040e030804501454989103401040c0b40d1208001c02003000503400010079890030307a0244040d41d80d1102c10143c600341c0c001038119540c800e00c0700b0000201ca1540d4698400c0c441c1d0300741c1303081c0b0390b200340180e0314940c069484a180a50510100350310326a02031504c002445940c2c417941055150000c2c10f55840300c6d07140301a0003040e0000c0042c00303001030380304041503035940200f0318090070040c260300410070b81041d201100d140341041003095201c104c3c601a00e06175100020141030a928110040c1c600741d001c5d082c155014020304402401d002d0b0203000e40030f90798940750b801507039600c0c00d0725066007210f0006050903101e1140200c1640401c09a8041c2d6034107a9080c24503c502c3ca000304400c0384175000c2c80184c2541442000e102000b0400300d82c000604984041c0c8040449a041404034665110b20390009040d40d48130030702c840344005120b0548030450b4042c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 992223830 1250 992222580 992222659
    0x110c09060622030308010305012306150c0a0f050d0f080a020304030215010e0106030f0204150c0f0c180e031207210e03040501020d0c0506060f04270201080a020405 72
    0x1680180c0b5500c1036803081e4085100c8000420a1100c04c1c05040f00e04060b0032055034408400c090381100030724001c1c00190003042c84250820310410120100ca40c242ea5240407145021801e04d030024150203014000c84060140d107207082070071406245808900f054a0719111420b6989800c544020340005001b40c2c11403194908540030901000801e5010302015240484198140040a001e5401c03610308414001d204010400c500b0b0303c0480d1a240c0420715103480c48180f881d0703041c51211079843c00009014a054000006481c004003880300c2000d100020f01446940940d0790041c0d160b0140140390070340340b0801c40c00078000c0d62003205800d080f18002202d0701c0c080185a0925001c0b50b029100f9031032940d01c002000c1c092980c040141070244005444c022211130250b44d42c1d5a1142c40107031041c0e001d0714030402d860000e650f850f0001040f0900c085402030140415940c026030010b445d440581c0416001e1000c140700100ea4001c03103003070750300c0640603404813113010101c80c494081183d110340d40c512415 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 992225080 1250 992223830 992223877
    0x1509041122092001021612050114241c120201061a030105030f06060a150905060a0e100809150912040608011503021e07020f0a15110c090606 62
    0x240b207800d105a01400466110042d849800061181054007190565210b400c0e0b0142d51003242d500f80c2c0540f013103a503041b84010250729249016104100840100312103c1041007100300c0310a0206a4a940c012400200e60f1245010f020500361441003500c481000c00020f040880c20305c002c0036020324180e100004074103a80d071802c850070000000c401a401c0314000010044c910f070403c80007819108a5000d041907080240000b5409803c42c81603484a50001d0b0000f55218000c0b02001300138100170300718a40e10481d80d83c2c0244154410070117148580d181034000011503100368003407072050481c0700c000d15000c40900d002188200000b00503407202e02c250303052401c43c032482c880600018151a12003034101e5041a94854548800700e01b0801010300c14000483c580b00d0071080025640a94980c0590b2030040b030000c20003208094030301caa0001e0800c00005840c04030401400009030b200d94445549a1002212a0325074103001940e40d400300844000c00c00610740b6900a18410742540b08420100051 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 992226330 1250 992225080 992225149
    0x80a140d0e100509190516091d0f032d0f090a09050c0702010f0203090a0609080c0607050d08071205040f171e0d110f0315090411 57
    0x1880c0914003030341c961590440c8188104600d0b007209400c41030034040c526042c40f0042d0345801d1628010300c001241c1141c0824408148686411110601407a840f5541c80700700d09800b402c2d0082c2140f800d1942c2840e1100c400101003640c80d085610423010314906914010401c21941d04840c0c15074030011513004002d000b285c48801421211341c070b01ea580f03071030f0708800081281c0300c42036070302031400a401d00d010000024035840c121031300c2a5090800c6003045400020032446c5019950b191500841c4800c0b000c00c241c0c0d0040e201000b02c442003000c403016080d8803c207101d007d02030000b00400e0380d40540d080364600782c000c858040d40040585000c01804840d281c0d41c02c259401660155903411b004100c2c0d50070f0101c0c03141805035aaa440480d03910340100320402c107424410342c281c0c0543c10b0202060f030f80b14805054100050805c2a0040f040d02c82100110794070466005944040344c41d030540b1170a103218208a8041449950401020b0700d0000c0300c41c0900c60064044041c6c04119490102c2c80f0008410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 992227580 1250 992226330 992226337
    0x151707121d0d08130b04151e0b030f030d0507030b0d08070605070923010224100f08030315040b062706030c04060c080702030a0b07121404080a14 64
    0x20a610074044a8040215141c20410401129010400110100311107003403980541030000380d00c01d800c190140c0d01c90400c9034440c07081c43c4ca1240724900b802e00404141000a17508074039100c40f0301041041d0079043c3e040642c3c0e062101e144c105550000d009007503020740c155025980c41002810007080c03050380740000414084001c88201c420b03100200d00202400800e116056024601b8180998464103180340c0060151029402160740e450701d16110805034400d00291042c80c0307030300ea6480c2e111400010121207103982141c44040c0d5075118040000c80ac400c04050004886441d4041c42c41c40c1c660603000407200d2440b92007182c202d034481e0301800c0e490300d40c0001840c143c542070340811041d0521250298418595003107691088005105001c000080c1508441c201c496034140310307640c07480d2890046440c2c091607802075803501a02c02c61606000c0e0861900d4400c160070360b00e080300c44400e442c042c02100d82c201c951000a5400c9800100007400c982c001707000320411800c2142c4a500c0c0e40740c80b040d0a07030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 992228830 1250 992227580 992227601
    0x2a0a2a050f0c100c2a030308010603050411220513031403070e0909120f030a0e16090b18070903030809061003030e0105071407090609060b07032f1615170712 69
    0x140c101700c00300141540000300b03d014010703a240520603030409440300040a056159024400c840c4a800e003903181c03e02c0a4500702800300064240f041d03140c100109401c407660f0500a4011481c030701741680d8841040390072280b00b0300164a485140ea5491814803103140d80041c00a0000c2c45210b5120618105400190410003401034050303550b490005400301c06d42c0e803080d000c4100c503808004020340701011940343c01c0c181e6241c4840001d03e00907200001c7d0138404000111003c041052051001c280c0d4032400000036070380a5140d15415440c4d548056030354100c11204401c2020240c0c0b01480068030801d66502c1e03800e0145017190400381c3d5500c41c0899044100320119081c0e0088500b000070101034050080149100744e4108406841c06e0403003401407192020080070414280702006d81074008004442242150300442c001110030401c006030344903007520460102c058a1940001d060b030748802a17200035106a9284140d58041d502d18003011140904130300d040c0440d0f1200491515140e214aa8462 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 992230080 1250 992228830 992228903
    0x90e010b0a0608061806010903021908060c0f04140d021201050f0916150203041d04020f040b130b0301062c2a0a2a050f0c100c 56
    0x110306410801c040d000e8503034801001c0c40b006104001e0310740d50710b0b04103200d80115203010381241c0d0703110401240c5e0140c0c6900002e6100070407015141d4981c0505c2c01560a540200f41200c815481f0f08451a000f40a0303000420100c810030081400130f600d1520304030f500c00300090448000300740280d0000e020726441c0f444038000c60b9500c200b0044004222041180c100c07400d900984146480741c59694034003200f6018603040c9003080e500346000b40b0f2003001141d0051004583e000d6808501341c0ca40d982440050f20241c4c40303080903e80c2c080103861700c0d01c5000c041003801003403d42c0b40021040c00c14040c01c0e00d4154154555681c0c0000076190303c020b01840748090a25400c4040c2c1704502514041014018005508005031411480320505102010b05a0041200310700d50b20745a40301c1040310100c4520b0800321b841e145003000c40700c61040700080703080d0552084003a607001114040c0480d549400c005420f81e0b001c0280081110304a0007155a12001c5000302c45603a240100420b0420054950300100b0f02d55 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 992231330 1250 992230080 992230091
    0x1090c09020c060106050c070608040212060103140c0303040b12040f14010209130b101803051b030c030a0221010f050408030708150108010501031a0909160e010e040b060a090e01 78
    0x1640010f02090340504224104a41085200c1035442d03a100341901561044c041024042025503031880800c3c8402c182d0007049504540c0c4a25001c40d4907560240c10405502c03801080c0d449600e0048243c2e0f0a441c20f000645080180032044d2612194000d0000d4a918201c150b110012a503e11000401790f41400005030b80c61031407209200520100f61082e82d034062600441c50201e0390381040300341608061745000103c56115001d281a0480790707030700051241c4a60300d0513000700d40e0030503081c121040088040e20110541201815116240410300a6005080b544c0750b16050201002000d41c06450000000e940c06e0551803400c1104c005850a5588403804810407201301c0d40904c51a40c044010f59038000b220070540000380c0b02c03083c180601414144c40f8000003010442c85800c0d900390140c010041c84071810582c5055844080c5203a90410700411194040340804000300e001c4d04036410160907030182c0c2d50380d8a03480500b4401400c41640081000300001d1405c0d0070b030040032041d050a8000041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 992232580 1250 992231330 992231347
    0x1c0b0108070e04020a090923010605010915080106050a05091e1c0b010e041a0f060108100f1701020c0601030602030f01140f01080411120a050105070c0503070f0501090c0902 76
    0x544070580e40521114900481004016118400460101c54000c1c0000c6085641841c1440d03040c0d5400944801030990004400003155054010b02d08590080c2c03900501661648580246961045c1d0341070046071242d801042114442c100828041100f0301c4c0c82824613920000145060344100e454140c0c0e03800000e80c03081c8a00c1c050481d8000c0016900c084281244559103d082e03c0c00144640101000b031800010700b1701980000318011042d2954580c0d90324904040c24050001050383c0359400100030b5030000d040b0103494041e42c41560095901100000d28160511072080220700907139039107540a200d6128001020003280340030f14440c40d400341e20b03071901c40074411245005911503801110240070308009526102101e01c40c0780001e19001c010b0342d80d00d00788030b000c598034406e40c0d68104010111800b0440b4000c901021414841c00090149448140e0b08942078441e44801800b02d030070030090400010f8101c4031260843e8426800880c02e400d0a07250403605074081c2d40101030250300084c8110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 992233830 1250 992232580 992232583
    0x108010509030403030906140706020c030d0c02190b061906020d020d090614210703091109090304050d030e0409030f11010507052a0a0809090c0304050d030b1c0b0108 73
    0xe611031034034401941004e00e035850040c41c1302070902c5040140800140c100b800c4101703c030100c80045030440ca017555604c1000c035182d079a0b0381c4004661382242c3e2500c1d070b005008510100303200ba244860b07000c00b180c643d40705445e913a90042e000350445901007820380308500069030055000004140c03680151955240c1840080d0a00380e04d0480001000704550f03050000c81e07000a0720301c264114142c0c8041d2205108141e01d40e07080c0c1301c694000c62a5003440100090301d54950003088000d440b44034074400e0b00d04a801070207d25142030b580c2040d0354009001c1446541401390741e9880780e6000780b80115104080c0d0700401d00b120303a003260503000610441c51074801c0541110601c030301d450440000b0001e6240460000b40107000e0807400c9070107500644c50280640ca02c184400540c45c491005803252504181b4040e400c561060011030700916a0030300250007410650103983c842c54110700070340912070310000c049004000010720a07510214100c2c02c1348000038042901d0345407500c600e030700b5001c0707506220549 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 992235080 1250 992233830 992233841
    0xc010504141516050a180b22030503030f100e01060f17151309051f15080607050d060e07020703150209060d02030a0b12030702271317040e010801 64
    0x40501d038030020902c45090303025030f080038a4074210710300319440d0240540121003445515404040b01c400c240c10200d29080c04400504000e207000110f4441d82d0500140520b8803261480040c100d500248000b070070300b04800300303000d43c08200390b03c40300c036116100c0700701c42080300003030b0007184c0064040318400c01d00e036400400309100d6507070303000e04203da61510601603070000001048003400303031502c0d400101450315140c201d010003582c0300d400d59500b81d0784c0c004031140040001070411700c030b44d04145a40120040c0b01d1403a0b010f98807038901034200303540c2d40042590705a10440214801c155500c1c40020f007004d8420721180201802c7e80903000e0310b407442c02d1100e5981039503048000d950740304100c5505243d94400880c0e030704101e481c0e00580c980d942c041c0c82d1401480d02d170382da9a0b0488201100800710440c0403000301090340c8229200c0201c0350303000e03010918047e400b40d007030030031200d1150124014001c42d401000c031380d42c4128407440c8000c6980d6641c000580056004500a0940c08018821032000b03001c0d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 992236330 1250 992235080 992235103
    0x60504050609090606010c060e0102180a0e010b04210614041515090905070f0303050c190209220212071a070323210415110904020c030c01050414 64
    0x2c0d40036040091081d5210000900b4490501c0314043c101c00402040d0780103000c04401c410002c64a1765018180300c2803014030035034070030b02ca40c864000104140c51401299416101c9901006082900f0612403802c2640c200244040134a0001030000006034580135911610506190040740d0f401c00349014211880c1600400d40800d04121203480d0385580243c0c040101c5403103141c04948080282003081c06c0c446950001000340e451944080f05154110000b0700b08403404400300c8550b51105c0c000200352401e1403070002d50001c3c4420210351014000e4651184200c06c8091001c0f508040354005a8019a0180b82030010303004010b0130031030310312400ca003103282c030f28000341e020b00d00047d0350b070000c2000080d09001040100321956223042c0c2c0c847c0b541078036201e0000c0e484411a0300580c01c0c1507681418200c900315551140c54080300c5440c441400348802008071000c010b0305001058082002039000303601e442141c2d2105002c00400381c442400303803a00035402131750216555a1182e0303541d0305107d03000b8403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 992237580 1250 992236330 992236339
    0x1150b1215130b010302190809060901060501020a0609020105222615180304030303090c061e030b030a0f06092117041505150f0102010603031d0411040303030605040506 74
    0x41c4030302651140c515050741c18a400c6400540b000100300180c0081c002c103609242020300f4035821403059604950b03418010105001182d0741a640c0d03100c500d007603400c140039041c01030708812080130012742250420b20202d84141880f50914040590344100e00031070b0100e0090210054004104d10500c2203080005000c440b11444028002080740f1541c4250440a0f9104800000700090f9203846141100c041c0030741e000203aa58890b981d04005000e80062030040d100000000b0f00050101c0c01060400800200ca42022552507007242d010340c0241800c40c117440c0c160064290540c00502e004100072400c610a400005650b9410700b041c01c100c0345220343c020621900c0718442601150041c64110004c503c101941c010366950745450300715503028120000145040c030b0306211003000f21945c0111f01d1801030714400018000030380120300f0380d01d02e84000b40114076400070684084040040705803804501920100350700c0f00402c0740c2c8115920503802540040e58408050080345094080c00b5080002100c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 992238830 1250 992237580 992237611
    0x50a03020d020d151a1e0705030301270603020d02091b0d0f0f0c090b070c0b121506041a0d110a0504031109010513020a02010f06170f03040303050a05030901150b12 72
    0x101742c6020712030320041e540c0c034001c49600c10094045550031105150b51080940b512960b4039061070f01040d0409121070403003400610002d0b41d2500c0c034841c01040329002405030a2288403034080c0079245501800780d01000200070800c030f00003a00390b4000e00d5040c01d02e660015003850503003411400c40c2c0c0350760307506140d090502001d0041198800b0300d901c01d44412561040c0d80c2c000c6490a43c0d41880d40b9072020860020100c0c548c142411030000d014411180390381e1b10154412031000300185407081d400344140e8031000c00d101d80415500c0c4405010713000c5501d807000032041c83c586455a101d0300110f040c000040e50004007401000b10303040d204c00252209540364840703541003c0002d5a0301c0303882680c42c00403a9010036495880c0340700350000c4030900c3c0240010031109440e95860510001710070410412441914a094800e110002c01c03101200d405540389402c20314051421a0300f503001034549984e030741d00c49400a00c600101d480c40401840c2a2000d159540c540e2401c16601d00c1c00103242a0b030075040507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 992240080 1250 992238830 992238869
    0x4150302010306080726100606030209120c151e0d02071502031b16140105100b072303130810050c070c18020d06080d0305091b01050a03020d020d15 65
    0x40004040c1d1600ba0329203185180c804986c1c091501d00c1410200c142141007100c0016680d426600a00c4086001e4a04002d503400300003241d40e6400c0107070340c00703504250966070000c14601507401900d5084d4410501026040e8004d04100903a0007884e4110340c841c0d4000386030400c01041420320503415540040c1507041d4500b81072486240302c0201080e200c1014000b40d035404500c0d041680c1003640e68044907160300316048238403160003450b08480d00403120701420320202d1b082200509441d42d442d44884160280705c00603030a4091030002e0101e03103005204c14011208016801420302000d008940024400120201418010f480016110f0604400c0c200302c50804030711150781007410781e0b124850950308290142002802446000c68004010b0b1400c000451506e8010603001d00c01000c0d03a40900890b200e0440701c588840300d4842c0c0740c9283d80759a4112140794000d80c080d124200583c100141403e200d10802ca007030b68002c040078101c181c0e48004610461400451080c0580740d50f11562a035030b20310 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 992241330 1250 992240080 992240099
    0x2402070b07080318010504050a030e010203120411010201090213050907060905060304061512030e0312210705070f110111030309070e0603190c17030a09050906030c041503020103060807 81
    0xe0000c041c1c5242c00c000006a000552403503a800b5418044c8000c00145c40c2c10f081050f2950304149003100080c0070b658010026610000c1070342c42d04c090030144400f40352601d507683c9020b80c1584542c24195525072000f0009a40c41015100e00410300ea107000c2240c3c54018a1541051400d0300b04500388030a00005209549a650550740d0103a4400c00c00100c40c0ea1650610700842c603994061403400034502180310806a2103c48200b03540300960455288007503410b050300f211700416090f003000f12a403041079031143c0501c00c1110342007c43da0800502c0d007405611407210707400a030f00050710072052051400416503849190310008401c0031010b1400c60030700880441d101c0c0254400e01c1d9040c001400421116030f0b09104000c03001c560b0140c0400064024174120000320454801c2000358020074010322840c0c0c60110845000c03480c15590811020708040410174202c101510540c0c041c4540300c041c14560311213209890f0701e400c81e0742d0340c9000c40346144001401d65026400542e0590041081008003000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 992242580 1250 992241330 992241337
    0xd0e070e040b070c1205040e0108060903070f06060b2803292e02100e0c060d0b09070201051605070b011215020a2318130608072402070b 60
    0x24072850b4101e0300d80310381804489030810520003038404030b001403400707203240d030000d0081c012507481d0b180c103a81c0c0e80e0340c407000c864440c80e04882008190700104030000c00280c0403203019980c0c6103d034038001601c60721030411070400d4000070b02082015101c2c00c01c0c205030b4010400b000c140480f4521f410703c1480205000c0e0b80c41703025070500c00c03604484240645402d540c2c508030030aa1288003040080f80103450742e9600e03194a402080c24401602550301c40040b52155070007480c4501a41c0380040035164000c1040c8940d60340840401000c069541000021a540b82400c0c0c601490705c0c0c0d4004110790400e00e02e400c8284222004071001c0c0042080003c2c00200c111501604460001640f01514102c46c2440b412950f4150b02d10f000c51342c4001114920a0f0b001401c02c10600004001003001c1044084c00712005d20032414902e2080040ca4a981424a031800b189602d090400d0700c0820941d070f030784d880c2c03034a00915500103881501803001004d601c900100602d184010552008004491500c060040c1070710 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 992243830 1250 992242580 992242583
    0x806070c060b06041809030816022505040207210e21160f181103060405071e020307110306011a09010521070206070201020301060225090c050d0e070e04 67
    0x3502c5410b001c00da940c0714029180140114009120007080f0400d40030001e10b00e01c8003c40105c0d0310600800c0c0000410003c254100c403041d002480001070b00150400729410940c1e80380c40040c1c041034041f0f480e07140c40c00030705a05445035107684d8510b0343c04c051082002c080301349000b0130800c0d4541d103074600c4d564141511141c00c11a02c41011003142d5090001d003401406414181c0c1d001d68030400041407600b409000c0d044480c1781140e18100410828158290741010111550032401400401c015140507400603401038035904050301206040300d0040200e0020440b0240503070004260801880b5060b000c0300c5503a20100d014106540c104024000c0d209032140f8021800c242c003050340245039001d03a04891041c16103400450401c41406240c0c01e8103501107802800502548000c21b40881c014000d0324103aa4082e0058840003020f0060040d50070f042035081c040100c0544000100c0400700e03c035040280b19617507511551080011030a40694083c20b8080e000390748004000c106003d0144240754016 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 992245080 1250 992243830 992243843
    0x1d160e1c06020f04080a050f031204060b01090306051005040b0f09070c083708090c0d03030615030b010f0c120e030a02040f0b0f04060b0304030305041a0109150806070c 74
    0x214490412800034040c4a0f28003241580015000c1100c810005803540034510900c01c9405181c01840d5494490003400480c480c0001d6000100d4001074940d040880045c6040c5000080195a916490300343d50007980c00d0b00ca42c011201040c007450034180030f01c8034014000c1d145124050790110218000440003080e0300108205d40121200b00320a1034111070845124846100c1a2039900340041c0f0b00c4c1c0494004401003030008020802018080d9042520900c42e800140c49a03411070070900840701800ba400303c08250f0340e03a402140e0271140385034020134034440382c5e000a03007211035100250020411014600c01d000c1c84000c104002901802d18200c5c03081c0314075181e60400d4242020030b04c0d268074010025802130400101e910400071651140160480c00c499090081c4c61920611045070114040c00c0104070741000050082406500200d4210340715041071074a011007011140d0300c106003a080350030129112261440152003584418000c1e0003414081c00103400c02d2a0040d0413050100030040c00f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 992246330 1250 992245080 992245129
    0x90509070312020102040f1706073912090305060712060909050a021c030507110f1009240f1211160203060a090503070f020a1d160e 58
    0x640400d0082000441e40150b40c80000403000c40041d003c0e4000c0c0c020b90150310746003100066170f8006100741e0603100c00340f00e02410310b6440d81201103418100c00001d00d580f0541c0d00840c036400100880309410581221000f111422003285025100d0080c40310001007004100701c001d20100e1008251550402c216040c000301e800844103500b8080c0406030320128040d07181c03660b014107111022410308000b62089036503241c102c07903081503100f4a44a280e00600004d030180003000014801c100d01030309205000f480007112000110024101200c420b050400041c000c0b80304019000300b134a100058100004c000050020a0301801450704030a62034200411488901748000703866941e01840c0c0c101c488855803541c400c601c01070018600b0a0b010124002c0c07289500140104111384548840b983e03001028503d84151501c41c04124803c03120240c2c0c1c4003c030103800140750440c1d8084800703540440c1d900c40d0f20750f00e80040b06240f0461800200780c10f22500e01145011541c07480b20790301e201f44201454029 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 992247580 1250 992246330 992246341
    0x212272d0d0c09050a06091803030f06210b150117060a080f030a0e060a0f12110a080f060316060c150e0f07060f0e10020c150301051212040905 63
    0x1851601e40544850400c050204801150340c0106105042e800000d01942e55980c204204131010034200c5501c46001d500c002000901c2900110350300a000440821103d44444490300d968032100310782c0c911001501003660070405100708042d03001c0f05035440c0c82e26881001001900c4540d10014894000c503030314002906c036070341e252000005841c0d2001280c55241c0f05280381a9642e100c01c501902180c40c401340b041c0309180807001c4440343c102c81c0c0c0c0e9507480c84459100664100038080700c1400e8503501c5810300e1220f15001c1003e803081c0c841681d22074001d41001007100d00b0307941c4090101402508014420501003c0081e45e80c4100d0b64079203003e0709103500a0810a100202c003500705d803801170030540c401ea988000042c0d200d404111600540b40b2141c1e0b140800d9038500b52000200000c5001d070343d01c080300c034075281012403500c9055006951904112100140c001c02020240785c048141c0480184103505218a1100c3d103044440d0081100c00e025070042c1c0b00c203001d51b10407011010380343c0c400560f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 992248830 1250 992247580 992247589
    0x6050402010c12020d09050a180c090803070309050a08030a0804020613092f0301140d020a080d0c05010c0c050a14070e09010504150203150f010212272d 67
    0xc01c0c036007043c40684546007000d4020748038204100150006107006002140c103240008000045a4882c1c050350260300b060000c4c08041d00e0401c884000b8045031040008070090241700500350a84241e54180c0703a1410241000b2400c86282c02c45141c1d03900030b0003d407071110740000314150800d80403120340e91030354000d50a00810301c1185e000403902d070341001c5d81e07401030b801c50f1039600d4207000c503498003483c0b0800302640820b40c600091240700801c0442d01302441c0c09003407101c400e40c0c0d800d0000e85108540d507282c440042c070f003076a04038107c4001100908040d080c440203110320306070302005281242c903c41007a124140e403665a4039020b44070014101078031298050800c400001000c4500c10101a4034004207500c0c000c00c01201c05842c0b600c041a0b12814800380d6108403882011200600240300582e6005e1100c0014146001c41c107621036000643d9103510104050480440100031301c040c105604200b0b03400400441002d2030123480032029100c02a41514840704174070f4114030039181001000720006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 992250080 1250 992248830 992248847
    0x609031208150415080105070309020d08030402060d060b0703020d020d0512060402070b0c03091c05070b1906140f0a06050f0703050409020316020f07080706110a060e0a05160803070605040201 84
    0x2681c018a00606422030f88504d0845500f00c07541c5030002c2101d40e6400f1416003d40f400d0140c000e6010510840c8a000244402c020390f030004d0003d0010390412101c640c07440100d6455421050140c44040360000405604104070506d1142a00c0508210540e2440141081c080c203a00c00405280600014680c1d4070303168183e80e1b00e50380110440c40f950a090a1000e07081c0e00c183e9144131070740a414122403a200e441d9a446070181c07910f58580303140c81802d80364450052806060012030711400398000c889250107000e00d0300038060300e0030000200480402002080244054003e000e40500349007041202c3d0400e0a5410003809a00303030540d100301c1c0c0c2c03a0031502441b59403c041140c1d440802440459500341c2034030210014250211612011056600380d52110148102c11003544910420301000d84111100c100f24206801121480c0e00c45540711000d40c0d8603018822400e9103c0d204000900c40100301d4406441980c4044800e0741d420300c11119100e20844002411158481010504591103000003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 992251330 1250 992250080 992250121
    0x409063c0e1f0915200307031803020f010e01110409090f08041e0509360609030c07060903110103050c0d0203041209080c0d1e080a020312010609031208 67
    0x85805240000c4a04002031007000d10a68410144c3c1d91482140386003840f440112940c0e074800c45c02d0780c03a8070100f4914140d0006116100701a00c0700280e84e149030101f4000407020b446074025002c28050b00d03420300d007150204098040c0c00d03030500d0810080c0101200486059545030352010809040608090700e2100e40048002c3c090140028000741881a0b0401023940400805a4569441e03983d8100300c20564103072940112098400356050809070701c490030714110b40080c4a07008800540340501d03810030401320740c0c27441c007038100041400441c141400b00030090012814210021802c6884d03030117408040028541c14503687c4c01c049076090707040d0030a603441002004005d550364942454040411502c01c075660001c61803048003c40d0707046010400c107180601c0505024062407554803004400b000d02004668031582c44503001011401c000c4c0140100b80340d40d00103592b42d108026210001180590001d0300704440380c0d2081c00081c0241d1922501101180f6000700d25454840c400303a02045079004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 992252580 1250 992251330 992251363
    0x2010e0906042c010605091e04110a09051503160b0a030f06031103060108071a070c03050a1a0603060106080406020a030e030c010e0132150409063c0e 66
    0x16480c600301142c0070782c090303603040c60f00038420507503a42d040c00011002540d20f1010541150b02d0400000410301903503038490b0041c0601c014004651000c00c100144d1900300c9103490307803034004000d00c08003032040039071480b5415402440b0515009450410b40391090213618844500000c1e1894458420f400c01c3c2900c00040004000081d940d1408600b003c12400e5a2030103405150000510790101184180490703003239034040c0c8605052001211500e82c84120116604a0603000c0800071480070040c559500e0b1043e04440c1d03180000d8951443d24960042c82c10784250721400061088542c8070001940081c1d200601584841519006034080c0c2028052117505100110300440300500540120041c8150071008102004c8140b00111090303c40d5154001c510100401411041003030f00400380e444820324a07100300b030380c0d03004000a0a0340c210f0078082d208140c5916040e80c05481d0700c0c2d142200c1105642c05454550f082c0444c0d000d074a10f4005401090b40e40d42c40d00402141c03011700103c60b516101c000f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 992253830 1250 992252580 992252621
    0x2105160b030f1803030c1617120a0603030203070204180b161d030a02010516080d0507080105012d140d0e0d0f1403060d020402070510051302010e090604 67
    0x400415a60000c4841044103410781000c28820040400040703e40f2903000c0295282d9510600c0c2c0e50070540c0726050104411100004203004a0407034074a000b8050745540c0400e40d00c2e0340d0800002000e0b90f0281c001c100c102e26151040002030b8000040311441c1c0e80c181d40102d148980c84220108184541d1806000d00c0c80e010100803e82c0d802c0c0c83e603d2600701c031585940580140c2003000c441030b0340e007001c06940c0580c03016204002660050003c0c003515065a0440030290a00c0d5070b0f015030b03541003041c8004d24035480700305124010b0b03003200d801400b610003841c041c028a6007404840040010703043d000f03050451017606550780fa5100344900300e5a10320700c0b03848503550580b101101000b01100c044144060150810841819209101d81c0354080036036035415000b203e1941040c1026440a00401e0b40101c5038801000180c0350b0f40068900d440c00392010300442c104159000003900c000030702e4034469512010920340140e82002e0500e0041906541c40001d907030702d103030200d001040d60202181c81c00341d4a8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 992255080 1250 992253830 992253839
    0x504030809100902210319050903060109050705160c05060a091d040c06080a3e0c030d09051204030c06020c030a1e06090618020108060a210516 63
    0x4a03403405000c104044403001a4184401030403204102c00003980710981400349001c06850040c00c403580440c590540c5d2a100c81d02e55400b264000307880c00d4401181000c21900c030313240380511005005220012081c80145850100100a0300ca2604c00054811004d9a0740d02482040c0382007101800020300002d035680c1207003401a15007521407148040300d03a020041c9002020300d500c48940074981c0110404040760602c0802d41c1d8101005142d000358036a40c201d060a1401c10101801c50403400000c207071a0b0030000303074440501540d0f800304150101c104020252545030000202d42849088007000a1340703a10618100d401c1100c00d024121180d4000708011062026200180742106c0994080301c1d0004461022b06032640d0101901624149003c40c000c2480c1c00940d0b070002206228a90005980640359190b9007214a848203402208201545000c219608210740d0780d04001c0840300d915640e4a014169400119844054480c0069144580080280c10404000390b4100034125508880c1c54 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 992256330 1250 992255080 992255087
    0xa02060d021c0911010c06110406051c060503250b0304062a0f0c05030d1d12090303031605130909120509031b2101020d0b12031e040504050403 63
    0xd62440798220414070041e0010a94512481c140158085800884113038010010350f01c1c81e0380341506a4107a80c4031202d0b10710340e8440310014000341440303032241c58541000c00d10400a038802c4c45052740c441441c1a4092085640000d004080c80000381690902c1104500b40c140b885001030703000904126010007401b003004581d8000710704842e442101244410b0b40501c51003030041d04542003502145407018031540e1a4880c9001212841c01241103928101041249400711a02c144000b01d524a0300303000c111884e1804d1200803804c0031510320150038041d680000030345921000d4100104141d4a1812800342d50280090302e50b0390641c21240ca11003075440102001a29280700200e032204144011642000e025000b40c07030210001500070405218001100703550004024441d65009401111400722580d40c40c541c0d0f40d02c52034a400158645082080b1103040d50006d00300d02e4400d034007500d0308640180c400026101c40400c81c80f1001803085550144105902c1113802c8070382c220f41860100405c1c146c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 992257580 1250 992256330 992256337
    0x90d081b09060319241e050315060111030408060c091f1d09010b030a1e09140f0715052a010504150e070303030f0e06010e0901150f12050a02060d02 65
    0x804c00c001c0c082507200c010000300c101c11510311016601e00b46001401000800da1060240300014080345008503168400245407040c1d44d5404c50072480c0c40c4080041950703014201031180310700e0714000c508080c00c003510b558607808020544003121034081101070081da50105600070120402c024000ca580c8a40310060404188942c10b410b141e181103804480c070304003039000c1c034101c5801240250542d02c5d5000c401d000340c40c81c030700512800140388020060380b007114481c00420902c110000d244030a2440d0500d0309222000700e61035074580010f481041104042003401d95006070a15003165100181c1101c01d055106d060740c3d0624004800214002008055010364003903400f803221015241c0740308184100f5034100800050f01d54015a80802c0040d0180e002419290000e180c04a00105000700303103454000241e001a01040c0c40c1428026082c40030700c2078030380c140800200b001070142042c000172843c0c0e030541f24000b10601d5540c170100603c6428845007075810780c000c2c0700079521040710404401a41 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 992258830 1250 992257580 992257621
    0x6170d1107050105091207090e0f0f010504020603010e090a050a0804180b0a061209050a0302010c081807030b0901140705030108010c09031e1502030705030708090d081b090603 77
    0x1100c58140380c40500d0000340200488905958041ca003101450a100300d508185c00e900307003203103c0d014000c00e082c42c0c5801000c0045007001c0040011620001d040342c505041a1003c68080c0d14007421302000da22501c04480c1510030220488030b603038031580349643c81c207100300d040030b01503001704035049081000420007881110700d00391400c04005483c0b0303942c200303d65001c106181e020f001c80004002550007150f541001b4040c40380006590005501c40c40d00380180034104400517551101c402641c10307080070b0b040d6006440120648031a0b000503a0260355020b460001078401000c440004000c01801d4006c030f0162900c8118210b094203141e003010300243c100380102a440e50030704080c220020300c01c29482d401c69400c115191035a14100f00c1001d041c0d080b800701501c60803c41400d08090b0802400194000c180c02d65030a640ca1a000000802c00381000e0301c801c40982003404845280c80d4490ba0586d0005a0703a104111943d900c0c960700c182e00e1140a006541188010040285c100d02c514407610210 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 992260080 1250 992258830 992258837
    0x1b1603080f0601080601200a0203011a0414040f0f110d0f110d03050913020403050a0c051507150e070f12020909010605030d030b0102071206090c091803050c0106170d 73
    0x1d03110030b4015600440112032131400601c2c1c90410384c517689034042c0603088404940013928411111a008282500c2c900928007c00c141089004840b504052282d0802102180d1510030682450b94842d0280031103c24082c103480d9841266000340b02e00d11150203042800140644040c07031151030440440340601e00162070f428810a41c64a840c2441e455141c0740030f500d87c2d2820720b4110b0703a00c100106804e42180900190b6828032011002402c00c100d404000c600507099441807a03d0441084140e204198844510350000e0208200068007110441c9201c0300c0c869011961803403904007589031400c0c0b41e00040c00007200c8100010302a10040302c54038080e00030344007082c0a80d98807a00500b80c5409204154041d400401b8800c580d40c420342c0118070a490500c1a43c046682c0c807983c03c0c00300c00e600f504c140e943c560380b17103c05800c0200340d1024600500c0c0005c420b0140c0c48903c54842101c25803c1400b500b4817070005440d545408081d400ba0700540003e12080703440d41a03484500d80d58500c4000f116021 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 992261330 1250 992260080 992260111
    0x1090b060907020a2909060a0b10090308090114040b07020117090c0607032c1c02060a03090c0f0b03040b0108010b0303041a190201321b160308 63
    0x80c1d040000c10144945070300d4004200086036607440e940300e00310400c0104215040b90400c2202d808060f2240742c01881068000c1c4000e00704103520404807401c0c0d4003940e02c40c00e07454201020381d1382c00c1014601201d0304103504546a03000d4000580b4000040d4801904230380c000680803810001c46406880001d0007030340c07000201c820a0802841d025425100e0b07422541c080c1882d810607160070001000340c10300c01d25003c401d6500007090550303005100c450400c0301d091000c000d6031150908001840343c4100c0040008004041e94011540d03e12941070210308060f00c4105560501c00d541440b08024080828141c000c07a2351802202c0e00b44c1c00664046814410407000080d0000301400740e240c09500080145140c40c1c80c21020b0010030307090301d0010010000030300464040340c505140342c00c000c00707082d0000b20b40c9612000d0315420441c0640d60020308000708012491049484804440d0701250891000184040901c9000f8403405003100728502245100c0c4084201035000310440e000701c8030041c44d4242c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 992262580 1250 992261330 992261341
    0x301051c020d1416150f2c01021c1e170601080702031e030a140c030a020702041b0c0b010611120a0c020616021525020f1305041403072a090501030501090b 68
    0x201c0c01d1030101820a91103003080701c030320144100d42020404800500480f9940c580d5810300ac00c58030415980917000c201b6410a524042d001d4001c10305407408d040c03801e201c0a14070103180101804001d4096410401c00d00d0008113154001c03c1251440080e03481520300c0181c0c1c4440c000c6040c0e0086808c0c0d02032504145655900c0091005004d000c0c40c0f18900040c11039880c0c4565000035044940c3c1070740d00940303449607250186610680391044a51554032051031a9003410704075180141070b030003141048500c00808088400104400b021a0208440c01d503580102c401e04451f49005c024000e580044000b03030b460324103083c411042812074400e03604002c0e590040a43c68410b1300a05e030640e03809007280c8659913980131080d820500c501c2d10040280f5041c08140000c601408441c048201059542c2d10a0100380401984a80301c43c9503504002e628003540c0343d0b6580b00200d0102e00441154a40702c80a81204502201c18000382090b003004003c02e60792404d2181c0a00340e04442511a184010013040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 992263830 1250 992262580 992262587
    0x50c420f25030b131a2403040609081e0c01051501140d06150f0201060b480c0109083016060f0b010c0b1602031e0301051c020d1416150f 60
    0x520300c561b100e5860440d034460300c411002c0c1003841012100c009003000a003040744034013480c0c07180102040c950240c40e540c95a050740d0848d44050700d524006068801240340070380e400034018641d180d640c40c0717554a448a161601d0058005a00700e500305900b19600030a8150f8044198030010996500038001e15030381d42c0e02d011061040950140c04116800c041c032003e0407000c1042c1c001c884c1d684100c0c220501000c00c120101001400e014152908a1604902c1c15a48040600041c010002c003074265225003540304e0b20050b80000103444100034001508a444004500b82c81d0070f9240d400e6420721820311031812500a0401c5d130400d0446c030b0b2815021001a521038500500040d42c400d140c2000c0b03460300c0a0240c0555240350844045200c00c00c60b000c00c2c24500300c410061440d91440503602c9504101c10042c9078005259124a088100080e00c1d0140c3d544900b0f018096400080040d4081070380e103103ca08204449692401408807a81c001800c4101100c200c19190364545d100a4860100b41046 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 992265080 1250 992263830 992263879
    0x1090c27050907020c040501140a170c0d03170403050706060902090d080903030c0a0f050c03030a1d0d02030d090e07050c420f25030b131a 61
    0x45081260500c0e040c0100d04000c00d11580285150048903100400b2400150503544260481c640c4001c0c204002c0c0445e09250808001a02ca200c00c00c414142c0c1c0601413139500c00c04402114803c4400000c0402498002c0f24484642e0004c030416001515050401520b10792000c2012034209241c0710000a03503500d0740c420790305001401042d9140d03500c12038503070096980200d4400b85c1c1c1400100300b80d01c50440200003e0703519038401d5400c00e150344800d060850422480190786d500907003040010012543c0e2206400395042c8001140e440544000800700341407200340300c0000c3d0180303e500b00f00c0005581054115040b038061044101059a40b204108c03814040c0c03040d43c81896001c0070142c1540b8042c0791400c00c10f01c240c24007811417980c1c04c1d0501005950000c0d81008030803d1130f014401c00e80b00040941c0d03880440c545040710328000c01002030308110700c03080c034a00c100f5550b81103820a03a5190000440003815204060101441e0000b0001c0c421101c07000c41481814155070205000c058881d01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 992266187 1107 992265080 992265137
    0x13150e10150602030301080a0303020c0304050406120501360510050408130801110909090a050105091b15120903040506041203020114061f030f0501090c 67
    0x408906859034001070b00b190001c00046c4090000090740c2c0c000203601d4600140c0d12007800d0f1441c0c0c21405103030000d641c460f04001c80001c03080e1140c81c1e11003420380508001c11864134941501160a03540a400b2903042d1a00b62a0a1640c2001c00d2034141031805a4165680c600b507080c450811103104072022a007600300440d40fa175a0340f4000f10903001030300c07100c4000c010016030340118040a00481002d64400c0d51400d0020707a072003c0a004200406038450300a21541c200100b141d0344516a102c0028015031605008107007510344a60405070b503413500c00c00a880c0109100003400507440c0180300391041c1c40708101c002840e032903010041000b084544080d0545a0980c50002c5c251004d245007404840508070620ac096500d2600b4004150070440700174400c0303001d064058010f4442d010700c940c0380358602000041c41107219003240100d082d0541d9032031585e0158802044030303c4180c059 = true := by decide +kernel

theorem cover : BRFrame.Cov 992086330 992266187 := by
  have h0 := BRFrame.cov_init 992086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 992086330 ≤ n) (h2 : n < 992266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
