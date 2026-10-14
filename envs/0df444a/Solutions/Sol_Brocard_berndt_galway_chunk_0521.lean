-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0521
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:14:19.875518+00:00
-- url     : https://prove2.me/submissions/7fd2bc46-422a-459c-8b4a-16e0db868117

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 93525180 ≤ n < 93705036 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 93526430 1250 93525180 93525209
    0x60c1e060603022d0d0f060203060103021e030103050d11030a080403050d020f0d060902071505190f09030e06030106020d05070204060314030d0c020a0803040f0204200703023c0c1009 80
    0xd041c0000d0b0b2805d803102030b151030f0350144441c0104d2916001507504c5001450b005140c01941c415000c220607134042813004008d404401401085420025110300e0743d614100508c098003902c440b103a0b203101d030b80f074020100088200450105030188003510b030221071048065417508200e09000790b442e0462106201c026007089400590503a0b2807003220382e0340f038200e05010703034140c0240038240182c607000e80078000d511a00c0c3c1e104401581944581312080030001d0002c11400e4140c14000d00035040714101e02d210301010001004000e8001880a04002c05410100c0c0ca450040c00010f00500c0d01e1b80c07020b03001e0b128408200e032420802200400301400c03069010044070b80c152404a90328440031800034410401000400c01151801c000021054402400800e0481d60034255080c200b00000000241ca14040341c10010142c051150b0480d42c0745407020f060201c1c40368070b10340952442c0d0908458421a00031000c0083d60014010100d005401510240031f803180004020b04581d40c2c0d11a4520050661 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 93527680 1250 93526430 93526519
    0x11a060a0203030c0a2109050c0118050103090516080f0d021b120f010e1e01050c03061512010305030d14060102120c010e070306050a06060c1e06060302 67
    0x2402a5400d5a449030700a508542d6000304902c05988010241401e210183e1584810484e10711440f14891030a00c01c040340904e00d501d8040e262034001c0000f207050200e1400c00c10b10844a1910070400c44400b4680070900c1c4050341080d6003000380c00e042c100300f1342103031500118803620005440740f40f110107a0202d5060034040030f0201d031184083c1c44500c00e0310030500c2c1c03c4c01c000d10701995040020b008110a481d44442101c081a007101c200456405490f0091100040c2c2101540e08056989001c8802401766190080c078010306840010800b511a51140f4088220312080f081624040040c0040e4816507503101d0400e40c0d81c81d005540300051950410f130b0a407078400d0840030b0090003004107800400c0707600c084128492040d0415450481e9940d80e82c040700c034080d401005140000c2d4011400000c071410401c10000c1501d0b0607801c69414004c1c8400d446000501d03181c41d8240d20b0481c20b034002900c0c00780c0e150480141446a10180d4007541e10405441d0014050308005241a800c42e09040ba540c8074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 93528930 1250 93527680 93527689
    0x6061e230c060601090b0319050c0d09051506010207050102060a0c0e0a14100e011d0622050a050f03070b07170705060702011407090509150301021306090801020702150d0e030c011a 79
    0x232a602d20b40188007160000d00400e940c0c1180350031011a0a000b07007010810705100c02101c66a2030103032241d07800481c4009000291a420313603000b400a102620301c090400001130743c0e0700e8000d04015559030f0340f4000b22003080d01c01c140b80d401c0e240e00140700300c140c2036440c2d15074504040320140300b91042e00d4000c245603155024529207503003004183c64030400b00c1d10080b20036410450b00b20300ca44d0002c0d002c00001c079140c030f800c611482d20410ba00748064a458104001c0c09408012604082d004400613062140345030790004200d02159007490100c0e66412107131514a0003c440c0c448030b0030800c2004217404040080100d9070a10440c0d01d42d008100d0030a60a207144180c040a540071008603074280d4051120341420800b07941e200b1901180300c81c442402d0b41c0400d00320303401b00244101369003140c2000e109496005c10304c1e00050210500075800e113541a0002480300e0055903901410351000141802c90a00f40e801c01010810303001c050f282c4405003150854042c1010a032002e5450a8600004003113141c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 93530180 1250 93528930 93528937
    0xa0801120c0311030114090f1507021518150402011e0e1207120f0308100501211e051503030415030905150901060906061e230c060601090b 61
    0x200700003140c06061071510b405240e61881d00d00e65825548072856070304211410050300e400b0328260340080c48188262a0315500300004059030721000da90360b4003404515980024900900300d01594610000d4940700e801c251000a8100f100c2c07054029000840038111041600c5480fa90013a221410243e28440d0501d104010059840d00420164051411507003800106103881c00003003001c40340d4160b01c03a40d040811400304401181c10091002e24101055404515660001009a03080f00340c2c606240c0060500324040029641451712801800c41903280c5800005109490320804c41c1030b01e0508051202414044460400110307030004031812905001080307030f0442d03041411000d603e0034000c1040300944050715040e5214802d075802c2441240a01064030700498a1800009000d4900600315054584680c411824415a0300c0340c95001f003c070440f40f81c07400d582450b21089005400200032000c603800180000300d180042030300c50040700700140c514080c5101341c03903901c2500e68801c01d4125511 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 93531430 1250 93530180 93530183
    0x70b0109110c07062a0309030b0c2206110f0a02010e18090703060b0f0303071104090b010617071d0108250504080601090612080315090903120601080702030703110a02060f0a080112 79
    0x244054020808101019070349c941000001d83c030f241c640004d08001c00412005c0c4201c2c41544401c0d11002c00c60103800040480d00300000030043c0c6806040c621000f9107480b051030021341482907003000c4580d40c0c0c3d0351000f40c256004080c203080c0400c0c2070002d00d5a40c3c8052a00013100c545240201c040d809140c40c1000c5c050b07001009008514002c0c0719076030030400440700388015412a0b101c060b03030000a400c0040d50350180007a5a1000141081001900030742103000e0415014042090b02d103051000c20344032900131400307003800c1c807070070b917440301c0c00c82c0d1010400c1501d10388190380790620090a0650b01030010800c0303070304580889104d41d807110101400c540344e520903482c10551b040365071000103c01d071001e903601144209019010303841800c003207414214100c0e90041d8542000905500404100f0691a00400c0a04e00200145402007005c1d5480c41604409401c2c400410000d0f111113030104845003406d58003804080d1a401aa280003299030044440715010070940000482d03100a070448111449 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 93532680 1250 93531430 93531437
    0x21b0607030e19020a030204020304080a14030408030403050304050709061d011e030f05030c0d03050415110f071410020a110303041505270c010e0303070b0109110c07062a03 76
    0xe50711103507241803c0c001c040c1203802c400305020020150313a03684055132289000c0c407910b40e41d9501124004040c031003444600f03400c411051060201290f004015241e010754107052950356900c460070709514140480d0300048040341810404501603003400c07001c40701c40203140d1144230b03580d0700d6200b039402c980c0844400a0140354454401c10103e000041103480250140c02603d280c100c5141c00607040034108000000800c1e221000d00041251a0031550350201c03101900b00200c0b040241c0f0300186200c0c03034000d801d200710041900d9080c4040b819040403546a40d0089599003600d02e07803004041c0d0010000381010031105100d92040b0070012045030b01c00c0c0d43c0b00582d49030b02840c90034050000c101c080c0024124603048111070303c0340344462915503010700049004110419094000501d80403814001c00d0107074005011100025043c411224190352840c03d01044021945103950640d02030307803442030a0b41c441c9050001e81c0e02e0b00300c8400c800c7c20800c014100900c840d6114102001e120006004001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 93533930 1250 93532680 93532693
    0x20040203041106030c040b0d0624080402010806030f06090609010506030a03021515030f0106050a05060a09180e12040503070605030609040605180f060121020303071410021b0607030e 80
    0x441c5040f40055520400101801e402c090b10343c0680c015039000815440c08290740d4040502410480c0351404007264803640d12407054800710980200f020201a000130305202800010601641d0284002604540090123303001071800461480d0f0752407054600e000d1035441e00c4e0100e6983d003001b0510310750194040c1c00800c4a400740051103001c480000340a4a143c0e640098200181d69003801460f0796aa501400890410700340400c01c81c3c110b40d5580070501c03c0d130082101001e595000346000302207400317684034001540b5095042c040613121140c0052aa40507065000001c1c00c0e040c4040e1003510415801c480301140c680000303881911003620302c81d40c04441480050001070f90790300490313400710030103103582ca0400c2020b4840d0300e000040da4215015811000040c8610f012120440100704502c2401305062005500820b45034440e0b0000501403080c0d101c40d804105504204041b04403091140440d9111610750044124681c100740c0c100751401100d002c150018464051440c001e1a480b024150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 93535180 1250 93533930 93533963
    0x60a0e0408030408130b0d0e0d0e0d11041e0b09150607030c0209010603020409180c1703041a09011e0206151f0f0909150302010807030f0501032004020304 68
    0x205a04010411504c0600400c4028004041140e0f41001010307043c0320540c682034443c1508055a80861401c50168001440305c4441d6901a8031403022800a80e90402c01605d6420150010080b4048041d0000e060401c00d26401c000c01c01c3e540b000c0c4103c000c0401c12500d2120801150f404140d6071010740a0001032200c50342e107071400c000d00c0304500c00d041091074461a0f45c0400c151032026408940404d0b40860304011907a1035014504d465114440d000441d0fa100707994502141c03415010300001c1c08034203912119424410000c17200a4051000c0d40ca008074103254150b003007503105901c42400903030010003000c000c00140351407007d05816500606141c0d6030b07114141c28074405565038554804001c40d0281e0481e042c1e40c070319044010180e5612100020a400c0c041c0c10006240c0c046680c20749003c40300091a52002c0105061300e509191074291038a61120450103000c00c41c02040c0c2091030800000700f00022400c41c000b120315411085038a48601c40100000c9010455014180c400843ca00301d2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 93536430 1250 93535180 93535193
    0x306010620070602030a03183206040f03140306090606030c070602030408090103050c03010f0b37090b0c0c0402070203010207050a0b04022e080c0c0a05060f060a0e04 73
    0x451801d80c4100503458081c2011a900d0424650300460158100040f6841c8096040c0102c011078260b0407580644040c00da511400b00398540d2818420008903001680c1000e003250115010b0030010600311041801d240c2081e001001c1c0310359003200803405040a200000d002641070324400c0320b00801c14891540c489080c4a07003a40014092000300030304209820010f543d600c0903500a6024051990300c0d404040d00240854001601000b2402020b000400c514240003205009583c540c1d0030360340c3c5600ca040000070382050720240c90003945800b1440404100c140703929222110502d5582c03550f01940e118940403540c468051042802e0304145c940e8040d605050700100296031018000600d08001c0da214203007000459003048540d4514001031200354540f003621000122440280100180061261014003010f203803490400e1280762000101c1d016900f40542d10140600d109540e20038015180c4540c84510440715500100e400c0070204629003003100e1030a064840c01d401d170a04cd03807a60303251407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 93537680 1250 93536430 93536447
    0x30307210603081809010e04031d0a06120c0503061c110d0503030709050f0a05040902010c060528021e070c090204031401050609090c060708040305010203101d0603060106 75
    0x40386914442894098403100d5032007408011070180b210a0389412511040c4082210b410001521450540c00140035141050f0340040d007003941420415484112110600000140111001d61050207000c00250141e049860810102d00d81c85003005451052001036031240419102e15402104001305da003e640150780c40c11003014018000c0880044507031380040c001440501c0100c0e07030742d0004400d000840d9080040c3d80c0140008076500c00040041e900403421403551840703405d01c81d5440e54441010f59010740e21920b96560400703c240601d207081c5e00320518520404621884181c83c13590008403c0f1514429222904c161000c1c058040c00c0001084405810001003500c50044d920f60001d4452068030090008510501c440440514829043d60844a00800c1140074030114010009142008520b101580004648998680d50103051280081c0555080144207600c00020300c40110b400000d42c008a42e221030303030342e0a5810400c5185c00050303015100c04e60103500043c01400581c0c000d0810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 93538930 1250 93537680 93537707
    0x70b0901030e120f120108030a0c06050a1803020102090a080a0209070e0102160603090c0501110606150d06171c020d05070206121e01090903140f13080f1608030307 72
    0x11500f9001c1d0040022005a010030502e2403941d40024082d000f0640800c6050700400d591400341d41044004440036083c0140201c000304025aa030340028015001548041619480300b00403d410760010701d40603000b58840241588254410b0f00005000040091030138681a4040c007143c2080d240d42d0b07401da800181c4945094150300a600f075402c400d040c452584001000659030100e008007050404080e0800c060f0415410030011f5500c1c08202d410020350b480e04110143d480c003030151b20b2070310611400d0185c0448054850b00301040003c4241d16a4000d0240f0b10100c819241c4030124001359448481d1a920f6160140c0c024201904802d409000500281d0707002070b10442c0f07401808032540896000444440c1d140c4000301038801405200200c000f030151048080c1040000c0c83c03034401911144117904112200e110000d0724120081c1024240c0e40f040d224642d040da082601c0320721031911243c003034081c014280700c0c14014202400c01070030b0f56811a03003144051441c64540303100440c3c034140c06042 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 93540180 1250 93538930 93538933
    0x90607080a170405100c080601050910030f180605010602010207050a0f03260702060a0b130b060d050c0a0216120f02040603050610050315040b010501050c070b16030809070b0901030e 80
    0x1800b07004080c9591014407032880707080a0001c04241c110424202c46528441004009000d001c011441e6000b038112441080c00725a4124503008a8408a01425940810801d41410140000d20001440e4145800305114040a0185070780703aa104030700703e0103440f50243c51580034015120106049a03100d280160103403a01c41644443d041e00c0c16103550041805d5088084038a080082e115810300000b6040704410f0b00c2400f1510303d540028600144030001654003903170b201850304265072001c0459004010500f018001d900e0200700a200580107404c200001d4081c46084511040c1c4840030354095401d407403940c034410542a2500d2504d5213000070101e0308a0b56910000c00800c2080007441d100e00e02c40120781220505010034076003040301c3c0801001c0d1040b003a50500000130750102d1500e05440087c41d1203901c035444540340e00d2402e52144d00ca15480913001910454031502102c1c00c06502c0d020303498400c0d50340c41b509d400503500c82062094603e020401d0002600a600c65000812900088030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 93541430 1250 93540180 93540197
    0x91014030c0406170601140d180302030301150c050a080309010f052e0e0f0709150f090b09030709020f0919030201140408060a021b0316020f0402090607080a 69
    0x220505440e8001d03501d89503040320102d41003080c954441c5041c003c108440311518418240f400001c1d00e800303241c00084000100c041401d5054202540c42040c8c28044c90b12220114851030070060740b654428014288a54100b0700300e51903e9005211103884a54040010888004203490f2200d8a81015020340b410303540341c0b1840850240d6500480f4022480ea80c5020071022051040351203081011a60001042000c0400c01000c4081c01e0f140780e100c44189022812030b560140100c4031f100c00f0b40c000940c0c0101c04146450b0f143c0e4441c06409002c403064994042160711218042c02c0c44c007401025a42c185d001d11001d1060240c582c01400680c5d09810074541031452110005050b1900302c0e22145000841030020030940d82d20a00b0062480300e14a4514641424003501c076403030b150020821024a500001c41c0001180a498006082c019620649882e04414400801200b17407101091307204110580700001140380c01e108590005600501043c64000c80344d84208868125056400070300424a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 93542680 1250 93541430 93541457
    0x50c0103090c031506140d051908040b03071d0a05130b21031c0212010317070c090203090c01090f0515040906060c05010f1104121110020f19080910 65
    0x824682130764a014150208544e82042407040041c01c04801103480380c0c0807005040d020410206030408034808000c00781c0074030a040e0400c0c044500c071707a50181111031000800c100311198403500c2141001a0100900307400385a12082009070201401220303407020030b2030039580402d003455011002c01d00000e81019100c040c2d0a03074900041410b010701e001c1640000482c216408040711212500340d409890031810030b1900004a986010140002000d443c0112a6a100310740d03103900b610741941e44145052513142d25250500043c3d0025160100305200b110384a010320340c0150f030321000781d402048921078000e2a16042241d02ca0601c2e15440190808100104840e0418001d0002910320b580f561100c000007407500310b0071034030401400c0c0b0941d450300300d414040e015490103e80484201c2201b40f520300307110b42450b04d03802030301003d20350748003560b50344000121b50045160301c0d003103c5c1da505031030406400b0b81c0d0032040001c04880c0100301602c01c1204412902d003a8803034000f0040310b442c4c0f41c2d2494528 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 93543930 1250 93542680 93542693
    0x190c020a14180906061003020f0301090614040920012102031f0b030103030c050118030e150c0c0103021309020706060f090b18090c130507080601020a050c0103090c03 73
    0x80e0003034558140000885400d504210320310103101442010600038500d00b005a251303c8103405050103104225004214540a100350191f51100700c1c051b0708103a40c3d5075504200401070140c0d2141f51100140f10036144560710340361064524080e0000f10105a0481140040c1401800f20844034103201d038142409440480074040b01c881981420f800680e6403c112544d000d1a0450760b218041d06152000207021800380d8409490440b545030030060347c11011450081d000d40903090f4290324403030760110034a0515510010204110400b500c2a10b204034800102e00d11612500008000ba50b11038082c3c4000b03944641e000b4181c4840807200c03c998551210040401d0307074032540c4150356885d12410300784030703101c80446a50020080380e1401c0021104260104c0d005c00c0018500d4154101c2280c0020007030803040c0100709842600400d140c00c42000c2c0600300c0002c0c101918031000148400000a58035400010f03480340650b0040c4c000d02200400c04011409030541c0e9004503000c0c150b441000000a80c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 93545180 1250 93543930 93543949
    0x2060a0506220e0613050c01030c05160327060804020907030905150603010b0906011b05070503010207060509010c0801060c120e060c010902040b0a050a030f020f031204060e010e06190c02 82
    0x64401c0118400302003060b003c1c44d1a80140c00d041103800c4d11010440000c1c000255191034420a007008a950082600207481500807900d044003a0b03017008241c1008c155101e1001e000700c0f00d240f540c5007074400d00a04140d04514440c0a94400b10760710b540424090714250344066480450740c40d010131b010728141d540344e00740b6a44039401e0f03920301854402d000480c0f50a01910340140801d03140d08540e8030384600003d082d50011001c841c58020b83d111b041080c4030f001d10044014040c0500295510545460140d00a203000c07907a010b029482c1950a40308940b041c02554120b4030650340b281480c03101a01d4081e5203500016401092021081c1c01c8455500e460340031702904c1e00b0400c00016403c180307005101c1a52008060f007442801c100c0c000744441e030340e000e000070140c9820680c103141c1c0d5070907031000c02c500c02d002d9140680d261080600d06001c400c15080200196410780d0f072980c8580c140c400065500d00210103030164800014007454008145c00e03d40c444000d0303c149070145000b680f64010607444e04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 93546430 1250 93545180 93545239
    0x180a02091801030c06140a03090c0b0301150801080703170a050c0703030c060507210c0c050105010905042009240a0306020a091e031103030423010f0e0102060a0506 72
    0x944000c0100f0a02c4034007107161000380b4050400761031125a0f4080300c0254456001ca44040c140d0b640d8807074052185101c06640604006403410780d07203507120a0098010310260b03000c580001c801c0c1d0000b281d00a4085007000c1101d512281c46c191a03641e58016260741e8208035a000204101400f4000360a1000c1010b24001c5009803114060f0014504000c0c0550f00b00510510034440200e0310405c5410b41c0e1090301107541c001030390000d5500001c2004030384002045074080c1c92982084000b0449000f282e000714012403180900c104030309a1040c0e404030f50120081d0303061b0300800728400503800022407081000c001101010030b2140c40032243c00185a280d807500165455540414020704aa81100c00314002c1e220450440c40388030191240c0011114033380c00020071040410300c001c0010745080056901508410240004148400100c4690f0000015010780002e00701215020120b0080402d10320061041c0e02801d10b60707844c02c030444040c0001520080e04010071071418021500c91a040d1920740c3c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 93547680 1250 93546430 93546469
    0x902070326071e020c01050a0203072001030e060c0d020f040e0f0411010212090d050f030417060105040504021804050f0102070303090b0705030c0d11090a0603020a09060509180a0209 80
    0x281030682e80180501c02c1c90941c0c5000041160780601d0880e0001000c6103d44024684981e5491415070101d0650040a000074a0800e80d004141c802c4c680b10241150019001e0368100854611070a02503958802660000340101c01003046516039103058000381000080c00102a01e000e0b0740e143c481d83c4549045610052500c910b00500003000001508143d400c04240300818810118100c442c82d50310450b03002c1d81c81414120762940800034240281d01b10860303148c0540703448a60f5000381980402c0c0021100880e8002d620011030b40785010b10030075009940280c0004e030b107020070340c401010344030016200752918455010581e1044401b40000e2102d1403090780c0100b0507080c1407600c05a210b001900b40c0c070034040144100b0440031461000d440c0c040c501c80e0404151805403085800441c49900b40d51a00105180c90100d00329030903800905408105980b1a20341d1039662800704da40340150040250710040e40302d451204c6030100c4c540640c110228010051a00040c04002000c005803d032803288039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 93548930 1250 93547680 93547757
    0xf03020a140609030d02070f171c1803120920030606100507030810030506280603020105040603150506030411030601060503040507031e0605040501020c010e03040f09020703 76
    0x1001000030416081d012030500420703480c2065200340d6101e00411545c100119030100b04e00f810321062005450300c81d6081505070344003150300c05000c5050f034000010300a8605901d864002100142d12460502d40c0382c01c00d0602c506001039900301e45040c094140220380325240e8100602203243c1c0c609461041d030641152200382d82c070003810306040107002045640708194bc0010f030004560050215000f165252a00c00c02070780d501d41c0284404150b54001030528481d10b001c000040a50303a038106108450882c9569200701c0440c0200c0913a01c043c000240001d206020400540f4042d4200300c400e5081c42600d0403500380c440c03010501c150421a000c0e2035000401440c04100d05090044134090142450242c2c0f45161503191940c3d00c0b6191f10006000368840c078400b200e0080d080c9541c0d084d8640c0200140098102420074034040c3d0000c01d1a02c0e03040d40390501e504c00c06140081202e04030303148082400003062400d064034009400007002541030141d042404034140c0c441503c40c1c03e2080d0700c0d035003c01c407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 93550180 1250 93548930 93548933
    0x70c06030e01060b0c030412080403120806120105070215150d060c03140408041a040e1006030507020c010903060506011e0203031905010b0d050a0b040e0705090705030709060c03020304030f03020a 86
    0x395440c40d0320204c10800300300700300c0c505d85d40c000c002c94040c3d6130043e00400301c9400301c1c40e00381020320a592015002c7c0c0558211004001e0380070080e5402900b080b500c0c04801813001c6080d508072038080e1910405603000e5801d00451b0306c0300b03450980d804002c00c161034490011010219034980106030080f21f80940d0786100c521f581d42c040c414404040c100944080c1c0c9441d06130303520105071255006604a00d00d80d1031890440856890880700034204441e81100d8608004100d603140d0740b01801000c003c0381c1000c0018060910024444c228028142e562041c81882c503240c0780010030300a040b0504100c641c03a0301e03440d0038102c210025910181540210350364600718445016440c0c1130040405401c0c1400c00400440c501da4050b02e100d014403003030015054a45a4036800201400013009800c41c0c1442d0301c243d12203601003000b900715981500c48140035a600076003228584002c89414012403001501480081e120f820780941e8144640101ca281680769111643d106400b80702c1240142d2082d58041d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 93551430 1250 93550180 93550183
    0x30515070509060f09060f04060309140d020d030207060905030f041a07020d0b0601020c04180212062208040e01090204090e01110a03150e0c030103120e0f0609010203070c06030e 78
    0x951100c10391901c1400d14100300700040091041d804c9100700000040b80c50304959031140100c4031030035215000c20355a55501c4002a010380203049058a50700700e0148050b182c190085a059003800043e40640f14840d03a040094001b03402040e020784910b81c0d103a0201d00010010030007008101820b201498171149800c415560300c001d41030560b908801c06000b140010b0300d40c5030290f03a00940c0304402d445603a86000040f864165030103441755005041280401c0c031038141d050040082030003641d041d881603040d0701c405640c8403400d0b00c1030302a01405070b0081e03e41d003407034512820407140f1030b0450510301507854901c60355201d801c0c0c1000c000c050740000e040001400610414400e403a0110091090460400b400c00007070003001c03000c0043c1a100c021181484581d01400c5014006548141113281004446130050340c10902044800e1004c00c00682d0995002d94a03100e0b00b858001d000d0f00040034100c0520582d60080c000b954103501c0140203500005514240b590081d00c120741d800076186c1140380040703 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 93552680 1250 93551430 93551473
    0xc060403061b0906020a0209040816080901030f06030822171005060d1203020c0102041d07022a010e0d02030303040b0603070f0311040b0a05030a060c260609041b0305 73
    0xb0418801428010030516030041140711a43e03804403110342c0c01e80d4480c10104d21a1107280c495003503a0141c41b03000c0003000840400341c0842030003a038040142c0c001450440c0c0c03c48940340009003038008180b103500a00340b0001c00c4000c0340d102001c2030350a0075940d51502102040d00c1c4281050503084141c40c402030181d1845282d074004000c4499200c4114503441d0400020707c0c2d651201d08260700018000c0c5a0b090940403140281003c0a50403c40c26502ea805003001a05803082c2e00140190f0604503468105894550042c1c1c0d00403030040810549800155690910305030403a82006012031100007503501803000d544194015000d0003041c0c50b141c81007500301803907a0090000c81760030503402d10100b4000c1c410b9510661003690b00141e00300c1418001001c405c465807000d0b5051181c2040b140400c80701d60418070810000385c6485002c02c0140f080c0c40d10141203400c503819030402d4140043c02514150b40700355081405061001c0c0d0b070f030031036484410007040560030683c1e5a03800900d01545031484501c85 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 93553930 1250 93552680 93552731
    0x8010801150b0714190302100c03060602120a090e040f05010606110d030b0d0203031c0c0203160308150402190806092203030212130312050609010b07050c06040306 72
    0x140c0718001d00b05071141e00d040c041c2e400040c1060480b01c00c00c00080a04000300c072000d042c20150b030007100155180007590f480311400d084030164103042c8441c14050182c003800e03041d5121600500500303007080044811a03000b44d082041040038450340040c10780c0c81022014004c2e40142c5205556051504082c0e0035a249a4030041c00c0000700b401e00c601060002c144e512114a080c5404654203201e01c001841c11042810048d41c94000040d61456403580c2500714440c4c0701c0182c400307021034554904103a841e4080e150403050078044002c40340e400030307200e002a541e0001809040d102c844c003103200403070101c1c0c110104d1528605558014000752070b80040c48598404401c5079400c0991400c0d40c41c00c8000c1031198003d18040102c2c00d40101098000d8042d1070ba14008518007000c0c0c1d10b05801c0c09102c1810101060f004140680f10898404002c2d02480d0720459010b000e01c0002c0c0d2a080340d448480d4481542603800c1e000384d1441e8000717541e40c00010001035001c2c00d000314100c61075130020805101040b14 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 93555180 1250 93553930 93553961
    0x507050c090103120206130809060d09140a0b010b0909040624030b1005040b0a06030c110a0f0201110102071101080c0c03040e0f0610140a0e19031203020f031902040e0708010801 78
    0x707071040001d00d108d00703c540b1401e055808130303100c2140da118a400f502408400070304040182101c0300d50320000080b0b80c181c040c069014020b10341d0340d0302464001c40c070440001e160080d40b01c0340010301003641c98025039202c01d400a000e035113218807808801005900c0d50822605401c0c104240020012002c03c03441c0907020459040042000381000100420098401c140030f158403020003506e1140108003000140007a5002d603442d0708003501e495000507184038012800301d0070034180c541c03c600051003504c44841d0700c041350384d0412031224015660410014402c1200c40020020a40c5a0505102910003050b142100c4c11071820400c1c07000c51806001056030b40114480301101290300d5014110021083c032810b14a5910400038004903034007114400c402d80c02411217088d0904060f064602e80d421240595244c50030515016000c81c281c1c810f94a110b00d003240280046603e40c42c04100300f02400d1803440c1d0061525660740305500d00340700126000400301e0503600042003001028010001114090705 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 93556430 1250 93555180 93555211
    0x109060b040e04020f150a090b0703120905031603020714010302090a140402040902030f091216030e030708070e1501030605011710032a14010503070507050c090103120206 75
    0x40c400800d40c021441400003501c5240302003010354841031201c130242c440103002c610400001e2200140c10303500c4901b81c6800540c50306400580015488147c484ca50b1f455070769017030165025955080948130f002e070141c41c1c0f070004103c55581c1d402540e0b41c10858602c20f801504c0d00c68500302c0309400c20b004014051b818940100070089541d03a03070001d031034240d03185941c0c4032a00d0203580300810000d000d6a00082d14042c800000e000016a0300301c071803441803802008580740c160b9640c00c0d80081d8001e130112104030f041c152502d00d0000e4003070304a0090803200a8203d601c240c1c0c1e52160140b030061282c1c17010281064250601c128281070303190240f02040d00b0300301030000c40d103860700003410900211481d10005040401003110503003c020b42c10001c5400031005142480b1401d045d20420b00d148040d150300040355000000c9101318290702211141c0161102401e60f40c0319401500c50750b100703c408590303d0145411940d201d669000700d0714007075030081a0003920820f02900c064606a4003520b11240c5c8821b40c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 93557680 1250 93556430 93556439
    0x30103020901031203060b0f0729011403030903030304031110050c0f03181005011404110910020a0614010e0f060a09021305060d14060d151a06031806010906 69
    0x507104941100d51003000b401d03504c0f00c00003084005010702c4d04100c1c00c2035130018845d00740b29424405000014014840c41d02c0300c82010441d15003403100c100800303d8050551004100114065040c00901d41e406000e0364901049140041c0c15a401200d040f4080ba40b140e00311132a940e1700b086100941c107041340701084541014000c0e00c0780781c041d0000300070340c1210000019002142e440c00a000c03100003c2d0480380000d00c200050030281009015007009500b050150300c04600d40f40c001c0c040c0607003142100ca40ba1a400310144518568001c1c14682503101c1e841c881d1001030400d00c0b0f40004880d0076141c448041d41400402e03810100050b28004004143c00d0901c030b03845d17845118200c01c90b8a80100141d03200452206100e5942060384455440300010400a603d603035580c206500c02031039600f1441e076079a9940100b024001300302401034030142d040003c0466007200e0b0303440018140200345800058042000c0000c40a5004580442d158101c291001205482c1045401c0c050718030304200b8804a41030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 93558930 1250 93557680 93557689
    0xf14060f07120e12010606031104061b0303060f080a0b0a050f0f19020a05030907050a06121a040e0a0204050703060b070314040503030403050319020307030c122706080c03010302 78
    0xc03620701500c039001c00d2110858960250803524102c090107003c49042c001071080c0c450091400e4403800300403c1c20040d102e00c04522020803102a5880c03511200c600c200500034213083c5040c040c40480070705a480c1c101082c80c07502001c1102c0184204401418501290302c1c09c6500300402038451108182428184051029184459036020029070341c8a012540c6000810001000115015000e0340c80012005ca015900400542c4100e484900320b82c1160359070010f10000d60124400c650000e00b20205030340390b6a0050700004502d060401c200c10459007604001030484003a400e0110140c2d20140c250386c21400c0c90301070701d81d02413114281000103d04e040406030307041c03040d40d100030204248104541c01c0300f8005029074010740005804c49840c4c03a100c0c503010b80d499000c44480115042003980c2014041e100000705c1d840075916a5074441450000d9882d03503444502c400c000320501c1005110400c00046003040b0b2100d1003406503200039402c0c68104054041d0034040c18030020158100300600142e00c9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 93560180 1250 93558930 93558937
    0x60b04030b0103060c031104090b01091a03060d0c0b0406050403140f0c0607020a092c01060602031606091a060f0103060311192c060d0302070501050f04050402040f14060f 75
    0x200100003082d0409184004c030000c2940340c092411f4404003160208020301d9961149082c0349081e07c483c00c0c8161520100c02001084c0460642201c40800c00101a81054010303001c107603104616002c1019141d5a0404441d007041e045400000e002007410424018030110301c6402034029000341c0a0704418510307140d20f944449080501950000a905085454030503c49008092445080200d541007110611011018000c10000a1809810181c8002041c030540c0115000c6400661500c0060040f419a44540300400d1303820f5659160607801141021301802c040d8810780c0f210700850b141001c00c12880c41714010703960341014907100c42840020070009021540d808212407400751038418280050b0b01040310340105420800d440c1c80c60001060b01c04c3d070014000c003207005000c2c4d6a40c0e0300090058500d41c480c0040c1c0141e100311010009540140f00510010038181c0c611440d0a4440020500b40c2c0e006600495801c400540f00f003080c0e507a00f1880d45450f40c002c596036440c14124100d240603a00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 93561430 1250 93560180 93560183
    0x70501050f0d020313060b01020706080402010c020406150909290d06060308160201080703050910110f0a020c030f010b0d080a020304120b0906010803030112140c031906060b04030b0103 81
    0x14000410121a6400314103442290b4001002950780e8580f0175103a100003000804116944c0d810320801a9403036001050a10554415a0b41c001c10741e603c03034004561041040341c085c0e0b0000e5503480041040d10b14404100e0a403609601c0701c0d118245000d604004644440100591102c20000303000742c2921840722200c11a1303801c80d21481c680d1b070203040c0a8010030066200400d4103800090040f1001626060f101c040c900036203542800d0741e2010b9096090329011200103802d50404002e90809489660141807041900c051840c00c1546408007002190312152207003000d0b0784041301203101c524007004820302e48040e604c000d105110105011620740d125a2400034612103020405410282c4200165401066107140036030012009061100000e0740c255010207880c06008000b10b0389240c0001100d049400c0c00e00b060300200d001d43c480b86104002149160344501600b0000203456900700318221401414001c580c4020071146030501c101c4202e80e02c450780c942000e010820104805805183c1100e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 93562680 1250 93561430 93561437
    0x60203090409060b0303030717010b0906030703090317010b1b0f0c0111100603140d110606100905060409020c070e011a030c090406030c06020c01020a0b060f180916050105070203070501 81
    0x120903501d44030018050003004d2581511010003000441a80460310800c032004000c40b00e00182d80b901c28a107800d1103031081030b03038102e541000400c045a1183c0d00885945000703161100494040302040203010707200380d2180490704d2020512031b40501c524407400407403030308401c01406030625200c81c0603201c05c041d016890600031000345c40349591800b84080d03072015403400d00c10402141c89161500010092203075940c40c62080c0290811031030700030340e604d03142010460010113803a690032041182c018210702c00c42c020051201c000113019203811001d80094008030b1000368840c00d180b900c032894982240e0051203458841001000b500c01e45500c2400340480000b6103e640781c0c0c5154446825104051440760080d2a01034004144400c180f100010307101b4550030340340003a410b8001242e0707881c84490301626400c0d003080171801c1460b00d91040d040303a4002500c40380c0b20900140310307050000011500701181da000460000320140c0c0d010011005401e0909280d800c1c826180c01295560b03080c0c5c011103050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 93563930 1250 93562680 93562691
    0x91002090d0f0c0f06020319080402010c02130e0a06090303151401083c0901060f170a120807140708070308061c05070816080d120f09050a0c0f0602030904 68
    0x52045a0b61030308050801d200e034075500e0750b0355000020b60701c0d8032008c0320013407800300005c2400040e4415140c02d401560143d42d030528100f02502042140000701513950503803551014243c110074018016840d11500038a070009001040781009015034000d080e200d4102060184248400003120b210030311154001c0c079002ea0940e440075646d40c4091003210218100400c1d103c81c01c2102d0220a0b00400900310089042d01e581c0c650700411400d949007800303003000c11040d40806001c040c109588610700c002d0580102c3d0070045003a226002002d0122007090001100c80080202c200c3e004250fa03088050441041440d21510b0340384e079400b03406408801810080101c0c044ad480759520a0400100005409518907031100d0b8903200ea078940c0984100d085074025880000640b4400c0783d00c4404884a40000d001e0300c0ca0603050481d040c0818810548915941b403401c0480841940720f68500540728000400302601d46040034208026203070312551070010240c2c020700c00303640c2c040141c6040080580e4045003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 93565180 1250 93563930 93563933
    0xb120907030212160902030c07020409080d020a05030406050f010e060d03030b1011010f0207050a0825060905010e06090304090b121c080903091c03180e091002090d0f 73
    0xc04005610195100c2c1d5041d62404149201003030400807101d60700900343c1d0096a59441d4404e074002140c90500200c0240140301c0035003000e4110b00e0b440d5111b560b080f443d20b01c0886403c8101d03005000e0203c0001d002008000400ca071910805400c0001c403203454103a5890258400050300b030003040180100142d0280008140c007030f4016101c003400091500605104042e40180207041034403000e000c0b9801c20314042c016005601c22140b180f508803003d8101c0036050340340e041544e444940200d943d003034144c4043c15a044680d4155144a2080304041040000c0d400d04500791045001e0b00c22081d0000410300c400444000308480803500c2c4950b02080541d00c150000d00b2181c44104280880c1c000c505000009500f103151286141c62103403511724142d165410081c2d0780f8000e0500d0a500080b00c1c03016440c0741c45206040002c1944070740340c0305d020748901d00049944050664004603000341d804050098685040c440a0004600d10700214105a10907000803d030381d03c0500082c04c844000d280744d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 93566430 1250 93565180 93565183
    0x93003050c031323090c0d050c0d0c020102041d10150c02090a05011e0305030a051e0a0e010f110c0d0f05060106020607140c030d05180703150b04060b1209 68
    0x314001014440f00a02ca650340c0355541c10005840c4000e4900185240d10800c1803514000141c013a540d40010b107402c001020411800600000e0112001d00c5010320044415846500610b07010542540c005a240c40c1740c005c3c00d1445010042e03400807200029010003240240e1540c07001e04850321070244110000100710300740c1d9a03412811010350000341c8402040400725a603044107048580310000c1d00d0901900d40450a0a03a060b07000041c41600b0030441031074040d1081c4007421000503542c601120208074070a85940d1035000540200108514029600f010340e0440c502e05803680042c01c02c800070702184240103480e140c0200d0703014810303200750190070284000300e21001c52095100003280c00958488001940e04e02040b54100b000454024004d003620180c030056800143c500c600540c201418500807501416000340b803051070340d924000c0f0007140e100411101c0c1c01940030307401d44030080009400c0c00d4142c4080d410902d0180e420242e04000100e0004104e52074100484541ea4654a0b18500103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 93567680 1250 93566430 93566437
    0xf0e03071502040816030c050102011119030b1012110901090506070f0204050f040c0503010b090105091b1c0509070b04120f05010c0e011803050d0c06110406093003050c03 75
    0x7081070b12802c2c0c69080c80d0401050f100341507d02031343c030103503410303a07940c00484c00c1e240c4000c42000190b2091024003d03000c4680c03600d414040ba00c1c1004500c100c02e000104100e24041550800000c2a00442c1d8905c00010b214021030b60603062a1280750800e05c400180092400b4070405014840000d1408244071400c0d0962805642c000e2041c0190b0400008800d40b08030300f80e0b0142c030241041100050310b40707414861700340c800c200031b0515074141c1c3c0307040100104210010045c4d032204000402c100d018000b040e00505000e260710780046081d000c913180c010100c03540100203a10740c0c0e2080d00c00740f0003850300b2825902111070000c4c14819000389846d01c0003029400c40002009903003407005400629401c5510504812820307656916800c048120401c039901c000d10000d4016000384407000401441040d016010902403503000c100ba2100110005c9207610a0f40f01000180150b031052060000901e6204103110300e5038004803141c1d4440c0b6004588950502d401070034840005181e039004041801074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 93568930 1250 93567680 93567689
    0x1101140f070c03021206010e0604020c010207020411041d040506010b0f0d020a050711010305040c15020a0209040606030209010806040b0a0c030e010203090c0112020c030409020904090c14040f0e0307150204 90
    0x141a210308a615203040e42d00b40a00049101c0d03054182010401640010394504a8407039010304c50080e258a0240002540452142140c95400304038201c0503894500445114018107110740c0e948910307014800454019049001107c010100c0620021460010340385041d101c003103000303a5a44000286071100ba1140041424099001260800540f2b40201c094036a550041401c6201e902e0b21400440c100d45044030010411000800180f18031602d03543c0210111211740122640d82c07880c0d030000703903491904031011602c4646601c01841107040c454282401010141e00a0041c1e0410b55901405908001d203d42e502075900c480c400b0b44144681c02900032040d03004021035403402c201000c0350f1035001d10007565000c2000b06000c8502c0404520850303040d0f4800c40b014509003801c00c1c010a029610014510b40e02035141c09603c004542100812030040258507070180d00c281a20040c03000340e50082c28000720803442c1140c440050340000c0202c0c1e0606900c2078031255154180290381e0300901441d0030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 93570180 1250 93568930 93568957
    0x200f0418062a02010603150204030f0b0c0d06090204171c0f0e0a0305060603011a0303040b03041713060f02280302010603050f1006050901060203071e060903030c1b110114 75
    0x2003041c001ea0f0190b0240081e80e0041c503010007403100040e901d006a205511004101801c035001480106040800c10354000134040c00d50b0389014611a900d40aa4050350411410a640040c0c1049600b0740b800070200b11090540150420028141c0080406000c0c40d10760400c0c85000c40341112198440c481802403108002c3c0180c0040707459080090b545c0d00d00316901c2d800380d8600b81d0300c1c10a403500e9800c0200503ca00400a42c5014203205020b0300942018004491134100d242055038082c1400015040421a0010840703501d464400300410341015030543d482590440d4114040801d900152700703000c100c4030602040d404e4400e19080740105020381c40078025001d180a0120800c102040c04a00c18a2507541407005503181c204002c00c595081c4640310250748108040000904140c40f4016000042e160030740c801c0419403140c6007900c10307581d0201d00180d90360b2035849443e9000114030001080003400300e1040708a65079000013190001c98014144015500709000c0e8000e50000c8a012091141 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 93571430 1250 93570180 93570251
    0xf09030a030e040b0306060a0b09040204030c0e0603060f090309060906120a0c020705010216060e01050d14011a0703080106030e0118050a0c06080f01090209010507200f041806 77
    0x30002d00ba818494641c900c250b0401c4419565803400003141400341400604842d1542d00c0e00203042c039990b01201d0b00c150455001d0000102150f80c0c0400d46004100301410300020740b0346001090f04081c001801582d44002e00e1061040780ca03000029154440821303503429680e0340f042c8000449900884140d01403204142d01040950742c0c0d1a000199414026003c644030b0783d403620010390300e40344004010480c00c00c0c003010420402b840b50400503051441030500a2038641e0803207400041d18200c0f01712860304200c0c0401040543d103040b0221140c48101c09009040110942c0e0003082c2c04c8040c4604010075454581c20310400c20300398405070441802141c0e40740c559500e49001d03034039084c0c2c14400780e40041c0c8044002601e84d000d0044d22340b10301c010030070f09050340e82855982c030001e400c8244c249040207014407003240011041c031000da0f4010320166591107032035544010004914a1050500e0041d41081030b0b50b11240764901e002c6001e25400000815102000307a6102070194950140c0d0f10b4203019030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 93572680 1250 93571430 93571433
    0xa12050c030106060302071a0c090604030b01081b0d0b04020a08030c0604150506010804081c1418010c12051305030a170f04020a121106041e050a05090c0f09030a 71
    0x40c0c2100d0900d01900244502c81e52554240c2c104d010b1400301406000c0c10383c40f080a5240d031902040d90201317403101180c2c2020081004030b41d4036045500b0032140c0c0180d840c010300400e0810003607043c601d09950b080340c0708c3c04000d4002c1031041c5800c40000308502d0540011404645d01d070361200b00540344031001c4a45030b07512201d02d40c1c0e8900d025902aa20b04180246c2040e0042072800707168420001a151880542c640d0340c1e800041e6400803a0701c003000001c50020a252841c94090701510720b407120840d072018103060080c22401031a24084800f180e01d442d8490300c1d403c0c3c1054007194105486e880024841c2c1d00c0718a1011a0710282d20010710030b010000c4c209110507040b85003014080d08141c0081c1d140ea40e000e405408080c41904c01a40c07003180c000b810050095040400d1011601c606104203804000d800450303040e03041078210444180c3e49418803200e6160841c0e07148010314040b10a10840d41c0340401086002c58068900d941c0408009000c186a24948003100d0020101800312800000076 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 93573930 1250 93572680 93572683
    0x120909150504050a05010506040302150d09061b17070e030a1a01240203030105060a0c02090403081905010b0f0714030a08010f060c020f01050a14120403020c0607110f0a1205 76
    0x141d0086a110b54074120209039800d40e94410749069500140006280c54256020800f100000d0718400d010800c0800107105030f20301c00c1c082d41c50201c1c4101000b013000f8806036119046030a20000030001c21400045004406000c428860f4104080f0304008050051036030100b0b007019128180603065060039802100c0c40f10420f2512030407140380c220002080041c1c0002004458030011f0800300580c400e100600c02864142d00402448034203042000d00c0305180d81c04194440c0040f10207901003121035041040802d6503103a034444c1c01c110f50400300801d40c1016034a2055006241010b03021040210f100c0003080400c04000545804210444e80c5503d40d90360018800034003401031103a444544a4001002ea006000c40035005500503c901c080992400044420360008600e64040002a10442000402000080030705480e2442d020b03400f8a0b10781000b03841c041030051494081d0b002082090081741c0c241202e1811303540d0845000d00c642c1c180d0300024074020000e4200d010f80c0ea030000d0038042007200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 93575180 1250 93573930 93573971
    0x41d030403122303040b0c040e25030e060112030c0b0c040317030408072a090e0c0a080703030309060212090a0c0801050c070b0c0403140706020105060a060c120909 72
    0x3030756461600c0b0b0843c00d889510740c4003140e10200081d203024008100094200c010055105103449111410903a4a54090504200035240340704403407400030303a25041841c0384280c0320584146040c00e0000c43d0f40044055a5074038148681c20301030070080e07503000426200d00300c800304094001c0c0b8400d54030705085050048a9000381310886402d94400c440d80c0c101541a0181d0b0311680e0829030a03828a515030f11860781c02e058100d03089001040c15400b203a42d10002a42d000064410440009541125100c9943c54850820f52141c86400203010800450f100000c0c5a01943d0380b615010420b003000b454104060300500041d0381010048000308000031800241c0e51000500814101c101141d8441d609422140d0640b520420850100f03c0040482c2d100040150400d2841c0c5609140031f651340c075507060350b5400b00004201c5c1d0700000010440380b9424003410303411400c11074580042c145000d8000d4600303009650024034100c06046040d80352401060540c006080c804070900482c090f40c1001846c108 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 93576430 1250 93575180 93575213
    0x503030f1501021f1d12070c050f030c12070e0c030f070806010f030c1205040c0e0a0c020a021e130c0f02030405030c010809100f0c03230402041d030403 67
    0x40070701d40310300a19840000c02144452104402c5407050400e80e42030009801c0c00f040b03121308004200a6210038034010807070142c0d454404a4035a072a904113180441d184c0d10030f40d02003403051104d606501c03185e80d0041a01c1c043c0d1607040350901b441910721149107080003110380c018509424000b04001951441800943c420011210100d0031541c8045042ea00c01c50203070342003030014400480e10320040380a40d010030603501803800e01003018400551441c0a0382d80880e02240e00c0c040c006400c019000e40381d5080768000703010302005d00102d4000107000f9a9032030b040401030310801c2d448009120a00c003103005024078a03009003601440400c06211040038140705a8480000360740e0303480d44210144040140c8007600d40003000780c0ba80e603507002c004492300107003e020455280169501c0d460103d82d50b1040450f5604915404101c0021066015084440d00b0702414291141885007403214080c003c441588907604442c002456103a60f54035805280081a20600300d200001c0c1c04000c4c0f1003600d0440c0c2d5000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 93577680 1250 93576430 93576451
    0xd0c030c060806040203040c05060903030706060b0a2c010503040206040506030f090c01020f06011701110a090e0105010306030b04170c030a050301030605060a06090e06030307020402070305221a03090a0503030f 92
    0x142c0f01c0e4000c0c0400c0340300844000e8410049144140140e2400714018801c003500201140e041810743d8441000700ca00c1da81c051544400c1c0000c402c0062500500400011020b000c0c04501600c4181072410045d100407251504200c0c0010014085648000070303107014101c0030301019180c0c038044141c55186201501c40c40102d120f168941441588006000a48000010058a0036903c0e001c5428140c0d21000d0000150355210b48a03101c07080c202a0151201c0841c1d030b905c81040740e2600d100c4002030141030304914101405e0040520115070030080040c0c109a020034501c02c00076050020b03180c10f0041602801f00350000048101d603659008010314180c0c0d016501c2081182c07290401c010400e25107219103c040341040c0820003034103411400c016030219000d41a2458410294002401c0703a100b04002c030085100403d1a64a615071001048880f5810080204a440c10400c1042030f4200c1c40110200c6000004002100c0740c50500c84000f14036031000c1100d842e410644188149050200c80700340c000b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 93578930 1250 93577680 93577697
    0x7060e03090f04020c0316020d1707031716052206030e06060301090506180106080303010b03070818031903110706060614070f0b06030f0a110a050a050f0108060d0c030c06 75
    0x11841e192081714003005200303004524008442000041420181506a9000e02103084003004160224200e1032031050b1912860382d101800e260140858002e40c00d20051828050100200e1030741404445050304001d06009481d034003141d0103000306421200f5800b905802c201c40005616070147c0205098083c80c3e001d6410039900c150a0508a400c0d40310094811743c41140800d40100309080130036105d114050000c200507480b031a805185500c00c0e40941c1449500000f00b090281d40022059000040d0094080301c070240300c00059503078007a4100c81d46691081d1101001d00700d0095100c948410f07010302d0655140c10755411301100400d03144c0b01c0c200111300c7c146201c03251800791408403406250b0041000196800c01d440310000030f03000604094052280d2441c1a0380b0b0401040303056003040c4a201142d41112250040c0721040d00740368403490041c4400e410a0010760f450041041d02c0c07400a2801441c2c130380e124070005044095400018100756030240011003445049110742040c0c0e1015210980c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 93580180 1250 93578930 93578959
    0xd0c0e01090b16080912011a3607090812090103060e010b0d050705041d04060b0303070506191503050a0b0c04050d02010f140a08091c0207060309050307060e0309 71
    0x1032103000f86115400c50501050000100d02601500900d400503101a803680940c0f6a036508594086620400f4845c0304820a801881c0c014030030038a00f41801d020101c110070070310b01072000c80728884551001c04039510018581500c10b400c01d5009109440844202d54207041210f04a41d001c150402e0002c1e00344140801c0c170303000e400e00e0300c0c1c1282c0042c03810a1030101100c0c204002131001802440400404100028840d008002c01011041240802134418101840c10004130340034900c005000c0c1d0802d2100c0c0002c240082281c90348040c601e80700200091031000b044c2c0040000c24100240d016a01c000031050140005103210340c6441007942c01401c0d102c951403000176000780d2083e16400404030720400e005500c2000c40d00440c00c09403c0c5046003a6540c40c0e121900c0e0009102d020016100b1010024082010000c00b000040c2450488201d561954002512800380c2e010740c0c02450b803a000d6001c01c0240400031103580385d0b040002040690001e0760003540b00d52108465600c03c0c8140c048900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 93581430 1250 93580180 93580199
    0x3060e0c1f0207090204140a0510020c1c02090705041a03040c062f0a060501090b01022e020403080a020c030d082d01030f05060c0702240d0c0e0109 65
    0x12000034619900e808251003070003a50071482070058114010a000010380c20124000790000c1c1c25019905005442410144441c0388059406107118032450803801c200550007089c819440e0f101500c22000000c504419058002c0c00301070000c0d0850b803403c00708000c4a5100c0b000c0c00c1540c86029502101c04168110681a808140d4004d451a40345c00801c0000e40d02841102c0c80404140d02082c40498400880000c030015040407000c00c0c1d00125500001c01c410b5100703040c05032440d143d04124049881000030750310036030b03078111807281d201e4011741d5100300815082c071445c440e050240a654841e124904100c1540000b240100075201c0c2490326400341c9004504480c000305246d640c45015640c1c510380440d01b840710000000000a50101c1b0754141d64601c212501840c0102480f00800506240c45441d10500a0208110701d0090100000507642c5903040c10b0641841002d1030ba051007000401c4e4180e00c00d038102d01c0c20b00c501d40018021107075044115504044403d0f04c550700c48036524505030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 93582680 1250 93581430 93581443
    0x1208041a070905091e04030e01021513020d02031c03090c0806091b0406120b0907051e01080406021c0519020c03041703041d06091302010e090612010c05030103060e 72
    0x20102d071012034284200e040a0384a5580300605003040074038036540600d0809520700c10340d401e0b00081c507004940d41072940c0401800304c182c1001703c0321608030b1900c0361811403a10654280284961820803440003550741c200a000442c1c0040c620031002c101030b114025009110b103000407104088200303400120414081030b1284241040805404c54102c03041ca030190140d0040171142c0d0250f40c03010041a03d404000e40895403034802d5103040e80f10f003400c5054501c0c02e001b0341e00180c0300700c0100302c00200d1000855031880202d00c003030a1110542d101c0d0700d06070020b4003652840003003900c0041030351440c1441076000701d030180f41036601e0013180b005082503d03030aa01c2522005c0c1c070141e100708410002005010381000c019020b110603a400c0139198401980306210907030010700000310303802c1441a2440d00061442d00012144401b01c2044440e50010340305009512030b0074491809480014001e442c1c144505840d1684000204001d001614020b8040d400a000a13100f01c2c1c5003211704403a0188c0019003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 93583930 1250 93582680 93582691
    0x70f0203030a05060103060b0409020324010504030807060f0906020d061505090d020f031e0705010c02090703150302060301061d0306060d021c05033006010e040b030a1208041a 77
    0x146107581c0e02c1d042c048010300b10140501d4100342c1d50340800180d6507a001f01600152041e5000560f89003014441484840e5180700500542110180c01801d603030703080401c903002c980e40202e00c203841740c00d1424120000d05000703000864060400c07812a0800c00c0a90041c25400d0302c0300b400f0070006444061000c10040c411601e0340c003045d0708200020309850a4014014224402081c134514100c00303601190528040c820155404011a110400c1d500000e00c11346001d000d00717281070103d2007119000101c15140150206062550781c2c06040390309180179030000051074010300007c2e0742c0c0d40d41c0c5400425040080605140c0700704490542820307440c004c81e415024520003001c0c405c121202d9020441c90071000d51040113849285120034000403070900c040e14500d4103410518012204498140003203000041c6106000c00d0840108140c83c1e8102203240f54240d8140c1d030000e682403000780402d141001710080500290a4144c4060710687d001c1402c83c411482000d034096403050b006660340d030642c015a003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 93585180 1250 93583930 93583933
    0xf070509010504090f0203010c0503061509060a0806010221090a0f0803030c0c250608060303070b180703060f060504060515070809060409140126071205010e031b0105070f02 76
    0x4200528244e0071010b08280982e25520a80382d040c0e00003400c40d6606030200020600c00700c03c11030186440103601d0100c0d064070707443c9131501e406540060780070f22440c01c40e9418401080080399859100b0081d0b00d4451071150082d11000c01240f40b0002e00350401c2115500c01c031029200414052622454603085401000046003161100701c1c0d01802500010b04040c41403003231140703120081036070600c44840b00300c401101c60269030a00380000c1000c1c80c0100741034081d51040105000049580e1005030b40300c0c04a02d035407c0310100322203407039060881075403025041c00d08007000c2009030395883d8801c00072a10202c07401c001042ea1141030055810012901101c03801e07040c4203038800308001c94010703c41d0030002040c041c6459181c003580811210403101903020940e4480050180201b00034000100c148004d12000c00c2c0700d8001c840c1035a80d00c00d401014103601900d030074441000000d400160303026075000107032611400036510702c150054920340d450125608003070101c0e10080c010b013562201c5805030390 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 93586430 1250 93585180 93585199
    0x100f05040902010509270a0b0607030c080d0903020c12070b0301031b0b07111806030a080903010603050607120c0e0a0308071a010b12150f1003021e07050f0705 70
    0x201004000c0c4882001a4140303c010016821385658440e014041e400c0c10341d1240c0c0002e082c49244001069000b404144c400786080036007040c42e070740c102c01e23a81c1050b49441c0c680c030890094901603007035004650b01c091070b0340d041105d00420140c001c81c4003106010156003640c078070151012129600d0149d07100d9032840c120300f00014004642d058100c540304d1b1072650b80e04070055980380c503c90b075543d12040007500c45038100d040d140940d1900c0b9141e0180140714164009060824400198a858015100801404002403008010340b42908000021600201942d0051520100c0038000084080c05c50f030383d941c50800c0755040a401200d00c11000c000107411400c7d2941940d0361040c141e480144245c40200c40485640300c48403540310502d001e0500a08880c1d107500807001d0754645040e0103016800d42c49120511241143c0300c088482440f058100c8000b00b1124400606800074440c3c6402d194450f600d031010f080d40b180300940240207491040c0225550500e0140d91b07039441d1010b6014080d480b00515 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 93587680 1250 93586430 93586439
    0x1e01080403080c0403051f0f0905070612150806100e010b0301050607020d020301111c0501030f0209100306060b0a090603020316030e010b04092001020703050a060507170405070e100f 80
    0x49440c07903844074412409a250540342d071602840c03c1c6c030391451f2114550064810100d0120240684000c8000107882404400107a40d80c0365210042d500883c401c0080d0000f80c1111444140c12004400340848000c0c20740c5920341101c10745444044401403030042440342c0014644040d2250503040342e0000c000d4a0039a401d01d020442130307078080d910590b40109201180c0003d40d500303214072411852041c0107155108004445502d440382c0d0b186c5c10401c00d038502001003000c9154454880381050381210b5010075651480c0254840a416410203400039141c0a0003080d00c0407020028107150200740c0b5140c48556403488100c040c0d05c412149039214540695896040034025084690070014160002c00e052f0703c0e11b40840c0845103900c609407901f01038018484500003002e04840550002807010742074050540c1c403810703552104e40340000c10469a80e000101d803103104001303031481d00b920064001d089003031508106ea5070308207a0080c4002405910081291a086c0c51842c104071120003030410a03075450b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 93588930 1250 93587680 93587687
    0x309030b07091508070315080c2b03030501091803200304090f0218030102070b040f0206040f0801050702100c09050105070816050703170a270b16021e01080403 70
    0x3030001401c0c0300ba00c600110b0040d01d0004848940d00c010358924a103498080700081c184d0740c003c480200e284202e40d40500a0540c0031490642442007512142c110a591800b90961100c4040300e40b80c1d404200c0d40b9207010180d2541205041321000102481250b40161020f0706900c91908020046045d110b88508220200300351200000f0042c02a02c0c1040d039038918410545005d200c1c4c04c51100e42c0010260550203031080d219100f151b0a90085041c08401d941307100410101420140000702074071070743c10455562004840c080c01000aa2008003592007e42d140681000d4030568094014204800c0919199129a01084080b0f9a03120041450540150b82c1c681c044581540c1501041000070006075000030142c0314103105d4401881490b185080c5002509607520040640d0b090800c801d8041e03aa0240c00701e6401891210000c007036800706120002d03080c840c0e603c46210244045510741180e0060200c0f645864020f6a894652410300c0c006081c10036000303000c50703010031444000714010074407 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 93590180 1250 93588930 93588953
    0x30b0a0524010c02061603081006050f0c0a02060f0403150911010e0402070b0405060601020d0201020f030a020f0c0709020408010e030313080c0a05030705010c090902030717060f06120919030903 85
    0x141810201c110f084150003050440d40242d01c0243e102403800000400c0540c8443c0d107603480f4a822190005141c10a02c000b880da01c607040c48078100b214040b400103050041440b0301d00382154010a0a82c0c0e9000b00c40360100550014441658020010421101070030f042c3e004120410386c1c050b05841c1c030440c0c480010b640c0c2801440e441a00281c0c00c0c065000010502061140514010002040e4500e00000024a403207420b5420404590040c0700c220301d00c075240802c0e26080f28559002584074080042413020b64011245d044041c0d128421300000c03205469070040c004d882d070b0f0341c00a01c03514412400059072403005039400c0c1c0c1c02c01c078080c1c3d0701000314000202030105140b07900250f90a001c05600c515103541c00916099405941d1fa490203a08160007518200040034201015400c61030302d803102030070000240003004c1490340d42200143d0300d0350303d90030078490421000b00100e86400b94150740c50421070382200c2060043c07146140e2910714603007444010071040c0d45a5500c41c8400d085075503c081062 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 93591430 1250 93590180 93590251
    0xc0105030712090807140a210507060216050709090c170c0603010b09011704021c052e0506240f0f07140c0604050604170307020415030b0a05 62
    0x380b034400006030300038050745082c94018568984c032440d01703040030480a01004403207000c41e80103541c1240020303091801d080c01e030342075103c00b50b00c0c169100c1002e6606115070740005080034400102a41001c4002c0d07422031489015004940180b5180c0303066404507005e001c009010007160060400c072055003480d03118505142c14080e90340d1050508003007500d6030000e030407402c0c0001c0f02195044555a02c41c2c54281d41840480544070207082940200b405a90700d070300d400c43c504841c0d281042c28004200100c1c49014401e59880d407050f44500900c50100e41604c41d5031411170b051002080c454902101c0306070700700714030302e900500c0300b00310030762140c2250320000c0c800d0f0040c5000d10040041c14400b00141100300c0c0215190841950512105c904104d07140c001c091003040f080c08140710710344070390341603c080c0c4040c1180c180c84081c5c00c80f5140e155025104000b984141400e0b6261089070000d4806800c07030703108192104070780e213800031258140c84046480d201201103440700c0c00800307405011600703483c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 93592680 1250 93591430 93591437
    0x21091404060305011401180b010e042a09030203011b020706110f01020f0405030c091612060b0c0102130e040312090201051201030605191512021c050105070807110c01050307 76
    0x1d6580e9a00c81e8217440300e8000c2a950058088010081c600410400c0ca0f41d0615840e000c110442c0b00c41e00103401400c2c00707410345004070b40d240f0036020340954507000100c03010286607500d2410319100000810030421800200d009500b411040006001000880380b030040d003640103040020b06082040b03c1440344101030002e2480b032010001240c0b1001e00c01000c2107880780354941c0d5910700341010302d403a100400e03c0341401025210100302c401c0c040401440c02200321460803660860340d4404002c041c00f201d80140c031080c1000195906800b00550040035882e036287d000c10032441e03031000c441d1b44150b411217001d07002c00e00c0301800130300c0e1080c1ca9101041a900c141862410300081c030000d9088410240c02c1202c41c01d60302c50034401b51312aa408407020540a46105100d80c41141d078001c400420248101c10600b185500c0c0300d030440d0b461164440c8000c45001d9124120b286e80d00780030b4003a02c070a4420401151590000c904454890102034000143d8000103102c0c0001c450011911580700614803001c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 93593930 1250 93592680 93592691
    0x151c05161112030702030d0b120d080c07200108090f0316060e0f0f071a0403020409020d0b0a05010317030c0304150605060f190323060d0b04050a21091404 68
    0xb02034200518024889a402142c4400d502d5440707008848192086c2c1c0c0c45005114401e030362140c8005070f044407030901843c0c5612180c41d40e20081c00c640c0680f0380c00800364000c01415032840c01e6482c102c4024808240c1c2c074480743d512a00d140d90f4458041d2100c205461b00300300107060451180c4080440421310410300007507101d00a0b0009414092001c0d0400c442c0d8124028590070f0b070600700440b42c068050307242001ca040300c201c0c03190a060310031840b000f405180c9505440003556110101900c050340c01c0302c020111844c1c0315268000038442404110345240e6900d0010004c1810382090704d109030754002c0064030b1611240c640c2d00c81012903071590400340d600c031000410144c5941c8040c22003070101c1c00f0003545888104001c3c07400003101c83d43c00e4040505e01070104100700d4040349040190000d0040d1360300c0980f00c3c00041407000100c4803015042e807079190188004c1003c000b03078841d422801018502d02c42009c824420400036600744107200090309240003444045101010f03500d9058005000056 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 93595180 1250 93593930 93593953
    0xf09070c0f1a0601090603110403021203040f030305120106020105070512060f0a06020102070b0a1a0603090c0d0c090c02010e06071b15020901080702010b011b11151c051611 76
    0x7280b2000814482c2011865092000658118400d0b00190080e410b080c483d9507000000c0040070702403844064401d0340f07560312810f14100103004413400b40400c1d0901062141d03c2c0e080280c480c1c1d00c041d03600e00c0081012400000e1441c410707c2914001c000555400346064400c0c2c020520384113015010304c1d4089c0d41088001000c1d0303507502c8160001d00c0d07260000b60700c904590800d408003c00c0203103003c440605003400c3c0b0148074040360801222050840b60fa40c0c49440d981c2c045807074040541400c941060b8640703101c40a1080042c1d01c54100e460010050003080902103040382650650346180d041c982c0700c040410326040c0a19982098455846c19003802c0341e5964450788201c03419400d86d440b074035030300082c1d00030355503400010715500c80006e00090101c02e0b24400002c00c1044404903e02640040e425044200b25504c1c59001514030000d003a5041803084450903865680b1103809400c052003581160180303000c0e103000d6203104400504490f401414600d40c161961a0ba805c5400464040d1840916 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 93596430 1250 93595180 93595193
    0x60906050304080c0d120b0301050610030e03040f0906050a0504180212120f070c050117040b0a020c010e0706030612080f1e0c0601140d210207050d030e040b0f09070c0f 74
    0x9004405c2d540d15000110800085102220651800b0901a904000800000d6161000d4501c4031102c1d80c0303000170300340700f103d0901030031401217070001401c0f94148a00050302c10303041d030001d0059a10445000313003503950b24020032048a0003050404a0742c050361127840d0140c5001c030b440ba130010650000707503940e285034000d15490b070354004400c21180d0b08012a10310b0500001198050240c1001c0c00c000104258404800c002100000c0c030050580200c00005180c03800107405803240741d100c0d80300a11101034030704074280c1c03100c80c40d00856000034540900015030316124915101501e1700052124581a090b802c0444240d02c005d0402c0301100a003004000644400002003680d1090400940350b40d504121200e00d6028060215070310824149504501180d920703007035014805c001d00d071006802c0d144060143c1c00d1020560101d540403040c007076083c00740741c0c1050b03090103240d00494007000002c0d148030411002e080d0070349400350400c5100c000541454001c0a40e140410f001c1c14062000144954410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 93597680 1250 93596430 93596443
    0xb271f0809010c02010605091923040302060c03010b07030c050304030c0b0d061e12030c060c02010212010911070b100806160e0103061a0901050f0d021e04060906050304080c 76
    0x1000500d41a040001049083c440c842c051003c1344002d002251401d40043d105100c05450021a44e005100755000c4c01010790144041c0c0d207070f1818003102c02481c1041701d1002c0350201d034250301501500000034807103034015040b6070581d501d580c0d65605121554804035800b018207141140c852004020100104002080e107500610107854225a1800098509001c1d240306134000c8414411401e03c4c078440300703042d40b40b841c195210a6500080800039060848216039400070103012145440254551503a064000b400030140c0c1d6941ca0f4010b903a01d0360800116083d0240c000307001c640511070702c400245800400c540120303012080314000e9490f48906801c00c1e01c140e4403c900c0c1d60708894081d00381038214000c0e00d07001009090801040d450301101b0212659400d4000440e4080003400b130b1750f1130380207409944590f01a80c080325141c50164024a00035440072580c0d00b101c44400703150780c0e101d04940c2c080b1415a00c460380c0e18250540b41c0707103040c0c89030b80001d041100e0b201803e20070621000c8082141 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 93598930 1250 93597680 93597739
    0x30e030d090c0302030d05090a03150b1002061012050d0302031003050f0312061c0b0a090804090b0315041509171201051201060803090d02041b0206100b27 68
    0x810155038035602c105403800c00d4641a00d424800700388511381a55aa2880c0c00302260382108069000020380c135042f2005010310511945d0080740c40c1e82d03880120f50b000032124801d490701440440e03600c1d224070700d1a143c4008400003c01640c0110403412819110f50099a00030310450051085c1c0ca80325550300c1d0030711450904c1c0700d21650021231400c1000c0c8401d0900c9402540c05d80e5031100c464200341044404480e9800040c200700032503008200744006035444644615040018280c403552034005031009001141c4078140b00e0303c0341103158440020103d0000d40110343c0700709410f044036024440c000c0074024075107050340c20b99003034480f01c0845070001000304000c00d20308640b44101d41c14030b000c1142d40d1081a40c09140360380340020034040103030000704840012104558a000e46507a40c400039000d0710190210710080a000c219241551b0303000a103950290a800103a81c000c242c89075802d1905005103425a80e050381c00300c0e1824100c010751442c4580d02c02d805805516044a08465121342d10cca5002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 93600180 1250 93598930 93598943
    0xd09021908150a060501122d0501030b06010f09030b070507061d060a020405010903150e03070b04050d0203090f0d03021e0c040b0402070b0103020108090309040c0f1e0807030e030d09 80
    0x1090b00d028040b0001e41680403020407010400d40e030500000824103d0402c4414610941d00c0b00509101c1401d061004048503100d1903c100385602e21072200d01501c801e210803540c00c510400407510540c080e011200848650f0385d6040c08a0346591141e605c1d081300544198140314040103020007141c218000c0080344000c01002c0111001c040031274a15250008010f0b01120740f0501090007260307400300c0d0a0f0111b90304440c06404491000e03000c18010145201024103e22001890008105054208600c56030060302178030300340b203a195401e07a203a102d41c07640d05a000b07018210008042c07070300c1404c01e100140648100d40e0100400c09086601c00302c0307a41404241d40c0416a07001941c40c203806825a44103041d982541800a81ea95a100303125040c0030003410712001c040041c050840c20000d0b02d900c024028010700c07000031681d0000d044100d1004601c400262080940100d03480a4048295141b58595820082e942c88540890007428486020039050108004800003002d40d0701403e100c0c1c074013405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 93601430 1250 93600180 93600193
    0x3062d04090f2112020d0f0903090302100815130f0507180b040b0306010e120106030809010e04140c1303051c090807120f03030603080d05010e070509060d09021908 72
    0x90400080001c2d031101c01c03001e0741034014241c030030f503005040c81c0740c4003405135001d6200d4401015000c040d000e002e451f100907503d0040030000b850740c400301d080d0440f0f0090b01c40f41c901c0c003180700c01220741c540120340c1041459054000d41c4090b0401e820420b000c0c071010b900c000752580104904206940007913400c40c00141e010030f9100e4105405038200340003090b01460542c501480d100700400c981c0030040c8140c0c1408010505240c198a8190480b070307980513000000c1281ca40c40b494400300341d4012410345400a406d41510842c0303414148a54021814805c8505075556111074190708140e00041a242540c030400b080000011000c100985540326031005001140c91070880081c8807901790350010002da40708403000c0042c81e8100c82403200598100342501014001d904040c0c02400c03d99200400161002031810300035030032075014074140e90448000b0b0700540c036000c03805c54142c05010ba038135a000380200f06400702d4034549d0303002c40c060b984050500400100c50f500440018820b82c0d100704071680061 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 93602680 1250 93601430 93601433
    0x6180f03030f0c1b030c12110d030209061602040b04060603021b070e0f0a060b0c0307020a05010305100e060301060e01030503070b06010804080901180504020d0b0103050c03062d04090f 81
    0x14014800d2080b416801003101040c600d000614540d0a0003401c01e40d00300081d52802414410124049219008091500c40e0350352164028020f1411034400c5003940124410310070540c1c0303e4002c5650084e00142a80d003030541c6030007034420344c440340e0a003241d0080e50307020841c990f5202c5020342d400501c1542c40068440d0307100d01c1e04603064181d841341d4200f82e420021060003a155403624140d044500c040c603006207030f80c6103443c0200401c1170b0703000f0300829a40414072182c131031800801003150324400d481e00c3c1941556000194199074003034801c803075124414481440490381842a4a500102c0100003040403076944c0900c400c2e00d03800b0f0704151000d80001a40700f0912416024554100a00b0718100301e4616068480e0180c0d4004c1240250400034000520000001c030b404562000c0c1000800440d0b440c2d0035144900014640c44005601003402c2800040ca40d4825070241ca10992000c1c1000441491442c01c205218422050801042c00c1003c10500e1a03107480c03083c0604140300c0c203000a08085503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 93603930 1250 93602680 93602687
    0x220f060b03040c0e040f020405480a1418150708120702010207060516030e01020412030c0212010504030903020a050306060d020f180c0d05060a061b06180f03 69
    0x40e0032600020408000348000510210f140808a451103c026030080e1a00d182c40c0c8203a20b80c04d20081d40c01801d08003800302c1407045d007075141c243c849210110300c03002c1e07040605079441c5d0746184410035154151900c002040100c940040412030702c10726066643c5c21881c2d5a4841c1070b001205181c442400218500500d418000c107a01e010340ba102d5445400c2c000103559007a514481c62760603500303080c109004070719083d001350140c90080b0b90000c401d00c281d03d011400f4404c1e0904001e0b244000900b0628424804031040c421581030700c03607505051071082c400e501d040c3c0300c0155031041240c10078401800d0b0040c0120070720410b030103140710340d07110783c0f04620318010019498000e82041e44260080418080300d0303038400821014403136041c4c800104800d12040012803202c01d40000108100b280410022142d1508005081c01f0805400c104620386903c0144142510280218804203049041d03400c05285001e5404410b82c0c0b042402289400c00700c5414040255404c04c1291079000310000391080641 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 93605180 1250 93603930 93603941
    0x501020d110706050a031811090c12040b0408071a06010905010806012c06040b0c07120b0a0504110a0306020901080714041e05100801060201061208030a0b220f 70
    0x254900481014007075640281c89594038880c000901200090482c4990f01940060002c1c0062001c0344440307001c2d40c00c144a1281c010a1130520030001c4000050300ca65021080e02c0c0c0b001441058950180d50b00d95503121144405441624084414000d4900042d4208110740c000c020741d050404c5181803032000035251420580105040c41040c00c108a20360340d1000c1c41084644486900c1c1d8029280489206641c00e03880c4806a000b40c000600420398030300400c000c04007050031100711440c0760390b079440700356080c0c085400007481c03840084c0101d08200680c1d08055000703400340300b10b00c040b5200500000c2a01d1456481100e0035500450041055030b00700302c0143e805000e506203a0440318268000e480a0b1150f40514900003008a000148103c000360510020302000f501c1c080203006e10a41c0980300c1c4000b440b801d4010340c2480b1001c142c8000d11008090200d40c00301705d407030440e102c5051400203001b4030440319400141c5044160340100e80300a20703291104000c0400034000c0c98129040d81501e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 93606430 1250 93605180 93605203
    0x30302060f0412030507030f020c03120906160807050d090c0501110f0303060d0602040f060903140706020a02040222030b07110a02060706020705071a030a1b0c030e0a03020306010807050102 83
    0x907185801c020109034004000c2e0f0340d400301803400040554405500b40c0086c5440c4900e1a081c500c00b20750080302e05d0f0008014100900c488060b90360b10b568080c10146e130b42c02c0c1200d0142900324509041c1c0d100300c3c01030f010325801510a090280c10720300c99007041d4046800e0304005980b403038034441c0d04028075608508401d01d030307407a140c01402e030491460103556a20311011701605d014141030520300f81070041c9541500d0161004c1080225120740e9480001c21200700307400240c5030705051b1201c0e0b0603c10000940711080350b800341c000c0e1031602d007203800f0480250080c4080d41c40b400e0034045c03500b010190b20402d00c00070310311030310b20b282c0319080054009041c80c54003451610107a200d083e840001d41c2d07801003641c003016400100581e403600344c1e103070090500c69190300c80c0c0e01204c200200ea032071001d80440030b507105910b048410411f2140034145104082303202d00d00040800d40301a2200e0200e40700e5000da00034100080d2400143c40e075290b01007031a10390240c1c000b46042d009080180301c01c3d80e043c4240c84c8502c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 93607680 1250 93606430 93606451
    0xc03020307081608070e040e030309030904061217070204060e1f06030b18040503090d0c080c0d08120a0e03130f0501050304050318011b0b060411040f030201110f031303030206 77
    0x31000c0120140c01040094851340a01c100d4070a01c03603103542d1f04c0c0c0001c01c117200c1c01c0054907200d0034404049941da4008040d107900c038500300440807402c0b01041c2541d000c0140c0203034000300506800d807056089980300e10826a0083e448510108400d043e04580a0107408030307107851601e14030180d811100c44140f0390010700815003462000460350707407602d602503165804050b1010540d00c442c41c00c1c80c5540b090800680e00000a03901600074403050440030411500032000b0f6442545010b002c008014100c841c00034208042401110200411004203030f41c0700e001440e0004051116401c41460b603003240c0c0072030003420264001400302d03d41c840c840b0b4005203000c0c28518214106990b6840c0c40b4003451907a00c00300c0c4c26403800240540c0c4103820804c030580700d0504030503500c0640c1c10101c605070001c46410340a2410000660150311080d02101c00711905a01c1046455003142e00460700d21002c241c144100e071090719008a041002400141100b090500d0135280d130910f1468042c0c109500100001c151 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 93608930 1250 93607680 93607711
    0xa0902030108210c0604080301090f020406081906090626010c1403150d200a06051e070215040e1503031803100e07050a080109050c0103020702130c0302030708 70
    0x61100052580c1c60026540080c028020140004540e00c2c0213440501d1380d81d215100a1006110b103420085058422041080c0145115407200030b080e44518492400060034070707000940155819101701c3e01c44040d8820115503242d13a0b4821000740d84091700304519040c145146c0140c9807a03940740290003030802600030f200d0540011000b0f08a480f4100302c0210f1710900000190420039584001940c800005211410440081c00d024108142d020074000d079455207140565418540700350440c0c100d072856034440f40740200c840009503030081c00ca544048283e006001500060352014035182c02d03c000401c0860303c0340c0c80c000b41301c0350350034010f00245400d1820301c440400580300031044420001e42040c2e540e40c03d205030320100c0e1416119659620b030345890180842000e034400714a00c000c9643c1110000c043e2611260840c1c22103889100c020b00c1680f100702002c1103540030350050b185903400106440c01100e50341d0001e40c00c3c0e0b91960340d4031000a500204100110740c000310619000340204041041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 93610180 1250 93608930 93608939
    0x30601030b031507051c02030103050109110d0f0210050d021602030d140706021c0c09050111120d05090309060403060c020d09030503030712150e090d02010c05030c071109040f020a09020301 83
    0x81040c0604030b0002c100d00006e85034201000a0810080003909a108568030760b503a0802c2402040d006030100c9044101c0c1004080918009130b00364180382d004204003c800701654200000900180c0050092040034025032010000d00d10140124480315011194070303105a104150030521004005c3c01800305490030014241c1100d400c0d41e41c0c06500c00788c0165076035025058210142c002d24844116241041c04c2e040c003244c2c0c01807a4500700c40080e02e0b41d00c00843d0f203004290721541242e481e004030340b205110b1098041d4080d003041d13030040d400d00213403490701c01101302141190344950000c0d0f610644403c804c0f001c030703941001404510341c15840c00d90481400c650f01e0070b4a0740b1000d403ea030200f00c0c03040c03a041441012544040705107024a00c0340d40781c803680c68800e5040e8035412290350706a40a06000340809a0040c01200045502961107925543e50811140030039081664252882107042544c86296201c44210074007590103003518107500d00c0684104002c5803c250000606680148010803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 93611430 1250 93610180 93610213
    0xb0a061511010902090106110106050609010c03080417070302030a02060114060406110115090c11010c050a1b0b0126010b031207060b03060411031e0c010f2003030601030b03 76
    0x148034000c0d1070300403044018141498054100c41e04080d502802c0b0400000740c054100f503455903d00c1c20140203000e04c07a6a0020090360380200ca05203070124100000202c002846850440e61007440740d0226400c190240c1c0207561690131151003100584d0001506905982e0100405401880044041d460020404001ca111401948142e10522000900310260407400b034104c602c00569190032110781540d0703448424094101c4e01c0019000c24880301c0b01d60f2010fa410300032030000702c1d9030391070355440c00c00442c0c011118031080e02c440505032031085401e40c0028032802807290007448007088060141400c441c10751001d038009100115031380c0c581960b4000544000c220001c2e0310050f1400306460b00c0c107a04102002e400d06e4440b50794036025a4041108010b5800d05090541c0403d80c111a003105c6d007103148001c00102e00f00701640ca036106182d140c1003584500341840d02861185032001c0c4561070000d41040718002c2040031440d41d0400b104218043d64940320f001c1013180f00700c004042c807404040030300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 93612680 1250 93611430 93611459
    0x4380405040507030f0e07050a090603170703020a080d0f0c0806010c110109080715170c0f07080c03190e03150a0c0e030a030e190605030610090807030b040b0a06 71
    0x21401980c4440c00260450300170351060b0210703007104200780510441460066102d0303c0b2401154440c0781c0000001c101150144212802c2d40e500103038281c0c49a103c080c40400e0360304009401c50451186900381e000103640741c0c010306840c00030782c40c01003890020414001c0540740c601403000c0810101071708012851380c1c08403e4041480d040748211081d0055140100c840500e19041500c403845043d10007c0d41070341070909260600e18540e44d0201c00070100307054150391641a184c024100006018990f0f80700c0c5a000180841803041c2101c0740f85c5905000040c1c05c40c1c000c0450001603080058000001c150000c0d0041c001940440141009070758481e00050791201c003400d4500001d981d4801404207038000c0350520700700207000742201d101c1407a03841c1c020300c4180c1089503a80914074643d26900a049107200c01015515a9210141546d48010600400c1400400d035075003008988540051a140e06024100141d0300034002901540f03010b0038034041c0201c000c1c009069040c5090410002243d611114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 93613930 1250 93612680 93612689
    0xc04020c0c010804020102070503030c030403110d020a03060c02010f1d0c030c010c060509030403050a0b012903070507030e09070f031415120a06020a03050108011b050f0c030c0102043804 82
    0x10f60f00903161400104e01d800c580c2d0300069054440020395240342003000020704101d80c401c503422a1000010000c2c8180c4003801d850003500200005800e200083c0325421003120181640b00000b501c00000c04198113940d031004000c1702e41c44030880c1d00540120240b102c00341d0036000b900140504524840020589804000c0140202c3d0781d5002144019a0900442e402107800c9021151841d445090080c41d12100788102d80c2420303016501403036031004804001c507228024000c0281180e581c1041503441c0c4c0c0c0071070800c40802070703081421080f60f035a60401a00952055035603101000410801400b02d4a20021000c0b010b04031208100c2c00d07608042000c0404a015101b00c2e40e911040481d4034604404c40d2001400140082200300da07480d410307400603040355030690080c04002c000c200c29080c00380860908030b00048040003400c8240d41440010003011460b0700840b403402c291040c84a08980103904014201409601840f145940d958490840c83c1c0d07210412004501c88540314654503c5180309 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 93615180 1250 93613930 93613937
    0x703030e0607080913020310060905060715090c090e15220f060e0105040201080606130b0f0c030301080a02041518051005030d020a1514042a0303030e0c04020c0c01 72
    0x2d40008200c0d03260240e0f00640400f8054a125440700340360300740650003c90322910450091180000c80501c14443c600072181c01400312440c1c000c440e1034518032000ba000710610216114405c540000d192000e1020040c0030074200000c07900700855510317040440c1450b051070400e03d0032080c422494009180190f01e04441c0d81e40c0202815a440c001d4220a00d00c0d8002c1c24941ca0000c0310149401c0c1074202c141300c4d5101b40da49941940c5d0301c000300040750003501403480000c07000c1103050200c030340c040e0000e107001c030a150500c509101d03100d0007180c84c40d40260001155600074880742e50450406004481e42c9540b10340d94100d40c039048c1110907040801030508483c04d1074a40b000315000b65009072510002d01405015580c00101540c030107552102d6041080781c80e08900c401c0c0c2e14440615200d44440d625004842155a4641c0c5d2680e6180b50f182d0707101c07640111100c03074203925000c4d043c00144000314841d0302c022560318074084a1074100129105181e01450041101e03030003050011484180103402400c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 93616430 1250 93615180 93615187
    0x30c090b010207030b0c1804110a08100503070f050f06190c031806020607080a05090705091801020c0d090801020a0e04020d27020a0f1401050a05090a030f02030f0703030e06 76
    0x100d1800f4210f80c0301400d591104c10600102510702002003c1c5440001000101e0302030110a000881f011100c515040078004d114802036244510511600100354070070482e031958032207002a0a2200c00d900030381c0c0c102c50f0b605c020002400c04c6954100340e581c00b1500d584c10310307000303803612141c50b10074010036020000c0d02c0204000701405100e40341c0b02d4844070044210380303d07102c0c1c070003035501c6005035419000310b03070444001881c130b070614040d1920807110007003c2c2c440c880c42d100c20300103100780c040c01d006a400c0c80d05d41200c0d4a41001d202074107089101400030700c500c1e0201d00000d08140200e0300f042c80542d004018803094190007907240081d41405690059031400700d40641402402016124016004945901c1504a052000c03a4404034000c40702c0c42c820694861501403413001500c54036012051000b44c80c50198043c0c00945009881814028500088100044d40c00441c0d42c20031100d00d405009280250304082008102000d00c82c001042d11a045803809070042140e8517509110f080d001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 93617680 1250 93616430 93616451
    0x10503240a020c010603060b09060a030507050f130f05010609060207080c0f0d0c0303200312010504050709030611071221020a0c05060c070506060603040f0b0a1b12060807030c09 78
    0x290b0440d110722072910020045a501c0b80b9020b4080c0c06650351007031195440002181d094546003a03500c2c102c90b48500144009031400e0140240f10820003c6075070300031180640303101d07410410b0040010b201036091b80006c180d030415401400d800c1c016004481158400341062140e41c8000440b240e102ca400c03a4514030302586103000030130b0140614002410030540d0b140000825410401329032030900c3c0803a6412500c0c03101c0c040e0513500e000b2031100340c0070b50328170720010415401c3c540d1000c0d0b04000c1c1c5207032159400e601c94030307501c00341c8a0090201c0c8512200182d52014840e01405810492001c2d141801244401c0ca00b45580b02c0b281014009040ea400951501e8880c019500c4502035a03124090311400c0c5070584803c061a0804001661207024210020b461460001e08580c4141e0b4441c3c256000003009480ea8005040000d008031060381d50340b105000886000840503444101d16603c07543d440400c034001d0303810b88200d607001292940c8841070520016030101400c0c0150b41e450000041c0c0303440b03074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 93618930 1250 93617680 93617701
    0x3020309091503030c0d0306080102090d0b0a02091206071403010302090402010f110f010905100501080304090506040f0203160306060e1309081303050a050c0303130e06040603020913050601050324 86
    0x601034550f0f00d4800060764145840740031400d21501801a1010080c007070780c445d00c80d03090344905d0f107400b81e000d500100850000f0b6031004016400400d600801400c0c42c80450206550444900c1144801d0784280c04112010b0350041403420980c142e4041c642c21545940c1c0030030744440020300001d042c003185103000d0291030f01c9410b401380fa000700d1000322840075203c42e40c0b041c000c152990003034a8034041c0e046003030741c104018015207040b24241b40085241c41d24040e070762001803070060a4154480d0720384900900482c0700d800030710302440c2a11204e8201d84c18080300a030451f040b9a004a00780030046141c1243c81d03452510503180101880700101c0c103d0590b151a908610540c0c4201050291303402001c0244a40060700030500340c4100d00311034500010104041d541d010380c4146170404000e42d407003840203003c40d448041e0803407000b40000c1850790302c81c2d0000f0050a405c503440343d55200c3d021580340c18040100130850040000b9005000ca0040300d508107034040f004a000880c405819401007100d42c00c0d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 93620180 1250 93618930 93618961
    0x2090406051902130513020403030504052106040b010e090a0b0c070204020705010501030b1006080f04020f0d0204060e1f030203120304021903050a060b03010203061f0c08030a05040c0605070302030909 88
    0x3181c0008654864413444401d01810190140f00e00a0108071880300c400d0b0403030310846090741c1d0181c660a040510340400c004064803000200d01d014805140c02c005401020030205020703502ca1000905039604281200c02c003e64000c0900b005a40072240007030101d404e0500080d000740422098594510301130020a020f40704140d1300501962914000006015581500d54040d030004402c0c884500e03075403003044a10907001da0f4062102c40ca0f12000c2401483c05801a600029001d0000c105035496500004c08035401070f031180f00109000c10030400c2107400500c98402440c0141000001d40341540c01280d541d01403201015003405001000c07805544d152201002c504040b12211405035880b0318101e621403c44040441e01ca50a14030365549526040c000daa1140c080680224100214598065081d41000079642c0070701008004a0010900c41e00066228050701d01c404501c078149450801408002c1d644140104201800030a00080d40802160030200c02143c150b912a180c0848416520702e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 93621430 1250 93620180 93620221
    0x9150114031f090f0506010503091c0c12080106120204060207090207140a08070c0611060601120e0706020f0c040605060f091507030e0102061612020f2b050a090209040605 75
    0x3000c40c00c2c0040d404103582c00c5003459080300c04003440107444000054843d404169960441a0085554a488054000700035060300700700b4545158214040e80300c202440c0710710300c0c4030b00003d280350006000719a08105a0741d5402e02c8141c04601d41485c1c00402900c0da0780c10b0003102401900001c4503400e0268504101e0090343d00030060f60b03111545032030405081d038130801e400c0300d081c1c040c21400142d4900400811a20311a098050800384d0758440c011510400d9034804158210b80c3c0b106070303a91070201000310101134440c3c0e40040c04411410120603161000600001e48114180142401217480d000c05441c2c0c0c6180c410710040e12944d1440009454030092240000d10340c101003801028143e21200300040d00b2002e030241d54054541c207000c0c09424030300b0550b08010a842050170000382e14a90300400300b10b102210001e04180c0b600b40607089820300300d2400c1714400e86100408120080c04c0c0f103450b8016021844c10004182c1c9540400c001510003400500042d65a00000b61400d69200241c081c81 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 93622680 1250 93621430 93621481
    0x13120f020907120b04050601080703051003050f25260109060218040c021507050c070f08030301030b0901060f0302010f020a170319021314180103060b0915011403 71
    0x510703010200810078081e0f092140c072240d080801100c0a41030601c00c8900030803060b51045c076203a0700c14000390081d15018001c116440a01d01001000c21002d02584444103000c5c0003409845107000380032582d42500848200714528002c0082040344180242914490340380640b070341420404254050040c81c0078400602643e000141c032185940450311100d05a44089400300312107000000e04903500c545010500c246003200001184080340588081d21906004104460368941c440011201042e03143c0d0121780b06500100060081100f07180846030f00c110f0a200800c045440c00300501060210751001030305000c00d200950300b11903c28488410402d401000c1c2d81030303e008903043c103481a401151034410f44075898000801d01e815900880f9142d14444051540c0613041805030303040410414145603100c8460001c6103001c0099081e05070003180902c1c00052400074600900030700020003000c00031a4401d0604d03203c1c15a80000324481ba621146081c01c1e22035540320030b005040c0003110f80c6001d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 93623930 1250 93622680 93622699
    0x6200312070f021e07050117060306060f06040512010e19080a05030a0e0105250906080109050a0209030d02011a0907080f060f04090602091905030a11040f020313030207080313120f02 80
    0x6003070001170041c1201d8003aa00c404c0c00c2038106400c0c078190300342540c5459142d00080003060307030351503c150a5440d4400c0180140c1c9455a86d0300000c6001d840180d0f60b9006035141c102d401803100d010b01108009004420307c0041e452001c1d030702e90006210f815042c1c0c0a01002002244e00c3c00955800400004010002002075040c00000948410700c076206d4a4001d4601003c000c521611920844003210000d0f221910b041c0d0070070f8080000b6002c01010100c542e43c2c240710344401503074100150704082010380c000090245104413031644c6003040030071260203410508244403840ba0304c44034580c0d100048250209444d00c1c5c410019403220300a00c0d6035035115040c29481418425540e0080c0750050044980070908552600c14022100003449507640c0b680295141e030300842d20700b58044aa100c1c00520003e10642001000d030f0883c0c10964040c20403030600a01c00007055010450100035140400040d0b00f842c03a003020a1048030308500a541c2041c00c02901941004612101e0300c680d6903005041920 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 93625180 1250 93623930 93623983
    0x2090f07090f12020a090606051815131d070507110102010e070617090a170705120f041d040b0703090201140703360303050315030706200312070f02 65
    0x500126090709a1198089110006080b18140700310000c4507882c1d12040d04040c1c80500502803400390b044840c1e0025540000b0b90007462620004005442c15000142e07140c604000d110b078dc070241141290a5000b9000742070114964108003965055070707002501d80c1221544900407805468421440c005c44c1c0300b00744021070300d1904207a40e4106c0307201c1c03081069529034807040e2069907840781d00e81c00790010214111000703429108000400c1114000d8084034908510903005048075880300c52030450003080441c050040c0341006a4010b55541040865008d40c109903d0344100310501070000c1052680d11407854003164041c403082c080b8a05040c050640750071460502504102c00e000c03144520051080030280e100c2e1041d407502000081c2d40c10140d900c5c90456405555035400a4200c1d0a2030b5070050550600faa001c0080c07030003910b4607a541b661004011500c2d2010180c0360106a41036130801c2c0000c0054092803480c29501c07200a20301401600640207007a810310800d5600c400040002011801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 93626430 1250 93625180 93625199
    0x170a050703051c030b090109051e1003060609090201121503170301030201020111030417090d06292d150408071d010303120b0a090903020601090b0d02090f07090f 71
    0x4003044200081d0f12918070380e012046088a420306901680030000c040140300c0c100a5a02c0503a004415458030034510000080745001640105d60a880041c0e41c40c500707004110482c000c0f80018001218107011f5140c00e6030001e0b00e40092407440300341c29541d03240c800743c564a200c050f9000441c0c1090500668103620351840190350b100740000c0c1d0242d03007030600880801c26080c041701c1c0700d80e8003c81c2651030203058504103403007544440b042e2a4490404401100030524600c2000c0f2410042480b000a0005004202c00012070203000d003441081440c045422007a08090001100084205a0b5a0031034500c00020381c100e1010346210a05040441e01007034200000900b50240c9800850400009002440d00441030307c0901000700050b41049180d03003607000c5a003101070305c02d0004055072045500c950f40d10085801c200d80607001648020010042044548203412550106448240c82e5004076008904642405800003100309140000610307801c0c07203148828040c200100404075001d83c0c2e26081c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 93627680 1250 93626430 93626443
    0xc01110a0c060f020d140a0c050703020a0b07020c0a150e03160504020306030a1e03030605041104030212070e07200c0a030201050706021218150420010c0615060f02060c0301170a05070305 82
    0x502c554a081d408c0c3c030303029001d2401e0b501c0c11a855402820f00b85a59503403c1d1400202034540e400394803072140014420b035200c140900c09420082d00d00c014002051100034000007080d03180030300035003100880507110200d1070407d6007601d50945000daa03903110400030901d000300b0f07414080e02c2a1140600e8105e041301c1140c00181c0c850196405110158940702000212150011840d184040030003040006080c56220050901482400c1d1039516903105080b4203203910890f850350016041c180d4001c51284400955040f820906d4010f00d980810718000c01c00072101d0f408081d051010104503282000141c0d012244050840c2c4480513060402002130480000038030381c0602c5a008014032080c14ac40905030b01c910a54011211a08044180d82498031040204040e40d0401c207a40c20b04401240032401030f0322040d41c02c00120400c403443d1540050501118005a10840d04100f0611882201c44416a4199881c007076030288002c0317111418034642243c0720b0004086000f81c6000106101022959 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 93628930 1250 93627680 93627691
    0x50607050c090f060901030f050f0d020c03070609050303070602030c0f0d0f11090a05040e240601020f120a080712050709060e0f0d060e010b030604080c01110a0c060f020d14 76
    0xc1054540f24944401c0511070226160741d040b0128900400c0401c21900c0d11007411070241e0b050b00d4240341c0c200f90980c20a90030303150150150740903010010782030030700301303ca80c00620b400d2400a407c2d90070140040c2d22486454005001a034012000c58403038480c038011900b02d00030f103000055440c0034040d0800e001d4100902240c600c0703490290760b01003035100e40c01250000c4600408546000f400c100400c0001d05c000030040c0c1d07032032140108072400c508401d1403030900f003109034071810007905e0490002490590b015580c1c44042d00001c03801410b030308192081d59080003203810103418607a500d0a0840e15007469811425050341400e00b030042d41034105401c0002d6551a40e64121280b1803041404604024540c4084d0015030f0803441d02c0110355a0740c403c0315100d11040c0040b0300c1303103445d0b00041d1910764250f0742600c3d134003030004a241d0f1400003403103603600104101d180c441c100741f40310002600c1000c002d580030302025287ca64100920240c1d0381105c040c0c10402c8410003401002c0013038007148110442c0c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 93630180 1250 93628930 93628939
    0x30c0d03091d01061209020607030c0321020304060c050f030103170702150d0b03030a050d1821020606041a01050304060e01060803130b0f040308070503040510031a100801060c0c050607050c 83
    0x2244550750f0740038081c006ca000c0c0c014120510700b0360103503030441c0c0c0080044010741c1081103003464960010721031000d160701d150301c254006d0707140d0415081940441e4900c0c00392000740082000078040004410f015681100c4d0095130000c03401191100c001054465000000c2d4400c040010619500b41c440010f0320390f000c0120400c00c41c5508002c24180d903446020300400c0841d08c10f008064108440360400c03603100e294500d020b014403146a88000810f000f4040d00d2030382100c1c100d21981000c0d4108a100c0d8064000c0304c080c410301401070009c5460910341404139040001c00000501030092517008055103803a14002004025510260152030303421030a11b0300d4060f02c900b0307000909004074005843d091440d410242d49040d15590300c1140542c4440760886040c00240400220341d503590700c00240015241d10b0100d00050001c0040c02d1000c0101c900710300c5000d115140c031101a43c001a030b94103441c89818050319448a41c2400b4180300003580c001c981c0600001004010040085005a40001d0584 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 93631430 1250 93630180 93630197
    0x1020903030f0a1b03082403010c02030a020d09030807082505010501081501080607030525030209010e030a0f02040c1701030c0509010602071401030f14040f020f01030902030c0d03091d0106 83
    0x2e940c41108040b40313070180000d0b07819004516128540314004045841204410940046000c0882c0c250780f420b800c0c2d40050703000440da002c85c0b035030103100103d8080f44520785008081d042d513443c05420700581c0f0000d820084003260301002c40c0703103c500c44200c43e00e14445800c944c040d02d241c1140a41000d0040d000240242c075030390f03407200400c1c0300c020f0306035034400b03025280c0c913594640110b0060400603d035030043c03424a010a45d1484c00d0306c00400c2204880d54015030f0320352400d8005840355101148241c00b941c07020b0900e0000c502e54484211045504030b8011400100110b000c603090502c2280803180386207080300000c10829581d801608864040d0b030803031030503a6a000305a0304c44e03102e40310b07440c5107040200c0004400c2d8800e034041c0000000c007950001c5d8003145040c1c00c071450a8110360480742203a03007015034410b44c80c0c217123001041807100746000c0c840716400d0340c080307502c2e865000704c1c0d203002e80940240e4104041c000d041040150164044401c407446c8032808006140303200303200301c82c085410301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 93632680 1250 93631430 93631457
    0x622030618020141040e0c07350409020c06060405010e011401090f0e040515090307060b03030904050f070314060f100909020a020a0317010303080103120201020903030f0a 75
    0x31980c140241e50141c4650500d42c03000344801060044902c04994102048070502031604002d141d000f42d04461901c00c070780c445003000703900d002890010b4030070700c60f025050151500044030855095584144400c4000341015060360801809a00040c02d150095002c02c0124191140f5030192100c18050303811100d42e81c0755001404110b0741e007130060b02c0d02d841d00c140c014001d1454801341140485010301d411905142c0e00c5680c0c401007051034200402244100c0107110038402c040104c0c0482d4a13199004103220700300a00304642e071344140700340100302941b100780c001ca542d5010300984181000150050000f80307098001090800f4040f20351201180c0b401070310820b0000b0340311440348108000380c41d00c40c0ca480078400b040300d420603100120301089007402011518004e6030000c0e081c2e900c1e154008102c0b111076490041c000107469014101002c25000042011031781c08034102d41102d400164103070300610880022030191040c060019098030001420303842d03400c40c200081c02c070000300e07035240c3c00d000901 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 93633930 1250 93632680 93632711
    0xa0c05010b09090d0c0503160b0f07142215021f090201020c041a0a03080c0f031e071b030813061d1207082a0a03050304030303090206220306 62
    0x241c3ea8040a903000c05014160b29000340180303001c090141c000c0b02d0524002030300421107500c2a03e41255404488001d001120b101d482d912600b01d903044c01d0900c6580700f00c0203000f0b194000c1c103041081150000200b540d1901d24110f0003409400d00548209070180610006035a0b01c40c0c5024a12119031a04406413003400e070342c402d203203130154140e000e0a59101204104000b41c00540240310811020014291030b0341e0343e5012000045104904041d1100c0400b0301560921805111024858008004500d1100c0c1009605030820101c8254a40c840cc01e504004c03c0340b201c41e007610095032031644404024801075002a142c054406147c21200070b444600440c2d5079402c1c01c1240c64418911500309609207881082c00000424400840d0002d40c0d5400c2c9052a180c44a0341000c84080d0400c20541180c0483c100310381007220540f43e512113189982e88059407071007544005020150717500311440841d580c0038100d4260940c060b8010b629017003c0c1040d00513200e1188011103105242843c200700d040031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 93635180 1250 93633930 93633949
    0xf0207060806010e01110d02010515030c0d08030c0f0c010b0a0f06080411130f020304110405010305030f07051c021c030b241207020a050c0a050603070f140a0c05010b 73
    0x6003a601d20340a034490a006640104007084594144100343c1c800c1900b280c400c100c1103a40650701d40c000306403170070319102c0c035040c01004084140c000e4209400003c503d489081005c1110360f404070801d6925507510480d40464043c840c0403000f0000000f0300203261803415000040910303011120310301a2641c60005042e064403600c9080085a40d09001030049224030100010481c00a00840b1101c0b00015000e0225800540c4011120781d010003030005000102c54070324506c8106036070401c495411a00d85550724018081c4041c04040001009402c004090140191a07941200108500c2003410400707526404c8264000800c0c01c1403040b0420310b02e200e4000c80c0e48a00340030b460860b41b4281001c041c003260500c078280001003102001641c2c07940048181091103901c0c2c1e9409019026100c0c504241000c05010607a4030801a4403030501ca2540c0300c408403500f0000c0c0d030034044c0070040210003c0d0794401c4110005041e43d800401c02d42101504005c0940680c0c1c4100c008000d00344444040010101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 93636430 1250 93635180 93635189
    0x405010f2c030a090b070c03050706090e09070617090a050109080304061a0a060c050102040f0b040e010602031c02030a1401151202070804030803060312030412030c0e0f04050c0d050a0b010f0207 85
    0x341a91005c1101c9502c1c400184040c0307029911103c410b540300d881d0740d072816146078403200002d05101310170040d41211002068010402c0000313402080d1400100400350b0001050440c43c100d542c3c00421804d4004105080d036440d032050085c001c050490400b100c2030380040f241500d02d42e0600c1c4d1004044084c401d00b541c0344203401840340c0241c0b42800c83c00c0b42d0051000d07404455565007040046110800c05860300b00411100624035a511b003400a1002c9250040c0d010b103056501c00e200140c844140111068201c6110f00c4005850381c0d50580b056002d00032031030a242c0d600d2014400072036505494074a0000c2c04072103454025103520340f0396030b400407445a00b02c0904140e80504c010b0000035502002190090801000c448042885440224095100791411a41e82c0b620700042c0c43d15a80500803d80d4003050380c1800f50920020801051300700c1d26401ca541e100700d544a0008642103141c0c000d444030f4002d5081c0402551174224103490060400c8000c03540415035001c10f00d80c1c01880029000c0644 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 93637680 1250 93636430 93636437
    0xf040b18090703060e0604060c0903030206040303020d060b03040303050f100302011b031110020a1404050d0b06150d09021810170703170d050114180405010f2c030a 72
    0x285200452003440003006041c0c080340e40660500007001c034169000d50425005080302a000e2400c0600c0c1290031516160407040910411080030030100350044be01642c4540c040c240940c1e140c80c1d10310254000d007929001001040004001d1005042c3d059000520440b04541800a01c1d00c41040d9030ba02440c041c80300900240600c450140e03120301002203034400c1440380c10300358180d800301e104407801d24460b44055030b459940072940034002640405500010713202d14802a284c00c0c1883c0118004800c00301d030280202030610301040544d221201c01d00120400b42c0344050f112403003806040c028083e000403c0e4801c28028002d01d030b80149001a842c018038144040684040c60600417a0804042188000742805160400804540e0300386041c503140c4002e18046948080d1403072404111401a0849220321660703000b81d901c0b03030326807004a010b00c06060a201090f59039500d041405020340e8444824018142801c01d03207481048000c1c201c420703003080401007120b40c2c0380c07481555074042c15002c0c0000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 93638930 1250 93637680 93637699
    0x319020c07030f05010219020d0306060801060e10020a05030307170a0204062705060a0f080702160b090a180603020111010903050d09020f1807020c030106240c05070f050f040b 77
    0x51041c2143c50079003403003a00090304029032820030322040c4102c2845080503801503502144803a900d4071408015281d00d040014035541070080043c032070600c074000c82d8001c05460b2101e01c1400e008110400d511580807040340c1d82e03803414100040240c2900140311201100841c0402c0f00e01010740251815108507036030702a08402060050f180b1041c2000301340c952810076190101c0d03191551001012101e40545a0703030744902c841c000003002503900802100454010005c8203100300b001801000071a440355002c95110152040018400c6a017a0f11054130039043c0c00c0003070030145003600280103d90003600c51001c0307815002e6015098407008840180000c000300300303a02d03002c00c4c0c80d88107401c454006420340c0300781034030100801c0c0c06004007295408420115820400c0b0f032035040259106650b4290000d101007032824001607034802400d04101074071060145e500381c1c2d045c441d0740740d014223641160450f452942c0e500200610b905850281038004c1070700080c4401581054000c00381708a60251841a6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 93640180 1250 93638930 93638933
    0x1a0102010605010c1a1305071d0603010b10050c07080712210504030f0c05040e0604051207021305060102030705100e120405240c1e06070f0f0c0302150109020319020c0703 75
    0x25030110041ca50703c1b210f4260200303c80807031403c00200c0c01810700c003801110785200d401c0c100c3d10710303403401000103129a0504441c6051a190a440e040d81c2003018201143c41c1d1000340c4001e030500440303800c21240340c494014006040e12030000e0003c07010b4002da0302c0c0344c2c40c43e051441c5020313207242d40c016680104030304100410004d90054400100e107801780e0110704000c1c1e01c800001e000c0e10a02d450950b124bd0005040c031041c44030900c990f403010134807110f52515014491340407a1790360541d0500950b10b103640748006181640207200300e4010b0b0707600a059498403440c8000070700c000d25110400c40c7e10780c400c1d0407400d03219204c00c1c0b044030f0035200024a00d05c0728400c1100c18003a0310205404906160740b00740082c420480301000000a2000c0008041c407000074141c000903e00003006040804012840746400d01035900202c01e54140420303468455000d02ca903040070f0f480c0018403260385013003820940c000640c2103416405103029196407047c04022000c541240c1e0300b60700450300300c4001380d04014820070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 93641430 1250 93640180 93640223
    0x20106050d110a030f06090c050307081203040c030c030b0108100b06160203070306050901020903060f0f07320307030b040b01081303030e0313060f080702060705030405030d1a0102010605010c 84
    0x2200c002005007000030081d100c0e6501e405c0181203036022130761591a00f00308000c022110070f01001500d0250000d1400c2e0385402c000c1070303071020001070314551420000b0204041c00740f102c592101445d040034140d424550b480c40c16070030f91a001d101d001c040307004e5080c51142d2901c141c0604545840e006020904100c01000303415004051400e040b0303818410104000009549070180a20850001c1e00042e1180b00c10014036050581c010020030038860b1110402005124048005e90095400c0c68581e5104d00d250900402c01807006c01ca1001300d110310030f001804410300d440198807500281d40c0134012030307841d10180810b49140d00c43e01404110148002140140c02401c40b03d00180a0318000c114802108002da080d81d11141c45401c100302ca04d0018000385412841005c000c02e42843c181c5c90928116000039140d0b00060021402c10400001103000d20000300142c48044520340c0082000c0e50302c2d44020b03000240d00d242114013650800300006400d41c012064003000c5900040340200070750466501c40e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 93642680 1250 93641430 93641453
    0x20105070210020c0301050406020d0c0302030613020705031b060618040507090216021503040203010b09010e0c280306140d030e090403020f160302130902061215100903020907020106050d 82
    0x10803c5204100101d02544d07000d0107014013641c0550001031392203404503614400c2e5041280c82c00140f600400501c01941c8130710802c2096514800c2d40141c80d10117900d1301d035003940b2406a0b600c10545010440380201034002c07680030702814085600c2c0000388640d03d032940b40000c04450107403450300508020420042180c0090001945a007001c0c2c40f406010350004a000e9106802c01c05001004010002141001d100d0340300015801c40b824010f40d03241c41800001c800c002003040d03050800c00f02d840f000310284149050320b04403c840080c80c400c840190020014400d6101d0205203400e50100285641001503154922541640d14411400b1990051095849018004600b107100c0c88507907010000302440b0884082980d0b0400c0f080c000e10f18010401008c003030b20903c0300c0c0c2d0b915140b078080041e17951904072a40c04d014a0382136121a42c40040e613401c1c0e075000594480d040410260303800b5450b80d000000d1010b9070302c00c55a0007156114804102d08a4020313024651700b00b0165014000030400c40c0101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 93643930 1250 93642680 93642709
    0x40e060406141c05071707080106050402160303090201050418020304120e0d0318030602040806090f03091e040905010e1e0312040b0c19031a03060f01060e300706020a0201050702 78
    0xc5170000e03652450300704a1807200d01c490601e540c1140f281801000000e018840003003c2c100c406604014031346020000c82c2c0f83c2a0303001401d156858404904590280c0c0aa070700400b6940410f001e8200025181c074043c0d40212800c41d04460440b05100e5064020030b000300d082174010704804901041903400b501c0f41c01500c440c0400400f080e040010004440d40018000341070104085c0516051001440d45800c1d601140c50945401c00d2041d90000d455105008001d00c0960030780d0b000301c1012001103030040510090240c030950030301700500303d9103900003641040746180d40004000e01c401c00c1c0c0c00380d03100c1c02038140462841c0c25100115010480c1c55a00603081803540204a07c0c1001a100e09c0342010500c100c0003000c42e0b280e1072041600c621020b02c49241c01400d0340904128035000c3c000448643c814000d010500c501c124062240d600c401c2c01c044080c4841d50707041003c0c100c41c0881c10403440c5286400f24468071400c2c002250301813021030340c25035890f8181c4030b09082c02c5e80c0b0387c03c105085011008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 93645180 1250 93643930 93643933
    0x606032e0b06070503041a0f180103090f05030a09050a0b0904200301141003151a1308070905100806010e07110a030f080702030a0503042303040e060406141c05 70
    0x31001680da42da41c00621145100f000115a150f243c00c070452400c80010310b000003a54002d1100d10303e5083c42d1012107480c00c4c44500c951103c106403100582c001c2a11140240001078003010003010000c001008000c55a41c5440f8408519610400c00400c3d5515001780360b512441800680540e00305600f0480c00a04082209045444040381e1181c154000341d2041b0340c50030f1556110300682c2010101c42007800a607290134083c0700304800244400810328420551441c81c84100310305407401410031786c0c6004104505583d4620ba4404042e40c0e101c8640c0941c40780c007490440400c1c0d07900c4080648108840c0b142018102981c0b8180700444404001003c043c1413200e0243d810003600c0062281f107002911039158544801c41e1080010000c41000300b46034199482000780b88016038100b000c4d60f62190340b081084000458144600038807404075085603032144800700300461043d80d0f910000e48510410745041103503c1c2d68030744c0070b04003203002c18103940c000607a407822070b00c108881c04561003c00c4c007840 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 93646430 1250 93645180 93645191
    0x204050622050409020f1002070510090e06010e1302030709120609050f03131a0c01050709080f061003021e03071706090d1b30020606032e 61
    0x49a031aa00c22040c4004000c401e00c0210401d044103a51800038180542c2e00304045000343e03001c00e419104510740d40d4815054120200d55051080001c0e02c040c0c030014000801c2e0b07c028010150000c81c80e405410709442d0207000081882d4403c3c0802c4800c04001400c5581120710104c861000b9840540b081c02040103a0101007001d01000c0c21105080307120b040001507024160030900d00b46202c500c141c5000350400c00a1106010000030542c0c00c0c0d5542c20712211001880e54044030062241c0b03c18040c0550a010800400c15080b030744945c00c0301c20a5040d45c4104805124080d200d81c0c04a0790610100b21112091015040109402001c0407102004003251440303900000c2c80c2c440c1d036030302030504c0b079030302030581100d8180910445401843e60310090540d00c00844015122406161943c0e100ca0701c1459982c050145501035064490070171b19510700381c080030142c0701c807048800444007000f510508000c2802c0c0d0400207005040740020000b5041070003048450900036804258120201d151a030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 93647680 1250 93646430 93646439
    0x306010308181908100501050303030106051602030f060103020118061416020d0602030601030b060313030c2a06090e130201030f02040504180204060501110303060120030324061e0304060204 83
    0x180207800e030b1400f26009060a0a281c82801ca190041000310300404900748070041016031000003d580c190303402421310350303168600d441d2901541034a008002e036051203074212480145001003100d9043e83e00070384e100c0b030710410304202d100203290162081c0400924050800c0c900c0c10000c5014007000440a200700502c0707005500010036850740d1758000d0300d10540c00018081150b81510812010003000d0b100c6e90300b58608408091880f02c451140a82800a04c607204810440035480603003820a440150b86a000910000e800968110740a0702001c074140d0f11001c1400071044031220700c03516030300140340800b084075401100641a00c5007260500c1c0d409010210b1241e0315409018200312150382d0f201030148190041000b51086640424144861a81c5c440704031007010044a501c10710a0030301d207407404a440560610307040703401e01154060202206000b0f0303520755400d5a0003856082c403039068240448104010b0780e48101d00c90301188100c0200f085141c403180c1d501a40e44103008210050429594 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 93648930 1250 93647680 93647689
    0x9080609060118060f090f060f080d02010b0406050916050c2a040b010801060e18070507050c0f030a0605040c0803071406010915031104110a02010c020708030702030601030818 77
    0x25a9444041d030480c1005021a0030b41000c015000181150207100c658a4101540e2903038a0343d0084289107078642041520a107404d401034001030114034104400c0da40d560f42c40940785c006c0c116400c4010b5081c0140c4594502d09801000c0a0741c138018150071482d103944120030440700244881c9070a0207000e011040c224002484540e240c1298070360080701c00b00c90100010b15030044520210300c502d19060348540c8690f4000a014191401410607080807180800041ea02c1100c01010f40d15407507038242045049030f80407001d031000c02c0c400d50444d0540c001802c03c0107a03421310090050303099401940c901000c142181c002d0758025004900243d4001d40301c013840c50465010500c1640c141407043c11180801104200c170900400c00b0bd4010094001e01107a039040314940c2d44005408015402c4400c246503585074000d409200340000d01e1a5984089003000e8080c103000c1e0810340150040e03800004007504044125100c0b164010050030769a030071035403180204c1c1c004440c503126501c00c26160b10143d4a4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 93650180 1250 93648930 93648943
    0x3010e0115030201020f0f1509070e0411090a0c050307050f04051c0b090102090a060e04140709150503010e0c07031107060504090b030c0d03030b010302091302030403090602030a08060f010908 84
    0x1400e00041e400300c0e0950001a04c0c2400250054200341d02640c0030a580041c00700d01e021a01050f20303542401621080821883e0400a41100c1c00564540c000d0200304000c007e02c03100403c400f51800d0202d543c50300074030000c5a11013142e000c0450410170002c0d59983c412402000d10b5030701c80509230b0030542c882d00451089d51781c061855220f166190b54800600180e6078000e54495000e400940c90118808041910000039110303071010303c4004400c0040c40c0d80e032078000041b1520312100c0e504803807400c120010520304c00e911076001c50b00d4482490580c014030400c00c60f81038560840b4030414544890300300007a5039104105c1a0304000f080054a10300000c184802e0700100025035900c0c1d25503041500b030f60119051090f00a109500035240c02c2c0094488400d09030101c2d426040000701c000444005a01070b11610030740a43c001002005004010010f501940c001e0740031381c5c0c0d843c20240d00c82d00e00b40c0e07a900c00c00040401050141f00000d00f185030600720101c80183c10302d0710585c0b5655074909980b9060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 93651430 1250 93650180 93650201
    0x3100f03200a2106020d140411030d14030a0216082101080a0204200403050102180f0105030118020d050f0a050c0a2007030203030a0207080606040207120c0203010e01 73
    0x181c40031105030714180e510106554003903048075804801c0d85410940080041526040b40281503a000d002041c00080e9056032042d41400300140100f05ca81650f03145500011a42140c2007904039030105494180024510510a05501c50b1a9031407030f01407d01001c2c1d04010903120280d0f808000120b41080032240c4446002c1c85110380b15111b1455102d2500d0b51100e0030b003012102c800400c0100b1488400190003d80c42d50180c0d40010b0b480a00310f450409441508480c0d90094000200001082015070060240221099140000e81c0348801084048001c0742d091500098050006200d41210a850b221207001d05140c01450408030981074020b4482c103e894400a0101c031042041603441402120f500c40380c500c0486140c402c4100300a004013680d000300c2001e03080e4511002c00c00707900c2001108042c54000f41166122004424000e641d105c00d4000d690071400340f140412020304050080d00e400c282c0c0010400703040c502c3c0700e2081740d08541c0d4041c181d90664840314410300341403081c85017803d045e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 93652680 1250 93651430 93651443
    0x1306030203060a12050601170a0c0b0903100e0f0f150105130204030f0c051c020108070f020f0703050a1b06020c060715060e01050f01080c0901032301090203011503090c030803100f03 80
    0x2503140c2380703105404c054811950601c0c1e8003d40ca07004006150080c1e40720075201184d6041e038880c603203200860306d0122108480031015140050103249031600203440150041d990044070f01103140b40380745580b102c0c1c3c00311002e00414201c2e8014001c518142802d03c80320780c3da5400041c14a69203445406a0602c450030130f490000c6440400c1c445400c001c03d030078010a208865007030403170a1550000f030500c14024005020000c00c0e48003d18017920074031001188100d203404440285480c0d080454035980340141c1216003134246a010301d90b603214841d0060448516402500b1400d0790758003481140c2d4001c0b40116504c030003101c0e00c61700707655191081e10007500c100181e1604641c1000c090040300c1d004030000078103002c64001000340501720002282d42600080ca0003080d05100d01041110040d0071484164941c48418008606a0b034554003a504a5006551400f44e014031800203400312007210001909002d00d00c3c0c000c6c0046125200150740210b041005111260381d42c00e20404040d000740c108440c807 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 93653930 1250 93652680 93652693
    0x21b0f032a0a0b0c060403110f0609010b03010b01111023070903060b010c08030a090606030510020a02210a080c160b0604140105100309020f0d1101090b1306030203060a1205 76
    0x15410403101c80800f41003058200b5107014180e803000313956001d004000504104549221120580090000341e80c815132040032143c04c0c0c00e01c1a500ca01816502c101c1500a41c03030500000c202c0c0d0b10a403082c445002c446005451100c2e40400450f000e003468048a0599040106005ca8007150282c81c0520030701c1c4035621040c140341145040b400340c1d550149142e0410407160440d4000c1070350303201180d8208002c400000303a42076082c501100589425417000e4414014100014050481a0010f0807542d0f072980c01d56094640228600010172510b050b80008141c0c18000e800c4628017550720310b50044a0001c0700303428070b5480d0071180c00800c1400c5040b200e80541005010b25405c0030301800a19400860718035281c1d604250100d9111400d49441d00e042549401d82ca2041d901c0c1c040c21284421400750001100520310305240950680c0b2000c0c850020700d01c43c0001460300b0708082510307000110345920168091a1890440184d000a05080d611154041c0c00040110b03c0c4900115402c2c416400783c5903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 93655180 1250 93653930 93654013
    0x305031602030301050a2102030102070b0f100e151210020a1404050f09130c0b0406080601030c1b2f010801240518040c0816021b0f03 59
    0x18100e2449500c40955005200520103552003600f2441a40c3d0403c4010f0540d00795031040800751248500080c0d015440090900248082d20440c0740c4102e0441c42001c2c110f8491182c122001c180520030780c20160381150110b600300e901411305031032030500140340401c65400319460509204120181090f80d960024000b4101ca40008044031f4540348030101307034205894800810700e420705040c600ba00c52600d070800220080c1c5451242044107401001c3c07841440c0c0c4586d0241516445801413001140c030300c80000f41e06602c01d01400d804820140c3d280c4000c000b803010101900c1c441c01038102d40000c4220300051048414211910403500000c0807411001507040015014101c107800005c02c1118451410056121812600201c0350152601e00c0ea90307442c2c6a140c4603424820005d0b00d40c05410b2102d01c60100d50300c0045a0300444001d80d94059980c2c03403010590395502c011013100404d1031601c121607450302d001c0a0980c0840c1001d400c2d01d003905020000c1882c01050500d00350740a102d016241038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 93656430 1250 93655180 93655201
    0x708010f0e060f16020f01090f03030e2d07080604080301030308060d0503040b0d0204050409060c030f020c0c10030e07151209110409051f0524060d0b060403020a03030503 75
    0x2801402100240005007843c001d503d5031080f00070800800b214010300d40034801882000700004070902c0710003c0101528030310302109174140180c41500020b04015215840000104040700007500340300440c0300c0340f01c251003500746400d0307100202903d6014103c400030b080281441030318840d503c42c250302d5940b0346c190324000d40804405420240921080d0415000150740003084030180d4003540d10103074890b0807900780e610203407180380c015a40090a0440c14001c00040c0d030403504103130a442d00c060010350b4120070702000701c1c003400c0d08503c41e42c0d1001c2e1035401c0b00d041c600511a0f0341d2410f45008284000c41e8004145007007881d520410b203421003d20141032060307100740514401407080b0810312800700191035400d031105074000498451582c811004041200410048280740000020300454101d41c1000000420080344c40003865044400c805c4001606d100c0607a40c0c070039000b82420308000c02e0841500060a035025010f4004100304408405a03450301c4002000714400c0e034400b6034a140c000c0e000d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 93657680 1250 93656430 93656441
    0x6041220030a0b060d150903020c03030f1b100203090d0e0102031306030e1617071d070503040c0302090a090615030203190501060b0c0307050d0903020a12020607050708010f 76
    0x30812014554021042580c000c24824407507500143d40784219100c038400100d68000f0f89100816520694a4401c0509000c0c6c1245490724000c1d0290790780d55484006140d102e20407040d10000c40442005003504030043c0c802d1294030300da2648121030342ca2101340459800c81c0d0054880705c0341e55000007020034803903600141d41d134006802032000e981000b2040e9034a004031401d034002d040034152a0300c900b42c00c1480401030411049c0e2526218221f0383d9640c1c0089904020040181c0403030701a004012400d441a6801000213815241c0e1806c0d041d5078601c0300b21019000078200f11041c404896001016941d5004c00c2e5000d502919400036038400f6928080c000ca54208044009400c5c2405003040541d502048000c10b015900400724000c01441ca80070b80103000a80003114281404614054101b07000006440810300c10f000b100c07d003021004040d074003845e451000a600510b0501c0c240301c0221100d210814552015054a04202596981d10304040c9180c0110b030a903035484102d0300300411240200c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 93658930 1250 93657680 93657713
    0xe011104050a060e010e040b04020702030a0c06030e03030108060103032709050f0601030504050a0b0a0b03030304062705070501050a0509040e0a0308280b0d020a030b0703110406020a020d020609060412 88
    0x8800c4d80c80c808400a462400c950201074419507582d8945e04054490b0f8045400e00c1e0703401026120015698504211070220f18060500001d1030921008002803000040b02c0c1680e1203072004000136843d65404075141d40d81011f26854142c1d5003143c00b0703401d850181e00310019110344c6078085414540b00c200f906896100070700c005c0c1003506000c2800003240021034090382c0c4540001d04e24810b41c0d03442003013002030489202c48036014400042003105106059100b4040800402100c41c0030a03c50080c06181084450002d422a04100d80c200620342c051001010394214034104a400d000110700020300315000b100c6950066007003031000400300b591080c481a80001c070318844400b0211440104058580a01155640b581c6c1c0c451100b066580d0350740f80c42d0441640200700703000c240e803246061440103009646110202c0d040001c0d00c8001840c2405507400c1c2c0e00d042d8014a00580203808010414007480700680e00840e007041410266114840200050b100e44107030386142c010140b030441e241c560031400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 93660180 1250 93658930 93658937
    0x14090406180207120f321804050a050f2e060e040501090e030f0304020f03061303140a0806010c06090b09070503100b0120070e040605060f03060411010c05010e011104050a06 76
    0x41300b4507143d410140c0946c0c1c00300c810001000006000d1800c07440242280f14409031640d010403070009150080c00340075200075080d00d0900294a440c02d00c0000d03200141c03031740b5841002d0500003030071810361103140c844008241d40100c054030b8840c031030703400700481c1d42d400280006450001d003006908041c002d85004204041e010441e4003081d80c1c0d0303503441e8001d005031108802c074008040f4095540e1038404051107240102030358828202100207560300040b0b010114041840c0c00320f000300700c803005411b40d80590788030349070048141d8800e0011140c5042042c802c4400aa03240b10260202c0c1b407242c41e80380700f201c20200230f00045041034101840c2010010000c0da0541c00c0c1215404543d0780a03450b1802c9403545015900355800120946081c903403590005080445120104001d002d8160812409241e00795000c2201e0502c201c1807603100c2c1c1c4200d078040c4c015101a02c51481a510440781c03152100d000d80c000055013440b41000c1030955540d428011000d101c0440c0500c514600106544002c007071501703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 93661430 1250 93660180 93660197
    0x921060c020c01050d0b030709020c07150815010e04020d050a05010815090c01081012080403020a05060307021b04090f0b060109060512010902090a051011060108030702011409040618020712 83
    0x100001c00e00e04c1000c05030300302c0a07101e41c10b4000c5c47c0c03010049080034004412056407114181ca4005a0354407040c4640b650f0540c0c0c0890300018a80100b00d268000c90000c5070030030700c40468070015607518502c0c0c2e20b0141c0056080144201404880c440c0c14010502000c0101e07007135240c0f0110a180034260701c4000201e0a43e0400d1003c540c0d4005800300305072304c081c2441059949c98001c60001c04600d0350103100c0314503000d05200e041001010041c0141ea1080310540355468541082c032010f03004c1141c5501c09a0301c209007107410b001e0b202160b0f40b5110001400424814810360307402c1118880300d101142d2688000c0e003032089640c0c01c4030006003e003002e4646642402e40b0230300c5811000f503061090f101d100380c0c005000d0034152250410300b00500b001a0811605901c4804014181060360315618510300540002190443d0044200c034412074050307458400c646e51110041c90140d0212a00551207a5660f07130020301c0d8100040c03c280080400040140c840c015030510880e250340c4090207004101080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 93662680 1250 93661430 93661453
    0xa0e060f031026060f06030f06010e1b070308071218050102031602011b080a110a05030901060510020a06050a060e091e010510060f030f0204140406080c0105190921060c02 75
    0x40c83c179882820710300a40032540707460020a0921004810018140c002d00c400494420b1076103890300d0040c0d205480744694000f081c0b00240c418040e090004000403007070008601903c0c820030705e03100010013001001510881d0060f2038000c503030034100f046907280d40110030018140820703040c03000d50090a000900c26080c0e1240791071440340c00c840d0440f0512030765001244025011740e004104200154940f41e03034801a5100150840d04210f0300c130703100d56091600100b003a0905090700c1d269200c580c0c0040840012540d02c10001e480001d002447c100e03514440000e12000001086000b84500c50207446810340341d56803595004100100c031403031a810041130000c002d941007440f0044545078503102001c10305a00044000e0003002800704d904600100b80484c6828001801c0500a081180c007004026540c0c0d4880c2d40300c0088074501c80c00300e0000c0c0f01d1103240d000081045081d07041546025018181c44080300c0d042c0c1031042c8c405560f4a83d4590381002007046612510000001e40d000031304544040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 93663930 1250 93662680 93662683
    0xa23040513050c1002030910080f070f02100f200307081b09010e01020c2e090807050d080d0501090207141504021309080d150b0f0a0e060f031026 64
    0x24148036002d00d0040c4c0b400001da0b8801e1069411050b0001c01907404680384400040c408103080e2201409441c8030b0300880c080307078016044055a4810354000e0324140c0043c2c2500307002880d80122884c90152103c8410300260012103030700602011100e02d00d80c903410241e400420b0298001c081410701450342010006c520030101c00da0b80081000d00c2e0001c502c03000800102c4c10714441002854001d09090041902001032a1700303100a40e9907047c0c0041c0d40300000300304407106800c0c0c0c031800c5200d400c105001c0c07106081201c1100030041c0103064051605c00c03403017294030442e070091384040681607000c10301c04100840e4002061810300380c04020210204c403164580202d0f03a02603c001c0c480c06141008509aa2a0f0740100c0320980c1c00c00c00060320352400180c8240507249404c0e03c1c443c1c0054290002c94a550454151103180d003420600606103804854260380801562a145602881c20305c003480c04170038840000c51140b0075040ba41e0310500c0c60b114074000c50b081c10807507401e02101d0840031150500720 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 93665180 1250 93663930 93663943
    0x1e02060a0504151401150509010903080c0f030a02102306090a0617030d06120c030f080d06080c09060102010216080304020406030506040318060c0b0708060a2304051305 74
    0x80300c12001585032520b140c1804000f0103142c0c840c90490a206110b05030802c2a01d0300c0341220031441c52a003d110524000311241d2003208074690109010342d4041c00404c00e01e00103080110405022110400c2014008900e560020300c559170059015820b0076020000d180240e0301c0200514020340d86104000240108200c40240814040c1c4404d82c001140325103c0e03000300c00102880ca08507070003625004421345d1252301c105020f0001a04100d030004001d0303208030000c1c1805420001d0300d00c216041d940d43c00d4010386065800d4030441e034284914242480380307100d5040180320748402020100c0400e0240021024010109419a44144108141041e50603000032905600051311703952503a0f144002801010640c00240083c441c69080208241e00305160b08803c48002d14181d0030160b80d0182200d00c2d40a07914000c00400f035020208408500600c851500003100504d000e180c981c807001c1c4805421740100c0702000c900413815100b0418101407154a130040505951400d0119094540c20f030b8880 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 93666430 1250 93665180 93665191
    0x70f020a080d051308160b011e1a070b01060e0301050a141602030d060f050a09020304030f0e120609030310050405040f02090606040e040b04231c0c060504050d1e0206 73
    0x548520000f503003181956010440242c5c8084102d4a6071900655042584480f84046420441c80c80c00030601a8903200d0749500500801d17074107040c59051003c5000b00c07084841b5100c0303447c074050141c04001402c03506401c0c068035690795066002d520100c105820348501a080303005141c07134002d0f44400011841403e980c408403048401d003040702040750491551250b02e0100301d80310b150940100d01080e01c0400c84084881c00c44984040b65115601d042c01c81c401920010086082c03a10b50300c010707a000f502d102c81306035001006203c5d8022000419414110222800c000c1a0000000c01000118550780303500508029181004203240a6855003400500344102a00c220185c000281507541c1d038a080710013a28925a41100781e080c24030b0030003046281518229400403112240301d298000f810b6244242c6207201000341041325500074110303044d011429100d400c01c03801600800104410340501b50203584902c0c010260000401d0b070041c2400d10342c514006021201b02d082417500c5070300181994109 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 93667680 1250 93666430 93666457
    0x92009150109030c090207030201060602030f0d0f0b0301020711010801080d090b072d02013e0705060a050405150301062a0f030c02030c01050f070b0603010f020c06070f020a08 77
    0xa014005882d080c500340c3c40180002200c50300030a20300b8094020f444454440d80007402600c5c2c5600082c2c0c4c40f402040318403070303925006108000c20302d145d5070002004220724160024074004c42001081c03d83c0c1c007044040e035564400714100e40195030711801d000d00500c00f15010b03000d2000d0705034008001d1f5046200d403440071f0340c02151036820711403a6003182102200d07000060400d44041c0b807805000802540b826400b003401d417180d1014008a48201300c00318920000e030300c069000c800380d09441d90741102d00000030700d00c124480070030642c41cac04c0000c7c10364400c10380341c41d503c66207043d04210040c2d40306044000e41c0740341880100b041e142c200502120301d082c052081c81500010f164448070300c05480c48040c080d810000382640506030800340c4030948500076004c1d9000310300c0050042d64144541c03c4003506205040140c8000b0035544043d05401c001c00800100b51181c1103083d0300160b800240c4405040d403c45003e002c81e0716007080682c403078402d50b0b00282500300180d132200e010314051141da20005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 93668930 1250 93667680 93667711
    0x31206010c020d230f0c21010e070303090f051315081207150902090c07050f16090b0a0503071502030f070c08060f0408120402030c090403020d020f07080709021b030403030201092009 80
    0xa10f00340405418010f4901f001700000e0010502c2c1c0365032550548406e80106c0e0001101065000d005103010064850150514000c144580126001001c264116881d10400c1c40004034020805001d40c0340303000344001c5500d0300da08032402c0052044034121152440035181110100041e00e0310102160b00064122040c0d031903410f40d09000c0d0901c0380702400014903000f1038440700b8000e00240401d400b0303280d070742c402000108180b10a12140c103405008056041d40300100810480c40c3c0030b40300c0d2070b90281030b10540e8149110b00701311203450f0304000400c550182a0000034031201d4030401009a1111042c0880c51107401c040d2112200b51050000d40681900300c040010f00359141001095035490020301040c07013518080c2402915000322500f64401070181e0170105200314000111a4195003909000c0c040c211315000b01c400003507200311401042c081506110302c803044014400b8000543c0680c00228884105161500303142e020041115404031140e81400403945541a0440e444030100d00880da0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 93670180 1250 93668930 93668959
    0x30a0201050f0f0409090605011512020c070f090209030c090106090b0703090b03090a0501060f0612020306010e060408060105090c030121031103160b0108060108031206010c020d230f0c 81
    0x800f8802c801d2468040350000500060543c591380c04407048a0040904001c16600c1d141d0f0306185503c0154140f0000308a01c80d6807030040c8241d402899410512804c407140d00b0b9513110030203440c106c2c41c1e0018003031690200e140503260900748400c003100c03031044940020960405902900480303040c00313100301034500031a5500405018005850140c4070b400e201c107403280390550750740c2d50340c8040b0b0000301da8650a080000580118845484c8162011912600c02100c4521002402904001d284a0401c4100d401c05500768503100c0040018040641c05820990f05140c00d0100703022000d000390040b56020001000511111103250207841008000250020710700d0038100c54208000c2c0000660340000a04100b900b00d604035511040f521520420440740c0e03a038490107490b07281c02d106040d26034004124044000e0100c2c0080e980c440c0050602076a41c454076004115104074421044030001c810321403000303980d107021000c2c4101414400080c18a841e6030540079403241d80360070380c0b98000c100c0040d5000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 93671430 1250 93670180 93670207
    0x1802070303230a0f020a050a03020903010603171b03040308090d020f040608010911060a080f041a040606080610030c23120106061403041e08120c09010e0103020405030a020105 77
    0x4080440303484500c42000b4110400814030000d075940a6164034000d00c4000c2c2d548240241e07007144106444031030500c182c0b40b03000c2e4080d43c41080c05075895582c034078000c000a803851820101228604100d03d844d00840d1401021805c0d90740b04020780d550041c4000c00010700c83c10115001702c1019a40e1104428040c800314510842d5690718030b900c2810483c01050031b100c150f100c0b01503a070040b00c0303040b20701c1c0500b070600030b4910403a0226000500c54900165a01c90072094541d04076101d542c4c10b58651000ca45074941608050b40c0842d04c1903100e6808110100c010441190400d07140800b4020485c0703140d40311812004d036032281c5a011130810b8100da00005105000684c0c003d8003415503844032481c0580140201200c0c0140300214080422024100d044030040c1d0380b02d40d920090450404c0d400b6540e0740c000900d000800c6030030060800440c4011080714040c107025400008007141c84081c1c800c000341840e03682c0c1c400b160402d4814082006030356030003c0d4500d4030f1502800e06d0742c1d9541d030101c0d003c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 93672680 1250 93671430 93671441
    0x914060f01124e02010606090302090a0507050403050a03051207020d0f0e0103091a01030204060b070503040603092d0510020a09050d0204021608040e0a020903030a0e040225020a0f1802070303 84
    0x28020542d00300381155500e560f11480c41c5044541c2d4020071089403220070968074a500ca0002940181d00c08000880c62400c40e0b12554001b102c60625a003071556940d2003e01c2c01005080403000540042142e043d003040c1d80c100580c10035114006084000c096100041000641d005082c0811008282c583c20590299201c0101ca0f504105035104180c84003d01552060080c80100d00582c41d010000552102400946010542c401d01070b5207000e00c4c04000300c016245c80780042c1c59420038080310500284040b03040c0b04010380c515100901c106420b040007402c006000d2009881540104144581143e014840c601602ea003190850510364090011400078013a10010112901a041000052002c15009402201c41c880d11040195039030b050460264041c1688203505684240541c0e080980500d2070130040190117000141095080b4107030b4418a0101c4d0240303502d6881c2100707140b00b54103090845001810307441480000d02c40c41d0522130240e800e581100e1040d8a0381c0450040c041520a4204 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 93673930 1250 93672680 93672773
    0x806040b1c080309060f1e100e01030b100503031603110f0303070215060d0206070807031710080118020d080a050c070b0306030d0f09060c060914060f0112 68
    0x303801c0e00380c180b81c041c801d90700903074180345544a130f00c0000d1100b0000489451090246e40030881e40c0c41c5c07111b801c0c104c0a11028102094000303000c034012505090321004503009502072807520740c190410043c2144240d03a00d80286009400401c150b15101c0f4408100d00d00c07260341480c040c2003000d442d106071410800d811000510300c0c00000300b4401c0b0694006100083c0c140b06011075042c64817807408014591198003002504101c050001202244002c006400814040d007804940b00c02e112542080920341194282348203102c801042c00141c07824410b0071003042e5040b403070362958801034000a04140b0f40b03040090181c040040d041d10014401c600303641c8445c21400441d02c469403140c1d44045150800c4501034024850307041401c1c01d140c40b0354004900340d00304d80c584503501e50500600300d1708081c9080068030301c183c59210940000300b423644000c01c580d10803009813140d070500c1021501c081c08103a003c0ca03684412441102c01040c103c81c00c44812010441e500606c9a1007548cd164031810080d40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 93675180 1250 93673930 93673969
    0xc03120215070203031603050a090213060807060302030609010b160605010f03021309031d0609120304061106090c040903110f07030501060911070f020a0312090f0e070806040b 77
    0x2450200950009480310021840c0e80408410b65514076040380e41380003c130740390311440e030000140c41002c90083d8801a000b1011200105540b41c80e500071918492050500b50043c40e5124010041d4100901c00000904294541507286003030000001e12155010702030780346d45000001c0c200110203914141d24074016444401884150b82d608451031829400344000d9000d505041c8020518480a2003580d10407941600c41c1c4000e034907400e115a14510790501c4003030700a2010450190b6036903078101e242a05285410081d940e41c0d040480042c503c2c0940c0012400581c0000140090800041207159281400740c0d00003500c180c2c41d00341164000b200b50941e0415002c0d1000500f16064042209015a4040e90081c4142503442142504030b500c80103541d000c0440078414030001a100007401080f160004040002040c1c50340c840380d03611001a9502002b050040b0002c024140140c000d000c001d100101c82c90202e0710700324201801141e401803031648281d6441803401c00d10340d150107200100b0000d81a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 93676430 1250 93675180 93675203
    0x150d06120501050603010f020c0a0f031202070b060f0102031e030c0708070b15030c01020c060913021201090e0115061b0507060c03030e060103050307152004030312150b070c03 77
    0x8206000f0030303003038448601035404e1501d80d4091202034000c8840411003d002440d24411130f440c0c040c030301c14021408804000400022290700036150003d4040903005984014040c207050301040300b9669070f40019415074200380004c4180b100490788a684a030010095255a40d64045501072144942d002c010401c0201044a90a0000ea01c4006104d11010706036184922005810956a05d0045040341d0050303004088020740c0307040020140902c0a03003d02104816241070325064142e800400c040454521000d00401841d001801140c0e040b0903814000c00c81204034022a074101c155a008000a200802e040784507101d80420314030707036056041010b9462154940c08018044940e41e502035000134280504402e8124000c10b0150480758803100031071420066984003110180c0308414500c40c0341d6681d1004c0c03402c1c80c400305800c4818183c209442d40e9141103250240ca103880c41c2d0702c00d40505191041e0201059000740920702983d03240b010700b03910344032700e40350449100030180c100910044051 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 93677680 1250 93676430 93676433
    0x15020405040606050d1508210d090302150a0903080a1a09070306230d06150807081c0206090a020f0d021e0f0607050c0402160803091c03020702150d0612 67
    0x131000c1c007400f040700d00c010b119a603505001d0006815050040350910703000300c1c201c100c240588810076407820580e9980982410f5000c2528000c1301c2a0341c2d0103a015130001c18405007040070700307241d803640700c00c0310311080103c0701c100e4400500c81c1c0c10050400d4a9150303103081044c00f26010702c0000c2c80c2c003500200290307030a19020000074064902031103a90840c0000036050303100000d400d410b66030a49000340210028803500e84466001d0580090400000d2503c80e07004120803000b40143c0000c0c00001004203802041d510b15031b49001c05220103481190080024003503094008600c4200d40ca4044441540842c0c082000580180a00030001d5012103207916816990a103201011441c400c11501c28505809020600809c0d218000000b0400d40141440460910300355010300394510104001d145001d160380d44240c6aa88140c0b0340d8022607020100008641441c0c192005114041d450190305200032a07012440541c6566228403c2e00c84c0414a0b00020740c941d03100341e00909605840f08002c260b203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 93678930 1250 93677680 93677687
    0x1407060e10020c1f060b0c0a0506070504060206070c06150806060a0902030f07080c040b030f0420030a140102130f0806010f180b01020a0b100801240315020405040606 73
    0x400480c0503500400c19418400d401910a0710303840b80c2c041d0090443d4000d501441c00342e00036500013100b50340b942c89034003117413401d080c0026244101d41d0000518883c0200e0030202d1421100030500001c011080000340030740c60740822560b800080d81d00b00a1192085450001c0c040c0004444014188164020005403440d0015100340205000c1d11180c00c1940c0340c20340c1800f644002c9a0408a61a90300b0215515510801d00d682d404814510f01c83c1c141901d5041d24520b0f41e0003030b103030030b0080d20852701804184407440b030182012210307140c60b01464400a41c0801e03140c81c0343c00000780c00781c807582006114072402034044608001d030302d450003010540c03552003906112420b8080c0d14690701c44c91002248101e2250384400645102400010800c030a42083c2c00107020940b220078114019501198000307804662100d00138180c04035042100c42c1815149801c680107411401841c061070600d401203900341044203019280c0280c4900140700290070000041d210b280d008507041890708400040b034560 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 93680180 1250 93678930 93678941
    0x4020307030b1017090a03050423040c05090f04060302010e15120906010f0b090105030112030e03070321031e0e070305031c050705070330050f040303050c030403090306050403140706 80
    0x4ea94026030380b07440300301c034890350b0b418200e10090106800300014080d000790440203400e03920815210703503207020710100480c080e104807082000104a0125000b100d51503d14031111100d44150703410010580b551300002d00c0d450381a04058014224a040807200504032800c0303404501185440c0d81c0300d030410400031544c0d1242480340040d0010305000c00304d1201581c404891401c44140c0d20242140d08041c0302014034000c85030b04400744140c952098040351020705c4000015030251080e0360382004103503c0c1051a0207a03900e000201481e20220003098030b0302012581c241a40d003040002d131071410300042440c200e241c3e01701502038071010510312450080911134202c0d024a000061003152180003041e5554003500c200180401e012014002c040440842245c0a9620700c4060710b40c005070787c103078100844806540c04100c44501d0800c20023403542600680c1d403c114014100c52540c9000d4070b004043c40514000200126100c0740403c05151040080036003281d0812003007035a400051420400802 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 93681430 1250 93680180 93680207
    0x414010306230106050306062b150315050c07020306010311010e0108010b3403110c0d0f1202030442090b0c010f02070b091203060d0204020307030b10 66
    0x1800c2402c980c800200700d2500c071402100407841880140d00b80481500d481c1c01c01068942c01440500c140941441000b0030036410410200c81180e013144d01d81600401d517150190b25030400b140319241000001d840c0350301500035680c200d600003840d807603000c007444061154120180d03051003000004000d1025050040011042c00d80301c3d000395210010056494260901c0703500d032503180c203210940c80da40c0c48581060b005e91100380400350034a842ea03080130310303040c0540007600003075004140784000c0c0200b00007401310b64004071443c2d940201241c1d542c007030722100c0c02030051110550427507003140603008101343c802034121104210114000800a9901e109089407010b001c1d8034200b08144540d509180c20f581d003c0d81c0380d544c00140609149001c1d2155000c2180c4010641d6234a10b6603102d0340c0b061010f040e9203482404a02d21505120411074540856404400030302a03080080c0821a41c030b600032030040c40d40c1600e02503213039aa260704c260001c11401c9016038100300740c2c0c0c407084e08999101c00304002c1803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 93682680 1250 93681430 93681443
    0x106090906050406030b0403030f0914030702090c180d0311060a09060b12030d0207020d020a090507020706020c030a0b0402030a0f060e0d1e0806150429070302070905060105070204140103 82
    0x1d9669104020648001e880050691014100030a0110384240c2040014507000e05012510164039600c0c0b00c045005101080155040820410f086141c4460b82e01c2d00260082241420021100c14a85c1910f1450004c81d10541c00340f01c020081500131241005211211416070340c443c68400002c0c40640306c80348084428518024070b686443c5070590061a0902c0760400460416444051501c000d501403002a030340006c0324070b44040140d40d02d6804801502c00b0101c04a4982080400a842c05030503400480654100940040042e100050f58141039500011840d181e07440b44d00200b4200403800ea4081c00704919220a8024000160000c00c010a01c0302c040b541c0c403060070a01151014009070700c0b816003111406180700c0c180c0c41980519017011005100d000c00c2802c0018503002d42e030044d03018811050012941c1c081c15600000c14090a80074015180d10300002c41c0d80c02511000a07002d1045501e07a90350114449034401d006540040b54003030001c00400440c00014101e0750000d1108840340c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 93683930 1250 93682680 93682691
    0x100c09140405040c0b090a090207110916021915020703030b030d02121602010318060b041107051510170606030705010504030218071b0b071107080709020f0408010501060909 76
    0xc50810740720303451150360400303041c441290810035101e840781c1c4030700a20740c2c1c000782ea007001141902040c402880043e11407440081101c3c4008284610800b00074810349440f130721294031480c90f640110340c550050700c05115030300d1921071514110b6214a010905100c4e0340f807000c20a5410182c241c4e10038100b02400314105d80c03029140307000490351113844010003014810240f10038800c0b803040d9400c0e130803280d205046c0400c4078050380342020086918000152a41c0e5180c0410b8a81d03802c0a20541d2040c09580d5407851400c8010740342e9994840e400a900310f0f1110360701d80040d0321140001c0a840140114035045c8a0500d819120165240d000f03540541c400e0040350000a02980900700f100e04a03980a441d0a1701002c031405a0310740500000c008100780304100c40d0091462915007001d00e8001e204401c40c4e50300b07041a60300180010564070034031b8074990003050207010042000501c04201c0d004a00050307940c0e020104844c00a00465101c14540d600b004004200160440200016070b191000308011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 93685180 1250 93683930 93683969
    0x2010216050f0f0c0f010c083c120402060307110f030d141012260d0e0d0207050409050c04060e0601020d0905010c02060d090507030804061101050603070e0702100c09 73
    0x72213095541c00c2562100c003402003076034254016031510b10b4960180c00750354200050028422000381c03004100200443c102040135060002004138060b00d420a400203d0400309400e222103503c000c042c1c80a4440c2d5408000240b91a21030343c07480140b000c85406944e451030345a54004d55a400202a1403500c908014512452424102260307100b540310b00b03a0110f0042c601008075452000c524011f840a00c42202c1040c1d21070505902d10b0321100c01022940ea840004425210440740d0340503000442d074202d200c0040c4941d07800585001900c2d401c680014915040380f4146140101c0d9000d2140c01a080450007da00c4040f02d00071440b403903080c0c00792181000740d1002215007400714001e060201d100328046001509160000c2c05588140f140300042045040d150946000c4c41588111460b150005007448450340c440c542c5100301d50841c00902450500c200042c0d1580d410f8061054451080d800254603640f0801c080500d107000600c04000c011174080d0003c0c582c80d424010000f407144412903010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 93686430 1250 93685180 93685183
    0x2405010314070309030908030a0f030b0301020702090f0c040801050a050103020f0102060f04080d0617070315020408060112030201090c0609030506015a1703070807060203040302010216050f0f 84
    0x300c042500c9098100c155180c40d02600280140c04c0141c081103035085000c6024441000100784481c6682c5503000c1000d00e22000070f00303556216a8441c0130340d005000e142c1c01030701c403460291340040d100106418256070701c1c840d0320181c0c025680075030303c20740c01c041c10710034104070030ba006074180c0380243d940000d0ac0c01444016640d0b40419100d0300316502184001902042d1448060804404221408594030740e03a0410401a60306200c404800794110013020401c00c082000e980c1701b5040030290a5080c1880e210080391650014070034500c8041c5400d0b84842090b1007940301e1b42055901c80072007060103454190080c0703a03030301c580030031078007413041c2c1c800841c2200030091b28a44240044a8110307a900448400b104e03040d81440384d48009000400c06c0b1101c001e5580b0840d280c0401d0303020341065040c9414a0404085010504e900700d80d0010800c80000c1014441103a100a820072005640c80d200c0d460102e00a2141c2c0b9071580c2d8411307400c0108000c114001c14640002042c150484031428080c10000c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 93687680 1250 93686430 93686441
    0x40506070e0d08090d0804031a0f010501020c010305040c030c0e0703060911030711070905070e010e0a0623070602031302010e041401210b0108030a020d0512041e020424050103 77
    0x110360011200d00060b000036500401000c0c1d00c04081c0100301e0b24400d44d038030400103402c150000c40750740f48e000c404000a44039074540c5990180c2c021002840c1c6503d030400207501d442140d000e290401d40c0700c0f4005414841d44007060401158402c03a180e0344e01d40d0350780c603007651060260f408100290600000140440081c0141c260340e0600380002807450700c1c1c1200c01d4a880101107180107003800740c640c0014940701103204481c0f0074400c1e91036600609a1860004104412458401e80f16907441c000034000194041c40a044c0500b2032000381e48100203040d10300c01c1034011302038020a554000002c00c00e41440014410f40124402e881d140241d0101d20104802c2d2610f07030707042c81c001c41c05240040211100554641c011200c80d015200c4004078643c85013500508241c21a622a500025070b000e125903040109000f0900d003440e1450070070f440160b20a00c0b0f000060000380420b182c007000201c0944007001d4600a003580100304002485059440c40e030030030b0101c100802d05c41000100001d441d4044d0090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 93688930 1250 93687680 93687707
    0x20105061305041103010c0504090605241b010c0512130b04020f01050919060e030703050c2101090f170408060408031f080f1b03031c110a050304050607 67
    0x881d440c007048503080103200042003500d8000918818584c1c50b203080c42001d021003020f645441d40c56050400800c241c80580e40180d00850102101c035514003909107078801d0610303411034802e0b0381d00712100c148500f506280c0e8043d040f03940383c074040341085c1e904400200388190044c68050500d5031140c044200310645110090300c001c41c0f40000800610300001004591501410458241043e074070100f8030703e0a1503114182c8075004074100f4081190060328154114800700c00a01d00713141540c3d80c142c0c403204202802801503103281c4904c072402009060507000e83d00b002000300184610390410b043c0c540303c080c0b41074a01c80380703462b41d1030440c846442c00c1b2010303a14440010100c6490356500e002c0a640001d0150000e491010910340e6110503103800c0c4030003000320310002c08800c03181550490412401d0500b07030650010582c0703e01d4181d1800320070307224002c68001c0c810390000798048104001d0100404c1c0081c1c82400000c90b140b1aa4000020354002c038040c42c02c6400742d0765000b2094495a110141 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 93690180 1250 93688930 93688939
    0xa1508070905031c021006080c1219060b010909020f0a110106060215040614040b01090c0306030c05010f03060b0a020a060f0b2b020904030f0807020d0e1215070906090602010506 78
    0x103004c00c0002c8203103c509842e10300c125445005529004030890301c0035041380c1156000260400030030310344100c0c001c69112500c0d000d4200842140c00e0103e10f140104002440c4a460b07455810b02e582c01404200001c05403110305556400407035104107003a500100b101da0101d0000302c107207682d60300305100d0142600c0305500141012684019407071a4460000e0046403210b48540b08034032555840d07440103018601c02c0c10854059414800b4038416540c207800d1039820140b4142c0c0820202e0840c09160080301c0e400c4c2091520200c040c00700b10090304480c0c002004403031000580200850340041c1c80da0241e4080c440800041c1e03491142041602d0141c00d22990101c2c0c010020141d60b0300e4220f4100099042c0c01c0079080104440c4d01084a0410486080c0c01107111807424400362038114031001c0e4490824030150004400d0584080c00c40b082d082c0701207000340e00c98051045951802c100860340c0c4141100c44030024039003154005e210f1401030180ca400540c0c0715500040450050042a008510040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 93691430 1250 93690180 93690193
    0x906070c0b190609090b06011d03060f0601110a03081906031101031d070602150108030a02060711070e01080a12050309100c05070b070c021504050303160609020a150807090503 77
    0x2100e00700e41d44144090b4203000d55990300004800c18140300780c1d035807644901110940e916040e0000340015a507080c100941d00340100200c8896500801d1a40d40001c440080c0711054944400495420301d00b0104403c01e031040d00030b11000d068001c0e0101e80b041001d207080701c0d480020b0794030710300585000b84001400c080452980144541c066000b038841c0c2010007582403490150b0303140c001e103495403692152001d078002c041070506006c0542034440c0902807040c01146040d008040c000d680c2e14004014004006450050014a4905210410007440340d164101c4c41961665515612044582c1040300c881da01c034010100c5030703400b45040c7c0e4814030070000980042c2c803407020980098070701e04092104000e010041000080c030780b07558140c06580c2e15682d491501d6058070500c00d0011080b148a2a808030511080006580010803074a840720742030595080e514240c03820001070180407000a5018000314004688524441c600400803103083e5203030149510707040c009444040c020302030160140c106e003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 93692680 1250 93691430 93691441
    0x904020904080c030a080105040c1b060506150a0203030109140609071101150b03041104060b0a0c051204030302030a02070914010302042310081203220812040602030906070c0b 77
    0x40034110350090045152a14021080d0035407829584030011a00200c1c10701c100520050403e4807651030000220300302454800401c200103000307007103401e83c024400b50b226400512182c4424440b05240241c0003071164035044003e01c060b41700d40090003085c00780c61415100c0c82c0500341c45c1141e00d00503800a007a010203511200c00c1290200800f1880754240e6403144d6000003142d40291003d0000e269541805440307041602e1f00c0007000c00307000301c8184980e003801000d05c1001d000c102111003403201410600784545951408030b00301510f200e00e41e82c4514000c80c2c00414107801000910016909900751190325840d40095800c850743c04500710102c0400500500c01414282d101071400c142148140b030746520010443d2010722011900c81c071801c1100c01081299150400064040082801e52182185084d41c00300c0c10040020384200502c40c0002ca4100c2441682e6044645c05202030300a14504e10300b41c203007080030b54800d0b64003280d5403040e0070000c0d03d40d511800115401c1c07a4006040d4540380c952 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 93693930 1250 93692680 93692689
    0x13050f0c0c010216030c03020f06010308181503040b01050901090e030417010e060127060b0a0c0807060f02040e061e061e0310080c01050310092d0504150209090402 72
    0x7452005903600b0441103421507a8692a0320403e03200380e84403850300f0100e02d0003d0610342e119095401540c4014014400510300e84152501151244c404544941d100b00c00a0000700d0040111800040008184410701c00e0243e0000c1c10303600c0c203488440036a40d80d00703448004c071003119201940582060105218086840404815500c1c07114000b10740580b01d200b11a0509000f83d00038180800409080184000d603460f000500d400c0c401c1d400c000c2285401801c00c89403080c0301c800401c00080d84010400c0114030f0060384c8109400c010100010000c000e00c1030029440750050411012040300000c05c0c500d8144014800c0050115425505c1001e510038000381d50400500600319a6410440f01e410100c034002462141c0d0744068050178103413038091090b06020101241904102040040001a03403c001c1315004854001d000000c100c0320000e1415940080140080140d4203043c4644101401031341010340150300800c44403200f1040540ba40f4224814024015000008280000d000d45030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 93695180 1250 93693930 93693937
    0x10050a0501080d02160b031003060c0804030f020c2202120703091e030c0201030b040e100209090105010f020607080a29040507020105100b030411061c0b0118291813050f0c 75
    0x804003848c88182c2c895940c0b10988a40c40419000200d03103c08210030701d540710100c514000003a001030000103401401040305240c0541118101540700c07041d44041c0c0c4000c0e81184d0b0403003400c0e140c18600c1d082440004001c3e00c0080c82c141ea0b2410a40f02c2c80c40d101c1000c5810030403a80d419110404c04e8001940190041d000d01d9803040d61050307548841c01a12326080c010841007521104005a458003450100050b120044e04600d04001c0c20001c0f62002030303000142c441d006080d5041050b81c507620b8a035030f800501400041840010400ea180303801018242c03840c440c1c005821035041c4142c0d0784c0c50808908a03002210601a4441020801c1200c0381cac441008581242c00341280515415001c000b281c000c0c2e106004505040360300b080c480c650104c081c81083d09d45003003442d0484648140d0249054080c0190280382d28030326040820010004040d118007000b4015104c01070384035140910407807250043c004400f8051000c0a003840400b80440c0b10750361041c410803494103610744a0000c4100c5642 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 93696430 1250 93695180 93695191
    0x80c060310120501150602010c030608060702060609090a0618030f181401090b04031a012103030f1b030f0b0d0c03080a050d02070c0512010509060106030b010210050a0501080d02160b03 81
    0x541c5e4400b03400000044203240750241100741c0020984404200005088907100d5000c00303519000703481840005a80031500350781040c000c03543d010860b00c40b500d07050306100c0c40c100000d24240c9130900e59000c008002003220b01050180e00d480c0b607000d01c007400c00d44003a1466800d901e1a052907940900010714800700703248002c08103150140781951a200b000324254040c0e00f090321010001ca4540061480728000c20b405003403c034240c00c46100f122040d2001c1d40400c60700003005e140d201d4140004a6081d688100503800703c0040c40700041c3d10744400a4000c21500074001822410807211000906194002601c8607a001f10000d000c0c900d1900c5030402908081283c10412108120200108003140040d101c404c1c05080a500700074502410003a5011036084024042c0c0d050201700801101c0104855045030054200401c8003d20b5100403410b1007400041180980c0c5400148403000c01154402811385030700c0340071503043c102070f0401a41d543d80785009159004c4180d810030310038644130001454018 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 93697680 1250 93696430 93696433
    0x412140309010207050d0203070507050636030f01090f080a0e0d05030d0c08010b03060d150c0c0c050117012304021b01200702010e1f09080c0603101205 67
    0x581845000410340c015210580181c0d00400e010042c070009009000c48041c250000b50300c0e000c1240d5820762600a00d00c81c0b03a20500340401d4010000c60407a001800c0d5403000007800035011001074504020300b8010181a0081c4141d49140501180510604203041d40203c040340316844d00e0307580c004059002190040800c100485028242c0c2c90b060100048a07106001071915590704180c3e0408607001510340804001c818001040940e403c0310440c2e0300f009040d039508010251030304080005001d1101c0c01080d16240643c00031109511564a00140e44503003515000c0315540c0c401100c44c843d9801c18800c00c05500001040f0002800c1c0a42a2348d000200100b4800390640000400300e0300164880720b480d02c3c2d0782d03011b25540c0c03400707100308401d0042203d032240125601d4003810046014426000f41801002c1140401981e10030300b43c00008101c40b000d04120303811000004002c01310600c0340c099148a1320000740c90130714041c0140c03841510510307030007400a854092400200590010103842da0f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 93698930 1250 93697680 93697697
    0x1204140604080f0a170a0e1207150e041a03061603090803072f0c040f0b1207050312090d0303092301060f090b06030403180e151201140412 61
    0x40390280b041c40402c0c103c01c40945002c50305410705c80341c04034143c2c481c03070a0765008210301c00394103801a40c0c9007480001a1000120701050b514114600740d9140c214052000c108515880740070f40c4038406840700c0c01c00f07543c1804034201d48403556181c00d40418180358150414130000b5501006090b20b10403841c00c40c83d0101d080d107440d44440c03845a10580e5003400058041c441c4034a1100c0344044002c02da000b0403005c02039010001c901310744403014401002d120b69115034500400900703d40114000b91401441da0349015085800031703a444000b0b03c0b40e54003034016400703ca00760001ca042034441c01384000e015400c0c61541e07503908900400c0000d1007140c00700310b074007680c0050040b0400483c076084440c00c00002e101d800c0522882c010003803076000c18107582c14405600400e40324141582e4006070f260400080782c060b06811020030300c000341c119440301c0e80c01e2820003945174031800c40000c00310001d5945580001c2408901404d941d107075454600000c42810200307000444901c00540044014640f5500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 93700180 1250 93698930 93698939
    0xb0f010201020c0a0b1b070f030306060e090403110705090a091e1110050f0a110705030c0a150e0607050102090a240e22050f01050301060e010e04080d06080105181204140604 76
    0x1040d08005008d5501020701e9441008160b0140304140c05815030707040c0f820400b00200b0010ba161a0001c0c401010000c401e18a0a2942d00410449000e060010120307992440c1c00d29012005082c2100d0903501c81440448011290f01c101c201e582e6425006000d400f000d006031418440c41e1113030400f000c1e0400c43d0402501c0201d403940405440a01240d0b03550074204001182a2441c200303060300510301c660090011864540d640687e04000c40325052a02d18090480640c1075030708200040b03060381c2003400003490704100304040d8000c0107106401c5442e82483d40d102c1e01040200318440c048142c0c0c2d400d401c0c04200d405401020110301648d00208500b02c0b1106000402214041a11496444a07151410302208100580e0143d02600090b0000c003d0070b45400102d01d042c40d018803030342d101c8900c12008141400f0441e002c0301d038000540c0005018590382e0340d1169000300750403503802c8072602134000302041242000c41c10304542c805011000381010309040c84400780c00c581c82c00c0c0560140c0200b00024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 93701430 1250 93700180 93700231
    0xc050a051b0c09040605040b1803070213090210110d02030403020f0405091006080c03010f020c0d0c03110105040b191401260105090d080a06030b15060c100b0f010201020c0a0b 77
    0x781300e00e01c51000840c95040034a8010710005025002c1d4001d40c04481125940f140d00006440300e01d07404450043c2028560704281008144946001c0e411006012005804a03000b00841030040b50030400c84909007444a8120307102e000f103000080d40041e0039590b5000500c5e160300280c1d08801c01e1825a070040e00403c940707100b10752403544000020382210750851114a021b11400e20311828610042d8641202180000c2d251140c0078810300a0000c804034080a06200c3c01c210040d4904e0329000300181d0034642800100d00404a95030440302446c06180c2c08140d4550007841d0104141812034000750b400d00705222210201114554141e21804101d1014076909005c1c0c180600441005400e0300800003500404041000b00044041420304204100050b07400c0b419982c04480142c404e0b035088506c10000300075100d0403103183c14500c0795100c0440c007600158805d4810320801c48003800e410307096200580c240d0040c050f4940c0c058210746010008550700c8400706030700403244030100b251a5090310502 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 93702680 1250 93701430 93701449
    0xc010e070f0807051509120a0b04150b0111070306020309032704050c0f09040203070c12030e06060411031602010207020a0303020114010b12150301020405040c0e03010c050a051b0c 79
    0xc03850103840d404100503640c0240b000f20080e0500703841c40301111102111300b40c2180300e000b20340c0e13019034600c0451102e1104280104014030740d00030002903d50509040610347e18020860303a80120346860b040d02c54660042c5101f540c03183c40c1901134480c45146031120030003900004e101540d07a020403c00194a00000008041031000300920318108906d41407d001c00c8800042ca0184802c01c00c0000c00b206840702000c0e1388282c00c003181d002d6565a105002100c1c00d101000000746894801401c0c5445103070550003800340203890104039080e40e030725001004117488213200d2003907003e45d007000410b030511411801d900b03120550303000151030140c1643c045803035603502d54403d5006075581e80c0c030381c0c1c0c0d112241d0980900403c440071105050120120600081d00809801d1042ca070461404000d5076031001c0d0103030350051000600402c490b21034042c0c0504865005600d00e03209510b07121075446035074007840a4440310913841e5a0307541828500302502d01c000481c800200d0f418032420384010304c1369a40388100c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 93703930 1250 93702680 93702689
    0x50c030d05040f0503010b0a15051611030f010b0105040e1503060f0f010b0702090a09020a0302132403110603091f0207061a0f0d1112060f1b07080c010e07 68
    0x9007030340d651400c02030798001c0b0f40c0c81d00301a2190b410004000f0155640c0072003102904e83e6030000104007401900c0c00d6485124810341d0651804541607120140218000e6020400c201078098030340041c407a6901d0b034200c452054446001c200140810311594544489a40d880500207810300480003200c800286803020483e800031a00c0301880c01c01007242040d0400600400c210300305130b0b0038142c0c1c942c0060700341c10004207600307080e60f40c41e00210259030b079040c20880210b80191001c01c018411540c0c00c4090650389060081d1700003000c3c20030107528405180d6000301c0e60040c0740d2440c290100000c0041d0351748054010600c501c41c4c00c4504660003003c48401640d098680c1c0016605c01107881c03c0000e0ba100c2c0c0490034402c64801000109a88841c1083c4580c010304940d0341c0801001c61034160034440d5243d0056400c07401c0c16418240c0342d64000384040c010200065800e480d40e03a045554982081940c0780107548c0708040c052180061903150180004110007000482c05c054002009480c081c04d0b80d21 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 93705036 1106 93703930 93703937
    0x230f10150806060d1e0c0b090a170703081c020a0804020109050105120705030a020f03040506040c050307080a061508011a04150509160504052701050603061c050c030d 73
    0x5042c00a1b41d00146840131903844030410491a004407203414001c4501d41c9000c070300014502142074500441500802520303096640c0c005150304255142c1c0b0314008200a40041c004050000e004042119543d840f4545410f0000404c029403075030001307050090170003d90300907481d6103000707a41c080c4c0b183c10403e03076036225103180703000038171070000a0215440e02000344410401c000c6221406180511051a60540c861080548a00540c81100b129602c444503070800218a0f4000d01d0303503500d40414480102d0341e1448081c0c00c4d10001240c0400d1502184040e861510700380c803882d00c14447c0e00d032401c80094105408101c400034050281c0d10030040e58524042e2661040c0211005410040c0011130725110844001c41c001d00c8968512400c80c6065001282a04000c030a40c0e1141a008000060020780f1091040c1600200d088c26180c038080c0c2c041010080c0c034100300d04541300c1e00555 = true := by decide +kernel

theorem cover : BRFrame.Cov 93525180 93705036 := by
  have h0 := BRFrame.cov_init 93525180
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93525180 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 93525180 ≤ n) (h2 : n < 93705036) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
