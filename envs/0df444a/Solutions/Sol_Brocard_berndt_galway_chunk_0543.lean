-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0543
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:21:07.604814+00:00
-- url     : https://prove2.me/submissions/c3052053-7756-4950-9668-c1670491d182

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 97482014 ≤ n < 97661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 97483264 1250 97482014 97482019
    0x1d070903140f0c0603010b18130603051f060b03010e0c1308010b040b03010c0906081009060312020d02011b050a020c0405070e0310020a02030a2007030606090e010b0109050d03140408010b 82
    0x841c108880c40c04c00305490603640c0c0401c1c0141420300160703880b50903c0340b02c804560090600750601c982c1d503c103409a0000355000d0340c01000410b2400c55030b0b12505148416455083d894a8001c1c04000030400450741103560a0702c1e20109600c0d007001421540c85003010111441030500e50000314200190002c10112104403401c0201c2c0d603e880a140c2a00c09180d00d41000400060090000a02544070700d60001c2e90707041c4215480d91501103810032034041d5001901e00c1c0080042c514000d50b810002070010760071a100a100030b40031103600e0381d80013104540000610074041400890144200004024075100910a11503410300d03000192101d4089240780b8007900445030b03001003a584034000c0304d140101580c010362421403460303000c0300c01c44556602c0071800d02400520010352a4104104400b5502034040040e0b120b140c10072074021100740c503103200e01c164180712060f10517a82000921003224000e40e1100090002482c04640c000d80410440071941804103020034a107005510128005070705 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 97484514 1250 97483264 97483273
    0xa0506010806010207050f010c0807080304030306241704020301021911010606050f07080906040e01140906030a15020a0207050d1406090304030f1509060e0c04060b041d070903140f 79
    0x1042c0c01240c65494601580c0d0b00221004805000365110700109224140181c5441c1e00300320803592a000c41c0d0b402646c0030b600007911550107006184010520300c10385032442290340b8407440f11400241c4001c00307451404141080c1d041c00202551429011103803108000b0040a044101005010301203016510790740c84203600e00400803404078020030856a1000d0503503591030420300300e0340c0d03020815440f80c03490580154007071000081c1c002604800ca4003900715402540e070b1000b4042c061101c803110040019129500800c1042c000c505d10882c4000c40210384000076a89180d5104280d10b401c0b40c5501c03054100c0b00110011040c440d0141c0103c0807101c4d0141683c0300c5881b401801544c03801b03640800b0780f00040d6140c040000a64072051b0b056448482c0f10301044109403500d42c801103400910121495030401404605107150510900700034040d0040c41d242498100780071003e81c0c402484100c0b0000350b8460128400c1030081249400555100d000d0400b40a00001c20540b1501008000401880f9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 97485764 1250 97484514 97484521
    0xf010f060302120c07111c1502030c030f0c130609151404091e021b0105090d0e09040501090203120403030905011e0c030c02060c03041a070b1803120a05060108 70
    0x1c24000c5510880707030000001c0c0b4944580302081070603440070600b1211650301c490b05241e0740c0c071105c4294001c0840780200c000100614104140805404400010068410070400161011740c50599400c51100104912544c0e551a09800c581c410511010451841c1c0000050156030003006e00c1309171441500302d0030030404105001c3c1d803808e06289044404000501c014000f600f005c0d03000d50051446c042440c1d00720f00c603c0101030b00300e80c040c24503140c0b00c46410444007d40c40c1c0c01d0003503a8120244034003c0c4a0180c1c9043c00510080c48805424801c1d43c40e980802c040c40000d411009109400034151103c40020401c010300703640c002d100403004100f1982c7d001071b00303601031480d00b640c910030300654912441c1001011100328903584001c50504c800724300001d000d81c1f117510280070f949040d8170003180c0c1d80e0f040c05410100a4040400f0070042c500c1008610009030140312041d0b04880d07040300400005c444000c5141c11809405040d64000c40f508040008900340398201d240105402e0f03c0f264210744 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 97487014 1250 97485764 97485767
    0xf0e1b0603070905060d2306040c020703030807051c0501150f09050303122a0d0e0102070213020f0d020c010b120a0210080601050c0a1b060801030b01030209040f0602030f010f06 78
    0x8110b0703807440440c81142d4104041c1c10a9001810203a400340400a080b120000004200c408483d9043e000701c0c0812040005078142485a01614905070005020551855600600d82d00d0b0003040c440030490080f0f10a02002001682d03800b107040000c90910903580c581230003100030400e44c100400054035000030491503a02034881c142c151440038016614260581150414280c8094103410103881092501020400c0c0c61400c003456911000c1c80a541c0c04501c02d000003640c84060715801035034410024a40141d80e000440301215100b5400981c0304c0c8500d6030014044d01810381d00401080c000500042e001c8010350010100010445030361480380034850b44c1d242d4850303042c40c2c000e41040d00c81004412030340c0034000141d40000c0514003145441040d0610b00e052002c2c100040345d146420082c1e640740b10140c0080c0d080513181c0d0b071800c44200d61540d1250440400c0c1803001034043d00e4003002040c2071012420541d01948e420503001d55907070a1100c00801700c41001d1040403c1d148259401142c1c45 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 97488264 1250 97487014 97487017
    0x703021309031701030c120c150c0203070602010b0307140307081e37020a081e01060e06031b040b150a120203070c0308250504080705010f0f05030a0f0e1b06 69
    0x22a04211070f0004035052100c04020b5043c40c7c60191040740c01d0600010782c584451042d000d51108030740e505100a425071060500d400c2d101d4110b00305590501200b01c0e000e40b40010140c0840d4510411910031075241000b180c107050b000c0d00811024000d081c103071204c414000007a00442d00049003111082041d8007000c00d0020072110404032400e03101a80d040c20241161f070701da00c1207030004006a0440c1c0c1d0745c0304031134034000400500c0080b00140710740003481e843c070071302c12030004154008048105150140004e134442d044042c400e4882441e282c0541e0b89038480c3c0c1d01440d132071580a0034184031a520119a141c4c180c00040341880041d1903590050034800311030080d240105040c1e11000b04440d010360f4141d8059000500003201d400d686d0030b0303001400000080c0100e40143d940c480c66aa2810503411074140440d64100718140710766044503410207a03000c02c00f032032080c0c081d240031900c9441d02c0200b2000b829412484c18078942c1048540514004089600c54440c0700207000d0b042d04000302420302005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 97489514 1250 97488264 97488269
    0x2a0402030f04110307050a140102100506100c0516061d03072405070503030a0203010f0f06080a020c0a12050a02100908030601030c0c210905121e0703021309031701 72
    0x2408060404140000e507039030b0a03003c04100040940b942d183e00d41010411400302640200c407205404c0f2109002540c0500004058a0003070034240030380e182c458081525103821810f001e0402c41ca0380810307028030005020024080c00500280d40c1700c00e40d1a50001e0210b44c100103c00f41040110f0300030b000624000802070115010488550081c3d850110032200004288584606000701005107900003a001d00c002c501c00c0320440d90050301c0354100740d611100e10f000e0b500038100701101000300344180b54000010680c44544560f01513a04d440c50752583d401d10f5007048005003003a640c17042c001040b42e000340c05480010076aa0881300d4070011544a1026a60590707405480204100041646944640c220100350a1242004580b10b2030b240d0b6000c090680f4884042c1080b8001410f040300341d40e203c803021005101c100c40a90007000c80b0909030381c440d014095141845c0014400c80340c1c00074428420700009580091408020321908030f5103501801314081c0c11000980280c485450304440024200e05 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 97490764 1250 97489514 97489531
    0x91a0711100c020a051203100506070f080702011e09081c050d090809130b01080601110d0804020f040903030f0e030705060103030e01051b25060f0509122a040203 71
    0x1a00c20508180c0040c04034a0b000c60440c0240c40407040402d03c00c203c450350b156a0010710503501d181581c40801300c18020f4022911582040020801103008080031500c4140c0110380c150381c400d243d20042e41d890844102c1c16564000c103a00b5400300ca604000f01c0320450f40107006403641021081030f82035680080031081c0010407001c2c0300320540e9440036449044441c1c841c4042c1c0303140222003000152810b071420a10320010380c4400f0110403950380100c5190b003006080c201129100501d0550b80c0e10b5003140e5122608204042000400b595034a074598090f00c1e002400400400c0402d0400034040c01c0c0800c080a18a81009984a180303030380001106d80f260781042c003810880e42542d5046401c0600c030401141040014010305007998410520000d800c1d00101c001d0250072410003200e040b10103d00f00100d001204440100074030380d042400d00a25480a15106680700c2da010001900f203201d484258000d8450301c288100e11000780f2907141d18080100d102e404c250740700d20302080180e12040700e5124 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 97492014 1250 97490764 97490773
    0x3120f061002010c050a1d060c1e0a0206161109090102040e090601030209040323041202040b0f060417011d060702060c03040302070b09031c08010609081605120709091a0711 76
    0x25030240c0300c0e10340c1120f4031005d01d01100c00003120000044075500309d03100f42c5078075400000d0b0f2900002c1d8170450440c4100400d5024100380300382c940004515000b000c80d103130003002d03e00401a04000103081e59075208100209444158142655401c2c000e4100340214004c100c01580031542d9428002070032412268010140980e541d0796a804407034003030410011060032480c6c1044025858514805003014081440c803254140d085401000144c0347c00740000d42c0100390900c031034100ca131940780c2120700343c0b15400481030041d80080c1c0381c54010048107035080a440c080796080441d6503c08180740c1d000d40760542c21240c00ba221481e415a0300e03c41540c3c000c0c0944e10080040007401c8071071010703007041d517401016585070782c1620008100d44500d1860880002d061000180615a0003450880c0600546402802202d04850450125401d02e02071759201780d113420f00c82d03105800100130100160a21040900080070180f403c9a80100c080c0c4d45c0d00745000c10080024041072080780c0d80404008640c0040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 97493264 1250 97492014 97492027
    0x30506070c020a0e19050f0411010f141309060816061d030609160f030c140402041d07260f07090906060504150201050f0f060303120f061002010c05 65
    0x1600c03000303400d84040340c000803610400950282c04c00a200d100d0110134860b1140d11006240348401c40d0001000300d03119000e5001440041102c4100034031441a00f0308090341801c40404003559030401200b115101c5080020740050355100d0301101d4004c6a40d840700500820b0b81342c410a41d10791094050820820540080030000d1901c82c84162100d10302c03880303020710f007441850042030a114003201c2c0d44800340c1c0300b408003130052a030441c03013032004010900340990081c0c01d580d02c19040025901c20748000c124400d0030600550340344e03811a00200744034004001403484040004280c4181107622070040340207952103d110000001d0803003d9000329410752130503603461507400c40310410040c1100040140d1000081502000e600c01e802c09442d03140c948585551614401c0c2403d001c1601c464421641003105100d0600856004142c00501c0c2480100940e5180c9021134510700880d0103040c241201c070014001c01c041c2c000001c50080d403094415007004040c00e14180e007a206090310b074900164003000711 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 97494514 1250 97493264 97493267
    0x30f0803040812041b0e01080709020c01020f070b0a05060f0a030201050307141b060a1b0c030c0501060b040e0603010b030303071116140108100f0512010905010903110c01030603050607 81
    0xc551052250710b2560a080f0214480c44000e403048404030b074040344e039940c0c4015070140c59211200400f01c0040c0303414a5810124501c2d184c00e030500c202c10242d900490592100d86080d01981c4020b48406a910f40340d42544c00d1030030031001c060755044031840c079000c08100d80d0300300305d40c15003d240c802503e407204051a580c011541c50740010066030801c01d41c000601042c405002c001e00f00e00c4004461107990a000c80b0100f820441d0207061184410314002c1c298442421041303101c1c0000c40641000e00d0345240340d050507030307062540d003074010425464814082106982800504261a01c0000c40d000c590384000905d400c0340d00640607503505030300a10020314000e21840302d141c0d039000e0b030b00c043d43c52080c1190440d14800b0800d40000d008501c21a441003000c0d68050380d195409103604064140c0d00e40b034102810000c40392030007103a000c0d510850164198480c00d400041803564400000c1042d00d1050800811141d035981c1102918002d44840b0301c110f6102e802160181c1c0d4109014021640b20340304d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 97495764 1250 97494514 97494517
    0x60c0b07020328090608040b041202070305060910060501030b0117070c17030a0b0603040c0312031d0a1401060602250305030c0105151c060e030c010c051306020304030f08 75
    0x20600461004010754405064074250030340b15a940c00c200411000318054000d0050351352600803a040100000400020603d0011400d81250b0004402000c90203506812820300500e0303003002d4214481e04050002410b800581080215032440d810004151030b60b0045064072034076081c150000340512011280c05c61340440d07407500100305041414412400e5501c00c0d0400603000381019002002204011124406000e148a20b4000712111450341c50a5543c1080c80c01d414000070300113422201000d00c21a000303501030070001440360b405016820350607103403603078842c04944103c0d0a54942003100c0f03903a03401400342d0b0060390540e80192040c545040007004400b6040040e4220f060301c03800001010034020b200070a02c603010a0700129142c0f825640301d50340c0030070206a45010f40700c2203030201003060082c401005c00c0ca038400004200b401c01c200d80d05285005000d141c0156520300b5900408164000000f03280e00d8000301ca488581540d50b007802d984034004e512019206d807110b1080781c3c00042d00d410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 97497014 1250 97495764 97495771
    0x70915030206030f0c220e0601090315020a0203090901080606030705010305090709020306030a02090108100e0d0f0c0f020a0605070201090803030903040b0a050418050603010b040606200703080c070608070207060c0b 94
    0x221175070402c0709080e600700c0070b00025040b00c046034403882410301c06604846082603100c1c400782484030780d861640e40c8003020394840d6042c5007c110360210f9202c510038130030b1088420150380104402c1c503c0d61690500c58903520140c801900c40e00c5011000511540280a02d40c440c060400203064802c0c1f03801350710780c040d5000410456143c040c01c80c8640069607804c0301c0318042e0008000a2803880704e4050500104c613074200f84060075910400203000544d501101c0c0b08203111070b9150403150801c403803034012825500400025405000d03d0300120b00d6035440005400034a0003640d41480c2c8a41d542422922071009a5003804030350400c1000b8408048414001c1c4058151403424602d13180d82e8451144c64130103202800e0400320f841e40248a03031480c09010b0300700c0750041100c040283d203151600141200460054190b05084a1b01000c80311120501034440119000000e0340e94540922044da505c0e00284d000e2240818401030103c3e10140c070002d080800d50708907859150350102591180115590b004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 97498264 1250 97497014 97497031
    0xf0d05090d11150a090b1309090303020c06040b071d0f1002030c03030a050601090914013008030a061203080a0207080415020a0201020f03070804050402070c0512070915030206030f 79
    0x1c42003a00d02d5182ca005140d103500724540016210b20b00030300d008009030407541c0310a22403901480190741c000c00081881c01210100c510009130103800b8a41034010740074400e4506500d000b004108000e00040340341c0d80d4031070955039569808000021610341e0b11048000c44c1590003820308200e03442c20b81082c25044030700c1100e600403281410111404e182c0303143c1c82140c04801440d110424030140356007100411010380450001403000400b078030038204850f1014800c102120343c505a40565460341d00851030f5010901080199907103a031400e250449a100303407003490701c081c501000000c02c0186c0701ea102c001507502d40c0d02d15420307465002e0040041d4021036000c1d510a1400c0000041c0000c600c40341040440d43c44c1c01030b0002c000180006402d02d0b4440100d000c20b9082004071134001686074045800b0355004440043c0ca5020a0500d071401c40c116400c2690012421160140c03124030004045040399803615041c042400c2180a03081d80c0f0306a440001d4101009001040e140c81820070444d41c0032520 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 97499514 1250 97498264 97498283
    0x10080403090f0803391606050406050a0f030e03070602070b011502070303030b03071502150c040602071701020403080a0503010f0609030b060d05250602060c0f0a140403020a0e010501020f0d05090d 86
    0x16509100303464081c22175005c001e503c0058102981c000e8010413000410365030608604162a02c0c0c0060311710b2107110005000c000c0448582807155000b544040c0c41c0250420440e0707100c06940c5400c030025402060140d0703400d0698400000e07040f4001c48055607910b5180c0c058040c1070310b51b80d0242c1c040c1540c0690950705025074040490090713880200042d00515540c0200250240b44100c0c50340c2040c00341224040034420002800034a400148031021a0305c005114040f026405045038024042e6410081c079041c000645a07103015403040c0614141c400407039000d40d825603180c50036110360300940300050201f001c001c001800c502d01300c50349060f844d0090082d9040000e0400d2844e0085d84030f0240c071105070101400c00d0103030a40c100200d0b030340300072812412403601d0009503a0a010380a11041b0100300300c070200d2211500403200d020781d4025580688025107050310303820759401000090088600610890003000190680080e510781d20f06480d13205e40b4649030504040c00351040025605032605000d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 97500764 1250 97499514 97499587
    0x910060c170909040c030201080a1526070b030612071202040207020402120103031805040509060402090702030c010501090605091f03020f010306080609060603010b090108100c0c0210080403090f0803 87
    0x443c59182c0344200e21a84442035000c1c01c41c030014043e0500074108080852170040e901c900d100603c01c3c241c0c00d940002c104244221002d0051800751250f0100300d04450041c0039001802c0d804104c0074601900702210302d600b1407405005071644d0390750701c0d1245901400d09084900d003d41002e0340180465800908058a4030340f0b40c0c8150703001c08400b81d03c110006130b136428088800f050302190b00409132004541c18001d608000717921542e2104080c0000e0b100e50803060124900074020421202501c810340001e104641c3c0d10b240c1900200071920030203004405c0400014507000c014000c2807003414443e5685a085821074081c0443c4011050300746060607034851000c80c440c0410060350f031181048000030440e515144042c10f081d600072003046805004848014010b03800d020803040c001d403420303182c00591040390142c04c8690043d08140a9008110b43c4c400f8410b1651000816102c2c070f0080d25407801e41a81c40407100e1031514103100d082e107150003c2c84096814103191072886000c1280a1114081c4032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 97502014 1250 97500764 97500769
    0x3060e040b060a1509030b06010c021c0203211806040914090c030703030c11010e06030109050405070503210c0309041b02060c0a090e07021509010b0910060c1709 71
    0x1410389041d2108200e600c01c00c03006140030402c200203000316000380b00000b40c1c01c40340601024900c5c00002d001480400000e00d0b5a40b00715048a041381e00240410880a04c10310b00c440c0c6251080c20690081c01121ba401001d44440c00b40c040e02c2c0403080824600c0c02c002107170f8005500481c4514542d00039801c0100092818843c0076030455420590308200300c40c2442464185044901041c844c0641c0000740100b010a802c4047c0203002904043c03014001c4411000403144144082c000f154007910200c0040360248995014510075442602141d4415444030101a030b1080c06986c0d8a5001040340420014441804058241c0304e81c1d6401700c90408810038002020380300c24031540a0303a444940c0c003125400b581009415000300716102498540808201e00802071142c40c002c0300101c2442901003403849200304801180210118542251420102c4919010380007c08110b48941c11802c00300c0c810303c125690f11002c0351595140c002e034900c041c1c4d039042404101c0702808580400c0078000f0640c00d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 97503264 1250 97502014 97502039
    0x6090a050910150e04140412080a0204080d0e03010f0603050309060a120204081c03020406080103060b01020f12040609050f0603010e0601110d0201020301090612020a0306020d2403030e060307080c0304030306 91
    0x40407980342c02c0e4411014134180001c5906500c04400b44903c1c1c1024400400d01c00f01c0ea40c4440c40d041d103404e811607564001600b020340b080750b0010806120300b421513400a40c0c041901c400c0c685044000380101104009400b054951303c0c08040c2041c1c1003000b01c02e150b450b010005208045544c00c000088071130340c0e103020040340c1040e840b42c00c041d006000c0d01d003608141d042e03042100c074006007002c60030182402001000c40b007050100410956a5444c1300314240c0c02003000c541c0c41c2c2580f4048a420f503c42ca41204042d40151140c01c01207444e00c0e40100b0b20b0700d010280c01c01d03030769005441d060640c0c0c40c00d195000c4640d006051141800b09101d030380a0b0300201406248440174448d000542c2e01c0d4036001c000d01c1211403a13480500051014510800141d684c1c032410001c494200c000580c079014052801e80080520001100c3d45181300d02252b6a015600e0142c0800c99010340c0307d04007404802d10600103584421902000041d61b0f0100203500c400c2194003654109010b80340008105450b0040700a14 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 97504514 1250 97503264 97503299
    0x15051c170316090605030c1e0304060902040e01090b151503040507081606050a0f050f0408010e0615100f0504090606030f050c04050d030c15060b1806090a050910 71
    0x10100c0002041662800c0c4030502400c05007901d04010f0452405000074010700000c5e00b1503010900001d0126007100060390f000d01c102d0b50390004155a8241440c00000070032403400100d02450070140301410006062161101d00c40c1c1080c0000140d80d05c0c07085001e103034a010340740d03540c0c442c800920381c051741c00b2042c01940c130441c4114003e0000c58101006189451144020100d4026010030148696a030181c00e507a100d400384c2c01e040c012605a46015104e6002d20740500d22019400310b00020300c0401500640b4201c1c403460151021912001c10004501c1d8421040c2c1d50095204000311021a118100e0b030600c4070001c0c60090306080d25083c03c60140e445550208000039212030341402c0c450821b2040d039030070003c0c0e48082c500c1c161810000c1624107000007400340a0000d0300d6064014020781c090210071212100100300555900c0d8081c14000d40c001141468660682c03c80441130b5041007c1100c41c002002071081803454030b04410007a0f8804001d0500e03050306904400000c1c584554440c00f00c0c1c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 97505764 1250 97504514 97504553
    0x206090312160b01090b01051c1d0c0108010b181201060b0304060504140c0310020c0c04060807080d211d01090b0613020315010809070f030605010f050415051c 70
    0xb0b50140ea042a1041c444103030022010185030150860b0b150b030700581107a0b0144030b80e0356515040c524050a1800401c00610a10000c0010b00c024402e21540454000049042600e80c800181d0721001d1040c010301500d0007081d516000f001d806440c503c0c001c80603007250704042002140322038541000400396041924111200c075203d1050004000301c40b50059000d0700c0f60b900038660f0305a0fa4001039030702c90091580580c0301d0380c00100c101608206204030150440060418804070303554200147e40c41c2501e03c1032400c0d80c0941400038a03600e00c60002030010300041d80c41544502d1402c44404000c0004110200c0440700c1040d540401080a000d00d1325a20302400030300340c507842c000c01031003000c0d07610440a1080ea403041040082420a1030b202504141081c030f8801e11a640352030ae854905012a00100340414000e40004104042c030341095041e60043c846400c0a85d68072005d1005862031000c0c500c02030711a004090001d414824503aa502659052042089030625210645011206440c008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 97507014 1250 97505764 97505797
    0x31803080a080a05070c02030c1903020604030c06020c0108161409180403020d110316020d080301090614100503161806020601080111131a070602030a0e010c0305060604030206090312 80
    0x480703000284031340755000d0241e060488507000198002a2250410341000d84200f0502c0c0004080e0f60052000f1070240d40d01038030b006c3e51192241040c0d040d8000a2240000500c5100500c1c5a00d510542815000e100825540500d0b1100b4500560703800c0b00310501401d5401c000c2c0004040b659403000c6c244c44c5c88600c4d05160640c0d061030f0a00a05201d04892444140040540b01c4807820b0700c000101d0f2004103030035003540d104e4a41c520020f580ca044d03091010b41061001300010811201c90390108045481508120981106800600440083c840019404620144000b60490803482d6100146401d1454816100e8031034808503d0f000d0b0b003503000303080142c0c42207006000c200300074815203010622a1660030b00b0a03480d0700004a14901c5401152051a1f0030500a1204c644020540360b0569000301e0543d05d906d0003042a00061941043c0c500d015828a0000c00406000c0d1103188d0145402908091505080d9000e1003982e0303102030f00283d00343c031941300f086007030307030410000740004481140c00c50 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 97508264 1250 97507014 97507021
    0x1e0603150509030f16020a0302040c091508010303090303120b040218041d0606061b060a1a0907020c010f050904020a02010203041505010806010302040e010b09040b01180b030703031803080a08 84
    0x42007110002444040298030800c0030b04030340262a400d4545080d4071402c41c540400072403000c50010f07203a03a403000b5085802d0940007119039421840017416116150200050300000300011145507401b03101c060007081040e80b0600110f84a500f62003c1d0580324400800c01c076032108040350403644500c92080304180c000c1082c81039403a2a000b4404600d5140c01000407078002828007031788907180038000e14855040080c00301120804c0540240308103040307800340d03082d51901c0c19008014040d000400c00c00c43c481c404850a07586040d00d403250040b62554001c2c001141c0080065607414007050301d00046c09414010242c03503a403a40018503e4a10755030001d070301ca041c03a1804142c512803042e24144058100300043c4180540000e4850440b0b030100d4012507200c0e4202901401030210045407030b04820710f4401c020520a03d0200c1078100c070601c44400f00400010030212084803806819144c1c550864942000803a1040ca400300881038244074103400b0035525642c1c2d907480d0744406a400045002107042 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 97509514 1250 97508264 97508303
    0x319090f12020f0102090a060f090e090d08060603090d08100b03010311031c050901030518060f0103021309020a0312110f070302040605090411090408130b0d060510050a031e0603 78
    0x5200c0030f500d00800035410302c02030100003103010703105019950400c20400c40407209240324610600040008410801e1107040030012543c0381c0b4224800304011899500100c0c11500b4100116881034110701c0282504000301d100071070303903168042c000d03240715100c4100100d01c1140400055000754445c400642d0300c10a035509160900e024101102c0345207800d2258000307026000011aa20184e0074a030001c1c6d01d03541c49141c240c2d042c0d852683c0c0300c03141c4a80e00c03c00422050018125050702e00132075000910b1190000003609032100d05000035000041c007141000080c800a900c0302e00f50349a4144404d19155814a6a10780a103040d4440740c0f079400003030f0800c154105032141700003070181500ca0450500e440d4450101d100360b07402200d8040e00300700e0001424031000d001600d4400c52401d545540103076648112b1072058101246003c2214a000305c00209490000780f4030071800b08680b0340904090030280c05400030001044180d603003440303074115040104e225200301c102543c8100d1141c910749400d2030300c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 97510764 1250 97509514 97509523
    0x30605120f120c0d0f0903120c021504050607060b15161103010501030b06220c020a03080606070b130309050301060f03060c0e03100903030e101409010902060319090f1202 75
    0x42c0b5580380d01042000e11500440071408203100076060902800302e00703013641c08454000407680302400710003001402918107584003504402c440c0c000c0300c056900f503032110444042407141d84500f5603c072030200503d000094441e080981c404d04014040c00104090b022094000c2d4403240501540c0e0b915041540704015802840328100c42003503000300415030565880c0c204401d0054203062240380c09260a984201e191a0240d29038000e0315006d001c8802c940401a5580d0b50384141100820304a20014400e410060b003074409036030b0031040500e596242ca4503090401e4080072029010408010000329107620240101001011915000c0c3d041610310f0030301c00c088544990010f402c00c4001c9aa020450350b001449071031039008594000341c15801032400b5001040d401c0058200d5000382c001c4003c40394226070100d00089200000101543c0e52018400d088405244009520003030138804102c4c1c0d0410030601c1e09051880800000e2581c070345480e0010f40c00f9a80310104c07500600b00c43c264030469414031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 97512014 1250 97510764 97510783
    0x8030a05091009030c060b0d140c240706052d01031205030906010b030a150b03090d050c0a061d100b1f080c030912070503040807060804080702090403030605120f 71
    0x40c810004078005035401422020040801b80c443e035100d02e24020306544a5248442c4603038000010000011081443c580391100c0c07003081c0d0722032201a4941408140c41d2889040c1c4540c2e0183e540f4601410365039007000a10001d042110142107802c40100c10f15a0383e01041001c3d420700c501e00e003042d03145190405070001c059220030100082402030040d8028006a2a81554000c0355229142e0382c45684c030707100078060b0646040c500c821000b07002500c40b183e1b20040d4001c2d103105094804000c014401510030303215140308620254001c01110011908551101d103403614211000004c190001410518102c0c170b5108a028040d170700d0340011501d1800340880c0d503940d1f44107403684c120f031420b450003c0c1c0090402080b0700000100000003640c0700405001a14040482c004125110719003400c096aa03604680183c64091289100214400c0d0180011038896688019400c1c0f50009940c240000400050011801c1c035444010100c1c665480360039030400d440b112801403101e281c40d0440d00e483e00b039001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 97513264 1250 97512014 97512043
    0x20f06060117040b090c03010207030e0a050423060102030d0e031b0c131112070906020708010b13090f0503030c0c1605010c0201082203031d0f1b01020a08030a0509 72
    0x80030074070782c0880720b0b04840e400750300003144803410760700c0c50050b50804c1003101e138007541944005a190304058008110040d0031200740c0360001940c1e26032080c04120344110894074001720000d125000c600050440c07691740200b061040e07c1c14070502c600c0130010354124010300e0129030030204111000c02400901800b00454010084c550030070100c000c2407218038400c0c0124040364440401384021960102140d90340702100c0c5e0042098034160324024086402801140010300840c1c2000610a4050049040864000308100c0161a0304010400284000c804c00c031002c107408010728009c100300344007a42c819503503640c03410b54403000a800c460515030041c0000903d02c2d080481841641d030300c00b156200ca1982030034180d03415121080c4041c2800e5140254581204c8062807100406905411030030910b6402c3d080d0445480850741e045413a17a081004c0c042c141c2d031045103441c844102070700d0310040700603043c0191190742c0c0280e25280c40c103030300c122000038140392a8400c1c418000006c001590100a96 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 97514514 1250 97513264 97513277
    0x910090b0a02130b0301030303050106120b010f05070501141501120e0303010302090414030a050a12091101030f0b09160f05180d081204050a020103050c041a160203030406020f060601 80
    0x2a5940c4145040340a0203581410b50b0105503207885810103014080545498216540c81c1d40c0e40b45002406418240201c2001400d01c060049215906008062504105841c1d441c4120402c240c21111a04110700a03901c564a03201e05031103c0030b6607815940100c00700d40d0140001c0241c4000541a6800c0707940303100503d40341640f011881400403096a05683d0304880c01c0f1140d0321170341001c1d11101010083c0d001240400580b5201241d084401854120900d444140300140c485120104943c20150064900f4040d19624182503110703501c02c2c0c00241d0356030400144c2c083d016020034111207003107881141d174810303004d2021892030300450f102c1204451443d00c0303442e0510f00340003a01c0d050541e9a580e8019607002d8901001c000a14055444545240440d254585031034142a07030340b0003840405a0200b850704000c1030300d06400c84200c8041d02d800009081c0404201a01580280c3c0480c9840b2000c109002d100001070758140010001892181e000b401c1d550302c00039940b03061480242513181841103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 97515764 1250 97514514 97514531
    0xb070908060f0402030c03030408060106180b07030305061f081f12120903060920040e0a02190308041e080304050d12020109060213080601150818070306090b0910 71
    0x10001a0541c1c8200c03000c00100d810f442e603102092500790b20b115901d41c14040441c0200340c0440c0051090f0403030b16669a035400d02002003400900507002c0c0c0c010764074a110308101c0240031070f0103178100541000001e040b03a1494013000003561401c0825042d83c2000075080c0c814003c848480605141d641507c07408040791651034420354549900750200e00030071009200740a0000180206e60700e200a6410081c2031080d015a4030b0320580749065480440340d007000c00f00b40c44600c0e09161003641c22100100000301084141074082040754ac1e0004c0f0b0040300215001400f100007036098010f00300418848080f00c0c8c5185000c0344160b500b807030640109400d580140810446030307540741c10300c0c4011034000d48081c002500b140700490250022400192909000194000283c415280404221000070096070306076601c610400301500b980c04c80b03050024081e9004a06004280005d240c0060300c0041180c038a0f50b940d03640c1d0001e4a00c80c080c140c88043d80d000411028407020301803080981c03201c0908019122 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 97517014 1250 97515764 97515779
    0xf081c29010c0303020c0d05031603060605030105040e010605030f0319081510050903061510170a0e07030b0703060e0105030d080c030603070f120203070e011d0c09060c0106030b0709 80
    0xd080900e810304000c0002c900600b410b010740d0481d40106484e0342910351a2041120241c8507520681e15102c00609803840051302034441c2c45220151002556820314503444d140412000c0d20344081c6207403665681e0302002620b1740d0208248560480074001564a500081c640c000302209034240210900054000f0020114030140c03c0c1070fa124001c43e0326000020010404039850300400f44220741510030001400a01e04041d00d090f601014111150820f1070a00f6200f110325546800500c5001c03120239001c1041000b0b075070802081e01e2260011141c031281e498032140f010920540d50540030aa545100740700c08502e803603150f405444140c00400159a141400070f1840c3d034024a55500d0b54000300c0820380c07540e0180701c280001c0c00801d180406450700e4244003080b998048a04034400d1213840303030000b51030140300f1442c5d04859080751524031901121040f516a004020041c41c0002010080103081d40d07100303c05080e9581c588000051403a04518182e900c00381d01525a005205d4516030402041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 97518264 1250 97517014 97517081
    0x5040b06030a1707150c111b0603040809010309020a030b0109050a0902010203120a06080a0b09071205030f251b06020c0604060311040b0a0216090b0904020d0f081c 72
    0x3d014840880343d80c0c0e012810184415051204018640d80c188404100c425901400c409900c41c8170f2401e8131407100c2407510b003041158040a800e40c2204050001801080c2c600d80a810541410f0601150400d0141e0008202030312540084901540f0784005110070041d503c1040c0e440b002e0740c02c040013510800c1d00081d5880c056184030717011004d8100001454110544c00801c0101000d10032220b0302099468552452017084035441e07810701c565000002e080181401c24054550030202035445c01112071050b840d50b5015a410721001602c0100001c00500c0100805101a00824491101304060b8011040e080f1503580000215030001c100c80352683d4a500c05c4408840307050030002450b1081141d802c40500440d031000031000408a50380c00790030f8002c5404600f602d1264020300c226038880000070700310f6111002d903d803c116964002401410a0440741510502600080c440c404095580843d19808130144407441b5490f100c7c141c1c5800168080c40e0040441e00060500d0242c4148008640 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 97519514 1250 97518264 97518293
    0x307050a0915081e0c0a0e13031106040809010305130201120902011e09061b05070308031504090c050102010b010302040513021c020a031b020d1d06040803040905040b06030a 76
    0x54603030300c2d032401d41d1000c140015400245040f0054844220b414040c21680381c14400c2038240e540a05140c030fa00350300d003800c403007820f1305c08a054003262603c541071015130440d018803088060040c2d1040844180000304010740c40349108009060b030743c4400c1000107064407400b81006002249540d25071005030f800030343c500401010f1120028408a65000403602010000c0c1d070b4094648100203c51181079004c041401640c010362140c1c1c841e650030b81405d401240201d603001d0306030340110b0428000910200700940d0000501c0c00350405581e91240080c00311015002c003202c034400d42c0c0c0c00c200001d50b020702421400c81001d00701141050f140101103107558001c031040c1c4402a50000d29030850300700f4854005a01e040c010004c64643e051107001a00400c4040c2c000040105490036100215100094150700ca01d070030795030440041e1082c1a1014105d00040481c2e52180c028031022450300d00401c080c2004002400000c110341c00e0505040810200140a540c041d402040b04800400c8902461017103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 97520764 1250 97519514 97519529
    0x12020307081801061a0417031e0703031d07180e0a14150a0203060301061a0703110f0d030204090c02030c03072a17060703020a1403060414190b0307050a 67
    0x45480b01ca1401401048290041e660f2000700040c0070401c131582c1c001910585192101e40d08030095203010700d6a5900070350f202d000e4086250001d4090113035081c0054840940300c2e040c0881d004911640b03c0b070921101525981c01a4410102008040c48120449403030009040b4100315a840f0740540a4507224000c802504600101100072500c1c40c0030071180c3c003c900c5181c102401801c10bc1c80b107070040d42c01500e0302442903081510114058a019400032607200041110601e8070410341d40603a43c00c0002024068503026850060000010070310030401c100c1c80c0c1c6c0d6070050740c03241000b43d08411940d6150701c2f10210f50027404020146000081110f66075a086545514005070b00d60700c10b080402007513907070020140300190000b03c030750120b0300c02044004c041c401e0700d59554644008030304a01034060050005107101c480c072007650200f00001c41c4c00c00000b51000c145540010030240e42d402050b01c070740c02000303020400381000740c58078820404200310450180c0501c80c60180000c980d8015400b4105 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 97522014 1250 97520764 97520791
    0x6030203100909080705060f012103020106090f020409110703050a050c0123070f0e0906010c02130c11060a200d020d0e07050a05030303010f151803050703031202030708 74
    0x5a07004603048040c40100000390003070108490b9894061074540010703004480a20600000c83c44c034221110446040c1c41001140f9103030043d410383d040d44903c5240070305400355503880c10041900d41141c0503040d0100100400560340c1ca20b400944001c4031a0f28015102c0b405041c01560300190b03000d000c46200d10114a0007540381d8840040302c90040c19610440d0a020202041c2900001400107051344682c000b500c450744a4481000243c5405480750007140d881011000024120346c0a00e003e4404140080d0210324031400c852101c5040b281d95141100114032255030030160104104005a44624101001c3c002c0d1018800068010b110002c983c600303c040104040c40c010040b6819100703001c600380c0d810301c0411462882c41e9142c0b013541c0542e502541403040045014280001124100d034030700320315401e94038503062005030300d0002035080c0c0040208001304131102d60070110100000e940248044c2c5462440c0d4500039211902840488a02900510402922680000c482c5a024441040c100d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 97523264 1250 97522014 97522021
    0x102091c03140307080106090e060f01080702210d050105010c0c15050c0a0b0a05010b090d060203040609020a0902030f06010804030219050f010e010e0c0319030c05010f0515010206010603110406030203 88
    0x584041e61402c612581c0a4000710030006281c0d030141c0c28038100c0c3c1040e1100780500b0744903a01c60701010800c44505401003107450b82081107512596003e50320000d40c0c41038801605241c641600c1c0d100c485101d80d4150030001c20000c40705045441118010002401c00400d040e02d55903412401c1503c07403265642d12681311507a15061030003001141d020405850585034109110f01d0300c5500e0540c15544104024540300020400c0d100d05c3d8211240b0711001007002c0c20382c200f5552404041c1d40020422241c0c01d440d544040f006072030b80c036521405800b028001685074036000ba0303076610414000b0700d03042c100f02c858410310000c240c010840b04038000355030a80c040ca42d1007a003001481c040f501056100e1f5036281a5050314a10b2041d400110760086800507103403881410750400da44ca2000e0800000144a071400d10400030f0700641c20706180c0c91007200041000c100d210340903412113904a514882141d034091110040d50390510409014256a05040003510556402d05e0914091409050305044c2d000020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 97524514 1250 97523264 97523267
    0x7180207080706020f0a031a01020a1713030c1508040b06010c050115121401060f1e0b0307030b0f03010905210c060106020706080c091c0311250501020102091c03 71
    0x100e822442c0c02c410f00795a12502000140f4459004644801c0068503020940017003641c001c4590408440503030080039544940d0b110049141040c6414074084c490070403d1880681c81114514000e6010300042407515241040d40c0d02401c5e040442d84041155101c100000210150b8400c0d401c1102803030580c1c006103052404600600310104040c0a4980a00e0000303094407006803810034851041a110480305010b90300c05081c0c0c0d50600800c1c4036456090005d0101c42030010f0906508460100010170051341d5000313000465009523034100001e5254550f111007400c1c038403098200b290fc03d50080181c16035a8444541361118800c8004111018404820f00304e8600015a0310060083d0705840c015656208041c1d0f41e03c56070710444011500044c000340c060bc0b40d51b001c0e113001060240c0b0380141e1104554080c001000142d108a041c4001a010420100c000700070100802c1101c403e58040c0107500d252080b45151140e1002d81168010001005980c0b41c0c2c1c0c0c0c01880f4241c04000c1c204516000303240 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 97525764 1250 97524514 97524517
    0x901020a02120702130504140f010b0303030105041104030f08030610021915020f12061f0804020112020415090503070b07020d02120a0213020a081006020c0d082a01060501020718020708 81
    0x819175418801031000f0700000e02c0d83d9005024a2030216002c0c0040c51070814260752001c0045a07254006000411072800c060304414142c0101407c01da107082e031a0380e94030b40500720b80705065420041c007004011081c1042840204146118001000100000182d0003110141d28000034005410034801c01d1b0002d0f4103030103903010505076605003925000c040004200007507040341d030240320311001e080b1200c100101100c0c42c82e688416554031004c641d200d80040d07807148101c0d0040903d03280d08000025040340950200502c0600035656038000310303c0c1c00e080604c0c1c20800d80000e243c00b101088550010fa8400c02c0c00d00107162306580e000300344480c1105d420304003030f00d104020707411212001110b00e2074825540141320007a502d8841850f152030720f1a051410b00c001e03000704c0300036a00c000400c40c0b092814289980555120703001a0749002c605c08800200c80058105400a1480d0043e041105020030b02612010300028030041c0341441c61700300d82071109075070481018411903000900d00b040c03211440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 97527014 1250 97525764 97525789
    0x5030105060a200a110a050603040f0b0c190305150105040609060804020f0d0c03060e0a1203181205090a08030a0519050408150412170705090a030c09060e0901020a02120702 76
    0x2803c0d1120303030b08203007480ca10403285040b000c0e20403146d0000100e4140b40c51000e80c1d0145800c1540c0b122000380941d0f58041d400409008003440080501910324041c0110110091303030406a03034089843c0c24901c2040d820b040c00c24010394144842400103204940d80401c0c400b01701c0f149407800804580321800071418400780202007a4010741c1d082e009000b40f14400c1c19130000c4a2250004008000c0701e1400140c41c1c1c1d0720708000030701d07014843c0c0741001314500c2508403610131448061040c00801c6240e8810140a00d44a00c02d008540040307844085464040c061030010415900913510b003500100c8010014401c130b079130000100000d020300d60380c3c0318426000c2d9000343c4009021181d0751010090780722074060701210120354902e1900f042e110513030312500481c0030308241603000368440d45032a0010768240d0465880182c00801040000001c907440c1c2413883c0c02407038210000280c060414409682e20040104182c48903030040115003170391540010306451440c1d880000640314620303403000074210030056 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 97528264 1250 97527014 97527077
    0xd020301090e0d0203190c080d0504030206060f1f050307110106080703020f04021306110a0803010b180108070807120b03010e0c0a06090b041202030111030c0a020d05030105060a 78
    0x40008070321610140e001840c200c0c252012201d40d41d140c00c0c0201c0c2d41e07110380040d10581200d50524090000c7c003074600c1c0024188102c0f101d40c01c09109201100403039074100c4040e07005910403030901403181040b00c8030294407103054401640c00905c4251648803400c1c0d07501a08100903001000a214602c10103800c00d264001400030310a1541d100750050390780783c25000a84c800d11910468017a035107401e108a80300c40c154114008074446c2350a1059400204070701c680501800341c4184440011210001103001e03080341c82d041d03500d80c5820404d0021100746903520070f0501110805105e82645c1041d00c3d2036200da0a85000b0502241081a0502908a5041442c0c0560078007400c8440d412020800c1000003400342c03a45110b695460004580028482c462420032075000c0000b4401d00310200101c01896002500200700100d040000709447d601c1112401400b200108400e040340358103202000e068105485d00609550425000520a00c140d09044040c440c042d100248200010205a40c404014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 97529514 1250 97528264 97528267
    0x20d1505061f08060f04150f0f0b04050603011e090c021c02061006200601060c061505060a0807020109050f01061a0301140d0c0504050a091509110d080d02 68
    0x80519080641825903640303100b4940e0280c030700b504800400c0641000020341e40c44821a840d000d0510421402c0703504d1154009888810703c2420409031280c40b03000307040d00ca0760855564644403200c0344c400c1e500e8006c948148405c100c20000c0d03075902d60560341035860070035200c0c084614500d06503052a80c141d00c0f00002e2801c0ca0401c404c103e401040182000800c0350a050400748440300807603c5101c11103a040c1107034110301c030600520744100490b101c400c2c3c04c071260788002c840da4610b1170f08d440c00907800900000d8100d500401008014000c81614403524540c0c3c207078044c2440002002405404210010000110f0000b07425501c02d4104e00d04164001c030276030b20a00340381d401541c007034040d40c05143c414a000100c5481705036110002c803812140301105040b00307034031500100107684401400c00d8884d0b207107828004c901a51380b442498004c8041c030b600004d64140a1804130550309052400368019468070b00c16901103101100c00d00172400c01250024841c0380e05140610b86070084a0114024a10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 97530764 1250 97529514 97529543
    0x70210091a0a020c03060108300d0506011209030203040e150904060203090c030601080a0f03140307020c0103060b0711040b040f0504050109020a081204181107061a01030e0c0607020d 80
    0x1c1d40000e0425000075030039184035402d4075040c10b07901d1030203110b0100b5070360101d002181d4039076009080c1203016098080100300400700c1d21400340c580c1c000320f54000391250313541c1c1442402d68200400804543c0004003c0c00250700d1520081c4d180e014500c6050542c2d60824001140d01200c2d01005200320801007001405c0c0c1402d0800350000c2d0001c6540200718400c240c1c4844440c5030000c1c0b850304843d00700b0010610a4100d981b032246d204d0034924124203012607a02d504080c046850040d5200d003000c0e500500e000450100014127a0f0455802110000300170000580403603040c02c15a1044103003540d0125a170703942480031600a044040c0b4502e903403880e1209000030401e06400c41244640205d41c080d400a440714041619100c121660b10b009504c20002081140e605826400131141c0600e80091010f1000220034900d60001e0001c949003565080001c0502c03403510079017000c0c50790178602008481551103910f981c0d45503241d12a0310807030300851030004658030824081100b0b580420359022024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 97532014 1250 97530764 97530809
    0x3010c020c09010909050307110d0b01060206040611121807080a0c0911030108150601020a080301032105160201030f060518090d03050601081302012d0e0f0607021009 73
    0x11452000e00344604425000000c5440407070051781842c2da088005149421407a9981c5404000c1d80c0d500349800060401000000c1004610240d000704115005006c092801b46080c0b42281c0701c045200b40303440020b100800381405101c100035808400d807100b10070031074080c00c0b401c0d1a100b45a0b1165004d4070400e10100d00304001103c5810845215041c24440d51004440d01c00e451f0000340a80c00403070740702c20b00003003a02c495040b11a4102d40c0600584040024540328400c0c1a8400d0300166000b107161440d00600f80c3c6545540d44100c2e01c41c2c9444c60519282085c1c4001124064130041d04150719061110600521079000c8401804000d11210071000028131500c6080001c8880b0000c90098011400b10b40b40280601440703101c0594400b507966a407403483c21004982c490b0141d04010400044050303024800600104105801004104288000303270018010341d0b042d8040c900800103d690110551914016175011503030403107914207840d107200e0046503090a280d000c40340203040d49000b0b04031b00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 97533264 1250 97532014 97532023
    0xf02040501091205120315270703050402060307121425030207020a0504020d0207050604060e070f030c0605030705270913020f010305070c08190f020706020c011d03010c02 75
    0x191401c1c0c98030ba4a1a039030300d2144068000a24001d0010340011003c14200c98001000390b601c11020021400201140008134042c09841012605400c1200381c59902c4050101c8079a03600004038541172095150aa000c145240005072040c414403501404120b065500c580080401c041d8038a100b01181c036141e0b44070f20862950b40311102a2001100032010003501c0b0b030088440c42034020b0300e21800c107407034007082c00020744c4500041b51310b075642401a00b0001f04284202c40c0210b0081c0d0011410001184241341809015441000701c1c041c6441c041002644d500c828000f2200d803401c0030380e01d036600d182064623944142681c81d014140e0301d000b00002c854150542c1c00070880296400905a614880e07840070111000324060360017001c441700d800156101e5000b00307500c06080d10709080e10400c0c03039840f8845608907484214484140b50360082c1920303480a500800c0d4a120300c00ae1200a150110103510385035807900e801e04001031262910600b5035900d004111032040600200a141c0919800075140c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 97534514 1250 97533264 97533269
    0xc0901080f100308071104150e0c1c0b0a15020a050606010305041a0a0f09060b0907020c0109121a09010c0e120714040e010c020307060e0d1d0d060f0204 67
    0x41804540800c081c81c001540661203002850b440d0080c0c141192511100340e007005000301c4440e00c0454a1001a0f00d580c080d00200d840100014140c150807c200b82400c80c074001d0405112504c01d020040280300c00309411303000c0c0c070f40b2490005141d242e000d021480d80105a000074000810f405c043e0030b5080da00003405403140303000d0310513107881e130329440c004600b540c8040e14042c160a400e0004039810308409081c0c0c940051000c5000101030007080114020b0720f5941500b6034101e40e5855030600113041540c0b805e035020910748090050b2280400010f81180b00a011b070040164070486040208010700e8415031051900703204c881100d26243c400700c2d0280000c0d41284002800d032400510880c11700301402a105001c04000c0d000c0305052442e070144c01404040d03900d60050b120030100c00140070030702c9018044207040c0c0c06036580c0c003441c2c10720005549414001c0202c40d402181888900c6621201d606518001d88440d0140750101c9800502d800c00308000240102c1d18014152100590342ea004108 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 97535764 1250 97534514 97534517
    0xc121606020f240106180512031e030708040b1005041103041a0606030c0c0109080c06070219080a080613060e0105010e030601032303190906030608030c100f140c0901 73
    0x2107001d4405140f100a441c400801d00d901490300014040070317000d2400c1d044480741c4081c420328a282d8803400541c5132902c200c2c9201c0c89400005c1d00300900c00c6a5580848414a1120124070714103010340000d00040000340058805482500030507504000380701c0c404028540244280001c1d541c2024404080c0c0c0203031011070302002a94101c40c444445046264491040140601e0941d51500010603980d80075500080140d541c43e9030200018500c10098030310034840d8001040301e46008000030380b801c00128803443c42076000484800c00201000c0c01c41d6105101071038000065100e01c030110b0130740701841c04400d608034100f20000c107118105202071812103030b099a0b1101001074040506445403420b02028020314072050300c8a0609101403812a951302444c400c583c0340c00811410400462500c00050000891a010401580b81c0c10301072031024060010103185030041441e000ca69900d041c50304050a903071242d102e220140c0c240c0d40224030407100d8421b6002540780c0075104a10a90000703030b543e030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 97537014 1250 97535764 97535773
    0x20114071502040e012102040b01020f0a0c09060806100b070305070b0405010902040507110703020405040507050603070306090b100806090c130e0412021908030a091a04061103090c121606020f 84
    0x18140c400c54001c0350500b030364450544100e0306c0310f80a00002d40452001641940304006040d1400b107401c0150340c040e070f8011040304d2405400c211124054031450391044007240c0c4580e040c07101c0901041045021281221105965050b180c0f4090300e05010341040070b08000c940e078003004280101904820542031007294100560341d10b990381a500640081c59682c01540311107030500c0141020f40c825078001d8040e00446075178603a0794000440541c01200c0e0035001a8450700f081043c11418002d899807607108480d01303c0d40b140f4146004100000062406204500e10070200328505a044100c41100e1059000920425100d50801b208214181c2e001c40320042d881e520300c2902440400c51407507030440d514803000c940209488500700d036040541407882c52503071008004001410101c03492040c408020100c4082d1610b03080400854400c40e18140342d040d010810004150070100d4450242001101c0c28400c4080110610b441d00c000b5078000314aa14003518045055034001610048010442c0d0448 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 97538264 1250 97537014 97537019
    0xc09090203070e040e0c0402070c080f120304080904090210030b0126010b03040614040f030e0d0308010501030207030306031203090b0907030206120414070f0521060103020114071502040e01 83
    0x2182248001c4600400042c01c0c801d81000c1898107802500140d0000c0c411542030001c108001030484c2d003c0c17041150646040c035010401042c0c24884801da0002b040007501400360100413a92891000610081c0305000001c0c02140541e5035600c08900c0d16005800004d0034030f020714001e0000d0102c001101e0124059410741460340b55052640c030780d4262030148a40581e41b030400182687c0e00302038401c455007603d0b00205a4100c200c003840d00d1145014410b22801c48410b0304004d0281c000f401081c5000359903154000021a03042140141160001e103070060b52040e0b20b0500b10010601500014003d00346088001c1c030041e450382040300c12901a08984549071a410380703059542405203c002e40160342440340070003070b122481083d80e05c40c1c003c0745001160450003031043e041400b1504244030490404038144800c1c1810b0050200c044003040c4180d10900030188030594038841440001c3c1045045902001041c0071041034416943d030000b0403001d19400c1000c2440070b900329004072001c110424000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 97539514 1250 97538264 97538279
    0x40b010f0f030f080702130203090d030e0610050f0f0d0809090601050403030e10030e06040f140109051903050403050d020309010e0a050d0303110906181002010501050a06051806030a0c09 82
    0x40c0102c070b90120b0740e450748400c541d031040e83c0b6402ca56810381e8011400c2c52001d80b00110790004504c500c10a2015181d030703007d45a4081c1c1150121254070784654071040c104100301846603911400d58030100d403448101c140404c0001c2d40344514284e80394028070000040402c1151040280400c030200300c0d00c2c0304080d603825004444501132480060001a4201da41e00c5690811124a51803220285000325008000406141c5446010b0320221030031441c59468209000c2d00c0301019134ad5041b40320007401000c0d12521407596661011101c8000c08411040c104100350044c13045034002c5038454199523013204c0345003004c0d4032030b08038a080c1ca01184030961345802c9858000d41e490140c1d00018030f031150301081610114010405980205100c142c2001300d00215920040600803c1358044015040e900e401001e001a08450108070000e580c1488014400c9644287d2540c0a0b1101460403d454200400c1d41500b241c030941c040ca600950000306001650000342c008240300e030a140c8030b5150b400d80e200d40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 97540764 1250 97539514 97539539
    0x50303030f010e07021207030203120a0b0609061827070201060b2b050907061101020403050705090a200702030610060509120106030506070c0b130201020d051b06040b010f 75
    0x3400c0070545000c40060100c040c01e40300b0301c0e4011929104880c404000440707981810f40c03110307034103034096400400e52000e0558004d400310760022000c1010b01801ca100380c0481e066020798000148182004501081c100c0885c00c02d070424003000070043c460201c1003c091000e540c107104030b07000d80d2010660004d40082c0c01401a18100e03101000c03038520705403003007010fa24006500820888180095051481d111406000366030181c1d1031403018008261901d480034003007052495a90310142d0040c00100b01280e00840c000c0d040f24419900812030766a80300444006188282d800074982034002070f00c0f80101c0c010400381603680d200394200c80d2503884102094407104410b1150350001201040401c00c2410884481c0d070141032a000081102c0c0d4036640c66a0134a80100d4441340001c07040f104800a126901c08095001144c948202c0c2500d08641c0000307442d21861841401800000109118a144210860300350180410250344040c2403502d807007160840203102c0d030b580c100b4107003001148103202a031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 97542014 1250 97540764 97540771
    0xb07031b050d0e0f0406060305160201090506010603090f060203040c031118010b090a0e090307020103231b070203060f09210d050a0b03030d0b04050c03010b0d0b150a080f0105030303 80
    0xb49502c181240b01191802168078940d9040b240076420b0042e9525540a04405001d25440210340c0c0c1c500918001600d103000d50701c0c03c045a0510b264240403c2010804c43c1c1911864600418580003030304007420021448400184030758070004c100710901c82c84941c0c40c400c1e04c0c8508000800307a034040e020031922074103083c5000f00c8406004010807240300b00c040103040d0298080c02032000240c0c1c03200c2c0c401e81184100d894217945c0d00b00103284402c40da4148100701e848040320340074510484c0b009100440740b80d4018003000282140140403051105110706460840d94000c080300c826142a260401312400283c800c445c9911815021024404160144140d10542641254184407103081d464015100250901180c3c0c1c3e03540b0a45c0700d42d91414801403401440c0c7d080045850300c200014041120303030090804032116000d10042c0100d0403800100d50791103804c21030100b08401c80c000062142c4400b50703d01c640b2800002034010f04e603508181c0941c440e031062420b48086a0b41c40d42816200d20084 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 97543264 1250 97542014 97542023
    0x7090501080d03050601021c0309050d0f08130203030706050403020309040609110f090d020409050d0f03020319091703150406080703052a09010b04170d0e0103020d14010b07031b 78
    0x1000b001c1c030640329070b0040d07030b000380144101c0300700040c0d06006890510b6030085c0e4000203500c8030050014840100554200c4c0034291401c40041040104001c2c0a0103002d032811410b840008110300c15940c00700305407250305410100402130b6007018039010396241d016420703a40c0aa401c0c524009644a0b0912515040e03840c0341038058034000440c40000a643c3c021040c080d44076502006c1a0050380b128400e00c2c01151058004210841110b80060198400561000101401001041000380c070300c084400f81000c4407900070690580720b18002908010032a4400c024034008010401131088003070010100800c1a14100055a11106c100d44c8070f21047c000580a58480c0450103107d0580f10180229601201d09078949107220307000183d5030007030a0740484041c44002c5014840c004181012421a590310b000900464241d4103006c2c000d100352003102410706602140b81030710300130349400c000320080c41d03100d09803010342c0c407130211034402d8014810540000d509002242c0036070341c05080c680c0c1c240790070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 97544514 1250 97543264 97543273
    0x3050d0306090c090f0b0901050c010c05092e080603010920010306050d080f0903030f0a0206060f0405040c0b0c160305070914010e040206070807080705010903030b030712110307150305090709050108 87
    0x5101c06c060b481d50051100341c0c1084230400c070a44080000f84641d042100860341d88903038808811b810803002c1d13a000d2020300d01c80704000b10101001d0158a40022940701c060070441d0550b9034810020b0300400e03041001528514549100000510b2150466482018241c8040140d59101d205100340c08007128001044a4000c119a07109142c26101078410000002e08992410341604840301e010f4000200142c00b41c1d201009001451410130811060f24a09980c02c21262806886154840c11f242c481d14003035840001e40100e10031010700c01c03030900e404c040c40c0000000c0d6403440d0559603000c0c00d1182d1070320395103071200004015000d000102c0c1201c560301c80e501c038683c603640c0800034a44d0004204442300c079800c0141500282c1c0003800f50015a000e80000610202581005801e60f6040c3c00070900c00d400211003404094548241c840302290080554410b8038850004a072a007940e0342c00c51130040e0f8030061250381a0354941c215610030340246050354005030f0354261250940e1003e000f0310180d0f810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 97545764 1250 97544514 97544519
    0x20616140d120e010605060c100506060c0316020301060f0e040506070305010f060f05160809090702030412150b031f140c04060806010c1b030b0108030708041a0403050d0306090c090f 80
    0xc2d00d800500c0d000c80d40da00000340c81503480c1c0000308560300503030b5a90f40301d070440d03e40c0101c003050030310400b60701200a6860702c2c9410b08203046561280715100c400c00b039409212110701c0a548003540400f016125401e0403d40854884885030110300045404036010300c0b400c00021404e82c401d000b510304880107040d2250300542400c1301910f100740c45005102c100507061004203802101d02d04101e01c103134010800540e4889104080c000c0381a4014814815580100010070801c090358bc110303c4030a070011002403400e414110080003810750381031074590600c15034649109294404120300d240d8643c0110410400345240e6040c0541c580c12611100e0409091100f00500b0380556031142d0300007014500003180c0e2030180e460210480328441c41068501c0e070310070244100100498144d000d402c0a4000718100100d0740c1d1841030b18481c41c0030307026042c2041480285e0440032032054401031355100c4161189501c11203030090003480c541c07160495860408400c44036a9008071030134000d8405641180d440d0f2030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 97547014 1250 97545764 97545797
    0xd0b04030503070c08030c0c0c100e040e010e0a0302060f0f040f0204090303020c0a0c090f090c0b07050708030304030302070611091e0a08031209070b0f03160309020616140d 76
    0x108020909020700c131020b600000018180d03c0218407403004090400c0c0c44140865000e440c0000f02c01d03400c0d000791089259600f08541003848000c1244080341c01003440010400344e03901424070706002c0121480f030003590808041d004210350344100c20841089a065132a550345604551090f1009044e1420003040180981015040704410714000c0c1005480c25118080341441c0a1519509540152070030805005c0d0513500d005052075020a404203200c00071890b01c075010003410034802e540310050300007010340c1009818000400140201d000340d13a120f290504010307003e940b013080e088410300d24152040c40640c4280f420b4401e07c0c1d10180035585003660080004071101120394007198005500240018034903820030061003200392142041d91142481d085003484d0000c20340042003c00810b00ca210014030b40e0400750f0f68844d04018031840180f64200098001702041c0c0c0005e034010300001114080c2144107441c5a05403441010482d9404404c00940c1e070301c1d0503441c00c4800028049422008104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 97548264 1250 97547014 97547017
    0x120e070b030c090603090a290708040c050d0c0602010c142d04030303060f0e04050c01030f0e07090e0111160308040305070c030b07020705150706050405030d06080601091109090c180616110d0b040305 87
    0x1500c150a0400e49545910014220000502040394070302180c050a1140c242d0a008414048040d42031590534442c4a0403868070703500a25996100c12003540c1080c07070a5003070801030b4960309144c41c10140d0743e5035180d06008014000e180924043c1d120102c1000035241c14410b40356126641260141803082c21039801103001c3c3c80d040051440c11030300c40d070702141d980c0000d200610042694200000c0e908200c1e41c0300600391042a4040321400106005020740090f90030304001d1401d40c54a0805843d030b54915013921240109000500758141350344003c01000782410b000e034060081d50b001c4640d0141e8940422007070382c6040d5866070540d00140310f00360004226030005074100d8800c00580c0e04243c1c000b4103440469206e540190341682c889401004011101e205922158a030b114455180101c4500420342560000e00740b4a440071000940301030441d00a86100080c980080c11a955400860b240c42c016030b00c0036100307441e12482c407180c0c403c5500d0031000902318103912081c3c0560303d42c0e441d00d090720b25 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 97549514 1250 97548264 97548271
    0x8010603050a09060e030705070e010b1603170c04060e0406030804050d02060c0607180608100608220c140108040f030302030711030403030f120e070b030c090603090a290708 76
    0xa2644030b16422001071410300405001400005c000c5859109904040d0310b05080c0e80d00c6815040d2414005205402d480002c54402c40070000a5101c1641c19107070403a1002400019480303042e41c84030038400a02901d9008000300c91040d07940e40b070015402c40801c811500d02c1c3c400100110300400c0200201d046c0842d060203031600049c4110305180b0000301160030103204940c0b810000710154501c0e41480382c2c0c145908060440ca207044400c0c0d240c1101d0081003030750700340500b005010302d040001d80c2041c240c0070080514a40c04542d883d01c071080d880d00c02d200078100e00500c01d031020b11206406855109001240c41550000b0040b1541c800f0f40d142900250b00241c104810414800c180c241201010001440250700c43e42c1e82c0070407100003900003001480081c403103210041c140500340188010004148068542c1c402e01240c1c0c940310b900751a1a00c1c420856219082003000c401c112100c140401e00122240c01002101203061040c043c10003505211100d03800b00080d5035010a080707510030640c80da0b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 97550764 1250 97549514 97549531
    0x51501080a0b04110414030f070303021209041803030608100b030a06050916031a010e04020102030a0f090f0e06101403011203031107050607031401120209100f1502011a010801060305 80
    0x4445501e140102043d40c046d80000fa035403c00e04e2081400c038103040014584403020b0001034411141541d81c000c0d11b03a00d814070800c16806010030703aa0307034aa03a15441070003201d4900381d00c2c020000c3c0d14980580038107010701c1609124016000444046d481d50f02a1200910000340548031207007051307503010014007010f480a51103104500d01c8071084020004030380f02440c003910034035542100d0300b0000f5011500582056088030105000d010060360000165900420306090004013900d1680046449804950200d44500b80340308001540000c01c0320800d0081009031141c05404031034400580307a44151140180e829030040004000400c010404080e1180c1f083c034001c1910f91000014100c680c1084100759a180c10203c2801401605032007070710078404400c0d40401c0258980410280740e00c0034120301901510034000040c2001010043c00301c00740c61000182000240c50f04034108040940c2301089003d5031810006082c08110450b14108400c4140e64a822903801c05400700c000d00000340c003100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 97552014 1250 97550764 97550771
    0x201060603050c1209150403020a120c15021c020a11010b1203120702010b0301060905010918020a06050901180f080708070f05012a03080601030f1a090c070c0806010306051501080a0b04 81
    0x908811b203098403240528002c0c0e0080842c0704450520300303180d03418400a030042c0b1075010911000100400700301e545501001d0001030301d501000e901281450070b04080c029a880c8000b1b101540b09400c50314120315811240000c22102e0f00c0907003070200140e1041c3e10328189500c28004411030000031081284d0002caa0b10000c1200c002090100382529920341003540c80d0368031140140b01500181c812111403400c0b807103110000e25819008204542d03c1c5001d000d0801c1400155400145d014521450048010418000c11503276100b08a42e1040320038010741000380602240081d15040008501007951f990303002d010b09140c5000010350704400811388207080c13405070781d51165170250711a40000d103581c003d44607000146003440c001401c407150608040c0555103003240003a09041c00355403050b09000f065440310b00c4d46e141c4490a24840c005c80100410f60b020780d040100c2c83c624041403842c12280725a105005130703203c0c18090b80550f080d2060017400240c0c4c500001d00300e10025008103131800401340002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 97553264 1250 97552014 97552033
    0xe0309150918070f0f03330e1801140c03150f030a0b01051309030504210b011517040506070c080f0c07030c09050c0d02031005040c020d0201060603050c1209 69
    0xc1d0b0900700407180400800d000c0500d069050341c2000807140d240f40c0030301e420401c0c403000088107160705401c1328035182090000003103516000c110085207006400c241d600f8112500c0c207000d400214028080120180b5402c0c0748407640c3c601d01e000302d01c50113002c8262102d4115910051482c2c81c4020281e040390380950b40b42d41c1e80300c2c070f81c40c14032402182e10b0003960800c031198108410b01040c2e200c0c01907080d681d80e01d40400a404079900c40c00303680030b03074007000780c1c01c03210a65410040c5074001203d0b40140812031000000254050b0b200f05011199249454030840c1712414541c11102c488200c40c05002a000200001c103014860742048800611406040d410500c0c041071030400c80d04600000010f80e80120400e2040c044206010002801c00c0380d0288103519040c2919000c90180f10794084003190048080b81d1001c0c0e0442c1e541000e00400341c0b040101001d47d110007542d46034003032030352000f41d440d003900440c0941c4a401498400e0044180c814540142c10308040208400102161210b00404061 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 97554514 1250 97553264 97553299
    0x1090f031205250605060906010909020906091203040303090f1a0d0e01020310051f090501120b03120304061404030918090204150e0a0c0e0d020d0209190e03091509 72
    0x82c0d039103003101c20070803070410800d072500000b15032000c2c02c80b601c5107c8800421001d6030b0301400311030980311a1000540c6590070b110106042e806540c9901d0f48c40843c681c00c81000c41d00000c041c0c001c49005c1d40e40c1036891942d0b5130700f441c003000240c090071100c2c903007101420540700d40d00c000504159544581c0000c03210000030000e400c80e0020360b1540340d400c14001c800c10807441c001492030741101c1940f000c9104080004000f400300d00c600d12070141408000803680d441d03c0d0741d0b54840e241d44403011303060b55041d00500110f1446648203c030300302d84261401c0c0700303601380b20000c0301103d00c1540d040d00c40251850406000e609081c44900d03110240307680f506006001a103540c040e41c00c52802c0d00300e90700c46503414041a11302e6010010302406920b4a0010401c46440e88504800e01c090000d450700c524080040c00400c0040b1904480a500702d41420144011000a0382d501c0d000311121100400403818000981c603242d214410569910180008400b0703030307000c4550010178103004004c000080c000c02d80f090 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 97555764 1250 97554514 97554547
    0x9010f050d0e300406030b010903080403230a0210081305010f0501030204110c150703060801020c0a02040b0105090108041401090507080a1109040f0f0501020405040f1a01090f031205 80
    0x50095140d084802c0207541600003103444090107900c1d00f80240e0f40165096401c1c00d41c0a00e10800013010b03102c0d402c0415503405011408061508642c10580c0c1d261641007007241e5104400d203c5440008000c028400d02c0400b144c0406002c2e400bd00c01c40f8403106aa07811161008082d20741801c043c5101215030004a00b48690402d102c3c106d04046580c0d8550b004010444e4070451b0080005402004a07081c05200455100c1c010406200c02400585600000314010800d41d000003080303610000b43c0c1401148006140003505100702d0b014041b44d1540401180c06004031466103012030804804600000d00040c000c085135603112000080c071010f1034954502d040a10382c820030703154001c400300f441072103440384c3c01032801c010990351960a030400781d50f483c1e112a04400c0c082c210180708086801080420340403240100030007002803108440160108005205180640f110400d0148007070000c2e5000d40c4600702125000c08110310030a255440304204914094224010010100721040310302d000d004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 97557014 1250 97555764 97555781
    0x806120304120209060604031a1302040e011a0102160603090501091a04060b0303070b0a05040f05160609150806010c05030708030a0204170724020f0f031c1109010f050d 74
    0x304000340b48a03a801406000c1e280070b091580100c400b08801d01c081079807258440d203820050b6403421950b640301c1d00402441c01c10040000d505c541004c81210122505401c00001200602c18411800c10007000690b0781c1c0c26464190404165508010003d0074040d5100e414198080c400124030041d00e9991107131600f9090050990400c08801031100303002c9280700e103c0701d83d202030f402541340c5003064540c0306075008014000756903d03860742c00181c10440403159503c0b8040d40130301221408900040e42500050060090900080b03030010009100003244000740040103240e02c0d076807003d4031800700444640590b0402541c0714801040000c0c0044c0a6000031849150484c50068a950031701e440200003002d861080d20711035010f840244403051500041d81404510807040360034145121406034100300307030b00210052a000d102c03c500c08000000c4014038040c0d19980c6e81e05450b14801900e03e00300e80545200b21004030007800810740e107501982c0806190802410700b01c0c1000381001e8000181c40030f09 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 97558264 1250 97557014 97557029
    0xe0d050304082503050304030f210806030d0813020d0218010915060507031d030708030301170715080c280309060506100804021512040302060603120306010f0806120304 74
    0xc075804030303c0443c45204480b182650107120f00404c1c40d50312010b9580c010f60002610802c1c9541e5864100603018072800c8581c0045000903201400040b0060610802280c4080c0070f0300a05410914251040c0394192103040041e400706d04d002d41c1c3d5003e01c6000e14054000b241c00c07107050458011141c16114901d03000b810403c9002c1907519041c1d00c40c54545186600c07040c140311060104400181c0c10915010b55801c10119109080d0030a4000a1030082c0f507a2004030180400000424801c0440c20306450f80080b0360100c40d0055034454400c2259030301041007a000411141c0131401d4014010000c1500d82205020b182c031412020251070481c9a110083c070022995410201c000c010703140c0581588890100c5031500314050b0450040c1140d00300400007480381c810b00c010103d000e10300505860300603d000201c50500c4ca01450040d50b54101500d09038400d104098000382080202da044034468035041e550150a03244030b40c001c0d609000080c082e294040c460406040310ba44003000504002c0100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 97559514 1250 97558264 97558273
    0x120010c0905010c110909070504090c1a090603180c18040201030c030b0102030403031206030803040305070c0801020304080f031005030f010f060e010f0501050a021f0e10050402010f0e0d05030408 86
    0xd00d00a4010000da90050b414844100240c802080b0000e00c000d80844040c0d070301d10101d95030483c050f4200382c110303086594014035001a072014407510314800c00c1a200000100380320005208001010750183c034400581c806400c20000b103c0044900c9a914550004800c60f82c034180004000346144002594201c107034043d040402c0f040d580d040c0038500d0002c640c2e04040044c4119100000e40b82d01c140c1c003001d8140701020441102015580d44503e0003180c001001030344904040c80d0003032240c3c0c49940203031901c01300c0c8580810ba0f89010720840e40030f940d00609541c58546403010000558000601404045400c244000b4081d2000d1200041c10b804500000070314003894403850b0f003141c0160300700c81c10b0503154500501c4941c00301043c0354103448003420800d49404081500300d2034401075040003504a500480311051f0a8cc054001d541c0c41c154060030b648040e0145003c0a0032079404403000380c0005c1c003d01c0c41d030051a0003043c0e106050500134040c5035640c5400e854a82ca164050380c000080c0781e00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 97560764 1250 97559514 97559531
    0x50d12051903021c050402010f0c0f0c060f11010b06070b0c0d0e0c0a08011a06130b070f1716080a020703050a0c050f0901030f0611070203010e06040b06040b030a060b012001 76
    0x30000d160a80101880320108118201a00009c1200780c0c00c0c20040284841500c040c014405801e10b98944290b1000350440c04644400006203021007080c03d0781f01007020182141245401030240032208440904031030700307260a070380759010101000f030140007101400b00704800300e079401400750003903c110483c014605400e002090101c024030a45c05044103902d40405075120700d41035013000e070440008403032040e100c81031507a15902c042066170000042800001c0e2490800041c1e0b04480c507114011136000313400c008208541c0c00c50340f24880e0250190400c40c6407400002c0c20080160078030494510443c3c82050301c2e980c4442c0351200001c03054454000344001048140f51200c035403150b40c0000c5d15075040a52540c0c0d5040250032043c040100400d80750051030708035081c55070946010b150020001e1216040d241609034888e0800c1c1c8064070141d0142c40050213508080c0604000141d015008006880c01500e5043c010300484000ca41048a00c40760455907100070410008496400400000d4421 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 97562014 1250 97560764 97560787
    0x913060303080610050409020a0e0d03020c041b0804061a0301090803060f0102010b0315041b0902030a0509030a090902210f070f03050708070c050f010c0302090316050d1205190302 79
    0x1000f141c4601e404000c01941241d0207401c0d1011641100005030b182d603851401560b40c9181c0050054000c01c2020841e001e0503030000d0040541c100540e41040071804520f89082d0144c41c1d107a16074045009030b0041380024680d40c1c0410230b0543c044049403018510a0002825208030300f000784c8a1090120500134185400c035035803030f0000c200340000c000e0b15200d180030a407550050407030703130340e50001301c40c0040c0c00e2083d40290001c0780c160a4020500c0d0b181c550300481c00a400c1a13807410b096524050000312400b00003c00c0340c114141c2078448503a51842c1401000180d070240c00303038008848803502c001004400f103410450080785502030400052505580c010450a01e113007040341003606010a01c1403407900529019000303610f5250501c03103080a418030525000c10140f001d00e4075841c0101040c011a41076002e8100301c6000c8040d41c0200b41e24009030111000b0500450307501c007440905040024030840220008010386040c070314204072400803905004044041c2600100741c000540e0002079 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 97563264 1250 97562014 97562027
    0x103090b1602120c070608190f0905060a0506061605010e070b04080d050406090b07020609030a0b01050a06020f07090b01020a06020d0f05060105033304021308070503031801050d020913060303 84
    0x400600d0f21400c060820b103030315940e11803a100b1a81848010307408541409414034441003046503021060203800360508204004040e600c805a42c07600405010801021150040c00d024100080c022820401200c4881d1080c0c128505c0880e569961403a102c006074800348819002405545402c45c2c9661401c0c0304541401c5141c0c50460401804110130b200b1142c111103004143d4100c94441c03612010f151010403202e100b6440c019034940300d000003080c10000d8424000341a600181c0340007080d1076860801780d0780d0790300340030007010140c0040c40140000342c0154884c0117802c4052045600e5044a07072a010b080380d001450b03a41d4015100e4422910100041c01015040102071805a144d882c01c2e016803040301da0050810300000d00850903050748900356420034900b24000502c110b54031072050542510318a280c0c482c08169024901000406140210954407103018994402ca40c0401c010011140c980c4101d403820880e80d42404951001d03161915603002c01e0501c120002482030031800d000d000d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 97564514 1250 97563264 97563283
    0x10050a0204050343060e040b03010213080f0d050708090102010605090103080c0d111f0f1e0e01020309070e0903070c060807020f0f030f09060f07120e030c0108010b07020103090b1602 80
    0x3c02d038421354940c84c103040407418401114864640522011001c0c1c0000e000780c2108200c50b64150700210788245550049145003086809542c201d4080d00710340000e40303890713050300cdca82d0f8004560188000700201c1c07a541c0003400300520520000440b40d03290400034150240070781050350404000700b13080d8081002042b046a01000e14100090f40200c02c0045c16038409080710000c840c084403050394989044545c201d400010f94504007407114201c07030b000d45a00c81140080e0001024103217441c510b103002061003202e0041c10448050081d490071b006103100030711005881414548000c01c82040070994090b42d46c0c02034052640d40403000c0c11f0030100240303040100324445440390010100030307494200000032200500540c41038a0344074400000000c4403801420103401d1a4840051b0341400c10588054455500c012510742c440d0004c4020141941c1d540000034560225052100500c2104c90072005000903034814540800c42c41525a40c0d1103c80b4000e40b018160030010000791400c054040c4078601c42d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 97565764 1250 97564514 97564603
    0x80d0206040326270105090a0314040501140307020a061a0906010807081506040302040f020702090a0608030d0902031614030c150a14070605010b03010e0f04020310050a02040503 78
    0x188003083c418010b4584001c1c0c0500c0759a44a04241e4070b88600b075200c074a07503056070700d0020004e6117440340c00d103030701c6449414040300040c04000395040d84c1003948042c0c0e0203035a010380d14001080c0700f0311444003083c0d20203800300056104019110700018503030b008441d100c005201481c1100c1041c41c0c203001c007007500504090b0600070b0007401c0103030b503540c809000c0703a2081e411001440e42080b274102042c40c91240d5000650450300b000c6044101225507001800010301c00c1d62028025500d45203800121038480c01429500d400c1000341c1c4000201d181c000c00d1442d0b00040a0302c0408182200003030038042c1c9035012410410031134010244500e0240050b040c480b10584038100580b1002c00e51100c1b500c04d046221042c40b68505040d403901a809060b6125107034031440420a0796141c0103172400303e03002485000745503242c2c07100161000c010340c0c08550080c0e07400340c001c3c072280f035036900b06101508005045041d000d40c240000191544c00704910312082084d0f6001314a0795905a811038810745000701001c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 97567014 1250 97565764 97565807
    0xa091206020405150306010f0f090803031e10030804050f0a0b07060b0a0518040f0507030c030804140402091311091801050310051b07020307090f0c020c1f08040c080d02060403 77
    0x5907d981010f40e20031a00068544603890507498401511041c5c0d0f0350f005070b46641720220402c0944040383c4849a42c1d40e40a80c1d15020b150788900e810b48a00c1c9241c04000c28407101400300b081b00342040890b2f00f904180003002a00c0081e1103d180079283d402001d000d50380c0945401000300720f8144581c841019020581c1c001429140e6582c05110071030024100030300071500340d501602804030a000d90400703076510240341011266203040c501c08941240c0180d504188804400300381d50328180c42140c580c0c2c40040c24509640c600c81800304000c24480311804994041009074114907a1504415101c004d03006a0715051941000181442e10000c1111103520034a00b005000c1083c000c0342000c6410008280e80d15911045440840c0c10005d4503400500120f0074140c146c3d1001c00702e904a1803002d141c5900310b0382002030f00c074108038103006480c0c00c8a141018404042c3c140e00e200b010601c0d4401c1c000d101892220b991000414500042d0300307035101c0144c1000091004040d4000c17140382110504580b1074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 97568264 1250 97567014 97567021
    0x150201020a11010b220b04020714010c1707050306010908010c021006090209061207020c060d0b030606030a080d091106030403090f08070e0a0c030e060108070513020c120a0912060204051503 83
    0x8000204030107000080c0d170203280448a00c040035410402c68420058815500d0f0206480c1c0341c00003040080540e4665424601c142c3c030b01c00c1c07207222400c0441c1710480d20b06100c0e80301d45405440c0c9601c0a0328050400071465808070705400309000341c99120076640d005242c0f818801184e1411a4150340041020b6401000042c8803980ca02050302c0045400003e5106a521034142c240c0c5000342c8402c5140d00b0040210f001e01081e070683e482040440b006400341c0742c090b40e4040c201611040300400052260b04280254201200d06610003804c46d44a40d9400c0078888e4164002031282e00200e80440000d5181c58050140240070000303240100101c00013403285900709810b19640301c1c0b00030241c0d0368190344c0b0710891084030f20a0704800c981700d07910b00c2a5442544c441440c07586404271030190740c0c042c0801c215900c034030101a2084503140129400a0204403c1d11075481120740e000348909c10400000d441e01003603103400760402003c29846504010f95461400003802092080070742500703e140d60034000c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 97569514 1250 97568264 97568269
    0x3020702060d0b2103070b010608040213050705090a030c06020c19060e15210702160510050c0607030c0f0804020f01030f020f0406080414120a050310150201020a11010b 74
    0x98070500b082c0c036030740412034282c240d011804903074010a4590400500300c05400b0100004801010386034042c0040f00107a81c0c90301c005484140b0f054074025009038200209003150107a650040b5000404c40c90310903d000d0500002482184a0b5001628100b0f8850010001d4036010844600c00e88000d8404001d000c3d6610545000c90460f80f02d90018016032203640075041c1e58040e4910304900ea030b00c00ca50340300c4a0440560088810380341e8010044003000010070314a60000403180740004030852910312090601090006004144182005120040c0040c0308030a0b02070000e10302c2103c05507330014a10600d1100144a600c14060841c2444007070424480580c6401100b00c103140000c0c24082202504085501d00a10846000e00c2c2d801070f0105001c1401640660300c40c1c00345020f641075041c0c80039007003a21601d55804c100380b031000c0c19003080719640c142d000d2006103610106404409483c5607076651a0424100c00145c2c0600607580002c0310305800d0381101e0000c6030f91131715900030440201448007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 97570764 1250 97569514 97569517
    0xc0f06080103050a1209050d05160f050f0d02030307061b120c090608060307080f07030201090b09030a0312060801090c030506090d092603040e010e0c0c031b010905120a0e010302070206 81
    0x50281900340c41c0e42c5c001034000d0180c802800280340240102e6607070352413810400d80390701100510000c0b0324405400000c0004900424200b038030790040003100259055400c01034a86028001260140014440a408162540b151040b9280724200321032601003c014020a07481e6090b0400c031341649000a000c00e020b0380100114192181428800c031240c642000003464600d02d58000c0781644225061035503103400104181c4100d038401c0c1c1740c8513480f80c1c86401e00c4010b4045c042c456600356011215000104e4032681080c11020200500007403055280d203400d5080d5000c151003903400b0001c2040400070401d040161950008100b00645014500c0d11001807950140c5d00c034aa030003501801140c0030728403030314108036007914a010459a4075039a440d00403807602401d02c10808071180a40000342c030100030070225410310182d80c2c0a5032505200d190000150343c04500403084544d0384000507000114208003804400300036054a070f03280d5008080040034072048030003450415006004041c01621803c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 97572014 1250 97570764 97570783
    0x305030405010f020a261e190c02031005130b040507031101030506090103150f020325020d05030718030204090b10050a0503150a2004050118031a0c0d090c0f0608010305 74
    0x54039095080c4050340c00106010b2030547c81554203080784082a185001e400a00501e0070b04000d00091415002c002d132240d600c56900039415400c0300b01c101072004490f922050344203800d4454411140d00c141c07208400c602c0c04807411a16a44400014030500000126032121540c0902e01444623251440102e1050181848020301906001c0160749124509802051040707480c0710f0704640343d14006080c140582c0c1c540c429484001c0080c442242d6040c40400c1101701107070305449403891074982070700c201d81c10174110304d00060302c0b0045180400103a441c1c2c007414480314000e078400e40b0305043c002e0840761000c0741903001a206803e000b00810040d1004a2070200001c0c1440d80c2d01d94650b00d00d4042d81c00341a40c03020010342c1d0203074030050554142c001405001900d03800c2c2e0300e2108004c10490800040c44c09400040e1007580e601248024041001036265403080317107001181e04142400b4a0b250641d03440c40c0701101c03114a045414840c1981c01e6003110002d00107442c219141c0e51568880710b46030000b50 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 97573264 1250 97572014 97572053
    0x12050622090302030f130315020301150c0c050418110307080a0f050f06040503031905060105040504020c12130302040b0301140601050309150a09051005060f060d060e010305030405010f020a 83
    0x40d003800c002e1500900030b6402105001e0310141d41c034103245101024005190200b01e81e60030807000740d20160381e401e01c26070b41a160410350718030304100013803010781c1c0242d036010084864404e24240800c0716201e0380240c006501c8403812a0341d6030306030351422070084110001c9290095110303140402c140400029040c000381d4200f01568201d2180f818140c0c145608410100d68522070401488204070b4008000e610880c0194002c10100701000140d506940e0199a048d00050050000340010315159005180645140c0100d422820b0b15580584582d04a0044810b080000c904108150706160082c101500400c80080004103056803088561020190903203042050100001c0c001010030001c0c0c906d03202c034401c600395240c5041c45000018140310b54003299140194810340b81008154004d640c090000100b49110050420341407008d00e41044a9004d4030035100c003000034601648103880d5010b1070268010f075588d10304000001d088030368004bd201c800c5611107010032003c41c64030480b000003003001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 97574514 1250 97573264 97573271
    0x5070e010c0c150e040606050a020d0e0904080f0d0509061506030f0408090310060b03180a0201020a150f09050f010c080c1e040b0d0c020d1106011a040f0612050622 72
    0x1280080780c4c15003200d189503400615000e40032139a80d8000000c1d004c10312280d800c49036440d204240c22103e0803e88498250840c8942c40441c0c0010b103044058002645000c91050804a030b000134602503413015508038256030011428405d14424055412a0600052340c0e682e146003040d2510307103601800280042c06800f004110019503642c20f1040f030044030344030001880296103441c0303419074941c400d455551643d0550303c0340c001054008030310185d00a405030080c011034001074484450000450b001a45001c0d07503110103e4000c400c8d44101e07904a4082c4c0001c008600340d9900c07250840d9260342c142018448103e080221002c0e61000b12200701103040c03807280d43c601c90503060455500442d000715084810110310b0400d808041d5024060188203542220751404050790b0648d221040b10003402c0840d00000c0044c081c80c1d4803108280c0b400c03030750301480d5840c00742d0b6854207440000043d0011400100000350340d4007000854041c03550004001c071010301d02c414080021500da0781c0d81c014000b1310301e6107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 97575764 1250 97574514 97574549
    0xe040506031c03060501030b0a062010060305031207082203030603020409080304170f0a0503060312070309061403010605041707030b13060f0209010504030f0c0308070605070e010c0c 80
    0x28148031107509002c500030a0000a900c034030010b4042d00c90341c0102c90000303240a1805001d8900b40500d034044070810b1b1906400d15400040718066560881e040b000d06104404500e40c01d40b4a0744a10402180518003440d00c50005c84810816040040d00e032100b000031030350920940c6600c4088a10084041041c443c10002e0903250940c0600400c0d440658000c0c03401d02c050b01400703191002103100724070400c0031240300a194403003003029000e0324090408440e4103105e044041e500440003950402c03002030032281c0c00c0e14405120043c039409050100c0c00510202801c0000716006124101842150980c5030305642c14501e005241d801a031080601c140c0305400b062068160602008ac003460700403800e0007a514100858804100060303d0440d0000d28040b08860429428400e171101540c05075101c900e090301e941c54980040d001201c041e2080c0381c00d03010000c00902c8010080410900c16400440c1c0c0f813407c0c09001d02101e07101c40301d0905100c5500a4400001d214002c02c0b429112100c0c841c2100c0351 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 97577014 1250 97575764 97575769
    0x408060a271406010f0302010f0305040503090d02030c03030d1407020c0117071e0302090f0f090f071e021e0606010f0513030f0605060307050607050703030c030c0b1806160e040506 79
    0x10710080c11002c1d9000326000481d446100c10780301301c10340c0e0003030700c401030703c40300d41c0c0c100b20100c510480e80034186800500012449250801c4485192130004080711007100002d80040d085a21040d000820942d0340e450b0b01c5070f1039051004883d4441c1060024000040e00000040c103e142c1020b0101000e01000001488460044c0789913107a0314000703840300300b119015880143c020f41c49191907901c2442404c030001010b1900d000c43d0040c2030005007040c034480d26405490486440c02900308018030500c048a9049400f01940c4405d802140c1d0340100641c00c0d6000300003001c1980103580042903000b0500f01304159030000d420008075030551404580d1a1034003d10b0101e15080c1e03800050086025520b0f003407d014082d042036015042c12001d540d4240e594004000e8207204a04000b0a150005142000468041d208440c80749000703050040300c0392020355440640030b0040300d0700e00d131050308a113001140c2c01040203660340c84410030900c0b0001c103903140d0340500f12a0f02c018545200b40d841d44001007141c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 97578264 1250 97577014 97577033
    0x2030711060c1609060f08120a1719050a050f0708061207080303160207032a03020a09090c06020c2d040509030a03050a060506040303120e070b0408060a27 68
    0x70007a12040c1e600d00194220083c090448621800300440d0900f00c0100d000e086100e51401110140b030010460341c0b81c1124120303601d030000b064410520044542000f0803030080c880031171003018101148001c1c0400401039000319180504130b1040c4a00c0c0c0b40410181400d21190340c0d800c8503ea0030400003c0d0b5a00c4005002c100c210140031820340100780d800569510f0010107103000700841d00c1c4c1c4038007807410703240200c0c0e0790b07002440090002000300e0240030880800010001e8419403105030300d000a9180d4010034828162503120f21440c0c0c6d80e1f91200c00c18401403c01e4040038241034809001860303c0c1c40005402e811820705211901c556040303506a0403100003d0070590070001800522451070b0694841781c0b80e4101100220200e81400300103100c240c035610440040c1c4030010311050800b070454030b003103503132060940889581c5c075541e01010146141c10000c240007400d03102c14050b80c49082c006d4140c101080078148100c090b041841c401003244003e40070030200041c13480801c852070b002c4d0030109040b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 97579514 1250 97578264 97578277
    0x20f030a05092e0c14120a050d0b040203070507050c04110d02090102150f0403080f1603020306061b030301090f020309060c0f1b010605010f05030411060307020a0b0a09020108090d0203071106 84
    0x12000140c3c00744000e074004030703021041400362001e121800c0103003a06940754407518001e4007000e0402c10001d101d450085d0b001c2d1840103640c1100166074841400458120380c4103445020100303402103281c204001007000781480c0400203941c1800040b407803d154070030601440301301680142d004601c0001c01d034420040c2d9049040041031110050030101086000d41400b602d06030000b402c0d200004a11400c881e01c01401504442000c2585041101d0100e00941000d040340394890300401c03107050401c1c078028004082c60790070009580d80e0b51400300c5000803681c0d01104d11304200e00500822084150202d031303c46d40700101d00c0c440c50765540b203581d49580c9071054078103005e02050840f60b50a0b40038015030010042e91000c1e00d4400038880700303090039105400103d4004080c2100708000c17a91909206c00038540022642c01103172641c8006988898250408603403411440d0750b141c286006642c0d00094450300203d0b0600078204120308110029141d110741240507250540740300e80f041880d158101101c44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 97580764 1250 97579514 97579579
    0xc040f021204030e010309050a1109010509010b0f030411090a0f0f11040b0703051c0203040210080903090d05100f0e0c060a02070b070201050f03010b07050105090d1d060f1306020f030a0509 83
    0x4270400740d4503180c0e060b6120131601c0c6004a036444004501803d001010034161100615040c0c01e080805007441d040d54030040c400c507100c0040b50030300c80c4030340c444100349401000c2419020909800c015990300490f031000c14189610707030911490120000410040f20b00f5a4000709a140e038814903800e040d030b33491007281941c00c0c0349002e41500088003c082e5025500a41c421904035001c00e184007004c80300b411080c0c9151940760410002c100c003074984221900d420710b12403030a81d00300401502085003110a100070006001751a200600000034080c40000244002181c400381482c500d520000d68404042c0208207a009001424500f07580c050380550300c04013018100c0e16500c2d0385888081003290045002200c4640c28280402c60803c004a100803004006544002c148525102c0011030003500b21026604100f0400c1541800302c110303c0103200580401d41801707416468950000d20b4030701e020006c01515002400390442003640710044981042e411070365010110081e03480207101c800020704400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 97582014 1250 97580764 97580773
    0x612070b040b130503190303060812040b16021c031808030a050c0102040915050102010b0f03061303030e0615090a0501060f0e010e09090d1404050307030303050c04090c020c040f021204030e01030905 87
    0xc0020406c9080740c610b200369000d0143d00d0395414400c0d82c80200d031f2000e0992410a000510003e02000080d00d48410b069036001e601c141603802103001d240f00302c4903000103c071400b99548241a0804c40c01e50715070201c3c441d043c01a078903000102d5142d0050b80c42007000c001c000144521110002d40641d0050220701c8001c2080d0601382c42c41440c1300055104040c055400c1103800482460110040710b29043c0180250001e66204221a01c2121500401300c00303060b502c06814060200030007800c1d00c00c00f2980e0000049080240410985072801032001c0005424100184080c03644440021030100d031a00300980c50a455000584040d1070a41d8a80e17005020103080201e402130003d0341e00c4080f40070f52079100d529001c214407298148540e0103019050781c411901040040d209074410760b44042d406070107505182c0c50b0b0316000261898512010300503032200100d080e080c40c2c90300c21001084042c060840c9032805070f1400e42e065240050002d818822810b80e0038519900032307004a00e00c2d980c400d0584 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 97583264 1250 97582014 97582033
    0xc0607061d030406021b0303031302010810030609051524012604030e04060501020309010806060a030905030f0c150105031e0f03040b0301030c06110601170a06050108060612070b040b130503 83
    0x290350348141e06840004507011351041e91b4600780402103e0282034000d5803d401c04902d1f800540b249007014180c025080c00000c0004082002c2c0d21440141c20b106a02800100f0312041203202c507200701829843c11403100200c6000c06408101500c41c00f80002c0c00c00182d480603094005608028080503003454000800030442050351248032041d0840b0110344c10404162508012039030ba0240c20100c6021480000c045480d525145018040c1584645030101d60703513019035503140c1503401401c14003007440c0012550b01d03143c15080c032641219664201450314150b00d03000000c0d0351501117064565110208417402800e10600384020f030a0004040101eaa98903541c2501390f581d0ba20912054440503210540070450621894068444c014036500800859003848400d024940503040a40824800c3c4c000d0742d0006040b0f0b015041c020604180904107030701e82201401124140301d08480e00a4000c5102441501850380c26102a94070700c041460f05c0d4078440d03640d4182c040f02500601c0e03045c402d14000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 97584514 1250 97583264 97583267
    0xe0a181205090301060e06030703060f02040b190905010e13050601020a1b080c0d110114090a12060b0f0112020a03140405070312021902040905010f06090614030c0607061d030406 78
    0x30b02081a0640c000c0000f25610f0000f400c92003001d40f00c0b5541a0040070b03041010400c1900300610540004000500d850350b28402a02160321403410100000c40305400c4400c0c45421040140040c1400c0c01d014035030b0b18210b400a258400b001c80c1013401e0036507410100c0e9090744204144140d02d41c0c801240220300030400710b81d440004580c42081d400780300c1c040000795141071003800391409981c0300004910303114014006560030031540d0041c90b8200800d120b072462558a4411700c000030007540001510ba503003642440b0b420b44400c00d0b013813800707800d03035490824444c1d9002c1d1007010840400800142c45812208085010700001c240744603010b00190144014000d01040340021a44203409412040a00903c2a41c036200320b03070046e00150420702c1c5480f0250800f9007003c42d00354490000080d00c1e1069202010441b05071344c00c800181c0d90b80745014021500707400d684813400b420440040104525120000b203c510803d01d00800207516260034855107200154854440362034801600d0712251604030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 97585764 1250 97584514 97584517
    0xa020a064d070b010e07021f0b0405070f020606090606120c0c1903090e0403170906040201020c01030908031f0506041202040501050f0105030a0e210d05100e0a181205 73
    0x114008610007544a4514020381604070359209502c05881c4065a01e890705804070054004d10b41d0040d40507480109500100c204401c04621303d001000041c400c03000018003044600042c607440034031078403041c2200400c2d000174010ba800102110081d401d90795400c0891480c0c01140d45054604080c0e0f814008408060f2002d00007112001003120200c0d4816070048845202204028012480000c1c0602001e101072180552013802414002040d4000c603409454a5404481c3d600c0301740c01c8541030000315a4140500081480300f481c0902c00c210303031764841c840c05100c041c1900b0100c282030441c68008030450401d5000405000782040d45503640c8020351207200441c00070072417280d80b0b0500081070724903000150101d090390680d106030650782d80d10030f02c1000f0501014500c4003481120555404d4103144000c108000701140003031034a40704810035500c203944000d002e8100c0c0c00e42040c024000007005141807075200745620f0b00440c0000180d2ba02005403881d040014100d90306000b50b83c0d947d96000030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 97587014 1250 97585764 97585871
    0x6200a0c1505010e0c070501020f1204050705010305011a181207090506030105221110050903010f0204150f0504030c1202090907030203030a0302071707050106030b0c0a020a06 77
    0x10011045100200d00240c200c0b1030074000c440040400f80040f5400751030880180072003500c2200018900500d050710b040d0ba1707401c821094441200104200300070450140600c0340140000c0c01c0c00e0000c0e50420425a4a00a0341001c010440001140d411000b0720302c907003640c0c00c006000e0031803604aa507001d62a41c941005000c2c04007614280b5010074035500781482200e21a809002d2040c1758400741800b591241c0c0156001581c0107005400001c1d456954900060200142c80d2507190340c030802c10003070500391944000c11960007803040c80100500812800d5104070031059150150b1040e04100e8151214082d82d000a003e00e045900045490414800c030804154001c80d010b40442d5a100781c500e41d0761542d408003c1d0560420b011b00c04119020b500038061440c80340403504440e03014040100810340011205503810780d1107903004c10a10112002590b042143c485450b480c0000381d400182d910158500d00401c810344e1000048000101e03a200906418031030903201d414140d020710000c490b81440b1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 97588264 1250 97587014 97587023
    0x21206100807080a0201030507210b01020d0801030515060d0605070309021806031509010209130506090f07090302090c0c0102030a15050d0c0306020306060f19090b041206200a0c 78
    0x9103000300300e02000050300001c0303c005000400c400b54440d4011009407802900358003d000c0d09503801009111030700b03140d40d072108507940d00050041100c000280352030324040400c1c0a02210b140144081200862200c01d0510b01c1e8100c00410b468503400715003400265480940074030301e888180040680e25400c501e01150085640076032145250303000c0080704c10140c40181e8940e0003510302c080c01054000515905c078601c00c3c00141895061000f041c6450807031502000510760f034104000c2903103000403240781c01488551600c2c4440c40c100b00090807201c501e000103482180f003440007844c0c001c145800c60742c0400d10b1500075074032410004010170180901c6240c0c1c040c542042800480d042c2071125000c101540c02c072806541513481e54580c607000b503002500c0c46400810070025444410090001000c042540740d03006851314500c000000c0103210650002d0191540401080114801034040000c4e4103403c0580000d6104d0007001115074800183c11540d42c9690108107207030344c5500020102000c5016 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 97589514 1250 97588264 97588291
    0x80109110103020a0e04050405030c0f06100806010308120a090218090f030307050711040b2d0f102d05040603060506070201020a030507060603170306120c0604060c02010c021206 78
    0x500c0c005409a0140d510715000091a4010a08651034190882c5401030300840c16a40b80c80e002c10844c90a01c01004d10380103a5612200600200c0280458000c4c01052444054040d65045603140c5140d4031444020062155031000856040c0529601c07024055500421501280500a00001050303078219003600f00f9005907a14240040c3d40031046a111718400d039191841c1040d1a42d80511810450780f40540150356801c00080944070855055035005503540f141c800306003c1d5050030607010800124a009030141050a5815100c00d00d08001d10140b90500d41503004000c1d03030303061141028001100401c454000d5001966402c50001c0c0283d0384a9682801000d89030018006244145500280180d10840340c1a0100f4860340186c040948603070408a100c9642c2c1d11440c80b4208020002080c980d4008140800340c0740064000003125050303030140041c40d6054000540c180a64031540b4280300110f2854011a0310407684c502c18994000c0c41c00c01a0322030024955036031101202c07400a400740 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 97590764 1250 97589514 97589543
    0x605030a2315090609130501110a02013303060e010e0a081b0712030809100509030d1a010914040605060705010518030f0a0327030c0c0f0308090607030c0c080109 71
    0x140410014401c800140901c10141c403611007aa881b000c508000307032029565060450924001c8200030200d03000d69034004602d90621050b614000303090748200d004042d10940d00c006510502500c41c0c421250401e1001840c2c031100000c81d80506580e800201c600e01034883c51104005980380a8642c00c0c0e071055025060398000e40d80942c0d6102c40d40107407407065050111000c00a80305082c00799004a015040e50011281c0004803002d5501c00d41d80016260000302d50910004041d01c00c010254003e441143c14079109038001801844550083c0392100c0100940f030101511250064002010b02402301f51f90b40d2603900b4064001d180982d00440c407020b56a15110298070000195042c0184404dc081d00c0c0541502090300100720040da8014250413400000d181c5d40c0e0841c00418007140251038101c40652103251003580c1218542003c4c00303050700c100f0103001286007801600c0380a401642c9503540d841c01402c00303407180c901f1400e0040c2007080300d00001c00c2242d0103400025280d071240d06413044548 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 97592014 1250 97590764 97590769
    0xa05070806060c07030f11090f1b0f07021003110a121424031203010602030a030c051606090606030209090708010605010f080a2f1312020a0605030a2315 67
    0x45103c214a0103039010350828800b20f17000c0280c014409100305030380c0d107d075408400416400300c803c841180c2c0f05402942000300306c110b148100304004a0301100c05180c8200c0c034401003110301031001d000c0c0c0111540c2c0e010b500c0490003584241a410701302c41050b030315407050b0f14000700b00c1002d0a0300907100c941016241c1443c3c14002c03103058000d04810f540720061030b4080120000d51303046960056418440c0482504600441c0c00c000c41c060a129400346945a81d004c60107015540c0b42d040680c2040300401841c02221280400800740a611002c0460390420604010028101d160406507100c0c0740401031000300f5000042040c2203503003200007400700f10754600041d29408101403144003c40c081c100003c10408070366021101030807414503805640b54035005440702c0c5d0103150031090025500010000030b00c1c0301c20364890300282082c0d00700c8a400d00003580442c401390f03440d209000600c0300100114041500075000a42c5036007600204a0540848641031b5182078002e89012500000c1d40381c00700d1450 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 97593264 1250 97592014 97592017
    0x101d01060b2d0a1e090506030703150902031503160f12031b051e030f04090c1b030206041502090a0506161a0f070207030519080405090a0507080606 65
    0x71181c0742002810712882001101c15481c0c141141030860054580803042d40c124140500a20740680d84c410b1280031810f80580103160704001d12078140641180208180d0391401d007169441400741c5800b14018803407159207482c40c8031030340085034400d00200170032130f4682c1c410204100b80311046044441e540341055158402c200d060240f010380c0303d220401448400064143c240c441072292420014808100c0400c03161040a60303412039058003c0030f044018011040203c0266800c0c000c069494603800b0708680d261442140b0a80c8442c03500d440c001d096090154000c181d61801d100803608000b211450029200c1c503003120222503460030421041e0042c0603620a5035000d00010305074140785810982003100303c5d0040f0010826100b2160304484c0062001c0255040201d002440c5410900b02140114000a401040142154004942000030410004680d1800c07483c403840100b40e1b0900d4101112288900d0700801d8100f1250000c3c072134260030301c0e88040d11825440e52600c0481d1561002c200fa207 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 97594514 1250 97593264 97593269
    0x4140f16090501030b0604080109030c020909190b07020a08040603050405060f01030f06110d060b04090c03020703050d090f020907020309032a1c02040e0601181401180608101d0106 79
    0x3180340000b408294026070101c030400303c0041c0400d00f400d03641c6080038252054400300f100084c4504a043d0114144541e04540083c4036002401f02c2241410004821651180d00a011350385424003044285000b4030841b41502c0c0c122103a1643c903511490090301826059800f00c40340e118102c00070713400400c0350f03400e40c4c140c81d40400400400701064030342c4006415407003000ca4421000708442951035003284101401000c0601000c0d445900c0d10841c04103c45040b00d60a05060040025000081c3d10808490091580c40800902c1c1100790501c96081202e0320402900054683c1c203000c1d030030b46c001000d40715611044040303848042104504000c0c420300140080040c4c00005001c10040c50100032860b454818082d0308140d490268001405a8040e85036007403d58114400502182c801c0403001100700e12446001c0c020b0709007261519800c41c40c148140710010941a03c0d50b40003040680085006042e0307217003125076981d101450f0a008101c0702841032080c2e038420740052640310060203100e04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 97595764 1250 97594514 97594517
    0x3090f0a020f10020c130c0e0f01051b031e0301080609070609090b010309020415080d050c0307061d0109050c18010b030f0606040305030a0c0303050603010b030c0402090d0204140f16 80
    0x480010403000c1c0482d0700320780d030b07030401c150b0066000350886600c0302200000b00f00d851803070101f802c7c0346561010b481c0d2240704550500401320452696441e98100b070480d51b00541110802e507a41e01c94020990945c05044521480c441840f02ca440046c6041c07009036040e5445c80d0140d9615441c1e03540401e950b890701e0720131a804104800030410031a65a5403002c0000321040c140490314581c05e03030026084501e6488000f4100344003217824800302d00304209880c01d4240900700245081c5001c49134596034001d56000800541d111552a00c080c4a030781001d29071804203030024000241c107440c18076290000c05a40f20300641c070004000214004c00e440c094122010b800c102455601e031080502404c143c000d05a0350448030130000000007030000c00003081d8840301c603621144030034100d2400030162000908000e12a0b810404002c1c0b659401080c1c01c001c261044600580d211035a101041c40d9128401d40650f01514124030030b03040346032519111744030395144441c15410341e40c2c40465042201ca240b03244070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 97597014 1250 97595764 97595779
    0x1005090105010f1d0d0b0405030705060615040e0a0f0f092d020d0c0e010315050109020c0606010f0e030316050d0c052125060e0f0c09131703090f0a02 66
    0x6604d28251169120f039900c019111843c241480c0e21340e000100015207044404d0340c0f00191500500c2418064180c1200c803c48030020004d0a84044c1c90345800f80b40600100704188401040c6004410f41c4561500e22035128180150080c119841c40141480c0c0001d4503600c41d064050b840420f07840580c0303490b8400340e14002c07060700000d400b03100c8400c149a20458101c01000c8000c9403800c1000411030003503215010300f826031520303075045000b03079201070b880344070303003034018000c4080449021694981c0208280380082d2041d800400c103d66801030b4107a01c6406000c005401244880d00b00d44114089000700c0c09c4940a050450f0101d4480300516800741c180d41040c032848219013070307250542d00a00f140d46105810109081485d440300c060000c0c40a0701441c03040e40034410400e05000b8485030311100d201415101d004014060345640e44c010010f0711411109000540b40b05981240e4000301d504103954910350005158144e0386984266040100b503c1100381c001e102d150005524951903501078001c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 97598264 1250 97597014 97597037
    0x9020f1602060c060408040602191203020a1806030b030601050d050a2901060c0308090105010e0a0b0607060f0b130207030509100e030616120612030c1a1005090105010f 74
    0x92694400103204a074441401c1041c0c400e00081000068000c034010340415948610341800645480b201380c02c0e03a00d00740e060039180301c0481c81030000c40001003c1d80c10302694480b0345030021036003200e5001d1084900c00711510041003103581988100e100c0c89003034045070038a98842e400c11111f02c03a141c000515651104001c8400203020041088400500020a50480000070701445000909802000000b40c0060070701080c15800039680381c000001c14003c0280d941840c000c0010100c0c014401d684003070719008080c82036207a41c002c550316160081010031461502c9403254004e40500c0100521900644c2210003c042c528401c5035032059140e104c480c81c0207074220034015080030088501007840703000300c400480c0e80ca050145a225241400410650050001000d0210240d404514801a10308003043c8605a100881490f040ea0541402001d01030a0f1524000052501000940500200302480f0010b440d0301821803e0317881c100c03036100c1d00c0d81c0ca44004680c1d000340d02d90050001180240c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 97599514 1250 97598264 97598287
    0xe0c0604150203071403031b0304020f0f01051c0c110706051602010c050607170a02090a140d081803070e090307140c06071a010e1303030f06050901090b0a09020f 71
    0x440e01c2030030060040d039050140a840350b0b40c0040c50101c110b10340e60000810050303403481c007200e84042800c45000b418154181a000700380c2c5e40a840a40714055000c0003002e81c401d80c00354054031904c1c0c1030f200d40d0800074010a4031440c05400d45c1000c000124621109083e154580402eaa00640e070740c07950b4140c00c000d04044030164059a00f40e00f030381403288641014004c00c1d014042d01e4490703143c60f01c2e04a0030820301c00d003400c00103400400401099105005101640d80ca1159040c2280c0c541d090802c2140c225800003140c6020202c00100301a000003084454083d40031082103550400720140d82c40560b4503080c4800300c080132030b070160042d0810414500000c0c202040036008811a00c112520f000084010411543c40114142d0f84264a900f6802c0b00c6110320101502400d58250b0f11030290802d2001408440200e01c402024580c54440305541c03000f00b544405c3c01480010100e88195a480500d1401001c03280001d0740108011503000c1608446030003140d1480c0b1fa10401145083c00320704e070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 97600764 1250 97599514 97599539
    0x305030f060409021005031b04050a09022223030703080a030218090a060f09090803040f0f02151b070e070c02030703050709051e0103031409011e030f0e0c0604 70
    0x80707250700603920640b802c003580b90f940100e00d8690716500c403190341c1e062062031002000e10051081c05050002c00041c840c68980c204030800f103070310041c00507072580729880080d40202c0000108444048000c00c0007d80e00f109213850107031849581e035008148241800905071140428040a0800c042c104020002c2c184258000c1c140b04402450f80b00d00282c3c4c1e1030002c0c1d690001075074400070b11030b20b400080c0802e0803280b400400518900108116140a59460b0788107400000d1020b07106d00b060685032814446920f40280c80650700400180c41200c1c03918100503260041992040b07107856a442501c454800000d0300c4c405d0701c0c81d2008140d040da9803010111181340c60082d08036014010182c0000c00110304110000192038180c00200700741c6800103c102d070a8150301602c6403100744440040021a80240c074110050b0907651656541300e80b01c0005a540c1001c100480800c0710508000c5c9110681c10f60000f40380311205101484280b0270409444d948d041964102e0340c2c0310000300000c2000c00380010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 97602014 1250 97600764 97600771
    0x905091b120a03020d020705060c0a0b06060c19030f0c1a0a020f03010803030601020c010207030b01090f0e0a060c030e0c0f040c0318140601060822020604080a060902030606010801030305030f 84
    0x5208003607003546941010b06041056000f20003592201c800000c0e400d4041c88102d015260a85415040050130384481e90b40d008000b801820340781c8600c1c04a11580c82d41000c507082d031400c401c1107071000e807007450811484100450007030b00020f07100614810720a10a001e902001908203580d01c2081248c1e000407500d180019045600380c0760300300480e10b40e081c2034801071802401c0002c065a00c9150a500290030450321000c0a81150801d0909100180ea10036405064480120b000200c002c04210600c0080c2a00300c4020400e2140c2c187e200100903c0381c1000000e00d1840d0740030b22a500803a2040e560b101201d82d241a44105002c1c480800340c181903105000d40c00c40ca00e00440c0721518107905404002304c0a00590300c1c401d01c4948120070075020460240100b9640c40d0045d0f1603e002100c8289540b2022030b041808880552440299a203c0c000e450180c00c6040c16a541c1c0013852520360700070074542000b24000e0158500140480d80a003030264100d9070541c441928607038809148900340003008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 97603264 1250 97602014 97602019
    0x3031804021605070321021002031b070809010e040507020d08060d0c030c06030507081b0705100c09090506100e0d03090803030709180905070b0a0e0402070501060e010905091b 77
    0xb440600b000b85510b41c140e58a2070701a0000d000401d0944c141b6600d04510214101020645100310009555001580016062007101300580320f48600104005004d0100c0300c4990524010442601303100112008144094090301e034000a03001c8113091001b44c64089030564056042480345080250140f00c90590040c2c009010340780c1103141e9624006201401d800540b06003a003400309008068041c485d16410140e907082c00c0d500703880c1840e1046003002a21040344003030400801c040040010400011104403982070080c080c60005650007042c000031071061800c0103040c400444ca90f410035510800040c501c69540502c0d100310503050107840d403400c040480c1040803091000409440510156008002c555921680702c0d04e80001c1080d5051070801280a841c039107090080018400219501110316450f402d940322109410240c0b0040360040e1100e808c18000100c8a04000041d07004409030361402044190f943d0721003880380b046800071943d441d0b15a100011010991340031140041400400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 97604514 1250 97603264 97603267
    0x305030106121a0d0c050a08010c020f010b0d030e04021905030610090506030a0b06070b04030302030f0a0509061f0806010308070c0f060c230a12080903070302070e13020a12050106140303180402 85
    0x80e800490540e07c1d580d800201c65075954402e075840950305001e0090180030a200910869a50100060613205407800003800e000c2d0301c000c13800c0c0d180c850b0303015517400d2441000e110081d0720300017102415590044990320b2068002505a203100d40c09036000105071040a0601d50031542d5044407240180840122250301036000d02c5801c0005900e00c6010784118402e64004d61282003680041d820707424007401c0c05090509203003c01c40c008400180090b80001d80d1981c0c401c80c01c0d86d2400141d8914120f4014001d0307030268400120511504000619841c2d105654040402d0303952042248469510700810b0002003032a0381e50400300d0a8480342525407814960840da0030b00301e5101d031503d00000c200045800610b260104401d032a0050b20351381e070115410028600d07107842039030b00a441e80b54034012056064032034008240e4003000200030380481a0701921007001d4540f02d04060b450130400034011191907003070110200380803004884886021304054021401d10455000100c40e00d40541c2c10320b80c110340e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 97605764 1250 97604514 97604519
    0x90504060b06040801090c14030a1209171e030c0607030213090c0809280206031506040303020601080706050703090b0c0a060213030308011409040308220305030106121a0d0c 76
    0x980b0350090006200500001510362400d00c0c20251f41076141d03106407000041501e80740001c0c0c40109504000c65408a0003504036180c100090380d103280c40742c10840398600c0b40001100c0e60721001880c0071280c0c4040000080c0e80c0090700000e680c91080a074201c8194000e54049208a40282c0181020844400030707580b16540300c858040803542807064040008504209216844101780410001801c0b26561188200c0400d100d1064190425070000e000d40c0c0300000046424002c6401c010004200501e015515076807420000d545200038041e0409500400c140010414042e900310b645803940f5480b0540310700e2404816500710f8010800c0d80d180b60181c01c00340e80020700503100901d01070f20304100341061681903083c0244020700503000000d034040342990390f1201ea500e03407031501d60003507040c07500980c1c9540320b0780c0005a170301d0043e801d0f881c51100518540b08054100d00510306131000c1c2d5a884c00f0707491161355890300362404040c60001500e24500c02c20224108142440c0b03446010f130500c1c01c4c00d00c0c0d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 97607014 1250 97605764 97605769
    0x702070308032a0306040f0c092603040303020c120c01120504080d0e07081006120f0c08030d051b03070804031d0613290d09020111060a09020a17030301090504060b 72
    0x843d030202c0c0188401c40041000840d01c2d00b84507400042007800d00421020300d8650001d0301e890303240d020302d01c4c42058602b01030321529200d05002c1c00e02c82c41c80003900d440d10743c0c03464040d60320408003088a2281c0032010622070119400286041ca40300e05a407541280100800910300412018005a42005003002201c500728140e005070341458241000070640645424007450820340d450410314800d500b043c81c108404100581038070850340e00301c03440c60410f440510f080040d504469115222038040410507400540c40d40d13214512a64590510002d08509491a0170360341c402260004045030075200858082441100c0c20401641c0c0000c4d0004846a00300000d251a00078504070701c078140b00f405041c004000720041142c0c100b020b5138150092103101c0401510a4050134489030700031551100061305584c800c08040c3d801003449819503e036814081c504001a14011038164003442d1b1884c0d0001303c01402000e0303204c050018501940c1140d0805002101404015006484254460b0007004160303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 97608264 1250 97607014 97607071
    0x2040f020d1401080601091e0e03040f06030204030b060111031204170706020c0d0c0206040905090a0c090b10020d05090118051504380d0e010f020a0215070207030803 73
    0xb0b0881c10120480c96144c0001341d40741c094141c204120305402d1042c040c44068994004420501c1c2ca01e8000c500080031000103491801254403480d43c80b0b05000c000203030a6010790007001a24000c501c0c600d60703650b600b001925181c10f49842c6043c594010004041122446840560401d00c44c6c00c045020041c1d0966010b0f03c3c1c0c0009409482c4251700090303110700c000c01004004028a01400c203003243c2221074000854034061071069410250b1100001100b41206000c2401115030000c620211151a00c190354010954803644900030700d154000d400c0098000500f00c1c6400c205d03075403403901d031107036550044400302c80e20130a281e0a0100d020300030403aa0703500d10040094003080448951a00c5c60001c1040086100e008070752207110f84e03101040c900d0f56094500450000c00201342076601e08103c0500c0000f8454413401491a510300101d007429494280c00604401d40150708603908100300c80d540030a800002c2d2042400f41c0e01c1090304100040c0e204000c1c0d907008041e0210814154a0f884e08034041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 97609514 1250 97608264 97608281
    0xf0905181209040513020604120618030f0810210503070203030d050403170402010f0305090c040903120c030b060901030e03120103050c01140c060a0203090c0607050604020103060e1302040f020d 85
    0x140140071030b15040310300340303442550b0340300090207040142c202441d004207041e0704c0703240030701416901805401828011035400c0241c03403009510b101110b1044504006100c2500b00c151440083d00010114003030700c50000c8400e044d100004c83c40d0300201c40c03080d400c8404040210b8200c460303010610045016a0b81800035011041c1001c002150354a41844d0041040075000d804c03c0303640160303800703100140c1d0b440001480b054105040000e43c0b0346905003ea4a0310040d080d8240e4800d0508141d5402c1591081c4048803403440d442051043c1d0340000002d0b401d96401c020a290411010b003d0b4901c55031103500080c11a040c0103003034900c0d1150310240460550740c240c205031000c3c0d2243c01c42e078425513407040241c00c99445886046081100401c25240c4542028085c00071980c3c0110210310b408406100103070b0062401070038150303034841900d811034540100b141d050740800e1030a0b00022308100d0380203030103200b854500a0305996400a5081000500c40391607000030956003404614214011031044006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 97610764 1250 97609514 97609543
    0xa0c0c06090803061f170402041b1701060509150702040b0603010324020f031602070506042d061b081b03030411060a0c020112091703010303020d03060f090518 70
    0x680b0f2500702e091140800768800c0704804c40b445200e01918503984180424201b210072444584951103500001d005060b40122441001101098070454160401e0402100f40030274012104240c1e41ca100c183c85901408840c145c11a071747d007210009004111000f047d000c0c2c4000e200140c0000f420002c2105c6400076042240c6440c06c0b007100b402e542843c00e201c0961200c81c000194038280041c0c0d0600c24a02000c0c207034251403694250344290190080c010ba10144c05d000d0002a2200c1d40d410314000c0805441c0854100c0011fa08401c0c840740200450321415108140c607214402194059104443c0090076025070300d00b14103011080f940c00e40110480424045580115102d013040d08007507003510480d40c41c01d072040d2810000e5280c102d40005c1c1422030183c09082c0030f00e0301002006100041d0124400091562440300100e01076070304072a000e103058038060f508903007071841c10802c103504036a41405481c0120000710000c003d07150085e0001540700407101c40b58612114240055407a046081c0c0c80901c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 97612014 1250 97610764 97610767
    0x50c1507050705060a0504031b020a030215070605060907020706080907050a0f080c010c05070909080d0504060c09060f02030f160c0306050106110105060609060304051c0207090507080f0a0c0c060908 87
    0x240001006245d0704031101680070003040c24981e5029095007607403000070791445041c4030550b044d5610000c01c0c0d0700858003d410400c82452985101c1c01c40d40c00380c24100d6400e490030003c25035a080a007001481210960010203d86040007829210560020b065481c02c2c8038030030000ca2240c41d900300c0302c802414848446151142824003803410055229080d40c1008007100e0f40e400030900028118080310300030345c400500c800480c03c0c1903031300b03214079001c0d00039407030510052001b04001d40d4018111702d5134513980c400b01140c65a4082702d40c010102c20100050780148100001e40519500034101c0342310400c104103105005607151007840040d0340c419a60315640e6001007249540001004072a05565030081149140c480b0004100340a02c038030340c602420000c00002d08005040286c881c8082041c1d480d1980c0c8010400025910f00850103510104ca0070f00707010500c101e000c3c0d101c0740d0185034a00a02036080d0780d40038900d00141a007034801307410054200021004039000d4464100240c1c081d500c3c3e03d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 97613264 1250 97612014 97612027
    0x8070602030a090905040c03022407050715140403060b0d0b090d09080c060d050a0b0603010f09270308070302040f0f050a0e060d03121e09020f03190201050c150705 72
    0x1500f029441c1c0c0c00701c550350317007410204030010391044074a2065950440d1401d256081071804c1c04120351f0f80039104d030028140011f0960510000041c07a03401c031340c20a984541c680e812214200d07041744d0f854200309603811042c0011b00c00901107821003a800d403005000c3c130301c0c1e55109403200c01f05020300703032401d001981010403c142010340c00180e11014003210001442c800d0300c0310021847c54410700c0c00507001e0940d110b005c1150800503030401824040000c00654403540c480c41011400e8069119881d490307403400049a200c0a040c01e03000c080304452020741c210440c21901c0c2900c181100400050401d5802c1201150700a41c50380008042d007680c0910012407802c06c400d10503081c0e100d4200c4141614050308118184e60f0303035020321050603414988001d222001d0a01c01c0301414808400c6e0311a064500900030022186e0b90140108038002c071107001403501071009241e2640c115441c140c0c900d140094000c2c001d03500a80040c41a510381d40211118540328824400e0101d005546d148001341001508 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 97614514 1250 97613264 97613267
    0xb180a060b0a02100f061a030a060f030818010210060909260910050c0604030e010e040b010e100504030b0108160803030c0306041107020a0f051003061a0c0708070602030a 75
    0x88401030642500c1ca1450200e6100300a03681c0c03002241407011103038550a9000c541c19180d00440020a035560303101003c10641c2c025030140390011201c81710b040340b500754001540e0003558480c0c0100d0303411004035880d210744199046100410282128103510a443ca11a00d0845c5441044010603419000260340f80b510f10340f03c0b140e10114950400c5c04100b090200e02a00c260604992070040f08440c003081c145144101690b0a010716030256003640a050100011305400442061800400f642c4411200c91074008000c1100d60300c034821130009201c0c0c0c294042034105128260800e2507141012420aa526a1000a0000c0903000020715800400b101c1d42c80350345000802c070250003004061810340c5020024101d5500008050901c103980340c800801a0b80a007000320b41c6a40c0d006855000000c3c0ca0340c87c042003210080c41214094102c10044101591092082d4015100b80e4144559107001414072212207401800414a03140680c420000318440100101d80081446402468444450100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 97615764 1250 97614514 97614521
    0x1b031c050a1a0a061b0807030f030b0315010e06040605060403051b0105070f0206070c03060510080d020f1005061c120318030c03120f020c0c09090a0201080f0601030b180a 75
    0x3400194401c0403040c44a0580d2411100f105440040c070f003a9864124030250381517029401000a02561400900c1905044c1d00484035190450310361420b220b902c1a01051503600c0c441c081c41c204008541d1001402401600e5000700c1d0450001800400c40c280c580380022400d07030140d481110341d60700c14001c3e0314010b4141700e1a01c2919409082007800c002403a269010403500e50319000388113540014242d41003100700e080a00103182c0000e4100b10074079103c405803c4411041c000d4041c2481182e082c41c02542c4001000c0c02e4014170407014103100c600805400d0098207000d0046d66000412000a41c449000744d1000b5016900481d0640c0c511140106d0183c00c0b030703095841084628070280070044c0030940200d240b1240d5907162400304203881807011110000c08103504400c500900008807041041400902c010a400c0701301e80150b0ba6441d0380400542e102662070000380403c112400040ca00745180075019070109060501050017868240050040464034480d008101191014803955003002e10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 97617014 1250 97615764 97615781
    0x2007021503100614190c05060c0c100b120607050a0908010902060901050a03270501051e1f030203060a0603120305040302060c0d060e0c0304030809010606051b031c050a 74
    0x4150900d10704240b11050380c520501d014000501603055441e812481103601102d41114400035034091001071007000800340302054500340c0d83c81c81070302c1c017140f204200a0300301c6420400c42d134010600e0f0300e100030b405c10207014000303080380e40700c03011400070100398205115082c40358540d60b40d155070307030b81d85040c010302441200c1c1c01082c202d81c5080c180a0050300e402044400f86082401c0298580c05144421000381c500305d0b5090001e02155170001d983c4440f04564078244c580301f03000078805607450a4510080034807203507500c0000002900450006001009690980d0303610781c0c2c0844100380c880e004603240200507644c0382d02c8141e5078841002446030020300402055620b160a1059040a40f4025903416018015040c00d01c40001c10312410b0310701d82e00000c01401c28a0380ad020b0b5182064080d074094008071401d6020408004c006210b0523010700c1079205907080c6807141410001000c84d80e41d17690040066082d154442040b03a41010303040f6440d10203034541e411030046800d280161030743e402d54494a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 97618264 1250 97617014 97617049
    0x109060306080601091a032a04050906011202060c120301050117040506010b090a050a08010c030c080c031303110102070507030213090b0a020a020c0907020f060c0403020d0b0a200702 80
    0x720140034419001c0361660445203014008248407581658403a1a216640e0718030740d06200b41408985001e180c800340e103d81c078262010b03500a446d5003109010658008482c4c03007107e60084001400030180c17521b10f00c01c800780054007050a02d011146140e25104594244803170b00f000c040010415036030b024140404508014800c941e403030405654007666544103014084207241e02041d104119151003200710010000104142462070f940c0e95001d00810000c0218000a4142000c3e0001e4a025590f05405070003110311309495a0348014030810b41958041c1c00300c08100b501d142030341040c0e1003400600407250165004d4100ea600d0f6104102803000d8640f010340381513050154032401302e5520b241c42c13079102b41541d1026a5440d00c410080381820f503080082a80b03c100d00701401081a4006811440075900d6401c07140d1645441d0001003060065100095020045401e03450000303040110341900408022008138009144880c00a59610018241c40f0084000b00f141030039440d10344590030804002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 97619514 1250 97618264 97618271
    0x70909210f080601050c0a0303060f0f050108070507021903110307090506010903060902030703050d2304241806110c0a03110d050a020613091a0a050120030703090501090603 76
    0x540101401a81d0101044400e01150070000381281c0d003e201164481d4030040d00340c40d121070311441e004d001804140540c134203a41e0042c1c80490000c1413100d089040e208142c580688960781c104040f601503008920481e0006203d0740390440c944000e54010b00910710580b280749000c00420103051400302c0d40e91142c1d000500f090140002ea9030810020301c11349410040c040f80c0f440c800d0000c20314100003a44014251302c14081d03140d000540c04801007003a0080d12600c0d149013030503001903034464003650140d0032000b40c1035040110100d482c121108078170042410541c0c00f500c7c80510459800c3c401e60b00040201c1c40004452405000070b210100070550b0459103410105e085442d0341c2000d1400c0e1a00d180100c2e80341032410180002006250242c0340c0c0100010b686109060113a2a10000f030b02c646010281044455440f42e004070342c01000d03460001e007081b10420300d410700440341401c40c000074031396403020341021078101402031000f4501203020742c50707090b282890324000402010b4035170310820030140b8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 97620764 1250 97619514 97619573
    0xc0406030210141201120c0b030103150207050f100509070909050303070305071205160e030a0f021e06130302030708060f0714041d06030c150f03070c05070909 70
    0x715a00c409600d41d03164a40b02030f0342c0450104a186521402008901000c11030b0000a8282000c182103500f080c450382c0e01c0c0032901c5e903d10703620700203020a010040006a942d02c2d07440c04003280c0e90161407a240a01c0c1154004108002d40508060300d61a249440a48403400c01881500c200028001810304400c01c1001c11800d880d081d4807404040c0a18003015115000304401610944000340106420390003000107041400c4041c05082982400002203200d0000100340e514010804070394440e04254104988695a420011101d108084083c41755040e141c180044d51500c0300680a0406142c0b007410290f411401054903001a0b6032040c4410350000d810403016405d20444240c0040035410455160034418082c01164040c50308820078184641c1100134001605085442c080c4205074140e40705406040184222040290002081540c0c200040d0b074014401d88010341d031081507858941c0b894042c40e640c590522140d50b11030145103844090036010b0040140103104003024240c5411b038100ca = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 97622014 1250 97620764 97620769
    0x70603050c0f0904020f1207050301060f1e030903110a060f14070507141912110102091503060a0314060f24100c02030303010602011a03010b010206060618090c04080c04060302 77
    0xc640f44849020f2900480c0c1800781c408488243c603c03429811120410a26100b030300240a50024170400e00090001d4552141c5140202c03080c8100c100c1600302d18034012480c18080d4003402c0800400c60811200304842a2885c10900c0010100c901c26200400d065540309608004c3d40c1200c1c15852207003d55500307000b5a40e4004044a690310f40c010b50001c030010001c3c8804c1c0c203142d4589400003500784002ca003e001c11100001440c5c014601d525040300b02481e58902c58203e0003408800c5420070f036924805040c007209400035603841900281568411616030740c4240d15003032580c41c140b40c0c55004005000d451003442402d02c2e4004201c40400d00d6451a10214000c14010003c40c2c40c01166124520200b0510403040384c07603040e40180483e566941c0d0340300020f00904040541c001c0d4500000180c140c645418040c07444030b0101640104402d03191841003210b10740c0520300c2140181d0451000b4641038032404c150610854501c801280c655180007119070a00c80c52040c0c4030710961800500788010b9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 97623264 1250 97622014 97622017
    0x60603060429010e16020c10030f0b0402070303020c1b01080f060409120e01090807031a07090801150f0506070f0b13060f0501080c09010f0b031306020705070603050c0f 74
    0x20b80000061a024040c0b402c1c85240c070200103240303441860940004030304502034000484c0609807403821404540050b400480e21100561100b81d030000e2004c132325081d020703c03079000700708404035140001500300b089a00140c2282c1c03102c00c044020036008a2903805c4c143c42400b082e18044600d10805c1320a0b50080c000a120203001811515140458000300d45580c0300c41c1d01c41c641d025440682c203a030761441c104000d4201c9950741c0c10b0f00d00180d004e000110f1405000b080d68400c0340d501000001c00b2210b5581c48807000d030b10080c24001004901580014040d209029024901e0080703c1d108020714206801444649c0f065000035019480803c818000540c100d072052000640003406813442e41c4a404030b00c1d01c10410610040c104030704010401ea01d01710b03da0f1085041351149801c5a00e00400c80050003840310003445100d103d4000074504107c2181c80c2c900039a80203001d506400d0b41c0078015a41c030380890b0008141650103a102200c20300c0440c0d007520540c0d4000b085a4415420300648902179100c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 97624514 1250 97623264 97623271
    0x1e0e07080619020c1b03011503050a0206070f020310050406060f060c020f0a09150f0509040803070e150f18011b03050d0f0903120c050a1704020d120909060806060306 73
    0x4188000b06040070308500356050380c285445030003d9416100c0c81c410320200618403103424a119501c0c001c41804003041014a540443c9d6010340079244050b40742e004c102d642d40101c00f05507201907806204100507a4148442c0e2048400c2d8100000c040c1041d0602c1d20890f1143c0c0c10120030310038122824400140c21114001805078101d81319041990602c0101d103091441e0703070062030440d0919100e255840003c1c0892070a9900094048000c10f5440007001480401581c0180c01180d0410104a01034490120f4820a4802404a52000c241400c00204a40c441c0f03050100078200492452000350044160002d80c81c42481c12881d048020620544000c0038100014180480042e4030078000015420a031407000d03113071008100300780c91400c0c041e0041c45010a0750365414540b800702207000e4007907415204001e600e903990320112036411031a4910084080c00c141e0748048910380d0800064021550001c031500143d0b12146580d14180115050750b00310380011003140c10500030084241c40000c1c03810791 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 97625764 1250 97624514 97624531
    0xc05151b010b011215050909070603051e0105060a090806040803040201020f0a02060315030c040603050f0d0503010b0301030305031906080f160e13020a080303040602090901080d080406050601121e0e070806 90
    0x188403114160b0174030710a11580c0810b0f0040c0c41e11042011041010030f500044030f429440c2840b0320359403165450301500031045454580381c00079006112070b040c0840a03104c1e4551034146103410b02c1d120fa80141c43c006c0100c40482c0c401c603001081204650f03050000d110a40651001000075168650014180380402050004c0a08000040040c1a5020440d02d44994000b6204101542c0c44c0d0511035203420505c2c41c801024880c9480001e5001d100700c00700c074121000410309a0450f401c580c1c003201c9590000d0400b00724000094008070804803e4400c3e4801005c4140c01480354008600314241040010344c00356040c1ca408800410180303078018580c603882640700e04500c0005a841c4001540090950410301d414030001c002c0004100e4664010101b0601c02c841e0000103030390b500d0505942e100c612101000090510300401c1c00200203400c91a0801014104000d81d800307168402012a030344042c0c868802d0001200c040c00584c924418040208211030107004c4403030802da40541d403040c01801004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 97627014 1250 97625764 97625771
    0x806030a110414180c0603090d0305040305070b16080a0c09050907091503020a02120c1507050d0f0906050a0b0d0816060c020a0510051003020103090c05151b010b0112 73
    0x10312503611030f401191424240c4036040b1042c00d00c1400340d00c0500070042814091720030350442c41d074070b4940322003600c1c0708007030020050240c80f00780c01d0b04a01400d0090300c120240b00341444004002613030f01940d5032140340000b59a614034044890700a125050160250340c00030302d40400020840e070320029480c00c2c3c0e001a2400c15054558100864010030540d1192028090f90785e41c0403500e81c2c0c16001004000d800c1e5003201e03290358295103c2d40103482241d540304010781c0031001c10b144140384a040c481d4850341f203060007428000b464400c5070036a1140200d00c112070f95142008800c01199201e0381d90050313840c0b54204a00c1e09041d02064001c031740090050070007070001c61100d0380c00b1040c80c1d20300380003030b8450700500204003c03c0001e540d6a02c103a0f0115031a0064441d80e00241c0c1031882282d1003045440050501e840c5960019802005042d805841802380124003180c5030f12800c2a182c82c052030781800540e100100943e810000e0b00300304502d81940d0501c540c60030540c0c0e0203424120b14108400002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 97628264 1250 97627014 97627043
    0x902130b0304140105090307060c0807050307030c0e0a06091e081f11041d090d090501030209010c05070e0103290a0f0906050f180601050901060c0302070305010501030602040311010806030a 83
    0x3c001e041d050f1401c00190f0905d81003041002c030100c00f41c107529102d44e03001c4c8174ac054075980c15145a0307011a2440300040e030520000e044503200b03804c43c900500319410040e05811300d80c8049840501590454000b00356450810000e214100d0800103a41101c202c407080106e0901030383c20340701d1042100c2603103500078882c0900119820b551010290600c001101542d83c1e6803450400d1680d221210078800c45640d080004115503000702d0b4a00d013600640d5030b0f08070000d05080042d00290401e0740880c0c1000506a810f000181c41000f50a01902e50007082102942c507500c1c0492148e5080c52001a01c40a070f041000c0e20b81c04014641502f2044a808c003140c0c03511b806203458001d00081d5400b600c100d080c0001e002030f481505184a0040d881503043e5002a504000742c40c0e507500003072103200c0e0018802801002414450444054820702c2071060b81d10950741ea031501800d40d40207810542d542035000a040082181901c2e0100d254502800c10701c02d14504100002d03100d000000c1c01600d8001e041004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 97629514 1250 97628264 97628273
    0x2071106030c1c0605010f020a052e0617160b09040f090f0b04110a08060118020c251502030904090503090d11100306150f020c0a06030e070902130b0304 67
    0x259103680a20b16070f5040c40c48118000c0b031018003894800e050100c1c000100c048202c1c1c0c4082050840ca540020003440b00703000201e0580100c8103828a250042d482c0e4000410402c42d05e03015030002801c1a0f0100140d100901c44024200000d000d6480e480d00088581040501014000d07101170307076000c0301d00055100001034503402034560032400400e10103410009504121131014840c0c061401001d403500b4a0440350f061003116100c0c2e003c0d41c84658024001000310340c112880c0445100ca04030805418400715110251034a04c1d60149040b0308029002d13584d003261588080034005011000411300c1081044802075100d101c2c0c408210b001d07584800001c414407008000f1200c140c03c000d4907040480455050000d601007807000c4141c420b0094000c0011200d01ca0300a88007902d80e1000c0041c150389d400082500e09414655042c000d50042e2031020324541d5504600c4001840c2907140400e102060702803088c10700c20031340c200c2942d0510503c00c8805017043d0800c0902a6600000e40c3e03a40d9403290b081 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 97630764 1250 97629514 97629517
    0x6081006080c0f041502012004090b0402090a0303021b040912030506010225030209100501090b0304150903200708070b0703030209030a03051e03040b07080622020415020102071106030c 81
    0x440c4400f0001034001403804800c0f000c00d2104c021940200b00d40040e0408208028019915020614030140014812600c05602501d1140c0c4014401494841d4090120f01e03a00101d5000f80d001d80c015041403084543c410040c00010242100d0400080302a0b0703540c03103c00c810540b0074100701603807080001d803541d008001c84c00540c40056610602c150030201c40c44801c62050208070300a00204000c1071015500b1034501d002e4400584818844600708000c4000d40c0d003008000f80d0b103a41c000381c0c5004503c04648122403825000340ea60302d5103072540003003001b000ca0700c00750030f007000d13a002440400030407070b0206c1c00d9000e0f184061030441d034603906400d044000c1e0045884c0307964140107600b181000c00d5040310007440c040c0440b403c4040b0700c003418920846e55001c2103502420204444d07002401c02c5100301c0806500410041102c1110a4808584201d40b003042084849a507030020313040c040d1241c40e02010f500d0091071320003945824001d0381d41c201003c0f118030741c0c40d004800100120303000219100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 97632014 1250 97630764 97630777
    0xa05160e0117010305030a0908031602090c071403190c020a06050c1608060a0e06070507020d0c0801140708060a0f050d06141609050603070e0f0a0b0a110706081006080c 74
    0x1e100b01c5295031281402078a03940102e410001165601c100010359000c041f05941c00f0010005111130014a25024003a003100700420315611000b0801a41d400204090365403403049803448000c1da1603010301d4000514401d59042e042007402601450744005943e9280d01c1e20680b0610b107403994650b60354140c03480c50403141440b2042d03651682d100c04140d4030f000040c134500c6605184400d00840c22010009600e131402035440c140000d44c1000114094107050580c20060f500c10784140114998a01c606404c40329100c00e170500280d812028803a0265000e05525040b44003140c0440c0818035040b002d00342c0203040c1c414240230700c0111000c1c0b4103014035948154410040118940c12524145080354003001c503045043c40403410810004c54103040c6102500d00c64042d44d03d0300a014044102000300d032050305105c440d40300c0e54401e0081081e40030394014004400e0103403203840c0102e03210a44d0380d00340485504803404014001d400c100290030142c6440741121482d051550707084c2c071041f0312008680b0820 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 97633264 1250 97632014 97632047
    0x3080a030b031c080f064f020307080a02090a0303110a0b090708070f0e0103031b0602040603090b1605070b0a062105010f0926040e0a02030108060a05160e01 69
    0xf0241840c40e10b4001c845240310340f510325080140ca0799041c1c00c001d041c0402d10719460040183c0c9954840809009503110700f03401054111410052800350410040181c20f0758032803a15401000340800c0680107540d55401071100a01581403022060106003058074a100240403c09910320320011b80c502442001100c0d90000b200c03503100d14100718402d5444901f84603014030b0b803180003400180042007076100b00540340ca030703190030543c2e13461910200d0780b885504410455200d01c1101e88030000b1400d100070b000034915030700c010400200904100c909410010105146140807825494038140d2000407123085e1940030001e06110b80324178014a0041805400010700004880007030f80d81503181c0580312981d90b10132070081c082d129402e030f0315506559614000030b081440e030601001503c05094091406001d800500301d05081d5581711100402100b9681e00070860f50000042c4203602c0c040c000d490b8401c009240500c11070030702c40f070501968081c0b00b5a040c1048100003600f2400ea1064402082d88000e5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 97634514 1250 97633264 97633303
    0xd0c0903021509030d05040e0f06030f070915050105040b04060c05030c060f0411041e020c0c1c0507120c0e07140a1713050601031103012a03051003080a030b03 70
    0x2d0381d942141e408200440c1c0300784101800c0b410268130413030844065902e208085e0030035032940803512600d04006092642d06009a465a07110035a003004a10018081910007003902c240c2101181e8440545410113410400200320a0200d015000100c0302220514078000407541c601d81071041c114090001300400c18000d003414449035001d04081540a18041c01d0000382c400d030310710708100407100ca00869210000000d40402e908612550180c400603a030881581c1c3c070241407a0002c1d03095a079a401c2c3c0c41d0191290043e601c01e01604010030710260201000796640c10b9141e072110702d030ba84040d01c0303251454404000007540301740c814242c7da0921461049280d48542c10558050110030140d5181000f00891100080c455281040004812600300300645150f900316102d4088851070280c65541664071110205030101e40d01403c54244030240b1929a40500d8810004080c0d0b072002d0a54420314003420000c0c804115108116094071029043c001184101764010906014a48048030f0309030341c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 97635764 1250 97634514 97634539
    0xf0d02060105040f0204051f030617060a140c042d030f050c010806060913060b0a050a02150c0f0703090306020d2007080712090902030c04150c05030d0c090302 70
    0x40020380e69041e100119070900c160702010743c0140072405580f1810764010f590a0821107046000c202d0842911494034002c11400d031149420080c0000740301b800c00c4a82c0c800350420000d00c906100d801c1112480c42d15071016410145440d04560040380103400410a00751460341d4195000b260300325104609849641d80d055490418803d290143d8606940902415505107002c0d8890743c0d84a00c1110024121402c1c02404010710034900503150006602c19510b00010651007425805441900903550b6000e40c0c648000300000d0803c1110712200c0c014000b41c40c1440101d001c1003007a90703c0b81508211085d120f8102c0d0604440140c890f501c0645514400a8100b02072080e68203c03506903040c40411154144124040d2036691185410181082005225640010341d900110108000306850f00454040c1c440c4200403c0307034001c0c3c40c4040455030001c0c00704100000e0b0340c1078840500c01410015503046241c1c4806850307104560324145050366444046030072074024620700c005183c01401c020403141 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 97637014 1250 97635764 97635767
    0x60c01200c1c05030c07260a09080703050c040c1808010b270606131a040302010305150d0b0c0f040b030103020a0e0412050a0e040203040b150a06140a020f0d 69
    0x28005606280e03a806110b5803501800781c146489142030b00310350b886900c1c5548954039500d040c3c20080c030031198030829006039441250558101150122803140c0c0942d03c40c0240c60260444449902040050300400d004101003200407a00d8030011005903000f1540c81c207101c00864500f042e11b20044400c200d550f20100700e480c0d05500460f4074403810f61b8001c40c181e8009400c1e524210081c00d40000c06001000014201d0030804003a00954454220034800c8946521200001610218041208680c0071604200b0b66903d801201d030080351394450a14a45000000300b000c20018030300113494210190007140409155504464610b440f000c40340740c035a0b440e050b144210707078428031042e071080e5070110004c00c60000c041c425500442e442400034076135080410060341c99401c8078555209000590039050401c0c0c450707000440c8201e1088140c0d00891601c4645400b140c0e01109111f801f52100507814003407141c102c10003200c1c107103484120544816034014124500201c14222030400d0203034a00000c98103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 97638264 1250 97637014 97637017
    0x2070c030618030914090a0e0c03060a02181503161b0c03060e0c0616060b0603040f020108071404030605090313030804061b1e0c08060c0c160608010302060c0120 71
    0x360320982c0c84c20165540c4207049070708100003100a80c0c0c0070340002d0105007004206c0c0e20071010741498a050320b0341c4c40141800242400021140c0704d1403070750006140207601c0111100d600512300d0803911015500540d485503019400001d00328402c40481c01903c01c00c4030300642000300d9072403104001c8100c0c030301d2901d01a02e500400344801c40358070f410210580112a0003080541c628000605034905000402a01020140c0120826180559a1400212151101402036100e50701032030b180e03004401a4400100a114018004c500700400c0c0340780134420390103007000c0750100e03600020045070984541c80740e01d046103d501507803032240c0b104003800010410494040c00407035442e0340303d040d03000d02191404220628581c60062030700d510044281e1148000b80080b2404d42c0c000e1030400b5100b40c40d14a41450600b054521105a800101d140d60480e001004084245d0180d1104480540e1800710b001c1c041d41d0301800020700c141d0010501000303131242540003149042c0f082446180791003501d0a600d120313 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 97639514 1250 97638264 97638311
    0xe150c0a02041a09160909022a0607081609080d020109020117071e0e0315060f0402070503090909030c0304030b15030102120a05060303040306090506180604030e010302070c0306 78
    0x610b041440307210040b054240143c024600c0138000d41800d540f01245140350390680400717801444000d5030003081d0101d042c4040e1031951200e10b148070440a8150300328495180d81e54411405520090401c0620303a0300840c2107812200003000501214089041600c40281640203583c42d44240d9181031440750b1305401001805000707803903401010b10105c10300c0079104000c450300381c046080040088000051000e60144040541c54000301004842c1700182c24500d24144030800c18181c0c0d028080146010206401c0d02c10b07003150118a009081d540d10b0307441c2d02035105071603c18a803040c001110b4071404c2c411603580c014104103076580c5075101e26051162250545904150500a54604403941014800c90307426082a04451660340d903220441c01c0600001450560940030034840000018440c1c028001c10300c0c0305030060001c40ca040240403a148207400075800d42c079401101840082a086075640c500041c0a1801695600080c104407141910a50005005600d80707010004400c4d01c1d40d201e40d15 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 97640764 1250 97639514 97639519
    0x60504060b07051515060a091403010603152d050106020c120a0b07020304081006150c030c0b0c090a030302030307030e1c1b050d0804110405010b09010e150c0a02 71
    0x646901e400201c0c509018140300206039a104502d4607040711007101d002544495201d819003e6815140041a1160802c41140c004295141014000b0540001040c0d8414170160002c000851a64580c2d22054422822030294541e5030140c0d1494640520803061042d40741c0c901d0850b0301c2e614404804d0060400348a005c0043c05104d070440400d280134108510400041002048410f1050319101e0348000007602e401e080d44410440050018014403203007000d0480410300148082c0340081b102c85076695156a9000c1020b030319400c000298000c61121080b5130048032022881e0755401301c3c00000c0c8502c03400198003400300540001095070020040d8481c0391165818003080303200310135865595241e42c1c004009548071840b041c4e00d9912401c4201d0111640c065004140d40c00c50311604e090203408011540098201030411090082d099a0318004001c10382c0c08010541c0b41c40d500f82498060240c0150402001d04c042d5826956031381d0b408980e420002c10700ca652110706a99180e039030745141600f20b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 97642014 1250 97640764 97640771
    0x50312090d09080312150102070816030606050d0b01030b280b01030f0603021005090103021c0e120c120a0c0b15011101090c050103020702240901080c0c0c0112020913060504 76
    0xf504030004000d0b40d050044480c0b001844d9281e851a00b504903a91a2406045101d40c0c0000259554104000d104a4944500090700c1070306604200f42603601390703000381303001d0702000030b100c40016210b400c020304594201044481c96207503101042030002c10090f01a4400107100b11101902c0d2580c0c0c0b02c2c0c1c502d04400d80b070400c141802e0f13000720710581d10503202c003075405124250000030781401103005141001051400606c2c003815500d1000070322162201101405640706414002c690003003050b50382c00b400d00200e031805e110340c2c61400c40c0e88a847c00c403038400700d4a010540c000040c0c000c1d10840680c40e0b010b0b010025528040f0151100074404102c1709001502d82c1e1500c0403600701c10321910102c290840301c4c80c0070442c104401500694403554040743c00408440202e501d1010b08042c40c4101401c1e1b0210076928885940010003410014091030a01a810404442d9041002928800061007801c004480d582c001500d41c0c024040e411103160030290343c1540112841c11a030040302510300850b400c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 97643264 1250 97642014 97642019
    0x3010e061002070312120905061506120105100e030f0607090603180f0218010305030705100b030c0918010c03020d0608010b032806060e0708090105061c050312090d09 73
    0x441d07a64814510301c05a085003105101003800c141a0100d80d00c502e042c00f0516820030a802c40403034481500588184d0044003c2c03000c00c2d00c400a03140c103460412210941020608414414041c80621403030b813094074440c803100c140318061030245090b003400a00b030320780c402e0895141c0c58070364808580d440002512040d0200e01e03207001c1d1252981403000e0301c05004200c80251fa550010b00345c5624103a034420401070070304c2020b6041650550185208501440d200d010b6481d2807440c01c1d480d0080c818000d801c00f1200b401d141c50000ba841c1215008440480054440752818441070040c202c0b401402e5003498190304130642c00d5002001140c1e540c1000b04091556040000e003294404885580c0c10b400440300c5501c4031041d00c403540d9441c0140c080c1003030180140d0762204122044c0c7c0c1d200410f01c0341d00100300a02c45e9044000c203640704900d0300c020302013880c0010006142c4001c1c10f030310400d100071110813031080c881d00f002655002e503512800748580f402d01c40c0040f50380380091605d60700051140c0350302 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 97644514 1250 97643264 97643269
    0x801080601120303202d07201201020c0106060909060e07050304061104090504021305070e060c03090d1a0a020a0507031407240b010c0b0402120a080a020303010e06 72
    0x1150480b40a04001210741c0401e640850162983c201303070380c0c1030b00384014468002504d0503006241d0310100440840e259010074180000d41d04c1c0f000c15254040d40184240c101007400c02c82e507d80141f00314076031000c2200c010380000d00f05d211000c20300b17420303036201141d407445071481541b040c0145d5040d038940c50143c40c1c0d2045a1429159240074803089100c40e04042020680aa806107802600c02c041c0800c08a81c01c1400160540003236225a18098403117090000b9030800c41a4888a0300c59031205000078500340c00003610f016000084180a02400521160300b03000a1040d2128844021b1034003100c0744c82c40c00c1c02d200001c070400c2a003035451407a0000c50b0f0740641c28422902c2260340c1c2d4403881e00300500d1b41c50075225103a40c0b45000d9000070040203118000f42c010030f0050403804545400a800c900194002c000f01c980700403200d0f050142014028010404180505500c83d0b41118201d170340c00c80da4401681040380202004010b0500400e01280d400c0d00400610b041e03c070054103101c403560b204000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 97645764 1250 97644514 97644523
    0x30506100801090206161a0906060a0602160b09040902090109020d0b1806010c03030f1b0f03060e06040203040602070209090a110907050313060b1002070806011a0316020c04020f0307080108 83
    0xc00950251041003061880040054441b40090081c1704030f8011800c00d82000d02114003c442401160b0040c90800005240507038800c0003811b051b00c0149000d040022090691080c0d901403038001ca4000f08d140d48060340e4503048484029400b07080c042843d6902c84403180a50410b4420b2054141840002c0200d410101e6000419401684113444e040d01c60034015650440701c601e09230700700340d01d1300b00701e2648070598003401000c50000d018011012175003510040c00b42d0082222001018100441000b46803c04110282c12003c00c450050796610b41e440e00300028814000002e402811f444100b10f18a407000c69030143c0039000711110068400381c2000c11451300343c100e5000f03020503c24004103c916041042c1c1040080c42040000303124a2201c0014182e22048121600142d000c5602482900d0007840818010407070082c0c86001d600980c45454905e00000308003100c900151203516200d035200700107042c0c1d00b0101400865556841010600841c0d00465464011417410400018003040016 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 97647014 1250 97645764 97645781
    0x71e08031f0b0f03060f2707030f05070c030f030501140609030715050d0501140607060b040f0608030a020f01020903120c0106030b0c0315010801030203122d040303021e070b0c0313030506100801 85
    0x5214410060504007081070078032008d00078800305941c03500310b0134800040748525030013006561110101b54086150082c55003410414060405041030700400428400203004007070450101c132116107441402000ca458051554484401080c403100080031250700302008044044041400344a03a03a2075071a00708003001312001441e0840800c008020102e60503034401c5000b0384000b013001c5000642c608090050703a549802001a40d0000030b207030031107250104404015003000c1c3c402503041c8110000083d07226000c691030766000c40c0c0d00040000c61008294045006168800182c07060781c1040d80c0c250400b500120b80e900b04041d500741b2100d8466004030710380d86c1202c0d4010018101c1030b200280c1031580343c00004003605400001d025060110190120b4031801c401c030500c0c0c0176110b502e1030400070314040780300c005241041119003000304404008150b0720141c910040c4050b07030312025030352014618070403d103607038010950004002c0704010340880c2c280e0190040011001c1055100c102c1c5908035140503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 97648264 1250 97647014 97647049
    0x603050108070b0c060a021c060902180909150415020d05010f1706040215090901090509190c0501050f0405130c02010f02120f07020a0203060903071e08031f0b0f03060f 74
    0x21740000301000c0264004110000100402042881e101d80e050001d54046800c0342c118590041800b50002d85007039001000c110702160f0b141e40c0c50415200140d01c1d6042034418000307414100d4009400e114104803508c48660b1100c00071580d400507125420010407003070007004032410800701c00254000d0014a200c0718840390102611450f10f0365070800a200a564244503a180b00c01d100c010501c0e13076211461402001c0c2204045041d2501c01030840c2081412002501d42c0c142c3c016030712010840c0704440000741c030300a0030078690790341410440b5182ca00446e800b403903000e42071010514030344900e600016001c0986400034801c41100000a0059014003588183c60007a02400585007101480080e034000016005440822070706402290071300f00116002c11040c2d00004012040018040d01010100042004500c030010141c0e1544828400600400184074884980e220303000001d0802d140101000301d619a40c03000010101c00751a04101c84061184500c03016116080c20b01c1c00c0d0180701080340 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 97649514 1250 97648264 97648273
    0x60b10170609041103010603110405010506040b030f0603010b04060305030712030203070c11040e031201030506090a0201050337061815030b07020a0209010b09041a01050d0903050c03040603050108070b0c 89
    0x70202031154000d0300a20944801005601d26507442d1000e11500c000346006a507500d420a4124080c80252601030348480c0c02004100800c1002010714025240c01c059054242ea04649803640068094a00c110105600600e003000c00010414004020b0080300e00c2a00b501070407400c0300f241070301240000c030351050205490210340c00000e41980480c01d13000070001e00010f00c205a0545880c82d50700042c2c1c581c0f800402c440c00500900000700302030b40e07125000400414401c81140e00003000d5000c081c0902079149007108003030042175101030b10003000c035034021303642402d01c41c00f10100d01c054002032003902c3c0d081e043c5140c40114100305000715480c0c40c0504003080110391560760b0308240ea00c0010701400442c0941007007080169540c1200301d009266100743c0c0f58441001600700411071b0220a0700320601d03004204044030b02e9812009580e1070401d0641e0001d140c2560b82000d4420384030b071001c602510f000c0000d0204050b501544114143d510708001c40f040a5115103ea9040b845828840111b90f0720 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 97650764 1250 97649514 97649521
    0x30203070513020d0e030702011101061d0c07050d03020319090203070e0903040e0403090509010506090d0818090a27050a08090f061c050717060418050a060b1017 71
    0x10911000030182c4007610740140342c040e9089500d002c55400c0000031885410000c0d840081d0341c1d004581e20035518204008200302071411019000082195600290800b0070500007050585800c0503503603465000015100d402d40050780080003035000311100004206a000200b0030080e6038850014000e502800070a441410000324550780c0100800d15052071100300070201d264aa0048401e000f81c1c401c0e1030340c20605040c10200414034005030400703401050300f403060010540d44d41440106013900311b86c14541e6081000102170070400e0564140703400c4020003041c03144080c0d8950165403014910312001044180d01c20303400c1400d503140306001d410380c2c1c00a550340d0f01150000004050080c0e00500078010a55224003003821500100c0c182c01e940c0b00881414401c0110034000c0b01e2b03001c079141c80e00c10a84040c802143e0b02140d8094103250160b6039980c007030030b031032114440700c503001c1d641250071520945224a82103010380038071401c89000b5100759620800c450701a001d80c03c4035503425000202d80b40e4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 97652014 1250 97650764 97650769
    0x30c1107081b030316050a0c060302030708190f0908030405010b060306030d050a21050711030319090203030702090f04030207050d02100804020a09061e0f0806071b0210110d03060302030705 83
    0x680c0900d42e03c1d4140010401c3d41c400300c903400035002c5100d00c01d0025165003c19810500540c503441d911040070325004204000c181c650018a555202c0401d0000c102139000310305100c0001c103078226800d02c110b480e000150050200500c0074520841c41100240f0a0f0301c0510180aa580001e07258140c00d0340c00248040c3d030031800743c00036000045c90707031030081d14040103110703e0ba84000061141c16815a40c60007401802f50740407400403000358030351b03000b189141007041500b540c901d0b0300840d04c0d0601c0d64441c0c1d448110360303091040700c0b00c0d01c0c4c00070032401d940e05118020100924007650214091f1040c2d0307000040d2410a01c50700442d46400420800341c403c1d249109451481d40100126400344c071150011550860f070b80f0460000d0300e000045454001d5505120222026a6821540c5201c1c05030804200942d000600079a000105103070181e5030000e2413440f02068000346100941c0500d100300e200b059664004011202494a03408403043d0082e0101c0070303811507020f804083d4150300320110611103070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 97653264 1250 97652014 97652053
    0x1e08030c0c060f192703020109060f0302040504090525061704050a020d080a030c050f031b0d1404030f050c1e0f0604050109030f090f06030b0a050907030c110708 71
    0xc0308600c18981102c10030400194000b6407024408038100d100c50001074801c41ca524141c6040d00c0170100d20f50381c1140c002802c03402152258030208111611425002032194050b600100000f0b08240130201e160700c1d0a0b40c40c1c02c00044034100c0400e1100d003031100801e42c0050345003191196241c40b11400e050740355040100700000c10595080c071a5a040000584031203410040d00d60283c40031030380f02e03204040000e042c3c82000c410f10040007030900a603500030b101002180c2e0005884016602e00c8480071400d20303820301401c3d81c1d2221280ca001142c400c400e00241d00303548268842c2d0354000141c004044195201d0040420504981d40a10320360300e140d50644da002c0000352588021554001c407410000d5180220482d000c45041e51540c007103108240d000001c80e907240820b8240260214140100007880c107405104000400da15450054034a0311075150a1024001c0503110420515003250098050f29a0380040c0e80000c00c5450f003c580c40c20080741e003400352251500680158004000c200005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 97654514 1250 97653264 97653277
    0x10224060d020d0f0c08010b0d021305040501150915060507120305060109120f02030f0a02030d030b01090902040305010e1b0f09060402090603040308010612020301030b06091806011e08030c0c06 85
    0x4030f140d02104001288501102c0001c1ca88110103844006003048104c034207685106000e140038a641440c444016a00d140f1545403942d004500050300c1c0d6103030704090380505050400840c1c0c0190401b40440c5088841d0002d03000b080320820100c3c5440e9440200b26980d01c43c180003e442d980e80c04040c110b000c0d2003074100e9038002405242111a0300d864100a1040035407401049400790303002290308046050a0000c03200c0c181300c0c00c0140254200b01d4001c20b4803420b414800704101940c5090b40d59450b805112010043d09a03442d04648442c2c483c075042e4020144030f8900c021a04c18032030207540e11051691480c21160303001e80151030514490091280c00c2e80c002c1c042c1035115800703200c81603598036102c015600c224040d5035030541a514055000e010345601e205500300c0c080c0104014004140c4030201a40c1000c020713502d000c015030b070340c0450105441407610401c40341d01800000055980c001142807490085141c94080c5407030340c840c0455501d1082d02d0410041e90450490b12800c0e1500f64082c241 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 97655764 1250 97654514 97654519
    0x40308090c04020a0207050406090b0d1214070c030303200a050904090203100203040c0e0c04051003022205010905010203030114011b0602071b0b0901080105090910150302010224060d02 81
    0x41d10450000e801d903081901c1d14801644210313420080e51500d405400000d20000b841040410365020204040450340c81014140c0861150301d01941c80c42880480c0e50f407001c03080303040e13224070007850100c0c0000e042e4402900042c0c188845aa4031004aa40d180200d500c010400c9241c41c200344019106a000382c0201a4010750f03c80601d40507031420306c14005804810503006035207241501d88400100c5298000000c0c11040108010440f0200c00c1102c0a942c421658000712910080f802c17030180c8034250b011319507000c82070001071303c03150301c141258103550003600d4900b0119140d000481e644e0000340f04010810040901090080d40105810408504d081040b0810841d264403154143c2c0e000c2c80040700c66a02003601600c1040800d020b140c064055849c00038540307010031000800084044c00f949120b500181c004c10b10032030040059102c0342c4e242d0f010a0145503d10f41c3c4046003031300180b005a016001c1d00981e815034984840020008032221100040c103903d0b9402070104c1920700c1c1d002280c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 97657014 1250 97655764 97655773
    0x5071a09101e1b080f030f070c0507030b1021060b01020d05030a0507020c091501080105040216150b030703060203011406160318030c0b0309010c0e0f01080415180302070f0e04030809 80
    0x2c0072451100003010304240000d00d607039480c00d000507d00c440080040c07400b02008588100322000a0001c02c1d07460403240c12000054094507041c81484405410350b2000f145400190110004809400c0114038018050b21f4204603020925005985500f60204a50700291782000081c81e0821070f54081c0745c0050240c41168000e801101c00309000c1c0c0402c0d500c40c41d28400e480f426601c19079000704043d02501d010345055040078104540b00118050300c410042020800068042210b5200e50200100010040880e10b02c1a9641881c1000f035100380910b05204400c02c8801415040520844003441204415480110000d0314125281606038842200b02d0120510010100304c460390310101400e8041d0080d41d03241071540340107085481c10705d010030074068000524111580d80c00380030720070300b0400c3c2400001556603190100d071400340104108000d42c0740003011400c1804203203800014501c65000c80e44030365110301c0e840d140104181300b041d0284800c0750020700024415803a054100c0d05817421903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 97658264 1250 97657014 97657067
    0xc010e0f180406060b0a1d0312030121051f0f0209030d120b04090303050603061e01060e04060902040e06011d0306060d0519151d0d030905071a09101e 66
    0x10b080a522103000d5900040240310b04105941f000111003085000c120014100034903e051401009d0005101c2d10355085012105500080e08034450110599404015036580094090882d20000846810340b66158a0103002c6098042503100b1140007910050040c00c4146660304201d80c41e50f1014401044161209840071083c0c4603401070103a01480b03900c0101c2c1d6450204107251416000802010603d00100d044a50003da5540e001d81950b401d89000f42c510038000002c2005080c00d507016040c442c0c40010001864080c82d6515402290261384a80c2004142e41e160b03407001d5690600c0035419046000490390900d00300c0d42250103035124009680e40b03250712074610700c84400c1a00040d500c203c1004090385c8000200d21a204d07030030720300000802001c03508000559540c041c1b80d60307400506659070180800e10400304180720040051895503004100802102c80c1d044d003018803000c0c021380c0c0c0100da00e1101400340c0b4245c040708640c0c4421401c42c04088200b00c96018000c84002400000c61092 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 97659514 1250 97658264 97658279
    0x70e0c19050706050f0105040c0305100311030c06030108030a030c0906020d0309030309080d0504022701030f0201090b030a020a03150302060904090c09020f1206030c13050411040903020c010e0f18040606 89
    0x580e817084c80000c8540880d9890901070000783d07040d0f050782e9002c052a040801280c0c00c00700314444203403070b041461520b1104074880881d103000300d0564a550301c06400310000030719840010003800c007410950b8041c44a030b4210003056a90b0a80340c05000e0240c7c01c01d1030049411840780d40400b0307900340a403401245c00301d0079843c0d0344401d0f404941c42800060300c450420042d07003070803520780003601d071480750000300c0b50400116954004410b01008000d8440e00311400305585c0702322a0035025000034801d5650300e04002107524001e500c07404981001c02c0c01d10b0381c01c11010740c7c280c3e07100044a4011f08918503140460040100901700b800040b5200e0200c0f42c0080791000e03591000d030600d810302440343c1e81c0d609016000c0410800c00148514840d50000500e1032058032141741c15140c45c005402d0216464840f4034141c9004010446444d420501c1c00f84075030203140d0300040340c41865200380c880b1000400480c00b440043c003c50191309411070a44c0d2440c0c4460b107028aa4140c2c0300c1d02410000a1440e00c0f0b003034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 97660764 1250 97659514 97659521
    0xd140403060912080f1527070c1703010614210703020d06080f15090f1902130501080d050a09050a0e010f09060e06010f210e070e0c19050706 62
    0x14103481d01002c501c0003c4810340c01210b425006101031550300c1540c905014078406040c45846060f0184000b0008a1411030620580c00c02c0e2030503c0d00d030820705240802c801041e0800300401643d01c0f10b20040d0141038156000112070613a0282d6444408011015122242d43e078428913070b80403040e40c0320000305000e801411606014816950300580d4410800340d02006444203038215400942201c412071814100c0091440d03800c0020342001c0e1030b1f540c3c0c3c00c00c0d02810060f11315074054590040c0100798000955044510170607501c02c455184032500071080c580110380c000d004072070f1a5801461400381c894014006003441091501d000e016040c1ca81d800302e5104c4403a94023040c0164107040040c8845214142d260000d407081600800c1010f103010f4032440d0118001e0300380340c1480541c107044058284147d8260510240b00310030005070603400f90340c400040140c00178080325401804804540c058109105500134240e1052280c10451200448500002c52004ca80180300c420400c1c000090035a01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 97661870 1106 97660764 97660781
    0x106171204090b150a02010b040e0303240d05010f090317040305030103020f06090d140c0a06091503021306031a01030b010503041103010e0102070503040f0501090302030d14040306 79
    0x800f0590200d464105645021307800100104015015080444405010744040080780303209110107840340015600c2c0100100b01e40c2822841013444150b02204240082c45a031446450340e90b41400c48014031440300c2229100c0d21000141500022800400c2c1030154000a4a14241d54010254841400000c0c070030111b4452444031502c0310019a403078850094070401c09034086062552a401010200440702d204507010340d441402c01c0b8441d030044403801d40ba003400ca541800752220a41c900c4043c500c007015801e00120300001c00030f01610000b00310503200010130b1541ca408103070601480c030784030b581072500b0a08140c6950340d1100489030b009401c10003c80c6211070807400a070140810302c074640322560000c200030b006d109021004104a41d0050600000d0300d0741c500064030050780c5403002940c140c0003010360b00c0560b40560018040982d1039900d5030f14154599840300222401070 = true := by decide +kernel

theorem cover : BRFrame.Cov 97482014 97661870 := by
  have h0 := BRFrame.cov_init 97482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 97482014 ≤ n) (h2 : n < 97661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
