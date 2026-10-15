-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4320
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:14:28.985996+00:00
-- url     : https://prove2.me/submissions/5380a202-7b6b-4d33-8ec6-1a9085749d83

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 776798561 ≤ n < 776978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 776799811 1250 776798561 776798591
    0xa09021c030e0103230702010204090614060729150103061d0105060a030f050103060b030705010f05090910030b070f110109230a0b010e061005070b0402012f0718 71
    0x1180015a041542d05d2074030310a0b8071200c54400c40c000351031000b200d00070305046c2802030207034005008907841c651500c10300181001c205502c00741c015101074900b07030418855450301c1207202c10000f003d8000c050890b50300e200100c1c4410110b4840e0104031100790000400b88001000ca48142d004000f802c20900018400040c2403c981d50448204643d155925104170310200d0282070108a003690042c02c00001100700052504040c100c3c0741c0a17811111050780d9a00112140c4030b00c0310303c0c040414403c01107203000b800c15000c501e41c4076800c0c40504450a42e250b40da04180c04c4101c1d40034000441004280300b00341c0d4400e5901030a042c08000a0002991580700d000842c1740700001a240c903a00200303800e00c44601800407104c0150400c401c0c503159070f50f418036248040011580544140b101301444888907029005a4071001d03001441c404c3c06a841c0d0340192148010842200d042c61514034015401d41a480c1380100204450f01c082c00455181c2008080d10b402c00207950b905803410120b00e1355a11701 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 776801061 1250 776799811 776799827
    0xe070e0607020117061513081204050901031407120b070207090e0705060c1905070303020f0102030705040b03101a04080111120412031e05010815010302032a090a09021c03 75
    0x10000313084509441e094001205400200703820028428049000c008001c5400c42e040100c42454041e40c400d0240c180705180c440c461401100e03440f80003080180b0100394825110500e450340c1ca0102c603a669120b0805551104042100b110000078040c03c11520b0707035042c00500d00805030b000050140c02e4440c4255520b40c083c40c024640074a0000c54800d860307400400200c5241c240308103800b160b1001c00e050907522500207000541c09442a100c403140f002d001442180d1040c0d22503503031031f414603041001400580d40040c00420318007804500114003501c400700c5260941c001c0d0b00e41d40d65207500e404801800d54001420f00c2c00c4030402441100365640d5031040711940103030b00a6840d42c000e2101030041c0d00a0110f02030f5269000345d80d84005042100d10b60183d816640c480e0b08545464103040e001c0c0501c01024000250160440807004c40d5031491a00d040080800c14200882c00c1e00580c0041400410112a69480a601d81801606604102d1100540c8200e16203110410a103a42c80c0070300141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 776802311 1250 776801061 776801087
    0x609070302070501140c1306080603100c0c02030d030b0406050108040b0a02090a0b1306200a080a1b05012003070e1903060507030f0506010f0e0d0201180e070e06070201 74
    0x15400090040800c0f02c00e43c409580c55807200416005820246070030550798100184114188200c1640424910b0040da05a407140900600500554511009041c0907048148100d400d209030210740d0380c0180e4041c0711802c80c516450741c00003501001481000b0640f442503200c241480011424800481c1c2d4003030b00c03158045034020016a640110300085248070683c0e61120300101001304596495032100c0c1005030840300070743d4800c960306c00080181030b02c03410f00d00a4080941e10102200300040c50761400703094080e20300d052010034000c0682d0101066000040100c503581d56880c412168008000645c2d0f03c400307544c1e580c40c0d086240c07440380507146400749058540300b10043c41c5040203802c03110764040065030b07114405202c2070070030a902070043d00804c1001901e080c100740000740d45500c107001c0d50139528603d80d00d0400c2801c2c45014131020720f0b403107901139040290203980389d06084161004c24000344141e86583c581483d183c90000d00c52001c007024a840b4200402c400300140c0c2e4020313030210480f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 776803561 1250 776802311 776802317
    0xd1b0c03081b0408120c15010b09040c03061703040e010902041d0a061d06121603172a071e17011d070f05060c2a0310051806060907 58
    0xc0c01092421101d601850f840015903100b09650985c1d40a01d0001402e210784000003100d0750350517170149020446009005002c00c8603000d0110b448a8507154110304204426030900040954907005100340f2010581400c100d503610004d01041a041e102c81424010f01000c1030440c145400d141c00c0d068420001c850302802c18200102042e10700039690302c0140200007000c0285074a0b4002040441e01250444099108080021881010840105500140c4d01d603424108070000c0c11a41e4100111944407000d02602d4418061100310700320703a04403010104810600013020f00e4041340158980702e199088020042d000401c0250030328103a2080300290b0300e1030562010f0100324600114010408080c8040502d15103003405c9644070004103019095801110003081d015441328103010091007281250034081c0c3c8016107a40e40080d800a003c00303007140b4520a03041e000032040c0001c1c80c010f4404e01c031001007a5240d0920041c0700c4039051a03caa07007040340141030103103050400600340b108011700c60424 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 776804811 1250 776803561 776803591
    0x70801050c0910030b1c0515040302060604020c010e0d02060103150908040e0603100f0b04060b031009050705160b010e09010c0c03180506070b0609060d050607050a090b0d1b0c0308 79
    0x2070f64040c2e0040030300d220025104465002400c076002079103c3c40c0304000d80b01c600403a0001c110408520154600c1981c054000304140d440b4201072200035840845c0d121115541c5002001c2c0f841414030a024a1000b99070050503103504600b4664140224a50454070323030742c07600d8030081c00140020306480407101e5603c0c050342141c0d10000441e0034646244042d140d0380745880384484800b1020350291001c2c6906407030030403600f503c40c50111914030003590a040362440710f8104014040040c0c111980c0020140307401c0342800280c01c040d031140840c01030b00716180a2181c1c018030006d501d401c01c00f070380302046034000d12624800040140240c210300d07078003804212101e844a40303c10481c4ea114001002c01421a41d51070741c0c141010b01510005884941c864820000400d05a1801400c4804080e80210191550703490b44c481c240d41d40e6001c0308040c0144960080001501c8249201620106003c1c29010402c2040b20521a04c0701c425444ca03d41401540103121011030340c8130f85100c0c1c0c0150f0510748205 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 776806061 1250 776804811 776804839
    0x30b0403080c12190b030d0509060a1e031b05270301020f0a02010905060601030608030a03050939030303090d030f0b0907120b030309131802090c0c070801050c09 71
    0x119203d40d803040010200600c00f03110130154400c845400074510000200300f42c0075004105502d41c0492110031001038070500c03048605140600c010598520241480f14a000005d50107500388800d00c41e0b80d1000c01c0e42c516201c000d41c00c0c0042d065104140790b00d003552811110791854940d14802500c100f0028120b000c201419482c00d40c12968507120080d88551102c0c0c600000031f0280030340c1c0004940502070b03c0046540b55000c1d02645013034a120798003031810400c13540011802400c004182840c6032149001161710281507000304002c3d1210340000d44609000c80c1c1020310150300c142e500d14040c1c0d1003003041150640c800700310b40e12180f046103030119000c0d40c03104007900a018200785840d48040700000f0320002c1e5420110000855012800c140300101400040503240c0c0155540f02ea0401e1520054008030b0601d80e12441103041c903980c500d44c1c0705615800ac200c0d080002c9030703c0c015213000000c010a03810400c0000600500000c1c00134001807404652242c174501400044502980000700850 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 776807311 1250 776806061 776806081
    0x15020309060315010c171b0d0215130605150f0f061602011202040f050109080712020609040f0f020a02161230021c0f02060c03090a020612040204060e01030b040308 72
    0x40b01c0700d908800e840600c0d46c02038840e003016600ca902c00d10351080c2ca001d513a807540c00300410f100a030203206c0d80142c030350392180540007140d4540041114440c201e0308403a01c000520703144a01805102d402d0750b0b0810b40803070a000e100c1c8250500350902c2c42041c20101d21400b0755210000c03603a0a218840550007040110310040e0741c4024135183d180d080500201707000c110700d204102030f20304480c1c1c2680e4061282d5518003256803249a940148030040011348e04140242c1441c00081541400c00703440010100101c480321002c58501842642e011900050500da126a0411916400c511969000e00c583c43c6044074402905611520060400030200028102c80404003010811840046403d65403a100002c1c0251036201103109501e02c12104009010380740d00c00c203090543c105254000f40b10503101e05c00903220f60b400080c000821403084e070600d000140c55003000b4041d14541d0301b141c0007035402c4c03c1c070400c0161141c58100c4186000302e0030040001c6000315015940094060900e10006d4407410880 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 776808561 1250 776807311 776807327
    0x6150c07030b0c07111014030c1909142b03020102090303070b040b0a0207121d180f0a09080304080c03160b0a0c030e0a020613050d0c1502030906031501 67
    0x2e441c03903a80a007084072190b403050081c04031501c24040c29041103440810841c0c000410030140c4002404440030943e450704600c011078025004007440c50516131840d600080040303040c20400c0014041030030402c0040060000c400c10704c00c0c00c507440c98520b0841e1010300c03a035003424464240689018403820b01814000c1d4102e030140b19010b8156592501241440452500c1c01e8038111001c280803400075241c508a03209450215500881c080f0100c40300440444000c542103011006400040e0620035203907882440d080c2c0c3d17001c02e400700103895144c42104440907290050a8000041c00c3c01d4195001030403150032030354003a500c0041f003a150300a6014491440c0165194051080201c3c2000e200f808403000e00c10f4451800610203111001001c1d00c110300f075a2801d58041010382c485000400185003c00282509180c0c03648103c5015a6400000f40c1d40700306a5400e4840042c0c0100034094402550110559080d081c001546480403860106130b107813000408007501c001c108031484006a00c22408 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 776809811 1250 776808561 776808563
    0xc09050a0506091512130b070201090308060d02010923040501050303181c0804170d0201060608060d02010203190801080d050702210f0625080903072904050a110103020306150c0703 79
    0x5503101038a02995000d2246c41701a800b0342c0c2c511107000004020303501c1401402038461781980d501c4800e89407001842080700d500343e022811f00c013602001040d210b60750000244a0f121211032248514102d40a01048490607041a402900304008401c0c05900280c3d68030800141580c07021900d1103072150440075003a1082004020050004002581340105841141c1e10310b40d40c1e040c0c0344901c0100d4005d900702c1c0c455204180110700c2c0f080004880780b83c2402da0584076401030061324646100c054417070056032040300006012030030450061204d00c50401548503032100604141d03103030100303903000601c40e84000350740303a02c42c00c3c100180c6030341090090011041d0591140308030341e0a401d1035410081a49001503141d03845001d0004214240b61080e0400740c00303038000300e010754506001d60312001a01d41031404034002c131520040e01103000106445840e80304070b0085003d44140101031a180e500712004007034540c10540140f041c004180c1d243c0901c04003c106200689030742e044a4900c0904180d140d40c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 776811061 1250 776809811 776809837
    0x509030a140c040c0509130b040908030405061006020604080f07170c0120040b040e0405011515030c09080303371e05040b2208030a0c09050a05060915 66
    0x908081c1007400a428520403500311802d000e02200007100311414001d2151250340326400e60504190410198018480c507140a80b000c220784242e600c9017440b50344103481c102e401c0d030b11580402403010200d240c542c001d000c443c8068403590030140c44205190052420300000050001001c00800900300606c4c0251b80481c1c2000c0d4072105038a040718000d003109915002c2803250f4500910100500c68200c4060710182d06080d0b013040e0038175010a66000c80108110f8940d91395105002c00300e04000400c100a040070f01c5d68450500000000500395a03201301800e05001000c0824425444d011041d02d500048a94080c2c0c004c031450321480301c10480c41000c060346440c0c2c4501440304003410360404c1c034004501803e8540c50354440011201180c20071200503062445000200f8190100d400300f80b02c18610240300305181e01096140d60540b9030090751022040da944070385001c03406800c040a80001d00044544070b0066240401064903481034242c480e200f003c032030b46100d0138424000c06460381c42652403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 776812311 1250 776811061 776811083
    0x12020307330e0a03050f120a02120306060705011503060c0206240328050c0a12020112112a010921050c0f03070201080108060114090c0c10060501031503120509030a 72
    0x42170081d1928034010000b11580581640c40409000c0041100c0070800340742d0040c4203404140744540701030380000d00b0203580000e08004603804234100340110043e0f00011202038500c3c91035444e02c441160300b60040c040541d040b60b020840740140d80100d1440100320460064508101c03100040d00303080484003581030a000f108420007000018402151000c0e12410459404140c8501041501c80711841407130010101240b40100551058202941021003060b01203801844c2e2142d03500160400c00102ea03c54504113845d6405603040c099400c0351300c0c141c40003000000004e803500072500b414600d40d210000303a0701702c075941042c0c0700d00c08507881ca08100c415150b240008504140e00c035441082c3c16800120b141c2c002049140002c50418104c8602109032a00d100302a030070300200d00c0700148800402c82d014400a00f600a090003202c0c03181200074000280d01c0d0074000058201e5048030b0300c12500c9107205000784001403441d02000c8006a10f070a15035141ca0081c00064a404803c55004004900304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 776813561 1250 776812311 776812313
    0x302030f10122901060305180303250c05010c0c03080606070203100c02030c010e030406170c07020d32070602030a050d090c15030606020607031116170412020307330e0a03 75
    0x547c4000d0103000802010340c1720310081240780d40c0da030006540035088242d0081401c045019248802c1400c1445801c002c032031000b4585850742151000e40b00000410301d5102c00100f01903014944070340c0000121203160419149401003a6a1042821072100340d80d0b03a6082520024000c00071b54075640e20f2074000f4448141c6c4001800d072250024440d00002c200d00c0b1050314070300c080c0c8050051203006280480780c00c20020b9000c00484400d0400299180a043c0495003070310903612552030a0280c1c141d82100001440c140c0b03081c540080c83c0e11803001c5400600c0745544035584481151b031120003452001c600d1441a04042c01c079201c4944c007884800e126210312503560340e01070700078000312810b0340c0a80388039039a111030036015901006c00c8810f81d28010000140d2904904184040241c000c100d010341c03294800c01c0881031603110360003280c01c00814018074811032808004c0710019045418505481440040b4150903100d688100d03042552411055030050b603115868400300030400911f0440711940c0c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 776814811 1250 776813561 776813567
    0x40c0503071d0a061d13060509030c0705060a0e12030d180c05030d0c02010c030306050a0603091104090f020907030207020411030105033a03060b07030302030f1012290106 75
    0x2074009000440103400040c038000c2c081c0b044900301e8201c00135205000e02d000c170008407032101c0200300341c01140000300340c0000315010348100343c800c10581000707541c3c5690000c0d81d03a103402c40c50740c4280e208100030000503000c59402400601d1020302901c60001c546868201103055010300700ca042226481c00202c00d4500c00040181002e4601840c960389086448a06058403984603442c0c8002242d00780d12ba8500551158443e103c7c00c43c064500014100d4450000800c0400c155004900003034131000c082c4c0502c0050340031055410f400301e4003000a40803070f0743c4030419500c001c01c0180c070074982580011600c82c0203404032480c0f05e50091042101d541603203581703016900203000e014040c2c454001070020703440756480700402180000c001220611590b444400300304508550141c100754a03041c00184140a04010f41000da1007500e0160310f901e010300c4800b400c0c0c5001000e01040f00401d00082082031028200500c155411440f01207040141c0000441210800401d482c40050850000102254 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 776816061 1250 776814811 776814839
    0xd0c15030902210d2006070f020f01051909020102150f15030606030c091b030109020307110304151b1a07030e0a08090d02011b05010b030115120308040c050307 70
    0x100c215039803095030310108501d801c4143c50b150518440d074001c095400310136000b4007211075081c589103440d070070f140d18100940342041401d0301d001c0040390228114282142d01071143c0c2c0e45040f0681c00800951030148441e8008400c1361114590780d51352130181109591080c880d60306200000108000ca50401500c03000802070200d40c0e0f60304034245000f0840c000d1170301090031030180e60010000c00c0c0c5014620104030042c0c0d0701a000484100c215a01c0001c0013040c0c4000d98020943e4103001030712458009805070003800040ca441c1010742040205120005107181580142e0545281540e0310600c0348840368201c036080314014142c02c0c96152a0006906451086481000196005e21448011048440c1e40341c00301d650080c43c10005004208003130504840d0060401e005141c1000003100000303082c445150354100655060351240008680c6040034081d0904441018184040c83c070314001d802d880290400c040201040403900114007030009080c9004044c08000341600d104594500381e44c11144 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 776817311 1250 776816061 776816063
    0x60a18060c1505091005060a0f0e090d020a0507120804051c020f03031e0702030c040207050d0f0c080f0a030f020f0706060b031317071b0501080a060f050d0c150309 72
    0x351807280120b4012581c0929802807212800500c0848140d8003000098480180728075001104444002170300d80c40d04070b0150080105800351000c03400d004005500307115106450f07806550007a034000001450014500f421100c2d040143d000802d001d00c1c4c002c1d0148241d40c041a4000c0d414a95624000a48bc18511b0030034801c81e00c804074143e6140a054403405007501b800024405220110603c420810060103c24801815030707103114036001c005412600f01c0c66041d01c080d440405c003400300e980c006004251103c054280740c131244c0c041da07031880303024810740501181c030010106845803198080d412040801c0000c5106640701e0000f2840040c0c1908180380c2500c0181c105040040e28410343d03421280100c200b14a041301c0810241c9a5400c200329030203000d40155000c001420209500500e000a0211010201c0c3c810500d03210005100381c0340a031041c200b2a00c2c00508201d94001c02c04c3c10411101c0075591000091881c0c140000207a0b650351004200c840c2c3c0032190030312594958041c1c03040e5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 776818561 1250 776817311 776817323
    0x80408092716081302180f16020615010c061803021b0103020408150c1b01050105010908010506130c0c0b0a06080712030f0e0a0306230a020c0c060a18060c 68
    0x95520340d840b50700c6680142d00e660000c9218000840c02da291030403502c807449800a0003459162141018240400908440f1141c1d00c5403020280042c6801c8200328042943c030520050150381060201520202444814a414414654006400c002c066001201c4003424828041049842414041e4544100f4517003d444050040107000241d03029109403820740d03003640c004084480c40c4003c1602102c0c80a44800031a0100740700044174425181c0702d134020a0806800070605502d0000003501484c2d1075045070000764104010081c0c152100050407244c44c0c1c2c8904003081d01d504200c0e0584886600280c003505591400080180280d125008803080361200780855100c10340e6040c40642e40f500300d0b0b01c001c0014a40b905045c3c81c541c480d80c00c0442500c0c0040035440c903d5501e42d101c104039403407814960b00d01d03101d003400d0311064010f40340d806512581142041d841e02220160154031056540c1240e88a424086208404544182c4906807012807009407441a19100c10000e406141001030072248 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 776819811 1250 776818561 776818639
    0x7020d02060105222304080a02061b07110a1205010b0a080313090b0604091d0601060302210a0e060f2d060f1807090303140a08010608040809 62
    0x50b50820300c1e0316004a1010340e98000341c1c2954422540007501440540ca5581c201744020945038800d04000503000300c0c810560281d070b80301005000f908104000300000244042c0c1455004070441800c200c44400f03900441d252103400e00742001810403042d640000c001c40c544000300004100b0150301410310340b0f4040300c5100c8020360303c125441c1d0380e00c1501c10312001918003c5081014031056084940d4950004100da030502d500c6000a400300c551020b20120140505a880c1d03820080c24011130340501007520341913251903401c0449120107100c00351210100c58a030400244a40202d900c020035204414050710394070304080e6550340c0b410354255040000010f20000d604c606141d503406a8003400204001040195205020000040065900709404c100501c0940c1d40d0000b184201c17070b200d0380c02911004101800d50070300818040c5048a01418040d04110740701d0b51a4000c02c1990441c1c14510704010740d680d8928210700c90b40a98440c55030400000d481281c0c861040e901d40100d00460301c0b880c485 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 776821061 1250 776819811 776819819
    0x603060f0806042f030a03201225060513020a0902030910050c1210060201061703071128090e01050709061b0b0c030726240907020d020601 61
    0xd01d0380c0c810f40c0c00502524810540011241504000c4c18003116890480c1c4400d440000c0428142203104804800060403404504010003016108840c207840030001013185c1812801405920702c40c01d20b000080c5001c42d108180303001c0c400110f6100c01d60340120180210f081028000e00101c0c0054001c0b4824281050702040815081c42568490b400003c01441340085201e06200184400340002c1d4200350100b00c05110b40410b451240d0180c2c08031444404c1c054680301c8024211005c2e074004240f18840c903074070103031000c03800429940295040055800411380550024080b0114040d68500c01809140c0d0890001800c2400d607080314403580b030070f028056004050900321001141c205001c02c29900c414807a1a1060903144200c5800e1401c2c1044089191100b500321182140d20004200c000803c004d50b16901c01c5105017600d60320707a0307040411041d000e50f05524401c010030b4803455001100b00c006880c812292400f0304100041d1051200707080c0184001d40740c0b066155500094400c0a000107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 776822311 1250 776821061 776821063
    0xe1e010b12030f040b070807080a0804110a0305030409050606281b02130924052203090b0d02040b040b12060a080a0303020c03120112050607030c120e01090602040603060f08 76
    0x650f8a4840000c05890141400040079940d0001d038030903030b64050140001000511000002c000145c1261508415480d15141c40c1201d148183c10a42c09030f080d240381040012400070569080e205004004600c0341e84c2c18011610354001c1d1a2004000002170b0f0034542c1c5c103690400c0307451040c0750342d5858850b9107103400c1c041e150010700c000d00207401003681018501039a401c0d61203c020f080c0710390014814480c1c02070740c213a01c3c1c801424488210994450510182600803041101c403030020b40450b0190300c3c801c0d00c0140c803403441c500c14aa05c0b00800907030742591107100c0e03044070702400e81801c0e615200e40d110001400583c1269403154040c0c144040803584c5840c20100e00c00480d400c0000410091019035411406900440f5241c0090302c0306200f020199a16803a485018024041c5c03c025422050308100307182c142c028000d41e09061400c2200348c40194080d040c034484800e004008030341201c8200340300d8010619040040c060300d2000c030340842d4203035158000c1340841e44141c6481041e562592360031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 776823561 1250 776822311 776822317
    0xe1608190309090902010926061e0f07050f210a1e0c030e1c0f03090209060609030a0507141509030a030c050709090501020a200a060e1e010b1203 64
    0xa0702103102d1040c00c01014071241c11580d059481071508003035840d5209404d16203035151081c04005a07110b582c454407041c0c0200030761513104118542d400c10200100c02e100088000c082d04e20b94000266400088030301e030180044520510190451640c0d610950f0001660107000b01400103902c6252008036075010392600400c460a50081c00010408040c1d50b81c2d68001c0510303078004401c0c1501c80b140780c4074000007400301c0c02d0b404402200b040518400300c80014058030100c031104003454030300010600940c403480d4000b85e100c141a100180c0d2a0f1000b40001d00c1c10f4681a0005e200d8403a844004c1501201c6070380344141d250090710f1b03c0721690001c0c40e441d002c501815040a806501500003040443e10802811103100c0c003c2064031512a10b6902d22400d4a9608000391603a030b400080918600340d00c01a450700611400c1e141c070b210201e0307d20745517480f40c80941c40a040662200745003045658140024445a440b40b030740b1185050040e030081d8017a0a841d00d543d0310603034112042c4001158040300b2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 776824811 1250 776823561 776823563
    0x219030914010f080f0a110c06010e1003050615010c050a1209151b1103030427020403050c040e030904060e01050a0801020a0507060207080d06030807020f04060b07150e160819 77
    0x4d1201e0300e076a00b0494042d0500c000308201d0320503441e445002000e0b04103000424007a0618005814a0341c1407241c60642403030050001041c00f0400c0b403040000c0740010403d5600117103040b650803406980ba000486445000c0040031f0040e0103034103c20010400c2d10903032066643e54075101c0858903562071034000d048071003244900d00030503001d0116080005051300400121707440384443e465040300c0c50000c2440d54010f40c02415807450032501483c0150cd01c2c6240c2408000035000651601d07045945007511200c00201d06800f230794860359000c90540e0140243d42c1c241202403c01c0012903039402000c990b6203404c5c4580c178052148031002280c69201802151a600c060340c03660b6150898540d04c8100940c412142038810480c24440c4002c0b240c03032070040d107009500480c01d40da00c51034140104080c60490450f502e219910300b02003000034140b6841510a00340d00704001001c605105d0768680042d04d64110402210702400070905040302510620b034080e5060501101e1980c1003600351244100c0c40300750 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 776826061 1250 776824811 776824817
    0x3060a03020f1206010e0a0b0d030f05090d120302090906100206040807081e030103050d08060a06180506030717070215010306050717091e06040b040209070219030914010f 75
    0x14060000d0700701150302d03140b4400d0207011508184042c40082c0d081800a8002028610a800a20512040e14002c5004032402224664036941c1e040e50040c005080c0e02c3c01810178404003241a420566a90110200c2c00d9045004107000c8502c0b904001c000303500680c46144103410030340c046201810541000e21210500d40c000704456104d41e100c80c240394001407000c44d43c2c00c0041101c40b401c01000e60303480400820781f4041075100e50540c6415810094252030410070400014104084c2d50380b0003410004541450419482003041100c445080c50459000300d80c12140001c2809445030740000820700013035989d14900216110304e40d04a032108118516001c004401d4001400880c2d65680641d8102851741000f5074040000d078102c41e1110b108940b151410340041c4000d41d100600c03d2208940000208040e0115103172a0361543c5040c0b402800182c041c1c66248005100580208409240303500b051910140c1138000e07180c0100705c011980241503000100081868155009509012914905403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 776827311 1250 776826061 776826079
    0x51003061a07050313090614010215070e041d030714060c030a0f06080105100303140c03040b1602060301230d0201051801140703031b050309070626090a06050c0306 72
    0x640c10240981000100343d641340020046003c011800c02c240700014110140089541071800140840c460340030780c2802d0654000003003a050811494007a1540442c4604100300f048408c00d000c03800900c028440c1c443c0241c80358250501c82c04000016082062040705151160800095075070f0301c03078400b40c034410244201480030540200d82ca4120480b01508100b001982c29035441c030003801c1d10000e4811100000740a49c061051640c80003200c805d4444481c0d00d18a4440c070541001d5483c41203209015420324089840180c1541d01c2e44402e10594008142c1c079105c0d40c4030a0260300061460b00b030081180164019000d603030405441030603500340c050b1203403030410921441e100d4241211503403841c1041240d900d203400701c03880c56018100c841e00940d00040c0110000005000c003680e100840f80c1840b905100308500500c0c0050120203484191509044c03000c40f5404107000b19207250741025052044800300525030b5000034000300d079140283c3d0144460f440d0300202d8249403000381d80b4190000c600c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 776828561 1250 776827311 776827349
    0x903050a1e0c0b0306100504080a0f02030a05120a0306060e0114070213060603090203070504090b1b04261902060417030f0c0a03020708030f180105090a0308030105100306 75
    0xc1042a1200c41a030081c0194a0000e648030780103401990001041d803c000701c24882c5030304081c0c01c84414241941005840d260034000303a20390382c607924030000781864801180c0404644050006010507540501100d048000d01c240e00041600043c111398000b92410600290300ca20408114211200607152111001140010103c00c1d5002200681e0809907610000d24440d407580304030001080e0b250340001c0d1048051040608110240d40b25511860410340d141c00402c1f1207281160300f01152400d0780480003a0790b0340043c098040c0307a00030306900400300d46a00140e043c40d0002c1420030f803003105803112112000140402c49007942d5020307401981c24803040c0056403031980c14200500880301280c3c100141c070342d401c40311540310494441c0b551300101d0f0500201070701040aa401307414034602441c03d0064810000d1101c1c09407450302c0d80c2000d5152a4901180d0041088a85d02c540241c51f0361a4151a410000001c0e4420701c102c2e4003824107211907d0403941701c0c3c41303103205a42032115110014103d07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 776829811 1250 776828561 776828573
    0x213031202060408300f0615070c26150a06080303070c1713090e0c0108040b040b070e1002250f180212090f010c050c0d0807021c02150105010903050a 66
    0x1400400340341e2081743c0c203005130700744007082018030070001c85966103864a0404203003c0400081c481c86404810140503020000c1c000c141c4040a4841d800307860810103032004240c03010354101c2c091407425806666103580f41e20421501041c41307036241c9001030000304d81c2c03424002d56922048039118005410924800001180220881c100f40c641711903c1e400c141411001800c001c4055000890f055a50650b507111494103221880c401c580c00d00701403c5e540340a4840600c5000018030003018014000b0004420b030380112400c0c1400b10016004002490307210802966421150041110000410741d08c0690050f801140b20140c0c0d11840646414071301d0801344503041c8580d03846d00280b407902444070041401e0b440040c24481c00c030388030050802e65801240c1c01d0844841d40304c41e0f0104403040010310722000c0d00050150394503100c0c0c178102c507a6035a4848128108201c00086401880380d61007020f208680c000340c80402036031902c1104e04503903650303c01510083ca15200040054105075030080108203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 776831061 1250 776829811 776829847
    0x5070512060d1b1206060e010f0b07020621092e150801090f0b0c030103020619030b04020a12060519030b091f0e0105070c0209060d080c010213031202060408 69
    0x221540d0110004081c3c5460380c6842e44890b080100200c0c0160340d043c0038031107540118030040003010101c1085d0750410500c4090400d041c00781562580001a460045490b000210303010820314102207204582d01211400c0000400c4e02c011201348258402d010318200c0c811002d000000c50840c00d40250115892940040c10040c5003071a50154881c0d800a0360303610078001e0f240741d24410410604d120180745002e1021070000381200401c0c2c0130510050005840d6802200c0d428804200ea440f80307445000012000740494841c0950171a00101e6400320b04d640020101c0d0220054400500c0b01640b9401882221201c07000180280d00f00040c040010580030029940c2241000064480303031824a03940550000f00c100760120459030342c88000a203c07a0a00c5600e40041852400c0c49454566800107181d081002d0001da200303007103260a607402c018104088855014110000350340340d80c1c60300780c61144c6249500c42078038082030013825155070a01c0401c00034851a804015542081d41140c070040c0311113 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 776832311 1250 776831061 776831063
    0x32d0e010204030c030506090d0305070c230a03091404090215030612030406050d1802100513051e04061502060f04080708070507051306030b1306110304080d05070512060d 75
    0xd5820400400441e0310309030a5800345020700e00a06950504040b41490722014180303c404041c60a4144600c0e90f41c072a840b002d01a030026581240b0307054a5007602490000711165903058800c0707500503410183c201012004030360060701c0c0d0300313040440d84c0180b00a4880031070f0300951000c0c094020030082031005020b1500724a02910480d07a55545040c62407440c2c2c4180c12010200d5000b240b00c0a10000314000e02e031024106403070a402c03c5015030b01251410b00d0f00c42c030b4030060000204407200034a8900c001c0c203004203c0206101d019480e105c20f44090100114491805181031600c08150b0b0800c000c2d01e000240400c0d801003515a84400c0c200d03028000150080f17464400410400d008144900c01905c0018061009408101c0c0740030104040e810b003801c07504142c03608202040000c205034290059203c441d1198400f012100c501c0e01c0c20050100e60000001142c0100034401030214003400780c41d01900d0302808102c90344501c10306449a004103c400b00b9820508000143c2174280104101161 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 776833561 1250 776832311 776832313
    0x30f0907120609050c100f030e010b13061e0e0a02030402010302161208060f01050a11161517010b18010e09070c0b060904080a05071505011401032d0e 66
    0xd181c4400d4800001d441512055030b4440d00c62000f0000d00105020100c031700c601c1299198000000140003030300f07800070340d900d84040c0f607a40e460003030a842080d0422444c0c400c0c020b01c0f03810024600c6050b48010007250041040d10b074085d08500e44906000701d100003d580076107810390a150749450504001e0740c0010412410182c0902c0b40008100f141074410004500c50b040342d030104a4914001800340a0083c4a01d104200ca00703000c4000741d1b041001c41701c00a001d4079002e540c03200c0303000e4064078100c0c286110034050076884000203a0000499036101c2070138599540c030b1040984010345040c0d00c1000780207124107464100280c010032100020740c0c40c9441c8060500c044030001c40000181c1d100012034100020039082c0301e48808119503503003856030107030f4211011007050519072200303107550041901440038404009500e400b03105503025800441b080408080c884c0703603100d4502c1001c2240d8a8030140c003003420301a800080b5800800415850240c01618006440180c2c500202501c21001280b4203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 776834811 1250 776833561 776833573
    0xa090306060b040e0901050115110f070902070c0b070c09180b0c130803251e051b030a020d0201031808030112050f0625050f180406080d0203030f09 65
    0x1005030056000900205940c0c0743c0700c0c0e10741900c110020300010324044259240c90018004100300050100600c100c40c80c000803420a402d06007441d1204658a460302841460f20000d118060754004009040c420b000018036107540e0100c7c0c801c42e00030020010700301c1020380ca090121042660010180c01c4405c1d9161100e08500d480d02d600060301600c2c40100980e0014103010301449460070003000300f0701d9800842ca03110403081500814000d8039041c4d004920101210001e010181c56403101504040039541c0c201c1480e403912a9840c0400880c2890302ea1078045071104900d070200790002c2554000d8000c00800801e81c0c0110700400140303501c9003298000b111801302056200003c1c5000c0c0c403034248000800391160070300b10b181004a07403e00609034003203c20032205982040780d290140008078511100c44204040a40b50740c0155880f002038100040364181c6c586245181413a6810025501040040d486911300c80c0c032a2918001000036070b004001140c0c4e020105494660300924003429a14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 776836061 1250 776834811 776834813
    0x2107110f070504021e030a06050126010311180901050105010806090105100e061306020a020301050a1104030f030507020915180c04060e030a080c03031008031804020a09030204051303181a0a0903 85
    0x75160007d50349034030b405d50b44034003e01035940c104e04030081e15140c0507900030804460414035880720b00140030081140302050070100054548043e02c81100c0743d030503944021441e00400c1503000748024850180000c0d00c140c003285807030070b104040a06941e000340400174050b044d4141503d02032580c14113a504654104101c00d0318048080007103010302115805400d503c00a40101070944401910303061806151440c64040b01014100303d030203d0350b01c101c10405040040c01e0030b8600d4021090040e402400050030442c158a030b8094100108808480d1503d0f00b00340007060450317618003240c4a903c0c24030100024001a80250072034150480300070704444206205a8031181d007074000080c4000c4552007c010310a000010f81000e0010744480c100440c00c00c01e040403c0c213403000404002d1406603900103000a40704e071140c03c82c0c10184d80c0103441031002d410064540c03e591040c1243c1034000a01c1c1111003800c01c9030141988044a00d2105c03400d98407101032056091552003650900c00707010001074008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 776837311 1250 776836061 776836117
    0x403050c060f06490b2401120209130504060524040b0316030b0115170a181b2318061908030301051819020f2107110f07050402 56
    0x540c0c118000a00d103503200100d16054402d914080e205246c041403010100311100c402c20301840f490302e400d1810314418400c010702c1c0c0c030081c4200c44030150001080e09608030424030070b400c1280a00e00c00c044c01c10069903000c0d5a10241c8200003800303001d0458545881034540341c981c0101d120540c006007514a898440d2402c0d1341c003140154401c13200c0780b18a400400140840715803807500c050b09800c10300103240709800d5002d681c00c4e00800c0d180c1c0480d9210038188082466400c1c01400940c408046020203089001c50042c07280640300d500070305908030341c028503002402d5020051000c0040d02004009442d80400e440d074030f0000f4a80c0e44c21501411660185024040c18a0300418840d4007840d03517541401c090283d23100c851620540603100800c24400d801e5805030100c581180741440c01a203945e81c0c2a1802194881c81190f0f80001c01201d54001c1c00e44003144c03a690050846444280040703120101842c1c440500c0100b035895600060020007d9043c10380050829945502440ba80e01c10202584 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 776838561 1250 776837311 776837419
    0x80d0f02130302030c03300702030a050703020f01031e02030403180e07090504060b0d0c09080f010f0e010501050603072a030e1503100515040306050403050c060f06 72
    0x2108014201e5100704194203007803000b40031815040d070182c1694804040d280c420000200f80307042140810401e075080c101100e80982d41c3c256401010380c0e08030b015a04003d503880500d40401e81c82840e281000c0303c00b940c060b20070b03100c40418100300c1d1110100b1880d02c80c002500f00030400e50610158142c5995411030b81c9911002501d201a44554a814172405c01410b00c0c0c0a90040c0d0700841c03808a050008061110554a2a0601c040085154400d5a00c01c42d00c00c1c10507809201c5610a56601c2d543c04801900454480b01c031004c0100620043d5210517801e03900c0070b00c119034101e041003010588141c40744041d1007001009622042a24a4085802492603445c04041d00041d00c40350110695103030400c504c10915000c9407000303045003890008c0c0b02c51128a4401c0f14419010316220540750008181603400840d0484001c0203a07141508000c2c2c1a94000428107880c0e015040024003030540d800c0446025010261628004603444e6142100031010b0560900100310005072036907070841c2000d18 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 776839811 1250 776838561 776838577
    0x714060d050f0708310c05150a08060402070c060513030c0b120f01080d110f060a09170a0f121d0c0103140c030601081f080d170f0103080d0f02 63
    0x5010510f1504032001020104040c03c510b1004090540c071101581c0340780c00b029205c070f200c0f1050003151015450003940c1d504459101d0b036004001055034250001c0040f024054600440d155480c4590b55942004201e202c5c215008016241d0f81c0e000307000c1680b04102402c080621140c000b80b070f540c0c40307842d42860300d096580021f034075280014407180d2004024900030342025a852161b5465410503c06540701d003000400300c400c10076680058581803504205000d00c0400c80d03c141c0340181043c005501c080d00301d1210540c0e61081d0583c02000c441c800c101201c0c04851165200e03028202214403c480511000880d80802911004002c040d01c80d0f00036031a1800302654014070502c0d549070000f4042d10340002d030810a40042508212070300d00c81404413a40002e0904c0d10740100d59843d40078003103082d882e4140300d106102c0c0c40c0d400300e0f01c1e00d07000607500c202c0303091a1602140c08440b0017503940c01e24021100a2809d941d0304004200158480700900000d00543c107011031150031000400e0120f03000098 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 776841061 1250 776839811 776839831
    0x607031b24060e13140109230717030f0304030c0204021c060b04030c0e04020102030c0f0a0b180c0409050f1204140a031e17070b0f09030a020714060d05 67
    0x8100601c400c4284600d100818181410002900e040c101102c3d44159a6a01920051041c18600d5468000390300002a269016140300400d1103588582080345a140c8072852241c4a91103000c00c9440031075082d1003a480ca00701c01903190090b000000d009540016004505100d8031280f1034006075035070300241900c49003482c2a8000c92200b264603a0030b6401560144003428010001800400c0191490303c00740c032035680700c00360030381c0383c520040f4603600c5443d034080030500920300368603030f00400840c40d014540d000e032800b0707499911043c88180303c000c000406441c0952240c2000340e194180340d085041c000307000e00c041e24480c0c050035030380e1410003032441c0740f4421a581c0000c0500c0645c0504070003054541e41030301c40011903415030340d4800c00180c95094882040c4114000f5008201e0102c07090800e400e0a18003440d11079120b4034201c51144010340780d6020b80500d00002031540c0320000f05031051003c195008142040c64400c104000f02c2d503d0302c901c1e0300200d041110544039026030203014060300d2080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 776842311 1250 776841061 776841113
    0xc02060c0d0f0e010207030b04110a150f0306050906130e01050c090a080109111318061d12043305120709030f060e0109050d120b0a03020607031b 64
    0x1860060062070724103202c0e002d03c40710100810041c1da0004600b401d0ba944088480003a40316410060309a01c604c2200301d5101d00c45d41800f041100f844010340403c078505032543c800b5840072036416000d0760352a006a64000c00301f400020a585062102800c101500d01400198080030504450940e24200d03030356106100300149688460a24506a00c000c00820008200d6429240d40d030520b0710114500342c5105040501076101103010603402400980074182c4003000f544994901034010708100354a101030580c2c00c22a0451000011520142c1400f81104c1030b0316060801031078621640880d03a24400c2c04a2502803040050340402a0351503140058032016104d40b040b019030164144002c003810104001184100002510152200312199028031701055425080e0001401080842c1c0087c000340720b0116801c0390107401c0031a513081020311030028040c440100c0240b04e61402203220007900900100030a4001c00d02c00c0d0310b20010f4044810155036007032859141c09002d5031516007044840c1c0d44070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 776843561 1250 776842311 776842333
    0x20105060a0e040c270603060914010203040f080c0c0901030c030204060b040605030106050f19030905060a0c1e03060b0c0f150705270a0305010204051201021213030c02060c 76
    0x303005944020600d1900300c0d0074914042e9039003e1505114030401105e6000c1c0c440c101110340d85520240b22803061481c0402400d83d0360308080d806044540d0b02a100340f488001b40c5c1d480d0070390600840f482181c00c502042645481617136001c00b550f00c0310704210845d0280d500d24803002d59400150307a008500444000f100305066004020480c1c215a1098a080c0d00070001003001329040415a411140242006031310303568625007900441c8110b4615020b900c41c6c41018050107501684041c078214042d1045070115640c040f1300d0421a138850550f9004504085400703850a2030000303005201800784c3c540407400f00d275504d4004030540c202c100744002e80c0c0c201c00014004403c04002c64005024082c8080700e16040900d8040c0c02c0d44034200c1d515041c001208405588100d040080305483c0001908544e121952400c00e14000d42190041d01d00c556a01c3c5034007001040140260b80380420220207502450700c840046400f650901d203421010300c031070b405168015945d1a00904010000c00015180040c03107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 776844811 1250 776843561 776843569
    0x1c0204080f0f19020103060e180d030c02070b03060402070c030f15090209010306050711071d060d1112010e0a0606080d020601240509040207080702131e0b01031b02010506 75
    0x110580320507403203441e200405860000b03d01c0041400c882c1686160000341c00120054036103500308200343e6043d10248a090701066096100d41c000080a030303000e0039520704044055400300301d580e000591009100340040b02d40c0d54011500114018001407401d0400c2d540c4400903179140c1e01c1a5503483c6008000414000d10602d5035000134460701d010811241c0684c00074035400418040030703040030f90b1039001400e21805200704805403014041140c00990b942c1400c46054244903180b010459400c001150341420100355070041c1d80e9000c001c2a24041c440000d01980c05d40c40d2a111425640710304400d40008401d0080d07000c03960140c40b000c114682400e07000c80c50710001c2e01305032003190b001d100100051018072400c0705600c3d009030a82c40501c1407920f0700300e81030b0107480302107a405880003031514100824130b401403110702e1007651100055119040075208075905940140311030100910784504405048d405011400b00c1410000b5039582c3d1002c044140c000750802950141c1e41d80c00604c242850 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 776846061 1250 776844811 776844823
    0x16410d230a09260d18182f2a06160315080303041b0b0d02180d03020c06031527070c050d18030b160806150405150405060d05070305180d12021c020408 66
    0x7107801e00c040050807c00401c3c3c0a03481500c088885454410038007403003178407140d601e1201c0d0940c80300c01c031141414a40081c07a9008095040440468a41780c040000c81c000064588102e5854002a60940d51503440d1000710950540509103600709000d008120005414050241810a000c0041e100c80d501e41c02c26074181d60488940f841025090354840c0000d60009643c440360740169051612501d032906603100c080068003d442d4019540007010804550f15010041c05101621640c2c22070713107540c60141c60204403800e003e82240c000f40e0840140d68080e002551501c0f9541c10294803441d901e40301c010302c084090f81c0c1d60018071a00607514144503071004113070340c0041c1e08949010040c110000035400600c200d11600b03011340b00100d8030501d0b91a940e01a07800030320005c0c00130781d501c139440c1c20000c004010884042c00030a2600000c2058204003180350204140d45000030303e4444202101980c11403100e45e0801016902000001c208020354060780c40000102440582c545003840c61181c2800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 776847311 1250 776846061 776846111
    0xb09041d03040f2123030c06040b0105010c0b011e05090403030c0f020c0a1e0905090604140307020105030c16410d230a09260d1818 58
    0xa01c808072000c1131a41441441c510700c0d500c1a0460600c3c0806034090103075103000c82038894640008601170118100210741c0610491081c2c5292050741c3c0c85d80015030381686040c01c05040c1d044004014018805001031046001403881001d0710981d64a000040c50350101315011000241c4a83c0d58003003890308403170f1020ba421041e0020344840130b40640450540e40f9a88240c1c8030303400c00c02c111030b80d840e245040100c01900d52a08103100600d00303140190b80e540c0c8151021202c1034042041510704803408400d039100305038140e540c0b03807450b2204203074050b0315001030200e481140c4a0741d070071200003460904070410883c0301e08194042440c0d0603c540140c00d80c03010f0f010070065924003c0d00d0488401081c0703811644014241003407403000103080d5080010400a009602180000e0f6040c1d540b40c200c0d00c15021150070500d4480001d42c8180c0803a1440004290f400140e401504c0100c000c1d405590482c0b101c44215195501c0703070340e8030180c15000d08100389003130041640d5403024810804030724040301200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 776848561 1250 776847311 776847329
    0x6091205040e071403060103090f050318090709080309060c0c030d0210060b040f090203130b1905010519060e010e091005211207080405040207030f030b1206010b09041d03040f 77
    0x4c070f80800e0403002d0710009005904050382d0340500001c01c1000342c6060300282d00402240c0e1902c0202d0001050b400742450010701c1203400c5000960382070310030702680e416140110099801c00300b15400380041c40e0040380f45804240581000c4071081c0c0c40410195011450a50090683c007144d20050302c01c0307660329088010320390b00030802031010700e03000140c41301113038814003005075240d56944103810740c0101e4041c007c050414410a0110400c5803500c0410b00541d07903282001641d994604010f6210100c030b8141c285030740e403480200a4580140c00213524880181406441c90060000040102c0c80c111030303115143d28039031001d007d80e00384900c10550294140290307a003071a4941c2c05541e542d02c607402402929000c00038106081240d000190380c02400058001c0d0f40318482440c0207050318030000f0401e000289002440b03e003a00c0d100462054540101340500040d034202040745440d030b40681d540540098580c1001d000912400c490149151700c944065500c0e10f082039413302c00c80981e80e001500c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 776849811 1250 776848561 776848577
    0x402120a0b042a030b06071a0a021612020f120726040905060114041502150105060406081321020705150313020a030b01090614100e0d06091205040e07 66
    0x300c50b50307003240008003024503241a012a0103c1004130041c2a00c000295003088000c80d68104015207000c2a5000d41c1031000001c1041d41d41e050420224001c01940d14020900208401c0c0032603400084055045141d10540d140c1d07040c5ca40d0000d03d003144054000942c0200020240240491030240e5000c060541c080590203014040c900358031402940104441166100c0c00700d04aa806070b94036582c0303e0121014662104e41d1850b40c41c4c00c20030100c1c02c2030b000d8000c2c02021004c01c40010702183c1a10310003002281003900700141121244401010820740400b181d1014011540c0306c0401c480e000c202d00030708901501c414000a00b00405603016070700440703003c250080d90701810400c2d241c3c4602c1071840290088928000a00404010343c0040e100601000c004552715074903400242c00c3c0ca001d00e00000c40d462100051081e0361705524982c0b0002141811078601500d042540542c020303001d020082050030725912402c04180d80700545030041400000c0c01c0080307402c4064060b034000d001d070902042d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 776851061 1250 776849811 776849831
    0xe03070215031e0a020d050a0b06271c031e0903110607060501060518010e0a0306090f170304150b0f0907020106262a060d09020402120a0b04 62
    0x41c1012004024221008000903c00e0b404840b810380007070084280100d42070801c0708000d4000d40c0320500e5108000d082c80d00041c500040c60060148110019103603034036100944012042ca14000445505015810340080b0b40c180d941d1a0440c01c66424244007034070102e00c610303015010364580320b4000140480d83c42c00b2410250040342400c212600000c04141d40c9170610b00003135481c4034031300d4000c149629000c00814503c0d48240500140000c0000110220134030200644081000c1c00c3d906a0040100206100080998014003901480f80c0d40314081c4108079a10b01500030240c1da042d0001204c00b000700300034403800707440454030780288500801c5880e5205001c035207040000048640510b21082c04030314451b10035403203800145140740704507000c84e40c0c880b003403040e00c5061449222584150001081002141034024204504002031510a118010103000041c1c000c1014034a909a40d8244240541c60b940001c0c001258004007422040c81c2562280c0c1c11115420603c0c0c2c080e5182210702c078 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 776852311 1250 776851061 776851069
    0x90501080d09050d08040302060d05010e0c0903250803070b0a0c030216060e0f030c0c0310050124180608040c090b0a1802070c060512070806010e0111010b0303040b0702040e030702 79
    0x1900c43c191111403c241d014241038609203e55400203401640002d1140d0b02c41d021940100d050301d849020b08001a154805817207104d0043c030071190361581003401d4020a051312904070942003118bd20a1000243c0d40700380441c11500920826141190381c03c0c00c03c43e01240a104225218040381411410700343c040c116803004c0812280010640e0f981c035511402030200401c21810a00c801354100c0365910f11320040e5903103482d80008032034002c3c401e80140c0c0519044034020781d8165810720034a09a0201040102c9062046202d540c00500c134252003003603404450b60301404040e00329a00c510819042615090f140b50016510080980d450020f40e80b0f11030b59150041001c680110b42854100d012111000300280b2071010000c09094195100180103908100600a000c52540d004000c81d45d07446803c2d605070758110303034050028030b2a100a030302d158007904154510048071400055500f520f00c0100f4595030140e00500c0e55004041204c40840c5460b0040500c000e40c1c0c10090b40c200f4445134041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 776853561 1250 776852311 776852327
    0x305040e1e181011120c160308180c0915150c0d020d02071a0d0e010e06150a08070501230a0810060e01140a020f01090507090501080d 59
    0x81980c805800e001c2150010a0003441a0258241091a0032410070040a4403041c401d90400c2d81d05020358004180c850300c1a203d5429070020f0404250300d008103078441410b08890080a0107200c000601101c00c02c14009500a06260700c0303600c42945508050510800700010040315881542c000d1925000f15100e0181594203c42c00340f0b8154260301c880000150110802a2080740020010402c00007080380000c6505101d502b1341c0a8450340c110b02e9a0481e11000c06000e04100440f500d04030502488400c0c00400810303007080750001d21081e16492083c2910b80a00002d00d10b03034441010300c6080d58003401c5000600d6401c03a01315900d41c0c03415006940781c1c0c41c24800c542c148030303c3c40b41080d01403001c0b000c0701202d00082000c00e5034402d40e9640180016005031075003107448001403c04101c50f0701450381103480450585488120f07800e10130a88100340d02c100020b0003180280515003111030001d015170b80a86100c1c80251908c2c40c14060748d54101d41e0141c0c8480265070043c110070712038030703044515 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 776854811 1250 776853561 776853569
    0x171c031a310609090501060f050a030b070806040e01020a090501020f0304030b0a090303090c0807030605060a0b03040209090c180603060703151811030c0705010506040b06340c1809030504 82
    0x400000c0201d2024800404150344030b0705555040100c500f00304081035000a059490300c100300c11410b9141c2c030900c5000c6a080c00010814034240010a030218000c0490940c050401000400c031240c800c80c4841c207a03080042c01c0400300b070981d84248410b41c0c051041150511ba60b100460619185407107054007444041d000d1942f540c0e4401c0110140761180d00301910312904032469909084d95481c505a444410380f00c2034401600d400042001407a11400740021542c14500c02c81c02c60304e85d42c00704804404050a004c8a51283e03500c144003584034000b03007039281e04140034560424640081454188200204a58209803420141d00240308980c60024299007001156041040c800c2410384014050348208118080c008010008055410802005400d2050340284080d440e41001e0005849454407803640c0a4030a000c0210910244811444414105c1018824003000348520f940e40b0a1508816101c502c0c80d82410300c40e003200c00c4020002030304242402c104004458400415501480c01707 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 776856061 1250 776854811 776854879
    0x105190509030706111206040b060406030b0109082a03010504020a1214060f0109200406050d0b0904030f02150702120d021b1b031501171c031a 63
    0x1181d000700d8100700f90b85000c2d601c000300304051103070307020050780ca40c2220703144140030003202c40050443d0a050151001001c1d014101904050605105402070112420b21a0400400110001d0000401c20040e2221400060790070480403807482000d01241c0c4840041c3d000e43e0501081c0001a2281c807500800c44040364496403040c4402e190801c64400c5c02c110448143c4908001c0c0400c1c0346040200c2c9040b00c1c40304008218880b44210410341d4642000e141c8095107106100c100046070091005224a035100d82d130010b050700e4068001000801c0646069001901803041852002d070100101c1a01c600d000d80d15050301d207071050b0003d55940b03482d03015442603100801c101c0316110709070b0180d03452025003070903111001c14041100c030b6442040404107a0044440c0e0b100300c40d48e01740072400304008141c4030600b0034280c0c02d02041d40040400610888040d1203070388940014800403c40ca041d800c81d45aa001c210080e4002c50b800c500003c00b0445480f0740b5143c40100025490b0007414203520394421 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 776857311 1250 776856061 776856071
    0x1031a06090d0605070915030c02060109050705250c05120705061605011a031c023a08060901060e0303090d14070f0f0b0f040b031005042408010519 65
    0x2000300e40c00b0150048001c0c24075041406210b45903801c01c0d168415504a004c10110340746c4d04c0c140c01c4080d00c40e540346400140e040000144198822600100c0d03100b2060304003d450140409103082c04510700540c151a9040e046800d501004103043e501c00c010103040303034044c1c070b28460183e00a8a40d106445440d208880c00514000214000d401c10344145801034020440001110788608944140b5a4074038440d024810400a80306001480f41c0c1500c41d4a60080030128460041d50415241c03a13202c4800c1d030f00d090140c40410b1810150010b107087c4056403203c001d810130310280845444180c0043c410301030110301c619903d40b800400c0c0c80b180041100c558140c40400d040a0742c1e43e40d40100e004426014030900810b0b05610300100c1c1084411709840703c03007001c0c1c0c0c912710803410340074910b028008841c08000c10005841c007540616000010f080036040d000303a54000007401c030703080316032100e210200d040c046000c00110302c10f0810003003052000134441071505071908024000701480c0f48815980d10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 776858561 1250 776857311 776857327
    0x1051501022806140103080c060c0310030b190204060507060c080103020d1e080c0a020306060301050c03060d08040f0f0305010b031216050c12032505060f13240b01031a06 75
    0x76411007082410703150a103070007175616410031000e2540196213000c190310503c00444c00c420510401c407032040381a010180c0e003090035595884224100500324100f42810010341140e00d50784d510091005101c0da8480317550b103c202d031800c102650b40b550701a4003481402c1f40100096190314094442c0543e104000c22903110096400c6030529101d404050103e84021560340908400000c011a006000f10b0459040e0f036510303010142070b900212a42181c20005002007045814900d81503a56188035400c1d05007010744410282e0307841d248652148103440781c50242001402000c0c481c00c4c000c07103415405031803500a0340615820b2807059040c4900d1011070004280140030b0f040c0714100b40c0110042000044100c030001c000ea5035088003103a41401c0c01b018100c9120903816903030b42d440403540700010f040e240d13581c41d445040d28074004010415044082e509207002402035054000c0856000302802d50581c13403c1c0701082160340c80031100781814505815040401c0c0900c060400701c100c101c41a6a681100f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 776859811 1250 776858561 776858573
    0x7090e0408031305100603030801050406080c030a03030b01020709050907031713150306033203070f030c0309030807240e0c10020106170d020606100c030e0105040b0a02010515010228 80
    0x221501217045601d841c0707000c0101030380962558100c0310203d40c107018013034480704807030b4480140c40e0036198190300104002c00081e010707070801801c10310140140c4040540c2d4401c90b209403201102e4049094010031030900c204241c0c04040480000507800e4542040d41203800801c0310b910320f001d0800030b513414032686203069200e0703004040550351202c84203a882ca11032005031380342000c041000c010300d40c030260a02c1c488200041503072052500071022414241c00ca803410b0303400703d07c2501e080c0c0c00c01041500110110f400702000784507040c8200d964200d4200e41f085442c03407807540414684642c901700a401050714a00044231500e003101100e0701d424003144468141e0050009130f10003c045080328180e4805032001148901d07402c40da68082c0c41c4c2547d41d000400080091a111200110f01d040c0008004a0b2084182e488900c01c107041092038591684901c9189030800000d81c00181e444404229885444812010448600307000400c11074941004450340b1200601c42402e4000280f00803030280a1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 776861061 1250 776859811 776859823
    0xc1d150d060f1404120c030203030c030a0f05040f022b081b0123150901090b042c1b010206010b0a0923010f1812030507050601060807090e0408031305 66
    0x2c0e9008014480c1d060368540d076040412502610f4100c10803500e445a2801a030303424070b00c1e50785030b03000d03515680d1002031411058001034070302c50105580714411881ea202c1c501c60640120700507401e0501c00c0a5920410010802c030846034044201d016011540700c40f5446c0400683c9680622220385134005030103c0b0466200305042d03070740d440d07080c032032840a6014030326901500b02d100d0085519541d13031201c1124481141e00c007509900440c06c2c2c0700400007100d07150301908108130020804103c0354180b000311501e043c0100c85403c2c000901da41c0f0000724103802c01220343c49800d800c02000101d4107180000c1d450b07040501c01e01c0351201c40098140781141c861301c94000038000001c5090b00c0c0c800b00018100100d280480100d010520700c401d828141809107409800308540d01d56800e103010b0500c0c810300802240028120b040c4070043c00140c001403c24000c0c640a001c035a40c9005043c41c050500429048282c4c0c4185030300c0c1c400c3c2e000e01000c10085000c60798804000d0085460308045440c001745821 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 776862311 1250 776861061 776861081
    0xe0102010e070e010e09030a12020c0309030a08030a0605010804050a03080601140a1707020a0f080f0f0309060a061509150917100c0207061d010e0d0c1d150d06 70
    0x405402c8001c03400c810201440c03030580d03d1030401d880840c2d4404941c2c0e03a880c45a546400c010510a180000310648550001c1c10700d4540482a070b0300301040140802c0c9400c0e03512104684802d000300400409400910400000f41824a4035040f9030829071100c1d07403100104c15001d020003500b40d00162050b4004e45811001011181c1d80956070151044001c240700d40071414412501c10740ca0110b90494800200001d009801109240070001c2c20f0340c3e2403100b5448150008282c0c40188240e488807090700000d584074041c02c0d8046c010515001d00349134110b44041e003007420190344281c1a45081030703201c07041d80c080d60b400c6a44000312580c207a6050700d038036803990f000d2000601d4000151034640780c046244145510342d0402800b0b5016246c0d000e0b070315403d05005140c0050600e007101a03620400245c1c0d0fa58550040c1000c1d81d8468210380419504202c5450983d001a00c615040004c0406414079461140c503d600030101c5041040c12a16050103007c200f0344514100e00309541486042ea011071036407 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 776863561 1250 776862311 776862313
    0x10e120d1a03030a030b040b040504030e0103050a0b030304080703050f0102030c03240d0807020a060f02030d0b0604050a06020a0b13021e030c04051006141201060804060e070303030f0f06150e0102010e 88
    0x5100c1384500200544018403940e03014500b010700140f901c1c02c0c94041c050103554547c07501480342c0c8505004500030030300200099046038861710340381015242031000380050a003034006013202da070950400718a0541340c50318a02c040d0703104004203c0c6e03902e81038040c2c076040310030140203078120080c40e4501030424150750080355010f0b4040000701c00300b000400060030314a1003558200c001c90f6484034140d07415014289200e015030010820079000e01040c1c0e00500855000800c401d09064542020805080d0260070040c056880a00c00d40d052002140b901c1e54050800c800318081b0903410b90100d14200c00e000c0144980d891070108280712580d080c0001404140080d000b00704901c1c102c60f402038000040d20803100401c2513018900a45c0b6800c400b10381c10303540c3d413051014041e440d103036040358099001442510309590f6014011041882407103814021406540c0214028440c45400c0d802c0380c08150f8422200d500d0058200000e04502d0b0329100c98100307074207100300310302e1000740180e014216004c404001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 776864811 1250 776863561 776863567
    0x2060705160b03040516050f06090d0b090303010f0b0a020d0e01021908040f05090c04120201140a080f0a0c08010302040c11120d0c020609120a11011805010e120d1a0303 74
    0x1c4020744000b0b035200394040c17001c440032203c08400000c1005254002c80740c104c1400e401c01010784c04d01c800280028440603015000500c46a22a03804503c015111040d080d00008010070a19078036140c0e05000d414455481e13868442c11031400b95464007440401e1040c4042c400c0c2143c420303030091000c041e20715180000c800c4090014640302c0d1383d6511030b0058103040240600d0110b400e08080c40d1080c4a11b1259403070525090601d00d1080052466480480c10048501c100940c410300f0701010304803080031901d0b02c80315810803c80d0003403410350041c00d08020354617200c0b8600304039130311141d4141100c1e0182c42c00030b42107403d90002c403503600b0030210800d11481800c00701e007140341d10708005000c1d280b0724000070090020680d40880c1c4625003600c2904d8582d000c2001d00c01804003080041100340014101122a0390180803060b0945240700d6420791041051060b40c410721a0078052a00101c18a4001d44408060049010b906001c0c00110000003903403403010a01c0040031304095000c00a000b4100c940f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 776866061 1250 776864811 776864819
    0xe01120b04170d0e06091906050406090212010b090618041101140a08062b080c15090a020f060a090b0f090418140102031302010807030b040608070305010e060906040206070516 77
    0x2e8480e51601a225120b031100180d480320f80418401240c8560382c15811800d5080d23154500a080e01601c21b0ba041540c4011050050395000d030114500c909100010842400c51420000101c134028926805048500051200000d031103110f958000e6018600761606100e5000403909000606040d44001c40009500000356400444843c0302e07000403100303184e0803040c120140c0e2b040003e0a0340e0700d81000e10303441c0f0b11000480110142410700118001c4580d0013101c03078080982010180c81d000c2858201117060019400d25540c0d080d814030040d107206140a001d81070080c0300007002e206e001070800f00451051803c0801000700c2e41c16450080c024400c42015405a0b010720451b403408940359081e8044090202c0d4040c000c0e28400c50040310701d80102d180940064442800040c0410201540e0fa035564040ba695886a04041c050101c0186110750540c034040d82199007030710319000c0a900c15000c2100c0382c0d1002491a40c416416140d09454a0140c82c00303a00d000060321004100820408006c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 776867311 1250 776866061 776866087
    0x1e050f031b030408030712030908071203200d0e030c0d0509030607030c08220c0b0406120b090105010507050f07120c05010e010c030e0612040b060a0e01120b0417 71
    0x700c45540e60040403140c6a208019649124034800c00940703800500003280480c1d022200e007919107205040c00309140d1040d81d40c10442d9442070a00b10380150038038503000d46107549403084c500711080c1402c00304400e5903001c0c2a1b82440c00f030310081c0909940c4405e82081c4032030007881a0ba41c00322a420403200e1096502c40c3c0a06142c0021420751300900c1220001140184030340510704071803c1c10f4845034a01c1d184c801040340002e801802c00880f450300c0c00684000120101540300050192240382a00c40d402c1040040643d41010b074440e11190600f05400b0840e0744a01c0c030f0342e04540090a00c1e60781d46082d0300c1d01d0390070110301ca4501541405904400540307001d000802d1408680300d0305000782c0311511280195622810392178001e0000b100d401901001074020b241401e5400070003000036042c0f8010705016480c1a100b01c40490f0214220f80500c403850420403102030180c10f114101c0c4040758102000503200440390400907159003407480c00324080c080c0c0400300c01c000820100f0f07041d0380e0307682c000918 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 776868561 1250 776867311 776867317
    0x20d0902120706170f0103080f04080d0e0411070218040f02060703080601120603320709140603120d05040305070606031a0c0f090d020406080d120606020604020105071e050f03 77
    0x1000421314440c4c0c410400c1006008083c402d0075614548640c903400e5072682403440c3c02008204110034400c000101e81044100500800c05420740d98503814501060280815101c400d421300c11240418400070b401a9960941c03c01610701c0d84441400f036030b960f8140a40d880a0801c00a500540000f911178181030b400b000041c420003007a240d9000b00040c2d00c10000444e4036030b120103400710200c40c0f541a0351030810090128013070006044030b599001101e04003030400c01141c0c00251610793342d130380345044251100c4400303500460880180c140c0100d14060302e03045200710134804840f141e031180001c081500490035100c00c141c20040400c06252246071014207907a4050b0500e04075074140000443c100703404412110080602011181030000d078100b07010740301c00c0c5504200e912545400000c100d860003004624000c07a0250346051a009007668100210742541d0090000c54001d0005c020140c5d800004840a80360700440825606e001c1c4203030b580d000c4440481c010400c0c06034180310440d40f103000000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 776869811 1250 776868561 776868569
    0x9030a0305072c0f12010b150c0604330603060b04051005100c06050a050106120e0a03120b0409080309011404021c05100c0f09050609090109020d09021207 68
    0xc20055600e80c02c00c2901c2c00aa4054040d003500e00c441da00000d022101250400d800b803003c0d00c403005029042d00014448808003001041c04d079985c1400e1303100ca181c0711103120022042d440d251440c02d0310035000c1d01e440300d50080c00600903c02c595000c030b201004168500155990b82e550a0340001a041184009040c00780300a80742c8908251000700240341038440c3e540650302904502441e0ba00d020103001c1c0850b0313480f00000a00812010b01400b180c164040c0c41c0c480c1580d6803000840e5070410780054903a0401c000c80810051070300d41d02442c581c5000940849903034050401950316140807008101402d006000e640d000b41c02d00000c4000c00411901950191880500038000049600e0045147c580c048401a620444c4440e5500025241b19071501003603000c0c40559950803558403a100c1a03c03121241540080c4107001c02250310360f031090000c4007401040b11820b150a00000c002005228180120425940c0c0020b000c2c82c4c0800039404203000d076a02034410914110410701440d00d61801e889 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 776871061 1250 776869811 776869817
    0xf010501050108011409070f18080d080c070803061905060c01060f05060a081b1207090e070503010b1c021e04030b420603280204120b1b0309030a 64
    0xc008159420070009a03999041c02802c558804c1d0b446800803201c404080d1018001e101104c84180c08403404080c908e0060708540d0f0040542f075481c9003004002807001030500d07000790018010000096038001c00c50742c111200320344c1d541c80d1402c0103903100c4d030f44509544003550000002034004482e64040d0003101c200ca414500fa10000c590300c00c20300000d4070803140120002851500091a1035000e290305030684001c0c1c2d039030b150504400c500e01c4806040241c806002003a00e40e0000c202c0c00346056103465100301a031500382d046501d0b003a011f80190090807130141c0019000b0b0b2210550b00a180d041ea0300c01c0080b24005440030401070301502c520303402030200340e4a0b1441c804c0020f0886c28102e9a541103000c4004908c440100c00c0114010542c200445c070039000d03030381001207207600e41d18a8043c41c01a6004180403015072074580c50010300441c54000303100d4031401404108455419981510042500101c80c05240c0d510404410760700e0020094411040c24088140b00400c0380000280002c030b00561 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 776872311 1250 776871061 776871077
    0x60311040f0b01140f190203040e100f030b06030a0606090c1209052e0218190b1e0408061e011217160605040501050603120c1203180f0105010501 64
    0x1400c00d019200b1101c00340780810740981c20011103403095402050055401480d4a08000c000c4125002c84c000e4900c03d000164000708040c0410a4100c0b0040d8003c0ba80c40e03c454541450201c00c4840c0f80090b2001506402401000039025142840040e039240d900c00c00c10401d03103842c0c4c9600c0d4028504031559800099000301682c0c46250988070300c801d4150000014819100300e980b410708203040c90310341400b040d20f60907800ca56019440c006018641180701c0a81e40c108090828454107402d148801d0081d0070142d82c003080010f810400300c1d180080400545401c0b102841f2a92895200d0380e440740300035105600030003175180040740700c000f0042c0450310b4280c1c41c0c1c2d0380e034036146106502c40c3c0c001030440d00c1c00c4451390310001c10010080207410100746403450356000c0d82c6c032034000b11141164182d80c1651a40200a0280f0301440600000f014030034095080c03801040d11155a0143e401403100c1c10000040490401c40400302500c4090b03810808403001782c580c40003042c0c041c040a00c99107000c5901d030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 776873561 1250 776872311 776872331
    0xf02010b18091207081e041e1d160e03190c0305010c0504060f05090a15030e06011203080a021803060c07210c03031e0216020306150306072106031104 66
    0x10303402c80c1c075090341000005d401e14100c0c081c0d40903049000404c030080e4203010040040d003003440c011100030b1002c4d140d040c142620700e004a8400d040c910058030640910902c8108104c09031036134021250441c003440e040c1e0b0f05142040c0403920b4020040300384c4410790034054200302003203003075002e01e03065910501c000d11040c2c4041e8410303502030041c1d018003030101d80307c0024145218403800203060810313802002c41d841d16076250f108120005181c981000042c0e2221100c035010300c0108000e50040052418040c80841503460003003504c5005000d540d807480d00011108070142100c000c01102d11001801d6881c0e0303050012190110b54800c500032581c5403406031020720395400c1d200d504c42080c00036854100040c5040e64080700248660b8207800d00c403104000a5070040e0f1041e10140c00c1c420300e49010310f0b8010034a801014a0840d0050036180c032120301404000c03840e01c0108000c2d4202c811070410f10303400032070541081490300003040e424900c586046400401e00510002c83c1e9041c0c002038404000003150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 776874811 1250 776873561 776873593
    0x30309100501120b0402060714030a0207080706090302060c01060902040b0d06090603021c0327090b030307020a0e0c190c02010806010c12050901030f060801150e090d0f02010b1809 79
    0x900c14080141840d607000e0001c84c0010005941c0f081c8018213040c541941e40d503403400c0c10800401a440789034008900c030740342d0a80402103100940183da0013440702d1490310100602c0d08000e0f000003805201c0200d40380207030243c2508400007500d00c0803030554a039911901e6442c1140c1100500410703490905c0c100284d80034080c403400007038075005059024001c10301c0005200c00640140100c0400c4070518902140c40e0820003a0a141c05c0c16000d1200e259103007090642c00d50b00a025403900c25082001f0035001a51a080e103141246d0161501412540c0d58180f480c10030b0260320750f5030b02083d00320070703411841550200c841c0c0c0015100b41c0340e07103259031590001100c400750b484600410f00600580d2a00e47c260088028008043c0b0514012884010700c22342038050703076065400f624040c1c0d1100700c090290480c100810b070140070303000f503070020a142c1101c0c41d56841718043c601c2c005115015200c000050f10071b4200d4a052381d0040c1424540036075206142421550482d0f243c07007240940b96403240a400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 776876061 1250 776874811 776874821
    0xf071a0f150d02010203070c0303090501091e090b030304080d0e040608030c0c0f190305072402070e060d0f05070f0909081b150a050601021902180a0b1203030910 71
    0x581c03080541508105030080c4102c0e0428424142e040d8032050080c2d6001a4151090070301031842581c500410703a1802ccc0000d8494000b0750041c02043d20f50802452400f12441071001c2150022080401c0da10801e501013403c6210751303040011140185450001d8913504104051101c10017a41c0c1003100f036595409050712405295141a42d50300611600e80c1c2074501800c60b42c040700c0006000a10020340a0340340d040d60203056208403965040700100b08410840781d290100f1000e04400008090000350307100079214080d600582c84880d070a6000301d250794a0340010308460550100d1400b11015180c14036695a101398851405001c82d40c00300031900c0a420700540700515440000e181c00c0c01080308940d40c1000f07010340399540c50b104a0241681d1150155202c030701660f02000002001e0803c0c1000a007403080302e01002200c3c0d55070b452078800588030300304807010510164030b0120480e129402c1c0c1d00050005910081e602000703c16400740b03810000302c000e501034080182184c0840041340303104019a2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 776877311 1250 776876061 776876071
    0x2d090203040f150605063c0403141c02010e070812070206070f051c140909010e060102070810150504090804031205070b10031a0c09150f071a0f 63
    0x3a614040780b1002401124148101c1c00300454041201520741c00443e113240c10134024060100d00c6c61158010b03410041a4005443c584e158070f800030603402501c01c203458415448000c120399201010b045840800380490b4255020f4902d48001c03130a01c0c680c0003806041100c12100c002d024250000404800005050b0f0300890000030b00d03401d0585a030204940750300b1000c400d448180d81241030400040040c0100303d040066414021723150700c03804800402040c17200b40d14410202082042e15000da80d0f00801c40d045400800380b80c1800e540f4040100e041403150360100c1e00e184074103407407614800c023607070045551181d0300360340547c5495a80c3c0c204001c0d981145405403041400b0803007400803c4244410410f6043c2c02e08209140440c2942c0301c600d08082144d60102c012000f0f0014010007031040344520b000b20020882e51001d00300725040e034075070b4480c8442c1e40c4d10445d10714010041d02d2003404244c1e1094018401c0403512000306042820702a90f4856003011030343c034110000b49901103038210b040e00030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 776878561 1250 776877311 776877323
    0x8120f07020613020420070c3011090403080117070b0f0a1407080a03050601020f100506130e100b010903030509060703030908310e0f04020105042d09020304 69
    0x141c0c0f510511040064400300c0c040c0c0e0026141e440c00300310401c1e000e07150450102540c400590b2400e0302d003131169100803e9004007040d140d20b1100e0416110b80700189003e05480c40f452501d036008a440d201700308100c03000d075540e00103031600200005e05400c0512176040707130454903184e00d40182c1c00f0f906607191075442c05a0440b0400038005440102d0048003d81443c4603079007007500c9034050040b58801281c00c100c0b81190715800004910f000039526004240d00048280000c10760511a801525240c440c81909000455a0b950014030315076500b0705603120901c0e0790f90f010840316481d40340c03c0c0d49030400c2c4000d4080d05420404094100d5109007403150071a0b42503643c0a05003495041080150340c04a90250101070b01d418260020820314001080f109005140031038120305e403106d9980c41e08003403884028401d45100c10802424030461203c1c2e50017151503082c84415038462006076864091500041c00014010210380c00f1a1002d071b0500303405207040d6040881c040c0d902c0380c01c0801d900c4101e5004009c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 776879811 1250 776878561 776878573
    0x2301020706020f031b0f0703080903010605090f130302030d020705010e240103150605060f031b0f071e050a0b01030b0a02191815050d0605030705010f0f12060308120f0702 75
    0x3800f0540450b160341e886004c011b0710000504404014035003800c2d9001502c0300440001c000070a41f90904c5180002d01d4140c0d5004618a001d0101d2406203030000c040c5002a01303100754400c209071007441207038030400b2030201c11501d030b04480c2061402410440c1c1540382c5440340605024000541d100101402172901c1c14a2110b0303030031959200c049010b01c8424401958541038007055581e80c020280c0880c801540fa4580c50f45800c0c40c40d58118890f0300c1c20100c0c103080c04c0000d400c0381050b1108440b004c0340c01030710004032011035419034840110105805062401610b80581c100a407800b4510704036801208590141c2c3c40e42a0405d0882c410034440c01024070a10b0120b040c0d981c05140c408000100a120480c1d840e0b541c1c510380841c1082403100000015000200095240090312502010346402e43c000c00c41c0504120002e409804083c40c1107043c440b8440c020b000360382c4144510b51030300c3c00c280c406104031a500d1a00407210b8100c440810300c80c5a610700003c4100b0036843c03a051050f4226402415 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 776881061 1250 776879811 776879827
    0x5040f02040e0414210304030f1d040b0a1a070311061003020f010e13050603160e0f060604030c06052a0717031b0c030d0203070b0f102301020706020f03 67
    0x11260a0130045600b050144072070083c0302c0304e5620801c00c03165405060300740d0740c0d280600d0014034441e401840f0f4030501c40d5405030001180b110200342c50b01d1700c8042c3c50001d120005000094031059203980300207440c0b4042c1300c4c0001c50000355009841003520944030500c0c081101c601c0203450780c0d01201c00c4140d01e44014002c2001d440c01c0d001e0700c0d000c0070041c103003454444c0c40701d008a0f40c070144950300781c454980c407081070000c2d40c00c4c1000307403010022010001102c0c041c100405a000454007800c200c0e00380c00614041145a0b1328802154011980800143d1029a80b108080c0c141e0700516140d0703416001d98012841c0001c000400b80281c030140384003520b0b41c00c1c01c108842ca001213000d107035a180352200380000c08500804082d0744584011500c0100140920b1b14100352805e440780c454139007150014800c181c00a0b103d410f249400002885180c3c24903942c4518048121450f40c2c010b04070751110701041c0303100303502d00084458058800c2c0c0c20355180b40c2e1144001d030390303403040c1d0301240031180d004000c000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 776882311 1250 776881061 776881073
    0x7061707030e03030406050723070b090304050a030507080d0e09180f030d140a2313060f23010b160f05070611101e0c030e070f05040f02040e04 63
    0x6620a12904000840300b440c01ca1852440e00101d50031644d00c0d903030303500780041d240c1c00083d443c0c0d20142003e81c1d904465901d17182c01e0014010a000105100c1c464408130720380c002c060080d2405440040e01c5040400d6803810701e1640c4d15030038410607007980181c1c0c1c030355401c19203e18181009140c000d4003900c0c681c0c07204800344820380c1407200d07445068000c20044e14107184042c0300030550200b22401c0860540740c03000e0001a094000361040700d6961608030303982c41c0304549000901e280401e00340540d00b0f41e60380e96041921001c02220040405140c080c40c000d036000039a0061020300000d41c120707c0c940e01e100d02c084600740400e0080c4020701c1d40500030300b04041065104403403e1032103600410681150b643ea040d14158944d0000000b2454802c014010380d0001c0100050050300c0c440148110b480141114450112090071811714a071124200802e40380070b034001400300710402086071101a912040c400c510300349401802d211b1800e18122400082e01402540c1c103490315000102c505480b10354482c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 776883561 1250 776882311 776882357
    0x9020322171602041103060a03030804110612010e070905011209020609040608060619051503040201030e07060e0a06091a0c0f01050403030207030807260a060e01030c03030e01020706 80
    0x1107070100480da180103041280c80018121039030048000c400307111500d00c10403042d034110407281e10b0301060610400c90740e55108100c0c1f4040341c4d00f40c28064201d4440f800c1c514220340141500c03e0300442c0000f90540b11a03480052541207450740a100e801e141c445450032140c1502c1841414001361605800080e9500c466001001407480240b10504d82204440072a080d82e6240d40000c420ba0000c004101c2642442104801151000b0003419280b40c240000a0310729480107180070f08070703100400042c0c01c6900030790045804030a00b4080b00d4049680d1040185515007006006000e00c0410000041070341c0154005000c1d40c40c005810104142e9030050205540c0060040007120312480405c04040b04080c441c85004600030390b000340c1e031800c281c1005004010090318020410808481c55001c1c5444450034410301c2d8040312005105490b40a40385015103040e421041400901000000401c4014622a003c03244244c076100b490103051801a6140e0350540b0030174020070500201011140310032542 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 776884811 1250 776883561 776883563
    0x2102070612020c0f0c030d080108060f0402040f09061e1509020f07080a02030301030c120305190306051008010e0c0c100e01090618020a14060f07020a030506040c0303030609020322 79
    0x6040c00319940a6a1504128503040c10303094200a5012005d402e080c00040c211421900342681c407940350070fa200b950b40d00c00030800170030a054200418115a1031340c004000c180040403091040c10002c0c01c10740001d0402d140c002d22290703412480444088818015642100240495180c1051400c1c00441c06544140030000d40300c1e0301040b911001805500103011085415401541c80750305603c0c003100340c3c4c00f03241c004d125543d0380d807050100080d0b4414200d4401c110010b58001180000820650191020b50000c952145602c0c0c8059221070380044810304aa00e400c8030076940d5204d12020031064829040b84501581181c1202107110209811800352043c175500006106c02082c1c82e0181118006091529120250b0064100750310740390207082c02800c1220218501480200c0001d1954410400a10060702000c1440d100355134440100c20001c50f0030400303581d1249000d00d05180304036903900089002ca46040c2e0040b60501052080e60f00c590254900102c8100403c17081058032404010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 776886061 1250 776884811 776884847
    0x10b0d030c030f0e181515040927120908070f0302040c03060b0307030b010e0a03170c12120108150c18041b02010b0910050a05010815101d0105030f0c092b21020706 72
    0xd1460720804181c008662b0300c60164826000350841038400074a01107840d4010013003503124640078420382000300d1a10301125070407030300040ca400580b4015000b5001c2c9500460454502004008a05400d03800c594801d0300c0983e210b5907540b4001c000c00086040314000071b04011113101001079100c001800601e03103030a20108407000200206041b0b201c2d075102d1ba90700ba1010b0789000c010841c8050070070a510301c84d102104010a00d14284026220600999200c0400e680c581840c40e1842d40300d50344003110a408840350407030250392200000c2c0c060102c0d44c0c00329004020401c002021b501c0c0c020288002c0d00d074000d150501d0145003200455440802608103443c021426500c295603981d102d405020718200c81e242d0320200c841c41030110100a60150304c40d030520408004000901c102a1241d50384031059181142c0c5034101c88021a0050300d40c0c00488428260084481d14820394160b88015000d200f06011040c0e0302c80140d412000c4150200120050381c41964240843c6004409110102c10598 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 776887311 1250 776886061 776886101
    0x6060306050405250c0b0103051c0305040b0601030c0c05030304123005180f06090f030a080117010b030a08130902071e021909020c010b0d030c030f0e1815150409 71
    0x40c030780d1b4900d800300ba80102c645501401c10352a1a81380d90300c01924645540c1810095403400752a601c1d43c02800801d46410503648032000041640030310144102c1d16088800c4a4a80c40d06260200320004801401d4002c80c4a4080c042501a129502005804c10802e510080c40c08028064005042d000d0030b130031208616511900032825003001031000024a01c07004100d00d060503203042d070410b0314040c2c0d801900d80080201480303083c1c005040349d0459185080c25105e00850181d0203004043c0c010a040d414001d101c0d8072001d128840c006010402c40d4403410a0000307540d882e410040380f03d030400042c190000d001408144d85008502817090500190144070380030a0070320911103d51300d40d00070002d1603a001c1030646a9240900c1174000c0380c8026075014220a5554802810f2004898002010481c80300c0740714900f0b41c400d11400e00342801c0070b0511000010018480c044000040302d4204218846000051b482d1402d00d04610380c4603100d4032030900d407504054284015082c1e906520350461014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 776888561 1250 776887311 776887313
    0x6040b07110a150c1218050123040e152704050f01020c101505030606120106080d0302070308091513080403080d0204030215130902180a0906060306050405250c 70
    0x900318103c0c1c00f401c1540d50101908907854a80b0094008111440c104070242000540802c404220343c0c0c191002406c003080e101e07258020710396090303420111403152410041000140c0b26032030b4450724000d030300c0c040a04109011620038095048134140c09021021a500056801c40d40c0d00d404040d005070041040d1403411420b004114207aa001c1420090168070207441d10409080350700c82c44c40d40342c00c1a2003e0701880d141200180e6140030151140d8400d800807d200c1c29002001d40c000320041c0b03014015034100e0360880d50090300940110800b030f0007042c00380001590301e000100d0901d1010120301c1c00c0041d50385812110440307018802c03c04983c009010400440800c2c1e01b10054912080c841e4005a40c4500714070520101500540c0c4111303010740140550078110447c0c5d00460709a4807096401602c402c0c0d090a621280c400d10819150420301503200416000820b0708040196035107600c0502103a651041071004a91080302c802c1c11350750304514260092980080340a201c5000c3d86071002070b0030b0039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 776889811 1250 776888561 776888579
    0xd0c020d050706260105090609190905070f0816180f0501031b2115090f050105040615050117040201020c06040f0e13030e0118080d0809070506040b07110a 68
    0x50b9420940110b40c4641c000d5081000070800c0013842c00c0d0700c0c0c0c501030304c6525010209030207400203000b051085aa034000261100b40c81e80c42c8007000c2d4142e1809000c00c030b141341080c0c4d444941f40c0c080e180d01035000100c0450940e41c00039800c403c2202403c61000290f190841c0700c1144c0c081c42d040c200350551600c000b03209800300c0740070301030286004500040040000903017440301c00015511030001400c000900660b8030342c00d41d1a00b8078450b0480d41840300000700030f03441c070024901d030388004000220303a2000d14180030701540264440c9110300c10411219141180a01c0c40790214441c09002900481403190b035428440c44054126206004451040418400048654020750072440744007404102c2048244550404260000a0710150880001c034648006040051440c0b1107418400100c10a12102c918816001d0013000198203645030b0290708a4010110b4100f0340c1c00ca115403051420100d09403030700c20b0489040390b07001000d0301d2814040e83e03070300210340045440c40d0341d20100b010800203840e04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 776891061 1250 776889811 776889823
    0x1110c01020c010c030608030d05060301020714010f2f1b0604030c17040605040902090a0b1914030603150903090312041d010b0d020d1107050a12030207050d0c020d05 73
    0x9450000580c84407225007009003100c44814100c4109801d001041010210100c211131002d0244400400d0681d100c10120740a4468920002c080c0c01c001c0340c01e004038150641c0039504450f55560140030304050048041c03460400800c8003803d00c80b40c81310240c01c51545400810239100d91040109505a01085203400e20310112015008540f9a41c00201003103441c684954000c0e80303c081482c1000d04181c0d00402c10b00036800307098a413690028118841ba03448650350001025010420340d40d440c80c189611041000c01d240c08000f040c01c96071031003035282040382600d101c0d58024008000c11140384852141128010f000e00b20140030800640540740c405014801e28032441192880e601c91405181d1540c1c03808040c134080c02e002003d40140500c1c0015000c54030034012403000541c0ba8080d00c20b14000404042e90001611032001036600e0800030040340900103113000781c1d802c0c120a40b00c40c0d0700360141e00c664203000b08642c1000e80f1071841e00e40908940440d103070001d04220801d5107030b1359030305117408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 776892311 1250 776891061 776891077
    0x80703080c0d03110304060b0d020d0c1505091003021e0301120b0a0b130b010504050d0605040b1602030301061d04020c061501141c0b101707090e16020111 68
    0x11000204400c1110042114030755000d003d10b07081021013900e00b5250001e01010704000c2c800360300c41040728802d079181000b00104680080001100c10001e14040c2244281c07486610740b9880c401d0341c14101c60740520160385400c40b0281400343e0384900290f0403002540301c03407040104001c4914440d41501c510070080d40c080d1000d00e11200c1056401c0c100401c245200400c1c1c81c0e40e86041408076001754851500c15000e036011315030041004a90f40380184d0b694010340d0401070b044030312400c50b001441502e40005001d00c0c0203400d06940b940303441d50b0603c40c1040351182d820161344104010404144206001003651f501c421030300355009000720008040e640700910414040d07100405120301d00c120804100e40804090800d50202e290010f9214039500554008038624200160400b401d00403035080304050020041051740f0244c500340001d0302c403980140e80c605d150120040013480d454043c020392002e580240d03208840e26600c034011a25180d0002610381d045540716000e4518400e0014041c0c8190 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 776893561 1250 776892311 776892323
    0x31303030c031b050d0c11101214070c1514070206150f0d0b060d050d080702070e0105090a0b030c130e2a060a021c081e040b0112020a080703 62
    0x2460800800049400160028007022a0b0040c40000c00000b03150408960030304009681c0c02c481d081c0000d00a08514205810640d00303042e641185511020000d026200d2700390030460355030f07411103100d84403c04840b82c5000c00c1c418408800880d10041c0e078284a0340150401050350184400010291201520100c002d030f4801c2c81404a40620b441220700316040656031108a00700308c0001810048072820060084405100411155140d817825122520b41100486980340d0520400170210b0390100c40c0305006016503040800c014101460060407540e00500ba00c019888245401c40180000c084103680361050b104004155210a100c00003505422400000d02c8028014100d051944144840c00c0e2425802c42085070441500052489028143c580c19111001107030140e281480075540480c4581940e0350592841e94000c51152180c08004401d26910480d91221298040d003514014000140403005000c0c000d1410441c040d002c0c0024044c0c9145665900c2e09800e11105400603941 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 776894811 1250 776893561 776893577
    0x5030405040c0503160c0b0c0705070305030304050a0b1503122214040c08061e011103030c03270a0209100f08010c03051e01290307020d020106300503130303 69
    0x3014002400703034103031170050901c0c00400d1040e9a130580a024024202c032104031000c07580d1418480104600c00240d40c0c41400c1300c0da0b0f402c0c03a0914550b50060551708940c2228600d000400e020120f80d010a462000075004040e0580070812608031600000480f441e060a0780300c0c880000c1c1c600c141040f0041c481580c0071101003817020240402e42e184007140c3e80901c880901071044030340300ca403c031718090202050401694001d04004840b000034052150510303200c0401802040c20090008500410090104006400f428402c44002c00b444413040c114a070402009400982460000e40b075002d80005240800e8035141e56860072801c001d0740100120341c0d516600504182d4141c0301d0103401c45466800740d03c0e440505004210040301c140940c00300e480806162414454500c2c03102040e0300c40305507404e901e91a0098009582d001c3c0010030000540c00c04030001845020b80488100300703154080c100c55140c0d40340c44e0b00c51103410b4060080b81c8903c01000540855900035000c88081e604c0b82c0d0b100b0390 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 776896061 1250 776894811 776894821
    0xc010f060513020702331c050709080303240a0b0d0f02092d060301081b0603150402031008010626010b103e011d03041205030405040c0503 61
    0x302103002442c509200920402004016940b4418001101a45e80080c0c40c4030100c822911000f0307840c200d880154644020031441c0805040d501181008083c4101c2003019a81301c2c04111851000b501c500300302d0341c104002040d125910250069504181000d910054a035150080790000c3c0351640000d6502e40c0109061032015a2805001540c0d0700c02031040d418603a4ac400012104990035003841c96081d5114000000d60205042c50f81c0b00071002023140391a980c2d078402180d10307200d056400800c00c03001d0040d50300da180f41c500d01741d9010703422421500c2d246080010908c802580301803e044102256114001070030320702401003101400c50254a46481140e81e0740711002d080180c03105c964623904160000d007550301c60548010a08600d032903c00b980c0405103a00c140500840e41100c04070a0315500314207022449001c01d648a10645c42c000c008100d60210200074445184c49810300d0390b00104400c200f015a42101d001d00310340120292403500b961203002a00f101e080601080100d040401042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 776897311 1250 776896061 776896069
    0x3120409090501050a110405100e060d060501080601020604080d1a04051021030f140d0f05150612011e09020309060118090c0b1b06150a1205060604090303020c010f0605 74
    0x7540100c4420824018100000a85031041c007e9006283c00780301d4450740c59003c0c3c2c0c8540c83c9866001c2c400f03450f8a641e4020010a0405040b5501909010030010008181d90354030009000e403040d9005140c1c40d082440107480b000113040c402400141b135012038848402d00395190310a030340c000c00c5030034041c01e9a280b0708010803010380d50b248040c4018603610102e01d0046604600b401183d00c800f0b00d002010101603410251550040640200b00f161500c1215820103d1550104e03003e8003000b0316400d0507050703010401550b8810702c0880c50039820020300402c20502230f2245803c0e042c0200100e00d03c0c10b51240c480c0c0e012030300102e81013035065224400400c440c031001e140c002686c01c80d40005103c0a400ca0301d43d41c8a4805501c5180103a40c0005034031015502140100c41d2840180f1003030321621704080a40d020b0003c0c01206441c814485401c0004103c03104c0c1c0d81445185502c2001342c03a051b43c410f010000248100d80c01541810307000c0010a82c074400070b11035850f403602a02000101030b07041034148 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 776898561 1250 776897311 776897321
    0x1060e0c0c0a060b040603081902070504090f023a0201080a050903030f0a0b1002011d06100303050d2712030b01020c0d0512031801050603030301060c0201050903120409090501 77
    0x200988010401418030503480104840c4485604440d0229032503e40030041030041106d075002518903100401d1b507040c2c5c0d40303002501c6080b20309268229010942c0340d104200c00c994a4010081605004016032401030400d84800300344002281c0080503429500036151041c070f003140080b01841c40285407004110340c1c020340500d4005603415000c100620307001c030100390f807403002900102206182e01c0000d408400c00350851161048098071041c10080c1c102000382c068902080da8003c03000c00038a00382040303900007038224403680342c0c0540b4050a0b0b19689066600b0744c040e507180011652509103c05040e119498004050343d03440301c0030030603a8018140361084901c0704c0205000c060818403d40003d80e03001580300442001141c10b82c81016041c0b9201d0700d07190038001c1600c2000c50200c1004110740702458201284100e0703100901030303540c45004044c0c50340b00c2400341e08003099048480d500554401d0000d0803003107030041e00302d49000e41c1007a41d06035039030400d920002c2c0c0e0315251000c94007000030038058 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 776899811 1250 776898561 776898571
    0x20702041103010e0106180611120d0c031109280f0e0601030e0c15090103020c25120201050301260a0506090c040624020709090809150a14090105091201060e 69
    0x4030703400700d0b8207e801c21004080c1e80300e03140801a050030805444141489882e030b0000204503020394507047c184084002e811410071030710109245c80810070340c20024908588080b40002c116403441d0780110264945604113400f030000031948950003054040350804402c0240400c00d04400d102c0c60000f000605071420300340d040313903603070000901142c90b602c03041e004200b51062440301c140c0b1004c010004070001d005111100390244110014009904125034550329020088007284441ca80c5441c03900e20f4100210100a00040c400c10040004041200c0c015448503074620754019864840c4a144e031500211080590b019001003080c80b070040c0c0204001c1d40344101c140e5007809250326008060348a10703d40b011051903028070300c0782208440d00c2030003401c001d031241f01d03010400d040603410301682d02c1c1c200c1d004441c020590842002c143d25512410b03600f462100b0303502da03440d0986040c42031400f504511400d034107129091059403015580c48220010308a50781c00005202850201000704040340502 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 776901061 1250 776899811 776899817
    0xf031a07110c01050c1207140f03031b03060105071a0117070803030402191703040305060a020c031b1002070f060f0e03030a0209010c08071b0510020d1101020702041103010e0106 78
    0x110340c58441d020604040403002420900d884081c402e41150410b1421690b0080c40900090018100b141d05d50074507007002048800c13a40c100700410a903d44da8401501e51102c20442809004c01460703140c0019079100a061500340c0c00d08a483e6034900c40d580c69030010f61030550700c500040c0054a209541c9200b0020004000c084080c41c004040c2e40300e100c00b4001a0003a0a90140022016403010394880204441070040da0560007400380e26132207420a00040701c4034000d080c00b0842c404014001e552100c0207102c0a10325111100280b0f42814030b6010055846004490f07120318820300910140030380d02d0041d09044041140d80c0350000032100704402071030000745816940c41c0420f40000a480d80700e14043c4006030780e0b00b01000180c2da15900841d000b0310314240020014200019500c03e25503009020302030b8040c4a880d84c003044000f52800c5110001a80a420004882c9208000c01034210558000061031b107501c54022800b52281c41012404c03030030000004008051105503d240105400c1c9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 776902311 1250 776901061 776901077
    0x812150619030f0b060a140702312d06170109021903050303040b090a060204090e0c041b1d06130501021207030c120509090411031204030f060c0203040f031a07 70
    0x2500146032409840a0306e401c00907041c3c00a18801c840b48202c034440ca800902e841107010740182d040c041003008980740100402e101c1a03144a00b5961b01440c510f1440050b07000c0722101c07182c51080d6460402d4400c040010b0307120307000091070105000d603803407036081000008100318005005102c1c0b00203040e2030700c0c42c11201c80007003040400e4002c02941d41090b8031485402185c0c5800c2c80e601d1030085200d2001e882036100080010b514001e0b680407809582d88a41a600c0c140398110800040350300d003070001c090508400726100c03001c1d489005000c00120b0300300251500306000f8000f0404980101e8000c0c0b40f01031002c90709201c0e540e010400400f0380240000403030b1810010741e8006084405250009103030200d0101030310840c5006900f5035100c900c0242024a01d0f103001d080002e03c0ca00c2541155000740121340448450460040494064a13004214281d05034210340d01c405c02840d0b224214011804244004591000496409401140190f074800103407120301480c0442568050070603c00d010b124 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 776903561 1250 776902311 776902331
    0x60f08120a03020901120e01020d1b08040b0703090501050f0a0e0723040f050a0b0a090903020613020d0c0305160b1801080c1b0303040c0509040812150619030f 70
    0x3100700d5030500002d1401603203800d0040700582c0d45004041040c00c0785820176441d00300000c4158080c002151420809200b8591840103110100a10080711000218104002000b1544c0314200f00e4000300f0902d00015801d04503298142102d1007500c160003480d651a086c0542a0014004c50092901c1074000c2c0c20b400b8a0213006084440d00b6045001038400d0b2080d1141503503640e07600c0010320b1099600207008d80d14004500100400780040341e180f080000c5000880c03900114440e918459600d9002400c598544046070319507a00c10304012030740300c52004810700014441d007040000a622030401040c64020000c0f010b00c00019641107006540014001d01c851048020303c044c0c031540c0d003030800840984035080d41505030b10a980b28200d0352890700d100201061400001075100394080ca20503940305494001b00205108180c0e4094a1520240040903038815040441604940803415482c0951110008550f16410106000d02c98200414a0315601ca8141c01194140c90403940204603e03841 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 776904811 1250 776903561 776903593
    0xb0a110f060121081b010c090806060a060c1103031204030e040902090601030c0225081c0824130c020d08010305100b0409060609061e0503281401060f08 67
    0x3210703c0e02100150710150903090005540494200109005042c00402c01c036492880c06030a643c0d0000000401c401c1e00041c1e50000440c0c180e00800d801000d01d502c807880c00300704841c8c03100400c1e0b082e51046403041b400e507080c4d07904200919003200c420701c440e40c15181c10305000c1d1040081c2d9076070328041c41c2403851490040c0e88001c4659807080342400c1c000b40c941c0055004a00c1e25413501071005440b070f030050f191060028408050310803518608110b5094403d0007a800c10003500040440d0040f0769028003080e291404418024886100044040d45859014001541c0d1540f0300c41071074082c03070b6108150301c08243d042c00350600c0700025040c485090b51640d640e09070781da12030303401c1242d00c0c0d80d881c0e04c803400546d5240c000c050600c0d0440e900f80440703602c0b558940c1c000d14942c0b28498031303441c400d041441c030032038083d284504a91009014140c04600c0028402c540c420003200d01d0701203140341c10010009004004000301201c0a1400080c119080600910300203110ba082810740368000d842440e101c6107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 776906061 1250 776904811 776904839
    0xc06040f033f021209070512010e06071b0503040f0e0a050421210203011403060108070b0906040506162d140307050607031a1c0308100b0a110f0601 65
    0x20300446030080b0698001c0c2140007030082c5602e5080b0203c0131420f014070003034002410000d030342040301d14035000d070900e88015081b034500c006400056000f000004107994010b0703e0341500d08e256081007144050096950604552042d00134078200c40d14104244510803c0340101544030040c8075081180e402c1030348030017030020a991240c0c1181d048042487d540310303106181d110011041c3c00e01114010340741003601c2020b5042405140b076003884581583c1a58540019100d0489425a0260486c50b00f800514412548100303c56500404108070001c1c0320307120b1314002d1030f010003000c80103401420360b4078000c101c2c10383c00b21029150480848921344040341951804030074561104020b0101640c80041600790b0081c03110103401401401d0801120903016000f40340b0350510760403006545002d0303a00700580c507010aa01c20082c038480d4aa4140000d008805998001c40503255000301e0765501d101d9020168420325079940019405544081c2c2080200544000907140201a101c191b04226810007541c1d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 776907311 1250 776906061 776906147
    0x1104020702221d06040219050a0605030408040b03010b09090a020f0f070507090504050f01060e010b0403080d0906020d0c0e331201060c02011e120e01020c06040f03 72
    0xc100400b201e00031440d5a801182c0c0125260441d03031100d0340b001c5000d51580c0b82210300b64000c44030700410b07000d1584450302c3c400c00c1d1040100942007040c00e043c41101c0c0c603040140119104042040040f031046051000396000b000c8601d04980e86e01c00e5001444508034001e010411414018407290000c0020001039526041810004a403a41c50f40e00b0320524011581e03111991242c9040700340820703c41e0114088075002c01c2c03500280840c90b40d8507080b05c0394000920482040d050244000d00004443c440140121403001c1c40104075080107803a06412a400701c038502e5003940d602c00c1c40400300740e04901400b214072000c56140600c400c0c9840c1c619521039a200c12292ba041110b201284070f000d400050f280c00a0038182203c000350384842c8090003240e00c0d004240c0c040ba8460300505904408040c04111a413001e40c1c0e209030b40e0f68045000005003002c440041d10a5400b880b01405002c01080068491030150104014152142c1009000136a040f00340c00c2d59a10b001c3c0d120366845442c04100e441c16 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 776908561 1250 776907311 776907349
    0x7110d050d090c180506180105030309040b0424080106080c0d0b0c210a0b03062502120d06090605060c030723010513050609030c0718021905071104020702 68
    0x20b40a4504000b42c441c0c581c000b21064245003690070030400940d80601e20520b02561449a8081c2e20b205e8040d00399800d120300d41d85644100441001c40c00c168020082d803c1c80070348049000421000c0035551242c4901ca0414058104001082010802d0160000070140326014111049140000c070f0490314030058094008440c050100d94500d152900f11112801041903120140d910b4000709401103000b5900180d40d142000c8021050703140c0421214015007151052180c0203440300d50003450058100040b00035030040780c640317a01c0c00b10090010048103132074803c00106141041c40701d404542680d00043e02420060112905c005000421184019001a41c0717200710f00041520a83c0c200180031050119403c03c0184085c003608520000740359072040040c1c6600756540c15010b40e40e401a08540b88850340802c0b410448050381a400c010380e607040c214090314203c140d9002d8180d416441c000d0f000050000900b0b44103106e07588860841d440c034225815460003042d90002540c0c40320185080002c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 776909811 1250 776908561 776908571
    0x60603040c0f0b0408010c0e012010140103170408060705220803030406050a0e0c090603121603020c06210a0e0609010213050303040503030f0f0403051507110d050d 72
    0xa20048400103001402c06002c0021407580724441c01101d80c000f4850003a8940c00c00c0b040451681c05080c040d0060b60741030b9240c000c1c100350341440341032414410600c807807a4007a4111a2104000600030440008580c4d005400c0c154510700c0d051300ca6441e61074280507141c10511081c0420240031075896001030191a03c103454000800e00d43c002e040200010f84c000448034800000d0412000c00510300c201d028400c1004103665041e030b41c0e02500c51710340300c14000d40c20040c1024590b01d0003006540d04288050100d90741c00701890048400e59101784200c200b001c008058040800d641003066143d05c2a080d251542008000c082c1070200e12440e21910b01e40034038410001d40c07606295400031801001074002c44110b4102815814004d40c04011071100c80588004045410b04002044030121103015000b58540781c000c02e4080303120b8011020354424107504000000c041041001012041341945400e0446420109809012100518406501d03500044140d01d6100d4001040c0d543c00c07592a640410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 776911061 1250 776909811 776909813
    0x403050d060e010e010806060a0305120d060e040b0f1501080a05070e09040602090f0a030c03020d0f0501050103060221040c0e1801240b040b030619032f1806060304 72
    0x34001e00e030000041c464640d0b00020340303031402d43d088034102c860a106a6900741c4482c0b0a01031440401e02002e401e681c0010700f006020318400c4018420b4a010315800250035440310b410402d80c10301a81d041c2c41c80c00c580400c2c818252010500180c00580016200e4648600a40042c0c140900200030340203e6503520000360a140c003d01000781ea00d0b40c01856108245001d00d4102c009401080388140644c905039244192424451000c40a894000813072010684c6160308120101c0e0b480c0400310350071504418500e0000e0700134000c05000c1c40c450710b0056100e4402e0b4486140700d00c000c4041c004051072010a000118505a8084003500c0b000b10b2609180c0e558090103009100c1803002c400e406621745108492103007804800a0b11080702402d005440980c0e6644031f21440c05580035254000c103080000c6605032a20200c104101c0c60300c2c511f40d221183c0e6079101d10b0084a072000d50070401d0404000d58400c0702d840c250046840b18401c991030090001c15001080d800100103200a010f4500000410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 776912311 1250 776911061 776911087
    0x60913060c200a0605011406030a05090a080a09050102150105101211040311100c03080c0a0c06090302010f0501050402040f09020d020c0d050a03050109020f09010c02180709030510020306030303040305 88
    0x1840c940c8074110040311008030039110310ba44800350f00098510515000002c144000c980d41c4010314040b00809840c2507484109141008060280c9509003601c46c1240f1a40045c0aa1024125040d5140c6442d0300280c680340029080c1640c0c1c0f604100c10520400060000703a49040c103080d00120300345400b0364001010842c541c01021110b600418842001c5400001c100340d01f1100c01510304150b903042e60f40d03c06081c2c20764000785030b540000d012074a6440082d524414400241034200c4482c608961810f00c9a141c540450303d001d101640140d45820140b09103800342d010b41401800b00703131001c524180c43e145070f503034140c44030307009500c5003540006900030800455010707038580c58440401d80384128285100600698028111140402e040c500001940c007031510945d585011114800c0740342c002c40d4001110b4000d1252007c0307034442521001c9000300702000154a100d04940c0d1190500e160840c20704524081c0220329008600c0d00400030881f290320040180c80c0c120b5403606040d5100d103e101050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 776913561 1250 776912311 776912327
    0xc120f16232b03020f010e0705120307060903320924120103021c030801030f0503120c0d0e06101e0801020304030302073f0e120c0306060913060c 64
    0x42c0b00d004040307500320140c41d08404a0704400a22035001c0320b1007803100800480c266032181501d940240c0281c203040107107090024460a01c1644032090300e00e0f00c0910750724a0f0032518001015400111116a00d540c10742d41c248880300c0540f00c1c40306003001c002e80052a4bc02c0351080c0601c546c000c1008050740c05009038065441010f480d610065940c45485485e440a080c4009100c02d9215100c2480b14048008040501300714480e010307610600e250b030030360300d40003034200c01d05c10b00701e8552000300f010503404030113202a213000d401001c036410f82e1440d1841c000c50544121a11074841074009009000c500b020040800003110300401e48206030000c0141201030040d40c0354404040d035400001000b0802d5803540c002c10f1100d2084087d1109610960844410480c407442c2d46202c0058050140302d80000c840188060b900c040d1514400c0241c00d440400e50139020f0010905065000b1042210540b409204c002d6016009136030030a800e00c2c1c50f1110841c107000784030b40030708038954171101c51848a11a43e40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 776914811 1250 776913561 776913589
    0x30a0528050f1011030c0a141c0c0807031e0506040219020726060f040510141603020306031906020403020607141e0a140c120f1623 58
    0xd940032910401c0d142910f400b48420001c0c0b0041ca0041c40302078010010013507a021309030b18a80310b4203060b600407041e2540c0201c90400080700c841400542001d041c2c1c400003212100c80c2940100e07240b00300800c00380c6003060250816040c0350805006180c45130500410007160150244040740507200c40001c1802442034680741c1e590305060b64000800707030b80c0014160080320400f50791208100d11421032010b4040018044c80e00c140c01020200e41c9402d64800070b903030801d0281041d95107074100340a803c0c0480d03084441c5801c0c0700e00e14804000c03070224551120750300c41c08641800d40c90f40c80c1500c00261100305050140b0542d41184a11106002407035050b84c1c0650381c0a01243d07510072242c1401480351501c6445a9454402c48481044910b400350001007038030a280c00400b5140f25990324100742a0110003915510301c1003401b9200d0b00d6480c14048850700d500000940708203070903801c80c0c40c2068100e121504000c0191201000b685540340c030281e11068040d0030300c11007480c503036001619081d04950 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 776916061 1250 776914811 776914813
    0x6160f020d0507081509010c0f050d0e0d0c05010b090403020a29190b15090f18010603020a08130302101e0509010f1a06030c09010908120301090506030a052805 70
    0x740814010310000717441e042107003170400c20106951403241350740c00d03a4145100000001c20300300100c07200d00e0042c0064807940716901404140100b13100361151078200038180c84400540342c10401004d0003400c5c440c00907000c805603800501031500303841c080d542e071141580040c5814034100380302c3c1c03400c0b02400d080c818010644100300c0160911b8400c0c0200d0a83c00e034003030b85501d03180c4900d40f08140782403502d07140020440081d8900300044801040100c00d42e00d10080e0b0044200c0c507a00980c102c05500c41270181072161001130300e5004104e030007000d0f40d07001040484030030074a104510200e500042c80314410180d020010818580380c095008403044080c803031200d607608120605c640040190040c04900043c80800c00c1805441a005040c400010000c990070103c1000803a200c0c00c0040014480d259041c1010340d4982d03581d4000070724140101381c010841c000c000c40180003c1501d0b004841c3c10032000c400038540314980340c44880d110100d4010804406001500080d84840c0c280354019110f80c000b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 776917311 1250 776916061 776916073
    0x60c031704052d1f02090303030906041e15050c0405100c0b0717150f030a0c030c050901060815040b060d06091b02031903270506010506160f020d05 65
    0x2c94500c0e903511001080d00c1140c009190000d07030484003808007182d88088240100342a03841105200e000c16095a02c0c011400d07001c20140704192400c000640c00341e11101c009044502c2c2030b003022806800c1249103482c24070644400000070a009204c0300c070650030a0f000c002040d0311aa0f00500b2144203550210343c0140d5031205140010350016000e0607101c0c014090221b859541d170740c0c111400000c02d1030415411400002041d905045c500780480607410140c9072040342e03188040081d10b00446100125110084440140100000040c0340c2000704015181a00300b54103084000c0d1101000518440c20060742c1c4100c0003403039591340c0005407039120107400b140c0c0e28405180d240c0003030501e6028989039113060046442801c150190351034405082030f4099420042142010b01c170300340b40550100201034550342d020b20b4048101455410800c00001003030240e240d549062030038084140d1103180704000038402d01040c3c0604100880da29980480a644030b00e03118400288200851600581944509 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 776918561 1250 776917311 776917313
    0x2a0f1906050c130902030f0a05164d0a02060306010305090a0204050a02072f01080916120209060301150504090302010f02120105031603050a201e0406091104060c031704 74
    0x80e9001394002c5501ca010800e641e40d55003d0700d01954000e0741d081200c0458005075003901c03486032050010781940300c13024444009105c0e481d4610091840d00312942032080d18058010003c8800c14114bc80c14031601815100d0120f80001d9414000141818181611000005d000c90400d02c00128507560003030041059050a40e80703d002508030b42c0007125a000c42400b24246200c9050381e0b034400b0f0f030342d20702090306e000d001d400110f0358414060f010000500c685c071082070b030582d203002c0c8043c0500390100100b00a01100c0c01080003c82c0040d0140e4042c1e40340c135090084200e040403008044e940280c0e400b148803901d03480c04a00510380c1c64126808203201248480f042408180e1140c101c07001142180ca01050036100c0380c0e43c40b000380c4270084c182d60000e500c0b14001400c22440c0c6c1c500c603010342e140f8409592403101080b04d810454240000c0c0540d0600c220065141510441c03000e803845a008110506a1f440c660100748194040c40d001c1c885011280d00400d441a01800300c04035840d104412b040c01d00d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 776919811 1250 776918561 776918579
    0x70203060c0406030609050c030c070309120f0201030621060b06041806032d3f02070603091a0a150e0a1d0d03050603032a0f1906050c13 60
    0xb090141d14000307820941c00003040e403024000c1c10702407041c00c69507a00c2c68545090808180c0c0c00342d00101c0511000303510014840c151007035140d01181c081c140c0801000124030004084601ca0b4000b07040030a10281071180b0313038040c00b8041d01d6a5034044000a4a20b200c1c1000940500503a400404c0344061011008082c1c02140c000408407486481c0c1c0550040c0310540074460136001006c0b288060444695200c0030441544c210074109111154014152441e807621490709456000007104100403401054103a6504200540041c039851074104811805540da8682c4511500d20300d400082c901004030312020125070200780489150b9107680021680c9408201c2078000032a00c01500c5450502082c100036070740140c81b0401c03500200a00328520380d80900394000e240180900750948020700c20390760a040880804102e07541c01165100c00b00306e41400107072800200100050302034101c540c0440a0405458a803001558051008107560799030740f2090600f8040c0760340c0b66484ca40050400111205 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 776921061 1250 776919811 776919817
    0xa0b06130e1f060302030d0e1504091a0f01050d02030a0b0a15020c0f060904020d09021002030c1606020a080c0f031303060b191401030f0e01051009050114040f02070203060c 76
    0xb4101004202c000180e10b44100f11049403101a415410003009801118460b22079855501d030011721000421100c5402140950825003003508820303035a4070f400304c90400048440c1307410001126000c1810500c0d40008101d070040b410341100898002c00070640364a40c0d500000310032100034160900702a80c0b20310600e40c0510014051000d8001c043c009160783c2400d100b8005815405040580b03030420800c10702000f94000e000036071460b951820448016030b542c410f40b04480001c0c0d4015902c41804101130ba040401a003280c40c0340c40d01d0034804122043d00424481c3d601c0760061480b039210880804a03608241c0381d10000c09440c080020701818641900e0300030801d40e402000c003000070100420a00110074845012030007868a1484200548845050000403c0d44189000700e12600840030501c292072840c00c0000c00f503519901041090b04801c4202002406c41d400c0600c006e514000c1d070b650340e00070321000c00c500881d214038101039444150b03011282d08941c05402c0f902c0038504090b548849030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 776922311 1250 776921061 776921083
    0x3020f0d090c0f0e060a05010f03021c0b0414090c09070c050706020604030e0607110f130501080303180a0f170f030702070e241309120e0f0405090a0b06130e 69
    0x80c3da40d02000c2540c2601525203803048002405410096080c00015250071250030466000c16400700250508100702450030041d039041c545003c10300214040800040d5003034130b200b00d00c80c000000c0400c0540718002460860890f0251801c1d4216183c014040302c034584840b81c050701910541000041d036560010341c1900c9940203950b860755441c050010003035107104d09a0040c14080104103a406940340030040d0314060300c001007114154190b88009101501d001340d010150a401c04000c00c105001c26401f00c8142902c000090914001a5076038890a6600354002600950100b4a2400038002000c100d4001485c1c0301119030302d0b0724112200a5031075017030f4010718080b00200c40100d00b1540c5091a0b42e0700c0c040d444a24005a1030381413081c1b0113845507048085814680720300d03405000c031305a0204100c00f60495940d00d800341060005000300d480305c2d08030b100c1c0151318000070040c00240100d03240910691040d1051110f0f04c2d0300c4005806401030190700c4014a15141d411254100c0000d162a202 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 776923561 1250 776922311 776922329
    0x1507020d08100e0403033c0b01030203040b010e0601170a0c170c1c1104030c030303050c2a0f19020a080105070905010c08041e031a060a0603020f0d090c 67
    0x6a85641082400001e14414640708000ba03d0105002a02a820600000300012a40e06403d980c01c0040600050490281420403252242c1d0900c0c40c0c2c558043c6400710703c0203080640ca1800d045d074481031880b005109030f0700c40d41c0c0440b01003110f583c800c8a00300d0244000001603480c5083c00d0071294001c1c940d801c20740e0042880f000c591030a00038076103290340c4552560030065081c11076003540e1307030b829199495001441d9a43c40c0c40c3c607000808002c01620203103011320004602c950a510b4041c044407005410311610000c18049854141150145a00c500041c03403900210f1020101100340b82c0800020100460f01541d0420030181f15103800e1008814001c07501200f40c41c1c1c2d5103000798200e84096848000044800c1e4042c03000e9409030100c03d424612901038245480d941707942c6185004018504446400c4500300100140f001015150300b50a018651421407410b20000168490782e01d1320902061540210b044070448004a040d40e00c00c603c0c038036043c0103108103883c000325015144e000b0724007030b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 776924811 1250 776923561 776923577
    0x13030c14010804111c0c030804060f0e0d0f0614040506060a0e0405030d1503140d0e0102031222210206090604031d060c030d0603030f1701171507020d 66
    0x542c80b0300c40da54080e9800062070b61889024006000507803284a4500c12079072485801480050f01000f0f040d00114081c550554803a03081110050400c0540e500500410040400f41c070703501d9694020740088242e2045111203003844602c1c00348050000c0d0308144031071280d810200020b00102080366485607504a421003113840c0c444036a054400c40a49000c1c00341d0307205001c21044543c06502c081d00504c3c1791183c5a80e216541d94400281069150381034801e500817000001d00a03400241822480c07809001a41c00c00218038114100d0741c40c02401d44c403d407a500000d0715090481051151000c540040d0742d410030400d1f034840200c0785101c1c000c018006105003000907110b100c0102e41c0d14015681540c0310042c03002409100d0a240d5404543c240e40007000b000302e58000d0004100a065915100801007001c6240d17007001f600056682814205110906045d00e003507004c0491003a040d13a07021a505034295904442161400490043e0607017882c86442c1404011038002a01200800417a6511a1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 776926061 1250 776924811 776924849
    0x3270d0c03141b062a030c010b15030a15050a09020702030712080a0e060d0c030c0806190e0c131d0a0204060c0b0612011803020f010c0801061413030c 66
    0xa0765000f100c07071000d6038201d144802a0f8030314192004051681208200518140d5102002c601c801c000c8009070340c080c0d00025803034001c0c030800e000362a01178404480354144005001d03d006803d00c0b004202c0008203690740c916000c00454508044060400a0700301000f40d9210f820841c029130181009070f01c20b00c41c43d440003070707441c1241c958050101e80c444030725400e0500c4848141c038101402d1601d03561045051007168422440c07403145503030540065401240081308040e01408500001e4401401034800c505000c0c298000f06080e4011600e40d040c4014103603881507401e04c000d004010f4000303080450301c08005440c6440c84440c0105840d0311b4603080d042d46820030881d0413442688034280204020080726000f00d4041d81ca010390020001d405661750f840b00030802400c4806e104101c4100b640d00d140040241541008600c1010080600030081c82c81d07410401303001000d0510915040107850700490501c00203090607242d1042600c010a04650f0b207a2902b45070084071405014800c40031011500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 776927311 1250 776926061 776926063
    0x10c0305130210320316030b0a050d03170a02030601140918040602090d030f03230c09060714071a03070f080603160914071103270d0c0314 61
    0x2000c990041c15040c01055551041d01c02004c3c0d14006140240710040c680c460300101c1c80d1515220301d0110b40984d403031800c400740c400110209000101010301d40740d00400c441d294214644103403801211000740c02e1042d89230840388104461683d110201840080c40302e60000c40d0051405264242c0b00c0f03204e072044245d1500d980b40110075040b03511040e20f1800c03611880c95420f0250b000750186901502c0c2410b0328021911801d03900e071040700011001c908050070581e0500c5203851961620113501e0b802c060b10000110103210141000f1500c400014007001640e40d058211041c0b1640311000007048601803c03090703102c40c030798441c0c20030b056448015070480d0385190003220b205031080d40300d9508000c1c0a40e1308958803d4002c1c0040d4240c8a48040c0210f508041707450301c0000c2481080200701542040c20002c5007100c0a00000e00f0701a00503405450b0b840044240c0711442d0301088650440c0315900f007804882d441c03d03e109900000c0c0005102d041c010100810000d8030301800c0030b01d4075a1842c014035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 776928561 1250 776927311 776927341
    0x6110306010f18090506120f0604020f0604050609090a15151701032a05030708010f060b070c0e0a060e130c1509060518061c0e060106052d0309010c0305 67
    0x4071815a40b103003c00d0080410550010390030140140425030b0341c6030040e840918000a04080309071591226042004500e003400d075a900713260741070742c1d8503040514050118060f8016420200e1094015500050030745965138080381100c80c00901503c2900e40d01e50300200541c051b81e99220014054103003a010b00102c035114107048075400720540401c00c1b001250b0100c1a03072011150ba45060b000074001406603000c10010740a041c0b03240c00020a04852070003c030440308168881801080184548408285200c1d0305030b00702d800c030412070005a036a0f0948040209596002142030103003038010722030080e1740c046207095464030079558040e4141e2074182122003011100f01020019103004006e019807131240006d05007a03015030b00c940044076101400524039030407601d00d0302441421041d018840d102e4500801005a174800064545541080001001d030710800000000c1a07010402074486140b0b10110924882c504507411a03c1e424002c2600c0c0c040e081c0d804030003000074100404101c40e02d81001701 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 776929811 1250 776928561 776928587
    0x7171305010503040f0b04051501060e041a01170c0d02030a0903030f15051003061d060a09020304080a0302031e150f010207080703022407031815120e070306110306010f 74
    0x41c40b5114446903902c551b40b02c401801240d9500030400d00015680101d4045d0340600b0140c1c0b22241c00c10a040c061108880c4010b9503000074010720f1a200c1d10f140d81084c107803c4c050526420102c040e41e0b46841d40400c5128041008640a20000400c901213407a41d10115419100b17603410301c1040a8a041c64040d5090318070f018140c00e841150803c01b5142282c00421014220b00b00441c86d245e40f05040b80216080102ca40480000074042081c10305d040c8800c8400b50401038001c50541c01d050300e4904940c0070b00706d000000c4c50303400801f01e58140c01c2c40c241c800c221052030720064000e140091901c81c1ca845940700381c9019491248290b600e81d80081160000c1d103280800412030a4919003c01030740c2100d44000e541c1e00d000c0c07034594841007250359005090035030007a101c0701a5010b400c0d003070302100c15440d80816030202c0511100c003541548007030900002c010200340400c008030890781d90380c1410340359030004206514000c43c08140158080245114440980f14075013150684182030f50745451030301c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 776931061 1250 776929811 776929823
    0x50306090f090c01080603010f0204230d03140904020702100c1506050616030e030a03020706080a05061003090507050d0f060c0206160f14030a050f09010e030a050c030717130501050304 81
    0x7085030f09548a480d110703034051b000030300100c1d034110a06100c408a90040d0402c00d0b251542840903078245003107003184981c0003004e40743c010800f6460b0b2001041c1a810028200e0508000200c002c01e0760fa940e010b40300c0f0942c009241103071322301e507101d0090140074407001c3c12909110030540784100a8039030b10a6404a50001e401145410100e51901c1c102c60546034046050015665040409803420400011240c1c070980060407a1418140085c0070854000e0019610034188001c10a13252142503229409040c20304010801c1d20051a0850030080d1a0700026005034402060b5410300c000c0040e1705480c42d026203010002001203d0f81280c640108641c0080040c911241242045202d911410341c451100e00d44908007180c004001682d9a10560f170071035115840f9402e0210f641400552241c019500e01c3c003c11120b144820b107940c0328004e66030302c202800400300382142d0518040c002c69403a42d9101c814240d04d983c43d0440c0892541124045510701c0380d095402041c02c0d401401202c2c01150021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 776932311 1250 776931061 776931073
    0x70f0f0306122a1d090a11090a0e0f0c1302031e0405010207150b01020f01090b01171912021b010c0f240204150203031e071e050306090f09 61
    0x1031224041c0031480c204980c803242224241440000007046010b0241c6005404a04c0c840c1d1515421812601c0150109503035401404c1e0840c00a030181280c891102c2003911441400e81c2c42c03500081c0149600c101c9804d860144d10310103007807508040303840156a03200b1910a221001c5c1031512008a02046508420030035030007000c115204c3c01900086d03849482040054074096040d501c0d40407140b00206042c011545880d440340d2150b8050081061200e50f110003041110b5440e240c9110a02062058420808403005e0070441d035032007880a120003540300c2018004507100e51800b40310101d80c0303100703210050103241e103160601c1c0700c40c54a00291040c1603584548041c219250000524444101150720ba81441414620300b00c031456103080700550365000517100c070714050182c05e11502c0611100215001003080005028000c4544202c0341001d600980c0c13142c2d1014015600300308107a10200384000c0f003604121103254490002c0d03118000584606400da200c81e10050f00954007030f40c1c2075800d50446 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 776933561 1250 776932311 776932313
    0x91506020f060c0306030a0c0f050f10020d0e03030c06010b12070f0c030e04090b0a0608061006140306120304080106080c1c0b0603031c02030402040b090702030d23070f0f030612 78
    0x30300244d50005801030039212940055642d8820b08a007581c4094120f002d0b0480c04c00c00c5c1e02c0c1c03071010a04029030682d0b04210203080c1c200d00a48500241c6040003e0007150400c41029440800c20b41c0d00c0a80d01c40101c0300c1e2549c440010103c40e8100030100c1600241150010304064440d144001d8501100d8503070200f4840c1e159003c2e94039000d002529a000340d9102c0001303021500201e2080d01a620f040400550f20b0300b010080c03418007000400d20201045161001c0020551240f88105e000c007058010b1500ca4032000c0004d52905440c0614034414400420049002d4030190b200b00d00b00c50481088510300300d40c507014800000d04030680b44041c0e0080c00e0b4124003084003118100e6003c0340040c260307854180350b00c4840804110030b1000c1c420b5254007100b044210b050900c150400060100c400c4281441c14160081d900d00c40c1600308125180c9400c14031401901c40c40640d40d0070300760034407a403071603103408240109403201d00e01c9484001741c481d446500b03034107000b44a4401681c0542e000b8003007100309 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 776934811 1250 776933561 776933581
    0x1b0f052e0f050d050c0306030106090501050d020d02060918070809190206130819030806150415021f0203060414040c1509051011071e030f0305090a091506020f06 71
    0x1c10000c80c824001c003081440d1440f00c06210b214460001c00f10704035140c0c14043d080c5400c4800c01d030050302e003240c503010040c00159240640003440560403620324001a14034404100b140c010800e0090b000135104440888e0400700c07900c0c00703204000c0b40e90360800c82d50f09c4020389075441b4806081100380d4a074080c050400343c104100100001d551140c2c003c01284c1d0b50301c550343d240001d500380159140b0b10140d00b01e0201a805441700b5080001159800240410504103032028881c1c0d11034a02c0c000c030146101ea612600074044041030203103000ca0040f982038400c0c1d900e000781d40221030261145207049002c00b84c2080185103140034580202a1585840c1440300c616211405010b49009201c45940300080a44c0d80c24844141e10350340390744200b65280315a5881e850640d003500484a103848a000c00c10f40000340b4404001165001074401c5030106d801e09042d1020f00c1a4000c254007e0100d010101f05044280c1221240c4107880058240700c038be80b01c000302d0311882c10314a1240f054002c0c42c049440514 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 776936061 1250 776934811 776934827
    0xe090c01090918020d0809040608010e060a0c0224011818060c0c150e070f0305030d20070b06150c06040b1e010303020c041d0a0f1b0f052e 61
    0x700c4070380301400c0c0f540010f200300860300000c865128002038a12207504207400341e81d0080c840c00c8000d200c4004501101510703810000c204441090340c84803a01185403003042600002020340034a01c0d05880e07000501e24140000f40a0080c04004e42c900384c01d00040c491049407848000b04e40380084100781e940d01d06020704a5035400004100c0180091404150903014517071a419a200f00001d094407920545810208640e120280380b803000807042000c02c5000c41260800c40c0d11100005602600e50040e01c850042040c0507071a01c0c40201700030041001c4119041e0003940d045030a110b214807500303000102d61060510184450b0400b4010400040711141c207a85c112001071040c60340c510344904d0622004030240e00a40c016030028121500d64101481450513452441e076240d05029001c0410555444408000034100310004000340d0500140b000c0c12151621408070b8142c000307545110081d000e820b02d0040e40d100f602e181c01000300c3c1484e682140084c2e0280d41e40d59046002181c6426280d440c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 776937311 1250 776936061 776936081
    0x70813020312040e04050c0103110d020d15060e03011a060702060c0304120c0303030c0e0904301d0a0e0c071104020a0306060210090803220c06090e090c010909 70
    0xb02c104068409001c880c0c10180003d440e900181c41050320300380c03d01c20b00d800643c0426a06040c40c1c01c0b410f161840104044900b00b00708020096a40c0c0070b03510300d80c0014404801c50403940416507001080c0ca9521021114869008600038403150b101f0260150050100341481940f0800070030840c401810582d015100c0300700e41d201070b2400c0c241c0d1000304003041107010b90112803031180e0325024010103030580703d440c00c440c0c1940340c05164440c1e00e801250001c503010f030010340b0340c10a1040513601c0c401107200e01081010700c00c040d0400700000320b60140c0f075486a5200b8030900401c10101e4400c13401c0030440002161400652100c490b00c800414503416402900c0a540803c0c1d103032859a42500e5038002408000060b44d00050721500d01100241040d640031003004c005800c02d00120003051804040d00e4000081d80310300d031011b40c5642007901d0300f1440c800c0f0042621011540009034260401c5060084550b034040ba03201c16034070754820726286d50343d006240780070580c0e8080c180003045403680300800c61 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 776938561 1250 776937311 776937313
    0xc041b0f090b0d150b0d0e0d020303010302031f180318080316020420031003031b02010e190302031c0212120a0c03020d0e0c011206080a021002150109020901170708130203 75
    0x30f02e8994071641159407141b018482d16a40740c902c181d0041c08104500800f4403480c2c40694155411503000036128001c007038003a4400005101c01c1c1c11946416031208000700c5100003180413804a519018003a0f0741704104180c0118034414000461074070101c111081030205d16040038480c00c07594200f00c0104100300c4030400305000814500e1032014080c008500400b901580c0520841c650301d0000c00c1401149810340f004c03413071081610f0050f6008200401c40442c2114440d4000940f8090290100c0a43d400a581481100350032030040110000c42d40d848141542076511a45050150161078410b4201c540b10301c4003400c00144048040d680001e4900000c0d240c09882c01c02309000320f00070358075030394050b181c150003141c1d10b148250f07040344d200d00d07031107003e15070a100d000e140c80076031502c8400c40745c000f038080d140114504800c140b0034001030802602080080e00c00396142c5403090001c0d00004d87d100d001c9050030501d00c130130140d814121032288425550742c40c2c407a520024201405000b00701d040b605 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 776939811 1250 776938561 776938601
    0x510080f061806040c090513090506131e05030904020a110c03070501080a0e01020412050d0801091a010503041401050403090e1b0412030c020a090b091b03180c041b0f090b0d 76
    0x107e90f07143c00c504203030803d1006000c51041d10394200b185c00d252024004015824903064228009a1850304c0c401714034505a03400c50705203845050403811031188000c942c8e03025100003189030001c1e4121541e03a8680307442c00100c3c0c65070741c60441850356074008c0b0b02455010500c041c3c00201c00c1174060300038080d0b1101c81800541081c1c0e4902019083c00a2588100c0d1150405d40c1c80442d1550302c0190359004200c045010700c1400e14100300c40c5100d5032a60655410010004001001e0110485526115555100081283e13103003d0074010020a118003c0c03100b03207520900032400d45001404114140c3c84100007652030146050702d5122907102c0301c00110140304544a160380943d44804080c030040c0904107010800d0790b20b910400c81c203680300030800544d25106044440c518034610003030302d0b400192034200c9202014450305080c50300c2c041c80840c83c0e10904200e02c0b40d4200003169800e01c80d4a500391a0b60440001400b41a52402c14a0180c0c5140440501c00e5800200c456004065245500072810103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 776941061 1250 776939811 776939819
    0x912010908040303090312090b040b0702220501060206070e090601030c0e0a030c06120204080c0409260414090405060c0307180b0403050f06041104150510080f061806040c09 76
    0x1a842e04150320035404251516010418424000c0c00306d001e80340d807460417003041c40c184502541140038500800d10505130106845086440d0112a15162602407014452000d00f406440010382000d00403080140903c0c40852025402650f8044522800412100560703440388011001011007850540030020703003102500c0d4503201d080110000c2d5000c0d0303444501d800c2c203201000d00650360705560545402d104200c1000810404a80e000450004a8002c42c1c000500e08140700c0c245148907025a00c00c0b500000004503082001c000c0084402901c001c41148078224204118607034211405450340e048140003032003200400c4000d66003e10241042d291500404000c820045621340040b004048002000e00600004002c808078086403a4014007840c40e040e61490b503890044010140220b441700490909005240c0a42d806014080e208029072644540014010103042d11190003000d6000b0220320315007001d90a4080044824507184078944900050000804103000303100108904030074042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 776942311 1250 776941061 776941073
    0x18031c170411100c06110c100c0323010f1d0f180a03170c031e040303060317070b091b1c0b1e090303070e0f040608060703060306060b0c0309120109 65
    0x44910b55040c0c0e20444e10540030701d4102c04580c0b8070b1854801306001881454210700001544803c0041d103103001040d0034265140c1500038080b138082c8000041e102141001c0007140c1c180300b207412580c40e40c0400600e2941d822080c0c1032030018035880b2030180a00c0000616000c0c0c182040b40d0023554424402141160307002d1038504003111828100d000510300101d00281050b00040380d50481c2441251038550704210303102010f805104c7c40c02c1c5c10170301c50300000201454026400f203001950000065041000040080310842c3c0c00940304039042c4401c400410082c1c0c5000070410003031024400600b800110701001c010f17640060b070010440031086c1210301c0f070004d00c4e6084558001c0d080e20408040d40009106054090203006002e81c60f503a00600400282c15030110304400741101c26240381d5000004070300410080d0403039030040361040c840e10041c40380c610360641c0a002128003c000c20014280c550183d011f9900c02c001807103025a20030700851106141c41610400751103880030002440a000343c0e607078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 776943561 1250 776942311 776942329
    0xb09100f020406030608030a020c101707030203060909010b01020303070507081603050304020306073212010e070210060302090601050f12070806091302220f0218031c170411 76
    0x901155030046410010f40d60540503840240c901d082c0518200910180700958070041051440c0c490600c50042e81074070360045082008103500000d10341c00750b182000014001c0d50050303940034002c035506000a0903052041c4180449054148c0c00303186151141c1904542d0b40c0c2003141c0544120f40104071401c40410004078824a543c030a03103640740c413483c00340101424407400601c11014004038031a0081c094202c0041034100704400001c104000c2c44810031344046014044039269510720400c008121040a40c10307191180602d40d0846203219441e440c0e0109032903a40c800250824410004949290f0151000d0050440ca42d00d200c0e0415200c0303c60304400e4034083c0c404002044400040c031245040a0a40b15030200440c14640c15403030301540031860750410403070007020302c010030031090084500d82d400a41d0042c107d41000c0d900c965180548044069141e8003a501c42d1040c0c0320040c055020241165400c400790b51240c3c0b44400c507803107003209a100014422902c900318030b080000300355201655 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 776944811 1250 776943561 776943581
    0xe010b060d0c02010c08190522030903050c100207210206130f0b0316031d0706180801050105060d02090f04021b0601081903051608040e0426070b0910 66
    0x4601d1142c0e0030b80c0a0300b110340003082081001081010440118030540d409030207500c4551000a582ea14950800c0c150105051442801c1d11142030340002e042d48013000c0e20a40e8080d0003a01c0040c06004204020103080c45540c00c0583c00c500390030040514a00c403081c2c80926070040030300031441c1e0350380001c1d156449001c80d02c94050040900703002803a40d807490a070242844041c01d0349941440c030594444524214140b00030541c0b00c88078001281c030044048800100760000b100e01c050b407191000390500c0c02c0d40b083c50303e200e44c880400080c80c0005007e1035040703500291a480c0361554140700d00e00654060b108080e00891607500324062519144000c184088a9140c915840d200f10302030076040c20010780c01250980c0c01500b01c2e580b103034841e29140c5070255150424a54902504110103d52481c00c400a030644001190004010911001c0907200340c1c807407400302e60070b41e0800c42c8002d40c00c6580100c00105010031300026000a09040800b074001d1359650031126140c5842c00000c2c1035a0110071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 776946061 1250 776944811 776944837
    0x1060803030f090304060504150c022706060304020d0b07050712120b100f120603140c031009050d050304240b18010b070602130306051014030a030207090e010b06 71
    0x108030b5042862402250404020320195107013600e007050080c010f0289014a01058050480000d680b07030182402d4000700d47c0c00340c401c15612000200f0010001d001e114401d07042e01c042c000050303d0745000300c1102d110399030092405a0310026a2290702100400411030000e10404128a0001c00d281401c40c500c4006c4542e110940300341d034a01600281c814090700c1c41d0107110020034620300180c0050710041d001005c0c4c075007004010302c091128406000c1aa1000d81807061064881069a90212f01c110a0f65400d4040f200010303881050f03102295200480585203811050b19101407034419802540c0060143d01000801c4034820203c4d402000d44402a51342159103400ca09101e0504111298811658214810b1550300d400000001c90dc03c0403801000c0341e80c0001c15001e9800901407980103540c000740100001d151012007410506904d014292020813803a2003003141c0e1030300044032401642d150380a0511301c2d1519860380d014007901008081c2070b5482e42070804064880101420860180356 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 776947311 1250 776946061 776946067
    0x80d0c1529031b040b0103091703010512070608010308030c120906060111030a36032a05010512060411161208040c06080402030106032004050619060e060c01060803 72
    0x1d03001619030034004642c081c0e001400c0e4011001e540711603082c1c80160a903400300381508064012001004400001088414100f4040810680d41c802441c140c6505481c40d000019a0382403540d0350360b005204140c0040c051100500008055001440e00800c41e0343d8401c0c280b0344908040a2400c1e8110756000345079000340d080080b40d680c8116081480000e903c0514540541c101004144807090180c442c40f4509080c110780c2424080021300e00841101d036440d08170f00da00e91505003808403400d61203041c010b0f000d60104c0b40700b600301003514080311016115107281c15482000303090042001405180d00580d0b038610384503000c0300b040080000c2c7e8440500010315020f180762228a06680341c80b030400300911b807000c100c000360841b00ea013030540788941080e0540d5516440024050010742d08010309903540f01d0050300c402d0003070315018017050324100d5051106a4a0f82c0031b20940100c01096600480d00f41e41c0c0c2009040d000b280c200042c0380f40600807074500900c0b9201c5500790b0340c581c2d201f074040342d01c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 776948561 1250 776947311 776947361
    0x20d151d010f0c03290a17030a0210020910121b0c140f0a15240612050403080c1c020a09150c080d050c0c07060207140a080d0c15 57
    0x1840b410115900604007000740c05c0d60315820307030310700000584901c410740f50b26003d1a89950300d042c3d420000386004460b40750507035018a0050307140d0300f00061200142c820200c604005100b40d00903100c8081001d0700c0c200310040a600c040703d43c14001c0001340c3d0269941c0040041c0c0c0e4090000100402c034454841980040e01403400032294400702448510a404c54061300300802c801048507640c540d0003c58200d590514603078620028044e500c921590319400017000c003103e08c4210313004011940161034006460050400d48020b941045400600061500002a0700d51014030040c00c0301c14485050094094002201034040b60305c04c00d0003030003180056004000b50407001041300e080604500d030101d4030300015038030f448490260095004619440d80005004541d00c0c2c801e950003101100101c1d220300d03603203c0002e910340c0c20078040c4038005200c1644400c02402d00d03480d101c0c102c85040000f08403c20164600b2210b010940c40103e880c0341d600402100c440845008001e014000404464080482 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 776949811 1250 776948561 776948591
    0xc08030a09080c0f240108060103021504080601060924140d0906020d0209032107020f01033903020a0e150f03090c01030b010c0305030f04030504080304030501021305010c020d151d01 80
    0x8040400d03402d0614542c01440b00401c0848d0103070450340c4c152004800b15a840c00f03400782c00c2c003e540007020749100e07110000070704a50061468044030310501c048a0310920001010780c040c402e00c503c8a01160040001356060360400c00104890300b20b548000411358816991001079034040c0000c1da41180e004110034100b80790612100c651064268010f490b608038400003c0810301600501a224103203c00c0380d144980d000b5000402d0030a4152486e0380082c40054164004402542a4200b01e0b13006e104c103410310501034800c441080c1c200381c840034100c1140c5020400c10240002527803841c80c206101074180010000007542c0101190790280441c4c1c084c0c440010229803076060302c0f904000ea0080301c6408650403208694128038000000a0b05039158103041e6070610450384404141d20000400009011040d0302400c0d14a0005000a00742030b5910011100701c040c0d264041d41c0400d00722000400128900d01c0d0b10501c454008022650440c8000e51452181c818480200303140d454403190020500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 776951061 1250 776949811 776949853
    0x30c020109082d070303080f04021519030f0605060d05100906170c060310050d020d1b0e0f090d11121603020d17220b010617070c08030a09080c0f 64
    0x2e02c00c0100505841d503280200140070150070201c0d00032341040403070f041d91684503d440c42a2003100d41d079a07031420150444c0d150365010702d562400092500c1c0071415040541d014074021a41c0040c0a0742c14001040b14240081c0b01c0a00100340180b01100c00003000c003c9800303114002c3c2849003102c0c10340c072030030801a4101010300b01c425124400400400480212102806040e80c005440000c0b07069014400702c1e095044600b0050b105654501003144200340d140c4080381a0f943c44400c410751600c480e014004001c07001c0c0c1d100885a04031000c800429489258010040c0e02440203c1c0c02e4201c6c0030306a09566032104603501a4012039891600500d6010480c1d45011441c1d441e003231034401c50201c1e0b1480c11010203013690500c0c442c46110b509024009909420700c45400000b40450f07540d403884080c0c420017051447c3d407122108800040d01d0b0a01a0780d40e010101d03049420b061950b52030620180080042040803210300c00d00b03110800b0101020462002e031000c07102d0081403c0110660584c0402d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 776952311 1250 776951061 776951143
    0x1a030105040f29160521090d0903050a020405060a330804020d02040e0c0402030c070215030705040303030510030b24100c150209090c091305040f030c02010908 70
    0x4102c08440048111039011404d40c402d020000b901480f540c0840200d402e48102c1010403c94904400340708040303407400703a040d40111100b00c101c803003100f5882d409440d00c9080e1700c00501136400039040200541015000241d010707030000c0c00e078500c442e140c01c41035000c00402014440c40e81030b06c4131b030110b0511070006444044006400c0c010494903160303000481101c60b8941c000e0182d40c681c513115014500402c0313151901c2c580200b003591a46841c510008240d04000c0d802d80c403421008904030025481a02100e01540040d9101840c050a5031810b50142901402280c2101000940003000c9040c000ca900c1c000c01c1e20440794110032a550003415400c0b188400903521508805a100500580050302c0c0184194021003644032035175404c4001000b13000750f140c0e080c0c01040000c100159946c59500030b00818000b2121159032904450188046610440d0002d02d40000b403040007021034080c0d041030400781d105141220445480e40c00060805a203010241d403500c6281400112440100300c40c45008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 776953561 1250 776952311 776952353
    0x1602090f010506090111010b0a080c041b090e0705120a0b091f0303110111070b0708070302071106071b1e080d05040e0a0f02160201030e010c050d1a030105040f 70
    0xa07504180009000b4850010b01605100c45040d10548130f880030741029000d004024601c11007a683d8071085a25603041b0b0040c944194688918110bc000781d070a00304244842c0f50b51030400440c00c110211024103806003041081c0b0505012000c101c51050300100d00c540281000824008014028403d01d440050081504502c03003103011074001d1501220101226014600a651805a20f40c3c19004220715400c0d0070035180000384c48410300010f80b00c42030251015030b81c1c44040350b0b22224102c00300e002e0040002c000100c44180d411043c6043c801401909010f60850b4489992540c0c451000744003a81c050304e020190382035001c96920707036010903100a203140b002910034030a0040b0001e200380700728015080e0000d40ca501040c3c1c4100036505c000d100c45272107401103550f011118550b0302587d01540d400c1b0300290070550f07040450030060041c0c1e501c90303181c0e8031924100246045a000608041c441290300103000344080f0702c0e140e6090050501580c0102141540e8507064200041040ca00c50640100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 776954811 1250 776953561 776953591
    0x1506030b010b190c121218050105040c08060105010e01050705010f090b01050109120b0402120f01090c050a080f060f220f03030b0111060402060d0207120207061805030a06020d020f160209 82
    0x32841801a00d0401d2280349044824501106d0810700242040d580c40d1040e50004120702d000c2001c154803140c05607005025401c1c1e41b5a44103940c0e07a071201d007400f50300e00040307040d01b10100c2175004002421010340b0950011462030200c1ca480301c119071451009444059a00700100171a5800140b48130240542c0340b07078074400c00d8103521000c1c3e0100d0080c0c002030042c0381c000e81c004003c81d02070025002c01c0040500070b00581d040b900744452410341a0080ca071250500d20000269200b0002d404185145107401a1186a40c0d0103104559400002d00003642d420071017841400500ea140c03080844948500780d00c04c03032000142801001c5a054420746410b10407120400401c0840003d68107038407560448585035a00003904480e03000e40035811005201e4403080001403603003500030802c1000d0311341300d0ba2803801c041c040f03403400d0441c1845e030310030150590015440c10340494540d4004191441013942e0140ca40260450040c0e40350740101c8102c410460b0121080c802c510f0b01c510b9580c0c1085500403600e003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 776956061 1250 776954811 776954813
    0x2d0e040c0c0212120f03250c1103030d2427091a04060b01080603030f2d040312110105100603090c2c1609031506030b010b190c 56
    0x40c1e0704100102900c2101d4803406007502240801c2010725100c0301d1990641c0b96000c0c44140422a007041c0c4002d03039650380060a1a040e0034456120b8881720303c00780e40d054911013507500e4043c0300440921101c0d4250108001102c42d106080c01240310100d03403024000d8040760b070100704600c11009600000454480d80c510850040d40c40f00d00a80350080940c40041c10b01d446180c1440c2d1800800280c0015240c580104014810301e58031207044070724280c980ca6120b40e902002c060b01da200d034408098000c00c040c40290300c441e010502d45011142c8503000d414480854521034004c5410517031003214100501e03102090410343c0244030300061303068ad030000e0042d410030782e0701d0a203102003070b000d00c80401d03546040c07110501c421441c0800c01000209100e58040800100d03035201241186410403400081c400402c02042c036180110403442084d9079014401400c540c0e0700081c10400340c0402c0c0c4515128403000c800300d016040600d0081c00c00004d0380e40d17151942585810182640142c601c140554120414 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 776957311 1250 776956061 776956067
    0x609090f110a120f2c0f2823100b0303040603050a0906050403021c050408070509040c030b0a0209040e01140613090b0a09021c0c09020a2d0e040c 64
    0x2d0151001403c1084640980c074100c100109290001081d01c9404d02001d1421856201005004d0314100640703401d11000750348002d0342c0c034121002d080f0b81c0b41d40320745441040344900d809180c280038446140c1629051a544442002d8090707603072034007c01c00780c1c405060b00611040100c2d5038940103a900500116119200091b200d0060b441440281030b2030300d0000d000e902031b40e8004000941d201b80100100c0c01c050400a50390300c1408508600d2510913046496244d016070151f9044030040c2c401024818145801d203d0340a1000c0d000700d440100407907020000502c00542c146c461043c0e15401030312100340200b0481951004071140d050790b45042d40141104000c0c010850f07110342c083d10101d01d01041c61809000030464481d001e01b400c01410140098420b80b900071455040c0201c8085071104a55640c40720032000b0710000400817098042e003048800d115801502100000d424250500398485414801d11076608603c003a890802c0e1520001ca503411840e500440e07d4159000c02101d0301801c009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 776958561 1250 776957311 776957317
    0xa03050a050307030e100c08011a0717090319020a231011010c02070e09060c1204031806020f01050903040f12050307021518010f0c030c020a0b03010609090f11 70
    0x14010004000300081403c0c1c001c2d04036104503243c84044135407030a40c2800b0b040c0203149003a00500000c05840000072080400503100400e5850252a1898500250349005503034911345543c20740403105005252040c0e505102e2031504240200c04806403c070944100008150035030030104030710340d400c001d070350030b6148864541041d4501581c0441030400b00f41402d9a945104001810103582040b0342c803111030740d000c2003500480304d007104403440c680c076403064554a541003118584050320003800310101c0d000d40d00303d0807038010740681000704e15541c1d2544003031a07000c0c41383c00c40c0c00960700001084c2890b440901c100c3c0e81c1706504201a60070541401c403900c0f15012107100d065011142c590310f8130b040c024144105c80120741d00401400420450300700d04c140301d80018138042030854418038211110350140b208809007200550b94148440f0071a6001d46040c20311801c142e810400340e8030302280346070011000750701a100399180c2030901442c0c003800400340c07841d04840314004c1d401d1401d40441c0301e94030b10503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 776959811 1250 776958561 776958577
    0x50a240f08010e07020f011a0102010e07150c0816060225110f03010204091805240103030c15090503090a09060803030115020f03040902040603060506090919061d0f06030a0305 77
    0x3d040c07116110940124606102c0492812455103403201443c515406040d81030000c1c1e5080c4c009001d1043d14813041c50303d40109200383c18003d40c0207800b21038524403681d80d002007640300e40a02d030300300042c041c2814841c05071340204a800a85c001a20b49680d41c001c4580c400413040d243e030380c010540322551151180102201e1003401030300000f07490413440c2d41c02e406440c003900900d8020071002c043c040403290048100b880544542c00380b0420205035580a4255a00e441400f00303404045918540c4d044410403a02c0109541008400c0c02c00f00303055a0302d02500300b0130b0780100b0095448103c442c00700400207110b680542d0722680380810400c42542d001c800e41e81100e6001d000c007001c0d2642c015007a4100750303054100854074000090041080e40581d409403059a02c0f07690308000c05a01c40c4c06000d034510500301a940d0140208002400c0e03c41a0390300351200840da0040499200d40c0d801c0200880341d8020303400c0005865442c01c01801c1200e13289200e41c072000031002400d105000d900c01410621070380392 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 776961061 1250 776959811 776959829
    0x9060919020d0b0603160806010203130b1b030c0115121104020702180702060420060910030f1d1902101b0f030512100506040905060a050a240f0801 65
    0x620068803404503031050f10b80440160029681c1d14016445200700405d980c0e2980200b03001c8804240340b5407000003507403620070b80c26944942c1141448014000307604480e90420f000c90301d14241840095043c40a06605402c2c0780010859a01c451045810154140c0010300e4070060000d00c007000c1740358681c40441c0c0107816140180d4442c0d0034000704124000c18074120388803910000900070b1042d4009000d511030344c043c0c0400d09041100e0a00082d40e1030075100d92a5010100303002a60305803400d507003c0034198030981000668880303010042c8040c0c510041001d00080c803000c0098050103800d200c890500e4102d0341003070f25100541d6002844d00c4580c140000c0c100004070810101421185a06201941c2c2010800305242900c1c500205242c0c1302c41042c014504154010400001200c80d11105071600204014101401c0c1b01e4840c0003010000c1181d54845511500080c95844602014001d4802060581020003690000090312903036080c0b00e00421107480142014258007410890554059074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 776962311 1250 776961061 776961067
    0x30a080c0918130b18060601020a0f02010806011205010603020a0e04020703050720060f030402030c090f18030f0a0c0b090606060d090201120e0717070815060607050109030305060906091902 83
    0x1040c0ca40e8840520080203020f070003c4030a0040c95441c00a0110385c11413035504442e8150b0342c01004a0300c41a0740c0c8001070854004100c0e020040d801040d0440c0c0c0700c0010b140001e0307941d4540c0c003d04103440302a4400c0b000310380c0c0042c0303c000c0329510020445072810182c1d0190304e0f0100c07580e80107019219001380642000d11100f0380710f000c4560300c003401e40fa00100a00c0c0c20741701c0900a828075419801660124803d12505c0d40302c80d5941002504140b1031110010300b060243e88a0890220010b40c2c1640c1c0039090208002403114010400050300000c2d10310f64400041441505c1c0c58001d800002d000868240e02034000c10a265581070b0490700c00c8034888170042080c0301c8c5480184e80640407141ca42030150301f446070410520500050020440e08822519a6540910410191500100d000b00c00c4180c0150740b500350081c0720f103615250441c2028105d1840d0a0440e2100e07421100c031035004400090301ca1042c402245440316005401c0001101c80401509207404007110312081e0b07020805a8075004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 776963561 1250 776962311 776962321
    0x207090621030c06140a0b040b01140c03090d32030a05130b120a1a0306041101020a02090f09060a020a020316052416021603140a0c08030a080c0918 65
    0x443d811500e040e800103013800b121560f8141c0c052524001c031a44881b0a14007003401003d407810f401240c01c01e142c1030b1030714222040b4505903d0002d0740444017206091204220161007511151714041e0114002c1704550050204000601d003000b0119064009118205140c45920a00801115075031074860800d155902a52014030341108941c0e0f109006260002c83c5640782c2d600d05074213a030320031540800d04000e450004000c8192034043c1c20400f58260348a940010300285d6800780412508005004894800c0c0e5141c5c0080ca425a0441c0d4036189848404148500c00c0e8040094540000300200c056040c0441c0440007552802240c900c100e0b4a0518034140050200034001501060f8011014821071113945610030500300c019501c5880e14854050810f55aa20210320301460750003030b00120650310300d16140c03150401c8500144052901075079146100140035159403100402202c030296032245880c080161200a00800d0202010b20400010850f5521000000034000c1c02c1e021005203a03c41d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 776964811 1250 776963561 776963567
    0x51b0304051f05070f0f0917100e0d030e21030709080111120a150302090403090801050f06040507080103150c02100f1b0e0d020108130b070f020709062103 68
    0x2242c0103100180341a014110101400d5000184a007a4545444014254800c01100c202c01680d1a031400540c6201041c01182c04a0400c103030b031201d0381c60440d201103900344000c1c812111802c811041076400101d84110503509402212410407410b00504800f55000f034030b030070b103030810200000d260000000008035180d000e401404050000c0c1d2008000c10700e5820a0282d85520140078800c50450020000d11381c00311900030011040e018902c4071890910b0340c0d0a00070080303406001107040c880ca2920101c0d00c000700348206c038442c0c0b5111942d00040d041c40e1007840112a006014101000140801480480c180500c441924140c0307003c0041c0c3c80760341000481c145403603100c04107101800c1c070200c004410701c150400402e92031164100d003002018400103a8031054031184403038016590b403001303501643c02000100e0340018049826a040384440e40c403c49824801c13180680440e01816500c48a140e0411041000c0c08409504000490812482c0e1809041c03065540003c5000d009584c0c042600c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 776966061 1250 776964811 776964823
    0x28050c0403030c0f2a080303060a06033201140618090612150403030605030a2006220303090605070b013605240105090108060616030207140103051b030405 68
    0xa0400001c0d100e0f0100802c3d070124840811410002e68185c8040102e41e244011080300d0240800a2503808014640701054000d8460001d15108406590560301e6043c804140c01d00340e000700d0080014035943c140a254a41c1c504c0501c99070b4095030341840150303441d01c9a440d4001c00c0660454020200307a1364940010310b46112554840e0050181482120700500044038140c00360f0700c6600c4c00d00c80340ea02c076130500d5540c2c3e00d0118050142c58041c0c841003010511000103551018020b85014608414108200c01c9c90404070707100300c00307603400703980401c141030340a050440641481d144c000d28001040d00c59030041c003018020085004404e20300030032184c2050400e031280031000842c6a60b04030240d109000188401c030b8442905030701807218200391885900c0c5401e413103031058440340e00781b03502d090046500e4480149484c1e00484104075020421905204183d6600d01c03e81c0100419400c142006060100d914042c50500d8141024061050210700b82c0102d45a0329510b12a101c0d0307914101240b82c04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 776967311 1250 776966061 776966063
    0x1602010e0f0301060909051c021c030204050a030f140c0604090509010b030105040f0303060f1d090c12010209010e060310051002160e010e091b0112021228050c0403030c0f 75
    0x144c03818000042800050708150302031405082610701070b42d030b401d844108050740d600d41303600180c01c0304100039018419140020740c06042458010b0070941c4540c003243c0440c00d0303031308241c80c850581580201006980c018500f250100c84000e003e449000e200403a101d40500d00403498801d84907000200130030700135480800d113404010004e000600b81400c00700e40210116000381c0000b802c2440c0401c00140700f011101c101c2d901004038202525207292001c4005802411404081c0120030811106584128200c1c105452403400113a0390305c1050009801521550700c1d29004540030700800480742d088100038421a4415103418101060208040703040c5001121024000b840c1c030903001c5014104155014140c4085900d801c070745032103e02078180c0d1588810070800910448060718030a9500c6103440240701d503c0000c0160a141c8441d0150304d0842045a840201d4115180000041e25039103002c11616014594200604d0402707680706580c91140f4000542880960b01c203403c104540e000c3c08024035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 776968561 1250 776967311 776967313
    0x30e0313090b120f030702010516150507121a040504020310052a090a15091a09010912030e04150e041a0a0b0117131202010b151602010e0f03 62
    0x5161180311040082c6a40b0706082d0186801035040f03e000d07034002903902d04040300400194100301050740115242e80c040250b138458100d01c2c0d20000005144640a1b41400103041e0021030145402c4a00920306041928821401e030b0804e5907000301902011000c10f5486020341d0041215a16400443d14112080303407a411051b141504002c0358031b58406e4508903007002d5070f00120104c81d440f9401c0d04280208040150b100300c030312204120000150009510031400c500f085032000d5503420f80030f003904191440135140b89100007031102007913034040640005442840c060007900d05641d140207000d920030f00b100c1d80c0101c4da2000300300105d0460318188802480416100d0340c5920f004e140c1640c820190004d0000741e4452413000c60050303500b134001c4001001e4182d5448600d1000c0b00074502150402511200b0004051240400410510000010356188580000c05e8078281f50701030010b40e0070000307002a41510144550042a800700d210040130700d40901e0705906030402e20000501007903001903840e80c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 776969811 1250 776968561 776968597
    0x30219060204180b0609040902040f0c090302180708041106040312030c02060c0f12041502030f090c0a0303050f1e0a020a03080c04080d08040602090405070c050f1c030e03 75
    0x4204041e0020816204040c05a070500b44042c1c9030780b000c0c0e5040b80000c5a03c5103007440f800016082560009803224001400407858207050714a5804441d42d804c2030380c2c0000e0070814140f09600b0181da21a80314008002844450300d002c6000812055001d00b0061864484038035490707041d03680000b42c07000755410114201c03a050031690007900074903c007121031000d0b0050600140781052080d0681da0055040080c69190040c803080401e40b1280041c81103070041100f49502038141c1d4184051482007420084810a5040090341c80e0b00d0000c100c203640c0d224451004c1d050000a50110607a0203090b030300d200168541c601c11041064480c6000d001c5000d81c100450b0303241000790f00081c1005114000d4441d410652225022880c982c4128011502503a010784032804a1a22842c1426030290242500500303111404000800b940d2040d036884002801c00c1d0740b0f80051080c203000c901055400d01000301603107044604d03104c0140680d125580c0c181650340d01542c000407424812510f10b0110207000240c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 776971061 1250 776969811 776969813
    0xb12010e060102250e160305180316020a180b090a1e0504020d0f03030507030b15040b07030c0c1215052701020d02030c0a03060803030705090409060e010f1a03010603030912030219 79
    0x20210359211b0350400001e0a04021900316503101c040d248040c0c41c400040c600e011110391075410700d11042d0070102d800c8208880005a035428031544014840b410860102e0500031110402c1000c0700080d0070541da0350301d012180100c2d0004240b1254402608070000304059075a0300004011411095000d005030115040c004205030b8140d11441c455030164034100401c1ea44882030003841c2542c810303200f15000d410031051025181d0407002e400582e20a10f05095054a640c0e2000c980e1003036603006281003400c0488100822001600b07001805102c05001c000910700b007130091060820340c0211f0118060801205c561070a001e404440490f00500d609650700d0034507010340391850b0701c00412480000d140c154040f543c5400401102c0c050340d0b8640d9003e08200c00c00041000500035600200d496564608a55080c090b0a0158110750741000c40005070451b0800e448241c1085070948131032180c0d1400006100094010008505403900b0702ca850180c40ea8524090b45070480a0a40c0d040004100000348 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 776972311 1250 776971061 776971081
    0x3010504030c0204051003080d02090a0314060f06012c01020c030d1d0105030115030b030109060c0806040b06090a0306050907120804080f06010f06121103010b12010e060102250e 78
    0x250814401e8030100010b0b56051019101b119840c000101800303000c004042803186a030b0054988510024081036a040d42ca03079805c80503001060307168045030040001c00092804454040e81d10690030300301031841c6031140d9080d41036042e00000b0f200d011042344100c0656a48200510300c05500040d0480f141c2e0a03440901524519a5180e004070340c2981140a280c25485141924121000300d601081c86134810501038026154103203a41d9015036a0b2070066012407803034007941088510a0300e62840500307110052005884600348405d000381c07020048060240c0f1466150000c4a400900004058135454102d83c10541c40b9801100c1080f42025000c00384401c09004104442086048803810b0580f1030a5507107a000900c0350b04005d8603072040c20002107015101252002c501c50750002440368080c21845a160000c1e0041d81d003051001c03a140900310b08610f44c903070151491284420840c84c2000000790f990b41210b80d20b2101000c0032043c0f04c080400f105c28a8080e02d112943d0900504d0071400c80c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 776973561 1250 776972311 776972327
    0x250803032701202a0a140a02060a0f021516030c02011103070e010c0215091e010903030e190f060e0102061038070b2a130806090a0606050102031213060b0301050403 72
    0xa44025402c0c0c8000c182c003403c0000d51040141d800340605040c41c20840c001d441840d00004be403000d6000e04400010781c10510003400303114840110183c0b40300c0c00501c5c07000341101c61140d00d680640e0f16000e07445480c044040c1c09d42e41d200a13280750040d42c0c51031350401291103c10400009401c5502c00390146152202c1c031018250a10094078590400c0482c004c401c0c00c0c0c44056004035001c2141004188007080c4103c80d04030030034002804034501c40403e4044000c409060b5404082c00c4101018140300071036202401070030101091004010360700b850201251030791500e20400f2806e640f11080410803584507214001d00300381c40c030006461404007600ca100b00e0b9010403012a40e429200c2c002514005802990901c20f150600b4890788845d403404000b841a400800c112442c1c0600000018240c041080450301c180e0b41140945004d0b0154070b84101035a02940245040d50014402507070070f583c5d0034000719401501408891131000d59130038843e0003804400c01e40c5e6010350811003007005140e00914a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 776974811 1250 776973561 776973563
    0xd1107060906050c0415080a0219180801021315090302100c021906020606040902041d07030c08070503101e0216020f0103050603250803032701202a0a 66
    0x14040e684c3c880352030804038840d9006c0c881060340302038008401e20384152221548680a08401441c0c030b0040d904a603603191203584408009441c0a1064080641994a1000500c040c000a504101a403040c607620211a03006e010f0300d45840486045886204105084c02550007a1000300d01c072003000801001340e55040c03030590190400303419900030250704c202c00c50111002e69016211035100d6400708006003811031801d990054903204880e41c480303000780e0140d440b0300c0c0141c000d01420b4590300c1c04c81031014166105140540240d0310400813078401290010445014620004d42d101c50844103286903280540b000e8105403011400701d14030310807103880502d401d008880ca0760866918034011001d90340102c0311300b505074000c0c3d800005c1044011250407209140e035009008065100d80e00685190001c4940c0c00c0a503000d4880c02c0035420040c410030401c464080000cac000101560441c24459503410340d40603c1003400952889080c60341d00d800c40c4007140c0c83c600319040c6120010040c0d40d81d00d510300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 776976061 1250 776974811 776974823
    0xb0405150c130f0e0610030b12010605130b180a02190503010315050405030a031a030f030a12060602070302012109030207080c01180e0606071202160e07020a080d11070609 75
    0x84040343c03000900041c0e0046a80d00d45948041e9644c0c03009000c0b1905d01040310606040c5c8134041841307290b40d00580041c0800d911000003c601e46480c00300010083c181c090000a80d240c082000e43e00e844000d1000d0301d030181c03c6140d03d0113403501c1ea5102c00910a018881c81212600025010982c0e4441c00545c1201e00400b01c1200012482c46107008441e81914001c200b98804c020b80d1340350034002c0d00b124020807100800c0d41e040030720381c2000c43d003084460180c20900ba08002508035105410903405685084c1c003003000c104007030901b14040e5503030303c441c04040e052108102ca510481c00c586c0c0c001000206007550203200c8400c04c0d240c080c0d0b461505003d510024041d0280264440d4459820601035040740b1070b250304100e280641350160184050a403a421210800810020039483c10101c660140742e0b5005001104042020040544c00e40d001690340d40011001e11840550004e980903000b60070185096072440c200140d040100184001800d13000408140203051091580c0300b043e020380560 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 776977311 1250 776976061 776976097
    0x1606090212011a010f2105010e01080703050a11040e0a050a020102010e28030e030303010609031b050603040303050907050307080601080c090c04060804050a060f1514010c0b0405150c 80
    0x9032924240c8100c2e0303500c0b072882c903401140000d65610070001702411052508241080c10a040300c2e00355210001503413061056115030041010401084401d80100703441070181c0407190456544685901c40504090910320b101c880e640415952940902c9150101c0400c940c403103201c51030700d03d1b02c1c0d00c5004001e0340594644007491104034804200200b0014500303942c10003540242d41301040507061100107804003e0311100442c525101000111b018210300e40350806820b1651401c05e60301c6809007039501c1c208440302ca0800c420b86030002502e81055141c1004a29030341e404d07100500e80360450f403049500d41320304140003403a0200070803054107844102d4150390040c030440e001d01200d00c031309483c00f4403004400c1100f008201d1103101d180f50807070710a07070640c0c502f21640e840744c0007601c034941c000400d5140e4074224030b940180d40842c088010443c668803201105141c0001800784401640301806000c2000002410403000384030781080e580605400d4801030401103074031012500700100c480e0342c04c4051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 776978417 1106 776977311 776977339
    0x2706080d110712080304021201090b011716030809010807021c030b0118030816030c080c010e192f0a0602030c07050901050d0602030c16060902 63
    0xd41c0c0c0e5042100c03800307103849040007515071101d01c0000107440340c400050801403d50750301c03070f0301201e0800c0b58104261515001d0604110000d160220300d40010941d0141204902c901d041a00125400d0000c4050340d82170000103408080e08400d002e21144070075611540080da0303c0165031068912050130000740c46001d03182007480d100443c1c0c5a00c0d0300240d55a0002246c21001010030946203c5d91640d29410814801d0f560340e00704030006ca00c214400c0c9801a0758060070213034090360440d5102840e40d0010b00800400468071040e01418045411000c400c14900107455000780d10340303541d100c580c0c150140c000da868070340442410403981c3d003803141e6503014042c4c001441d00e40c000d155506080c0034064142056608040d201d2441c0b2030041c0704544505040304030040d400707200140d0307030344a00d1101c004074040c02060b008262a404040400c03c5801d03000541a5403080d40c18102145030f0f = true := by decide +kernel

theorem cover : BRFrame.Cov 776798561 776978417 := by
  have h0 := BRFrame.cov_init 776798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 776798561 ≤ n) (h2 : n < 776978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
