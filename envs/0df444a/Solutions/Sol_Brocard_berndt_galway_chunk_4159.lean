-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4159
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:44:28.5619+00:00
-- url     : https://prove2.me/submissions/9fb39191-ce17-4655-a7b7-2655e0cf2860

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 747841726 ≤ n < 748021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 747842976 1250 747841726 747841733
    0x160e0607061509020301180e0c03190b0a1b08060a05060301122f01050f07060c051c020a0e10030b090718231e0928060f09110f0d0504 59
    0x30003007034002c0d503e40d41c81800180704402d0380c000381070080342c0300c10f20009544d0351b0000003074a044513500410780e04d8820101c0e817841d00d815500c074414002d84515a241d51030b0300c40020200540c3c5410451034620004103882064952203040610341000300030703100064a9440300042041503000b40c11030001c42d1080300e400010803500c1c00d601c040348103800d04e0705105c001c6840d1408103130f0244550002e04103c0c2c045021501e80002c4412a101c095101404104580305202d01800c1900450f0030040b50011b10380410784101c40500072100004429500d26141c206400100031039200302404107000c150781c0c0c01c03440005ea1944168640210141d48a58640c40f050113201050b56115404c05050030f0403207078025200c0700e0f188403d2402c002c002c07140d0f071110001c404041c0d805400740ba40000c0d403241c803080611400100444010551802c002c1c8106221440035603100141c903128450a00c6954621108200c5200701c1e03404803041809030050030307141ca141e030003241c0c449400c038546040c02ca907502c00c01e01040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 747844226 1250 747842976 747843011
    0x1090b01020c10020303060f0411030a060503100204050d3509030d0c121b060c050d0c0e0a030602130b070515010602070e0c030414031b010c1403160e060706 69
    0x240c1003124500240c000f2100001e440e8000a0040f074018103000150000d0340e0b43e00e400452928035049061501c034030300802008045c00380c0d0710416020b03010309241c0c0c183c517100500072030701075075030180c40d6541030700f001d9840c40c1e8000c072054000ea4241280d800324454115845098040102c0d01818882c1ca131249003040508040e2400280010b1165214007540086d01074040071a6040c114101440791002d02c00340030038203078000200148001d103805640d032040c64106025000e482d0100384c00f0031506540c0340c070941d00304100d02102da500042d52a01000090525001001c06141c0040c507019620303510700e0040e005400c010f40842d801e800004200550a0115440500400c4a8802407007030b545401c000005070403014140c0112a100040028184000c41c0d042c407003208440c3e0202e0395030312040c10088080c0402d1b17403481c035074950800d0b182107009131241d10356003902c0241341c104514644680d00c84285d0140e41000c0341c418003000500c2d4900b966500b40190039254042e02010411b0031188910002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 747845476 1250 747844226 747844243
    0x3030d0b0a061814041b030906060504230402041b09080d08100b250305120105010f12050a0b0a0f0303090f06050d05191a0a09020c06060118090501090b0102 69
    0x2c100603a2000003c901c200c8081e10100e48001050300d648600810215010304100c2039406614190405529122541039002e0741950b4042c100803c00c09803120204016103081d0001c4000c24250300b40c1482c190280b040b129604148000c0c00090710103025010544070302014044c520100d0104542004880300920040101c4800d5161851144c80c142404a41c441c1c840d01a1030b40c1c440003ca01c0e018982c4c80300b806042c5141c01d2480d000e5005241e03260040c520344c4442074580030005d59500000e203c0d400382c61400c5038000d15894006425000203211001010000c084000243d20744050b40425220500c0040240c8447d070124546a825400e005d081c51015521802c6118110807080013200c2c0d01c00d05640107000f81c04030205103907c5600d640c0c2c1014419808800903030340741c8500c942c05810100c2d43c0c2d04108100f901c001c4030362655116640200c0c014840a070703030340c0e03000107000865542c490400c81c4d81e22442403124902c0d40d80c031516140308891003608003040f41a503c0c01c512200d0340c0c0400c440710 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 747846726 1250 747845476 747845489
    0x10f050310050909100f02210c0d060e061002070302102114090f060405150403020f0f071a07170f2107033e040503150f0609040807021e03030d0b0a 65
    0x5140c1083c407881805140008074100500c1481c420108107c1d11158086601011841e0740500880b601e0380343359004c0905c04d40d4020720412540c402007400714004503180d011260024000701c1101c0ca409415540c100f9003200700e00030540281d000d40c0e50f00144c2e1203040ba07511140d1111540b00c1ca400c1000300c0ca801d55201c401c050b00c0c2d11500410000a030005045050111084040c45607500c4601e0240e1625009040c070902a02030b401281111590004500085443d0803d00740101c0b9000f0100044501c0ba20710301910301c41c0c02d00290800140c000300103144807102d8548051802c2a00c1850f0483c14400d03000241f4055150b81c280007550350b26028001c076191000003800e6401810003013481000c040096940d00c0300707100210440d86004040142c80080030043d05540c841050462091741601c400c5411891074142100403807003038242580d455210b20f41c01f80c9040c0c50410036400f000a00b1036a04031481d080303149010885000e4900388094891124480c00114240c0c0b241404c02500184940000d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 747847976 1250 747846726 747846731
    0xf090c05120f0a11010507062f09031b0f09040609020f040b010e0f01020f0a0b0f0f070203040306020f070807060e10050907030b1306060f0603050106030b010f050310050909100f 78
    0x2042c0c0c0420228845041c41c1c0d01c46a214003a688090060b98907001d51700018001718940520440300102031122840d1600100302411600050f001c0d020110740200d040700758140d80011251140a100950022850340d00202075500d03106600000550310b40c0b04450886445d600e8613880d4046050000c5d22021641041318140718002e651000280700c411039444c01c1d84180d403810790714a4070764028840c801d510503054050b2450080b040c201041b9094040c0c0318500c0c2e2980940000c0c16403003c03030303100c00d003c0c84456000e14a06032450300d13800c001c1e4000d20041c2170350000c100038900000e18400024014144603917004901c104c2d040c0c1080d0700b01103490b40300807a000d0510040007003880e0b02290f100c05403a40b107008041c060712003c6084207074003401301c0000c04180ca002c0000c03c40b002441c200c402222004d58040c4140ea8030340c0002c0b0140c0b41520303641800308a041d003000c0c1c0180d00800203503511002400620007081d036544000f607640c3d0301c140c40191044c2c2101c1010034217680c5902407102640f0400405 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 747849226 1250 747847976 747847993
    0x10b01030519240605090f09060d080304030203040b0414030609060411060f0d0c080f0c0f180325050a301b03030305060f030615040b040f090c0512 65
    0x40301040240b1012158a03540c500110b102a02e040401c808115100c8241005080e10f03104050225403100c1d0f1035a104510044425000e45009808548941030103072012070070f11120b9a624901c2d030005401141540400d02000c0ba04086100103000141200c88541d800d400d015014541040c0026100311140d42000b0208004a42e038183d1004104409640f403a90300d0042d00e40b20401801010407606020341000741a200b20355105000034010340c90035016101310380b00e100b4001414810008030721000401031000c0241c443c1d060b41a403400d940c002c3d05071a0030580ca01b010750303a0b031072410320444150300d00c3d06401d1206091203c03030840500f01d000405444060501400340281d4500c190541002d407204030800c003084050781c1610315014080408040383c603104e10b0058054501141c07480c5c01683c110610045a03e030004190f8010030100c0c18118004d89000280005004102c2c0b020390040e841d19501a40c4019a00c9581b502a00521803100c1607801c180c100700004106140210b03065115001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 747850476 1250 747849226 747849241
    0xd15170d020c011b02040f0504020a060507050c0607170c070305010e010603050c15091906170f04060e1608071a04030b19090c0602010905010b031b1306080313030302010b010305 78
    0x84914440b002404d1030035842c9040e40d140f50480300241e60007500319040c0342803c04da60305070382c1000780540e2007210002c01c119104c01c0d0441e0640112803024060b580b052a60102500b0711400070802c0c00d0107603a89400d107021402000c045503016800400c0746521960f420424404280700b007800701d81c00d1600070f000c3e5525549807150345030035420350203200e205800c0c070710840e03d0349001c1110503079800038000d0f52500ca03001c0f4400640042c1445044081071b162074890390604a1403060174840d0150700c1029070f090315170307480d00001024150700254061040020440d100003030f03110740310700418030b50300100907441c01e20a8554441d101c45200b0007681e1003c0c0814400502c80720003040d880303880c140b00400c072800c00007040009050340c1c40340a052007414840c00705d030b00399040d00083d40240c0124020b200035003040d414140d480c1c11a03130740d00c0c80402d00d46000440318940b4840340315500344102c4000ca8282d44a81545041d540641d00d58500119540e00c1041016020702559a004400742030402c110b141040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 747851726 1250 747850476 747850483
    0x41a181b01050427240603020a050415090812070515010b0703180306060f09150b0922050a06030b07020d0203040501080703150902041811070b09030d15170d02 70
    0x82d0004036040f11005a11000030161910300b0a0340391135050010940180404402d45101d8901244110390044c011071068000c3c000c0320300c4030f0321a0f6281880d051400c200120000703c00040c400400c446c0c00400a16000200300402140405080c070640c1c40c8d0705450954940959200d202c48840a80c200402900243c0d0003620308180d010309080b0081907440d01881c1c03500c0e04036000100807034a000e5020460546000c43c5ca0141c96103031000f0007449801d00c68201c0901002d100d07100d60b45408000c0308845040125800b00c0c1020b080e24051301d6440c81c80d280209541003107492406944d40c600e002c1090281d2101c0c50354100b90240043c2201c20b04101000752644039602035603040c0032482c00815055840307903000804410ba890440c00b011900c0e650000080c0d4003034880c1c680c2515000260800e802e00b248104180e0400710b42500780391064580e5504403546005004c502036000030301014160031302d180a0403080320031305a03601d40b8550500da81c200b800e000310142c41401d40c0c801c10799541c2064000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 747852976 1250 747851726 747851729
    0xc040902030a06051003050a05011b020303062107050d1b0e090a260a030b010206090f0304031b0807030809041109010c170d020a020309120d0c0803041a181b010504 72
    0x140f0200e40c5540d104108101c402c09940000c001e80b090071803000911106512060034007103ca00c07050b41601c100350041f40e0b607001c00e440c016404540c074094401281080940e101c030051041c0c00b5540120341c0c1c0d134002403860724092025681445114443e802007200194100e0140829410801441c20030608190303407010030050050902c10a1800d1440046c103811054050120f4914503d541c0c1607108002400303040942601da02510496021030000c5801054402c0280110001503081030316540321079940d02550a2001da18004803000460200410301500c00514028060790b941c448250b014041290110f41e98030b66138070327414810629143c0c1e2050504801a81081e1030004a0060002e588402d100b030f00e0b01702e40841c2c40041d40140050f00400a0610340c20200c0d28400d450030721803005512556480320410000e11151b003141c00090054001c0c60304940680c00048805104200325010110180d480102075407448605508543c070800c40889042032019015103c100c5a02c0041e125010b103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 747854226 1250 747852976 747852983
    0x9040c0503010e16140d0b03011103010b0708031312080f07050708030411120f0f0705030609370818040e06060f2d180714090d0501050f090c040902030a 67
    0x5140ca2088034501c90940c090070080d800c40881d646e4286500454000c00c0c00220b6a03020754203014201c1a83c81d0b034881075034100c5640c0b45459103440740a69480046a000400c10002d480d1010f01c2c05011400200d2800030410003030f00c0c2c103452401e010032400e41040c8018040804c10400704000c400141480d0b081c0c9401a03401110038660f0700003100000c02c1c0c4000110700324481c7c410054846c59402c400503e8141c040024130a9800381a1240241900ca03036044403400d140c0c0d400504d0003800c90b5021121a41c0030081200384c8102d070b450700d01a981024a0f410f4050310300c0e040110302e103059070903400c880d25441e410444007004030381450b08080c1d8580341c005080a1061417141721065050f181c00f095044035070000340c0b0800380c3c01180d00d80708000c0c200207034a4078056205a8021200c1000150110340148141d0302d4814008242100628050344040a0f098100d1011040003000a0090217000d0080e004554072010174601508014a03010b0030301c108510490800030546c01603200840e50880c513981 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 747855476 1250 747854226 747854251
    0x110a0812090a201c0b01050f06091c0f080a02150c070c0501080c0c1219020607091a0f030906090f01021303151d060415050106050324060f09040c0503010e 68
    0x30030383c00164256010600000c2202180c0155100304905441c2140c10b0740d008a13411711615250106104003805412219500403076840d102803c1178074502403510045104014129080340181e449241c1074028000e140b025038829511602d500d01c0200d030316a400070141d1595803c001e400e4a42ca41104000e210301818005200042540c41501c2011520240c40c0e200440300210031200b1614010703132041c4452100d80307031001403200c00c192001c640b042c002c0344655124500c00303080ca59441101c0013400e50740780e1040700800010741045120340266100d4442600035040d2440c200080d581801c08640340d0f103095900c100311480c084000d4003029016a6006420792050600c2030b810b050080c41190840c4039005e41c00c03015036443c0c110000d125442240b1030240d42c10b0031151510078100744d40007805948082402800000e1501d0440100540c4000300f120207991651141004640198401501884044c80008040c1841c0c00c1c00e00403804000c42a02d029495585041c070410359500c00506081c84401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 747856726 1250 747855476 747855533
    0xc03030b030705030d050c010605041b03050603030d0504050d0e12030409020702060d060308070c0506160f110901080a0201021c050f0d09020a09020c0d02011e0c110a0812090a 77
    0x8408100d0903003c1d0001a0490701703850b4240d10080d24039001003180f07002030360900724041000e09290080744500c40040741e12512551078580282c015000080106415100601000303000c40118055503009a0140c80a000c1d6003056540080c0b145400da149140035035086141c01070010f500000710307030441d00030703010068980c0600e01c0010164803944907010085418a800071051050460041040a105e401c88a0495550700188220785c00b0b1005174246050011912402007044c1005440c0c10510607090483c0c044200c400003681c201023a04510b08075808148808110f5070100584403505c4000c40c5182c03800240064020b05510456011003800035002c0b0302003c007900309400502c0143d600824a1003c2c646459825000750400c800f255164410840703021030550061007502501d04c0300c2d00034280c0e08000000c0f10005821440342d4402001107504800d000c031130f001d10081034030920030100e495413000141c804d4590880c000d820745105402c00030240c0d0008508148154030f0307150040c0000d4000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 747857976 1250 747856726 747856729
    0x1020a0c170307020a0303020c030d0314070c02060d050708011d13080703140f0d0b011d0f0a05090c180937051f0909020f13180c050405160c03030b 65
    0x60140c00c400940100c050301700401019004103c2d684800c0c002c0e4116914014003510031800e4514032050208112000008954954825410107802c640060b00306403a20f41e190b10041c00300d52003103c00c64001020180140155121800e038144110900b50564030107041c108295500e115281000400b20207001540000309402a50300814400c84100c607151107809081e81c1c0c8025601103840200c0881c03800e0314400f0198007400a1514580c207040c50242e1510040080c4103c0d84201061143c0c000c4c90300c18002a56078a070041a4403401b02000b605407a48030b031788099201e0070500d915040c42800d035402040300195124100c003141c1150500102c0840715104090390043c08482d51000d080fa09040802c9091000249644100d003401d02d034448900d6550900c0c034080764080e8400950000c1140f0309520a0f01d091078020b001c200683d003000480d00c0002113803400c00b1103071440840785203076503c20030440b62400c0d01c11141d20920780c1200070400e03c0102d9009194030030900008040c1540c0394a160141e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 747859226 1250 747857976 747857983
    0x91104180e0a0c080c090f1602120a0903060612030f1b0f1a070203160809033c1903030e01140108010906050105030102040f1811030109020705060601020a0c17 70
    0x200c0451400350b400a448a00782140074a4081c007a00f0103620480e10090741034100a002d082c8a90110a50070095450700c0c50b0100718040064079520440c480d4100440300504144002e00320301601d61600d2130110320354a0610162816503000301003a0146102c00740100b81c01c0540c49a0b0413050b41740080d10781c9105814003400842000000d490018030b410b01c1400c001c25200400c2c2d6590103a0304c00100c2d40d8030100103d990f8440c1a4050008030111079484000131109006441301200c01000c1d5007009004107560a102c14610861161000421705032810b510030b240e000220114902d8042e0001c140700010a826003103103101d00804060341d540003003000071003e5200d0840001c1d0400400f4907560343e00c10003030103090100f03000e0328401d00e400e0000440b460140700700d2307084400c5100c100e0041480c241a000d940a90340c0251480d00d034661074004c0030141800d004601803c0194001a1078004030306106140940c0280a41e0555000301c1c0c2500101d450420b4004c202c2d00600300b0303e092032815040c000d04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 747860476 1250 747859226 747859241
    0x12070f0501020706020307080f040c060f021005250203031501080c09030f060907120b0621030f072a0b0a0917060a0b01050f0316050705190c09110418 66
    0x107540b02242c08020001e0b240c00443c0202c400307542e0610551101240941111410754005052040300581040f41c0341c02190f030b440c3c214038203005079404012240d5124040e40c0c0100c80308100b195034017034a1004046c1d0040300c50410103961004500b9841c043d00d822201c0d991000415061000d0080094803042c943c104991742c050003e0207446020a405000c40d0b1380700c1c41078590303c56600400d1030100d00f606400c0d0f20032052a4115211509640b20303603007408650b10614010511101c00c0c1c0d032202c2d082000400040c203c2e0030000220941e07821242c00e0220070842d0300d25220030b6820845042c1612200700c20031800c00d40f0407081444d9aa030201c2d5000b5180c51030180d03c03620315045060351001d10b0f07032404100740c1d1194051420911840500e500116154070501085481404060011940b0341c94a99000c440030005403c2c0a898001c6075100c03a86019003a400f030010440b006541001000102ca803910000c10141d00c00f88400f10000001901d94000c500404626a800164088200070305802030715 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 747861726 1250 747860476 747860483
    0xc050606090a0e030a0f081509061003060302150319060b07031101180b0108061b120601090e011e0821030402040f022205030a02010e19030822050a060212070f 70
    0x2e41d178491220014140e14030162480e4081200c1c840002e59098a108440f207040f02c000300340c1050b0766510010030110100f031803c01c3c000c141d075440c2d001c001a20341d5000410302c9100034580540781d20706240d13401003219800d03005450b44c40c10040f0401000707100c0300c207440050380c3c542440340d4180540514240103150303034005e044a0402402d90300d070501070341d28500c1d410384c1c2d0500c040d0350403a540c13814400d411409070911040070030010003030180e0243e801404503401801c149480315406564600f9242400d000388c01926007110482c1c10b01d48850780456000f4000c20115001e4481100c886002d0aa004109103246100c07910000018003150303150307880840320108800c0c003103459004e50540c032581d50a5541418944002c074690104d00c5217400107080455071ba05070340314011003031034205002d01005503003a21f0010410803d000700001d5459009880b158498039201038810b100405503442502e05a0710041c09554013000900c4a150f0110301c840505040291071940e405403031602e01d055160109014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 747862976 1250 747861726 747861733
    0xe0415060504031109071b06060515090102010b0a21150f09030207140f040c03020d09050f0106170a0b090f0f07180218010324030b04120c050606090a0e 67
    0x200340190480c000e001030301c0c041c0300304011000c0018140064540c3c1920100b0100300903800e584610310030322402c90021440303484040f0310565a0404142c1d2107400d48240c45580c43c02083c001300c00d5a0920401c040d0b1201180c0c0a025145000c03c136281d44402b090414442c50800c95082c001e000078940d15400600d80024200040d5182c884008014403040710110010b00400340001001b40e42c18403056181c60004003003081110010082000a1641403040400d25030244100c0f02ea81d0b045101d003442040c0500040c2ca10144544501d500b180d0003078119000d05943e60b00c5041600340e002070f100d404c580e40718660754846d4a940000c41d1804200e8916112144580303100441c0c081000f00c2ca25081320314441242405210109142c3e00764000da5001c1042000c4070380c0044029803007070308024400800c07500d040010007101da105203180c0c205034005481641d0300e50140b104004a00000402c0c3c0c41c0a8540b000800c1c100380d440c40d440e17042c003030481481141050301080301d140b0a80d10880c00d07800204101c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 747864226 1250 747862976 747862979
    0x2206050312070606240302130803070b0613060b0306120f070f0609052209020a230f0906090a1505060712080c162006160506060f0109060e0415 63
    0x124510742e00100084030060b0038004001420001451100000307078001d40b4a813580b030aa200704030000e40050800c00c418820580b00098071314402c0c40206101401402c6c911154603044052000070822070003c243e809103010070800640c4940000d590b00030400b1107061119458205440380b40604800b945d8866002d1034a00003403041565401408503001030311071100c0280d58008010808409180900701d80d80208820006010707107510102c103c620091000d40070302d44514a81d10740d0804400c20070f806080d01310521f0030500d00301c5244940050304465100c071070f1420348041040e4480244c540000036454601c00f03d40070394a4240307800900b0703015090503190b400e6400c110f8403008003d0340110106101d1004208034510a0044810552664900c454078090b1541e0700e20b550611060160110800802c6189180d03951200604804050b1034100d86c2d07c001908149007808809445c4501c215000442c208250740c10102c2c1000729903c038102452604c1083e03020030040c010b032004503440307501c04d82d00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 747865476 1250 747864226 747864253
    0x4090b0c0706061d070302130e1005190609030b13050111190f02031806040b040608010617090d0c1a010608090f06010b0409150308030106050706140622060503 70
    0x241c02014040d94080c46015610b151003020001c01c03001003000c040e0064001032095000740c0040c1407809028041d90100c640c1d40e00301c0c51000809032004207800d1884142040685041d00c031141d00c046501c10ba00e80c0e401e10f0400040c060076a039202c01469003803801d00140c18140721800c42264150068000c2c0442c80c03e42c1d480f1012640504015080401c034031300e010300364a105484403141c0c82d40a4000b546050829113400640003c40c008203071313000000304004501d5402c0c500180004049076244c8d04000e5040c144042c02881756030341200003040d4400c0030400032440004821503105681c0c1025010b0790301c1406e0000510800c00e00303683c6001d420600010303249038070016036886814a42e0030798a4500b4000910f540f250028800c3c9840524180000c0c030072846181e0000540030505030084094035034075907076510300c0e4101340d0202d0b01042010540400340f184900075a1484044a8030344205441c01000041c0c1c49424500034550403c542104d000c00060240e220304003a0100404030b40300c1110501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 747866726 1250 747865476 747865501
    0x2e0f0303120c170711010908120405070e04030e060702011403090c040606020f1b1206010b1e090112050712290405040302120a0c15020a0f020601050d030503040204090b 74
    0x14915256076260140107a18248100b4200c040d04002c88402c8405407203080c01200c1d01408120401c2a55582e45401d0001405c50f60080840b411200c5104140e407425090903420b10001d58028203140c0c0b0780404220019034420b1000012400c03c40300700d62144081d000417144803210031900d00850500006100800d0000501003040c404201e4061000c0ca4403520126110484050280c90741e50120040c0c1005100388031a241c100d40010308840c5220090500140ca4080f00ba805046925400200ea40686056184c00d8501c1c0b00d103c86040d00e401e80c1303140002c3c1401c0c065488420f46980e101c000c40c242c1840b0b8002c3e551360030107041051210501c1120340070019030006445e142403e010400220070350526000d4140720741d030903030003070240030f07030740e1405500c1690007000050b0800031039000c458001050091140a00d104580006803144a00f0f0009040040c41c1e003801c5041d980703c4030041003295104011034000603858603180b6200d862b81d1010030080d002a103002420660b2401c1000030281159 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 747867976 1250 747866726 747866747
    0x5040501060c2a0e0a022a010c020706080f0601092309151c0f0803010603061503060b04060c020a08060a091a090a060903020c10020c040f02032e0f0303 67
    0x50904101c403224411181d510f5045102c0441d101022846040218016000002d40d000310301303800c05440c14041040107200013501030b04011200040c0340c400e22410000344940d0060700d40071300007485810f0400c813016181c480c0040100ba56803900000090700ea034030a0000000034600c5c000c1e0102640d0215034008142c21b02d07814400d0084409800040702844584241c0c04160400ba100c1d90004002c20a08074441e6414003050b034000a29017016400a4030010083d03000304180c0c2d90009619082c44600440400420805010141005018054007400380d085400711038039810109030074900c501c00300e165070744941d01c80442401030204100c1c028501da0820011b040c0301c0c2207202510004030b0141203d002c019524051580d20400080c000601b0b02d070b000c2100c0b14003c0c0120b4600b10120800508a0444440464010380001044440342d0609008052500708900825070071480c00c820403101b60108184900800d05a01030306960000c9414001e41c064524502d12824107a00c0c0d050282141c0c410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 747869226 1250 747867976 747867983
    0x2040e1c0302030133050c070b0309060703050603160e060d05070815070f0f0507110301022b092a03050f0303010816030209070e0a0803040612051308030406051005040501060c 77
    0x10b01000d803440081402001400850300000a883d5aa85c0c03101150560841300a148480c17160b94008516a00340d031000d90322561001008000904e0b01010040503514044d2807a03001c0e5104011011403050000d000d40d003904c10000040503030350b450100040c105040d410010f00680516040800e1110002c40c91403400004104203904c181c42d0750208403681c0d082c030074400b40040c80e585a01c450051050000b01680c0313001780400c0383c1c0f2282440019003240e111031220300c0303840c0341c0b0280704080d80d26038111905a2465000c0800407103a490715441101503040601e1b031a805c0f00d6104514003141c0c00300410020710741000494451140c1c1030112643c1e41c3c000e0040480910681404900046c01000e0f80015a6400381418001d0f8444c1e030025a002490401c0040c0e21821303903076011503141d0080005d403009001c9903413001d0020101d842c1030021030f50040c1000d200341012011041c04117603c43c04076500554071200004082c4d0b01c1001240b00c2e024107070000d45d4068100b80000034030355400406c00300850700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 747870476 1250 747869226 747869249
    0x507050705090106050f090105040f140114130302010c061112090c030115140a0e0a0b010e030c0f0d06140c03330d0606050303040b0714030301060c02040e1c03020301 73
    0x101c500800601040c00d10034800040e5003084400c0a000040703014191840060414034289a142d88645030716007429000044a44092446080c0d250392168a03a000403941a05c00c500e4503444a40445080b52640006030510022107540b8080040360760011043c4c141059140380c903408a80d241c12001e050a4541c1401846007020051507440e041c03090000411240d54120002442d290a0000090768002c90a620200b07200700000e2200041c1c4000f8840c0ca00c4940003e2401c08410000d0690201502014042e5214a020316a683c64000c042040c1600c2120808480e5085141002c09401d1541881d05022504801e1003902240b500107107014140d402c242904561841c014800c510007002030002d2580b011000394000742c14415440c042507070048001060310750725040400d03c0c5501940c094240020001005410300c2541400601500d246202840c515490410010810390b19540061b00c079540d00d40040002030020030041308500c03020301c034850050a0300340d0084c0094109205951b480b02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 747871726 1250 747870476 747870479
    0x150e0a0506090c0105160318060e12030702060d2f0909070f17090304030b1f051e1c02040e011406010e010c0b09031b01090302160e0a0504150c05070507 67
    0x101c0204400c0c035803810685d2030506004205444c8503421080030700c143c082c0000184d80003202030301030301c000340035003207036264410b0729803000c014401b031106d4201e020342e465041480481c0050f620003040b20200d2403400b5010410703010b2184821504003440000c0d02400020802d0b4a0890003030f000600b03008030040320260300725070703e0500079903222101d24079500c006440c00d07928007903449860441c0c641101284046030b0a040c0c881e991108102010740d41d0f80d4540f03210392a0181509131036503240020301410340741e814a81c008140d98521140a40030082d218000c0d0445660003103034546599132032150004c000b40103240c0c066482a008050758a0b0500c0d4080040c0005401540102132003081906e040c3e41e00e40b10b59907161212a4608000351000490380030812000500d010b1540003141c4515950b000021290321510f030181c5480b44a00000d0801e100400e41000401c0b000328156501121405010513255102d240034884140101c0000d5103091906184144140d44100135011040c854000c8400d8203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 747872976 1250 747871726 747871741
    0x70c060807170406092901140102030c070603020306030c042c030a09091d0d0503100801050f150f09010b04030b0c09060f071a041a0708041e150e0a0506 67
    0x714000c42d00c00408403210301150006146070302004103180510100908080d034442d01c0b8081013044514a02c150484200520581c8200d00301c0f00748030380b424001103240000b10601c054490b000d612914040c03540c08070005105490030300203200100c500074020442292007a01400940d00064500d01c520502c000107502101400022940e505095485190115140c154a04c02800040c242e00c80c0d450700c01030300a01d08100400c0390301c110700499112503031a403400301ca00911020060380107000c160704040610904c180a414482e0b002084d00c03002c1c1c2c880d0f210740b00100e0a03042200350550b8014006200015040200c000584181e9104004001c3c240c2c444000c03410241c050b00d581c4661010703082224050f6139940b54018042144640d86550704a40000c500c40b00001c011201981c14044502444050382242c4124590040c3c1d2424011594200b6846015160356044803500040c4884e13481031051242d0101070115581a0240500407440c404a41546030466410203c80f140718100128101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 747874226 1250 747872976 747872987
    0x8060703111c090206041715061509010c14391c0c060309120c11120f01090503071a070e0d0f05061f29030912070c060807 54
    0x220001c03880c400d03091100d546902d0503403910400801d821282c0e02c1215000503215600600014101002202c41085a001c0618103042d2061040e40361b86004808002da03658901c0c40640c00b031025141919100c0c180f00005803a48005000040d0405003a02003c1180c11000500321505c40310102c0e00380c1c0d84480c1c40c04400320109202040400540d07000c4480c4041d410f100c1742401e4121200c418207224625036445290711640707550401d100090b00d901c83d03c4103109078000c0b003448443c10b40c078240c00d810200d51540311010b015903903064403c2000703220b8200190010400341850300b6802c4001c2007592801e02d00f02c0c2e0b0765844001c01b291505154826850218100060507202c0e0f14561502250601c0172030400900e0843c0000c1220b0480d07042200101241003007001c90302c940039848030943c0440c0940ea007965980c440d644100b13059030203442d07190362204201d4059035046141050850303d0b912070300c580500700040c208400201100c04185541482503008494084070b0b5161958070054a036448229107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 747875476 1250 747874226 747874241
    0x100603030509090604060506041418040506131b0602070302040c03020f040611010f06030807060f060510260f07030c031a1014030108070e010e040203280215030108060703 75
    0x411410b1008941c90f0030490301e01c907405403004000180f250b0310b41c40000c070345030481c1e0000d2130010351000d14062075091000c88400c4241c0f48100c4400316107840d6075210382d20a401040c002c10708514041030010031019007802c4005404184200700c5680d01d40100a580d400a032000703070f100c0c6081c1103aa000aa0080c400c0b1207002039a60b50403440e0600707021007a2116014507078007103102e47d691101099240f200b849582c01851241007102d940f1540c904001c1e06940381303c6062900d0300d00d8180b0411043e07840c0b010311035042c0000c3c2000c90503110030071091401524415600e24136031084e40108000840d00c0c00b010780c41402c0903241001a8100e42900b2000c45540340c0d070184030300c176407501e074441245812031a9503101d41c09490201d106030180078041401e60020303403004800c1c2d07003d800e007803114203249803070390b40580300e00000c0d21040d117815000a0364078014094140136080044000000c1c050b80c62200c0114190082c00604c085403d58207000007980c400d204005c00e602810001c1495507201b40104030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 747876726 1250 747875476 747875483
    0x170d050c1206010f050d0f06170d09090b0d020301050906040201020f011e020708190e0f01020c060301030602090112050c0403021f0818010905010f0e0111122206050414100603 77
    0x400541d41c82c401501e15603481d98181c0d0600c24184414242079500f4080c4100f034202107540481e030701d441c24541300d8083e01280710703050503a0044180440015884050740c0102d85901c4404100075a2070004200100b020390b1000e5055402c013000c100b20f031280014140d016502c06c0c0d080307906001e0380e50403041c2210b000e403a0300b03c8110a40248480b88030200d401800c0c0c0a80514a003500d030100504441080918407910a00440c5003404102082c3c034044408001d80341081c0090002d080014002074107603c0140001411194041540e00d800d900c500f030041d00b03200500301c04020b01d041c501e100d006c40381c1152208034414001180d019007030454909ca40300b03011055465440198a0f00070700500c0c0d91210740c00c915040d658032800e0001092090181c46c01d941010840005d1800d41c454096013502c41c0c0348159101603c3c01c021068200110310030722540141202c44200c1c200c509d88540240510803100042c01241c1807109201c21b1245806c034407c00845003d00b240c40c41c444034582541582c10510016 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 747877976 1250 747876726 747876757
    0xf1a06030903040e060609041e0c0207120f11031009380405240a060603050c04030b04050a060207080d0f0c05160804080d02060907080705090c0d09170d050c 69
    0x1004912100c1351000c1d0040700041c049800c004101c0041011252020006801001000c00800012021b4030035854503040502c06131240c0c0e03060135201c102480c5200d1009001c2e60038015420284031629812400d40c400060a44124480e0360908034068002408240c5094045200200740f0031540508054800000922012000c1490340c3c03c5481c0b52008005654501030000110120f0f880c0d4401682e42c10754001440480e800d21803000b804681040e005042414603020038007540c1e040f45001d8400b1298000700041141d6514a041810400c0240c0c004100e130b8000b01d140010010900003400420007400c1003000090305800751903050300c0b03010b00d0500202c0d004004812220a20501090009015040d8180341c60382d52104245481030002c1c43c0300060300614148408500c1c240325240c003c000d8000281000d03030400000400419020b0803040030180f000400701c140315070341e0304540089500100d9800d02c010520303c501280e41d011014028403140340c440001c1c4419020030030b0315001801c0c500b10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 747879226 1250 747877976 747877979
    0x11508010f06050702040e0d0f030f0b0f130b03010f090311060411190b13061d0a06050a2f070e04080d090503070b01090b0108010e0702060c0d0902040f1a0603090304 73
    0x950f102d6201d44810398205880d640c020031250000c0100e2490542103513640700c1c00d081ca03120700030b0445001c01108000c150514424000c1952040c0001202031012100e04400450482d5114000c19804540c41e80550078118901c0d5889540c0d40094500c40c026143c10507041c02070881c41e521106c0c2104d000b407410603954080301c0d65041c80e40c4e11002ca5002c3e1044850590344030b0712116401c0d0441542d1420010103d00d050010917485045440d9814030300c2d01650f10812010001500c042160042c502000f401040001095115910b04400c1907d07450510018804005034030342400d4894418440c0d80c49030200004041c10000081c0d031040d904811040d050402400001025207500ca00c199010301c014003003080451050301c401070081096103130000b91640360307500140c20010160b11900d0b241e058079082020054010550725803094400001d06c3d074400307081c1c86c0b480080c502290088d402a10f0aa03818118100e1075000d41c240805041955000001d43d80c100300a42c4812602032129420a010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 747880476 1250 747879226 747879239
    0x2011e0c06110909010b09041118010309020423070e0d03050d0527012f03060d020a0b07060203060a05040b132c0606100f1b051212011508010f 63
    0x10340040c0b00032080e0b8503098103030000928112080c1c00c01d00680f080010035560a240c40e00c6961452044100040d003006100d0610329440c1c03042104e828149601c0e09495411552143d00c42048010181411420383d11968a40000010b04403140404103031b02451810052a16040e24001154507a40741c1380740c804600c0c20310001e0600500180e00c00003000351410302100300101c042e0242e2000303100006140304569103200309040007646100101a00f5030104100c104100308681e07000078160f80d030b00c114003c180f01090032024150b10180c0c01c0c49000c6144810400160000c50050030304540343c0104980b910200411210f88450b202d138015980841030000704070301d800641d050781220f40b241c1291902d00d00003110a0b80d04d244421000d4100300104030340740c5801c2d10946240b036028540074507504c2114401a0425074900031260045161301c41103410000108181084004207a01054540d0140103501000c007001307006108c0005590001c052210b8403a55501c0d0480e4800d60180e00c08500d080c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 747881726 1250 747880476 747880481
    0x315030609170a050a0f05040b0417150702330115030608030715050703060f06111c0801030201230d1e0c050a120209031221040c0302011e0c06 63
    0x482100c0c0c02c2d00c0192001158031211024000d81200b6841d0103680382114407005012605d0170308100180b0109020511440c0c07900410340c1d00b80c8100b070460311507291000000b90718000001c00c41d43d100c180120100900e56902107101c108801e00c0c410580201403030007825054206e0744261640c0344081c1c90004000003a41a45103503510065404d00080325078903203590b6030071a401000c040d0741d182d0400451100c4000d0501c02c680d44400c05241c200109420030280c04040400b52041004010910011701e2540d1024000c0c0a0708038050701050076a1620004050000f18003403200344c1c00326824800101021442d40a41840b00c401c0d40180c40c9401d0030468004020203006c0011264444841c4140020712414413403070304140101d07102c0302c2e03d4400d1164010a619807800da0782403403c0c018000000030b41c800142114400440c840c00b10f84982920401e47c440c600489200041401510144000c1c042c40310314560a0b03d0017a41c910a07040443d210140001040004c3c0000040740310b01d4100c0400c6090307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 747882976 1250 747881726 747881741
    0xa0209040b07140f07230a080a05040b031806070507081204030e040c0e040605010207030f02061e03040602090118060f0f050c0304060801150e010203071704090915050703150306 78
    0x600f00a110980c40f50b403164400c0d04140b51207400320100055480c00e101d40700d1343e003a10980314010b183d180c61306008030280e2101c4261304014862100030901c1c00c1d190340290290340107040c1100d0f0094803407901c1092650103c55003090504180180d0300400c2005100b5000c43e0340c810713000403c3c9854800c2d8480120581b0000910a83c104505441150a940d0301c41c01141ba241403156614283d08252000b00002c4901d0f560009056601030541000010982d441010340a40c041710340d65180c11a181c1d48181d02800c4a00d140d40340702e000000c0004000c100d0303001d440c21032000e0341c511841e4180060301d100d418159000328004102100710b010190f0303104860004c40300c601850b006041070a00042e50386550025007001d0041801e6000501103104c00e00144c4440b1480c070300d00f00d121a5180b400103500d9100c1e8810140c8981ca200c11942d4545218030704880c01010a148100320100081c201025a642c030b1039a00726210313042034086040b45210703010700d00d801c0e03a40941042c54680b45035203244c01082c49 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 747884226 1250 747882976 747882991
    0x190308042304050406020d050c0a0c032106080d090f1a0313231006030308071808060f150405070509040207050a060e0304082e0b0409060c030b030c01020a0209040b 72
    0x428007440058a89000391030203036114540142e160f00c20041000180d0300024003c4205003010302151060340e6001c19a104403a405041140300d80340c1000c203010510cd00200c007442c08a082030400200c01000141070400440c0d25540c40301550f032030b03503421411948203105100328003c401c0307045010407105a0046801186080d4100714070251035171504802034000320b4294401841c030712000d204142c02c5c013a082d10680e100e001007004506650300a081c1041c0608440208a07140b0484980c011001500402600c00344080314010318210403200c0340490101c0e4001d00a0354550801510b600303150003160b00409040e02d409080c24440400e01c4000c0d0081c4000ba1307800e1048541c10804500203110788110482200d02840d0f42d00d00b066826450710f00e4010082d220009520350ba551009000540380540c05504503022818040e0403002030064940804081e20040c5880d440c030304429016030001c85056000c4d01a111010701040042e070311191400740194018100000180000b40301d4204207074090307030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 747885476 1250 747884226 747884279
    0x9010b03010312092603311d0a0c090b0d0519180204180602070f0201030518060402090414010c0315080c1809010e0d0c05070e04050d0f05040504020d0b19030804 71
    0x1101205028039021003994056100501e00c0144e0034207c00044070340544550f01040c0031042003c0c080c0e00c10174100408030000c4c250f60750702031044c582c803488010005015030007581d500c03000d521918400030242518103c482e05034480310842e8000d1980200155400280f040c000c0c084c40e140c0a100107004403858201c0941c4d0004060000120a480030b0107141303009090709020440544005411120040d091056a50a000021510a2000a215030b203c1e81c1074643c006261124501560a985900100391880d401c020710458403030303495070060381500240000c144550369101c240503116800701305117680044607400070606002d0400c1c20b140e00704100100026075a84440ea0083c1403202c090f02c4000001c50047c45241400b104001550290903001010b0845040940c0c4040d903a0400d1030000050051040c0720506450141068900500e002703001950b5840c10100c0b410000c10751450618440c0b0514001180460403080d242030580340c0c00303458603142600703200700000089080c84c0380c04112003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 747886726 1250 747885476 747885487
    0x1e0403140c0703030c1209080613030e040216210f080c1b0304181107020909010902041d01060e0921040302030a0311010e010b0102060613060509010b03010312092603 73
    0x21010000b540046000303030b95900c94030160340f078a1468400c40c3c8500904020440c80180441d000100d809034101035403d1203a0b1300600380b803805940d0f0740c00c1308a00b6980301d440030a1041603060002c0c101580c2510441800c5448005002e02c0001e10118154201c0050031020a48000e24024142544c0206083c03481b64100054220351191544080c80c5c40d4210746c0006c1030801032400b01d81d0210701a41d418078407e2005001041c4003201d2400707803010181c03040c942d40001c104803043c07e40c491820075401070000d00c00c500c021b103c00d0704407a080701c183c81c1c3d4641c605900003440c0c2560b190b9050040040c600074140b15100c040791168180348000c01072424403020000000180e45c2046040c41e61171003034441940c901d44954415084595441c02c964a42c2d041401e1600d06a03408291180e2041044444412601c1500204002010643c01c82c0307800400c1b080000c9041010340002d14104c0b4840e01a449000648583c115064040f03231040760100c031640305003c8070700c229114080c800c81900204507410070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 747887976 1250 747886726 747886747
    0x60f060d0f020430060b01050c0601080c0f0a080c0d140607030c0306230103020c1e01020304110a0303051e09130606020f0309091801090210020d081e040314 69
    0x441c0c00070001c80941d54002403c00031380d4114030000442008545002e92101d500d0b400c00c051100c9501001030100da40d6241141031a802941030b42c2503805000200d945a42e100c2e4a41aa510300003e40030340303c2c80a03603440c1d80c0c1a24140c444901a94110405011a07003400414440f0107041400100c0f070708914080308402d140d00401c4850b208020070b40c1c000c501d0000e0074101500321040c5412a011058a02c418102003888a9980707211703445007031900583c2e40700302c0e0214905100c1040004008890041340401d240b000c150051401940900c0c00b5094111810042000c990503a10004000c0f817030034090001c4540400400200b105544904503103000e401ca00054456902c10034480b99a9039111014000c01f54100500c40581e00700340d00940c40c24007aa80012460400140690a104280c1e805540401d00a4000d81001c3ea409400c0b4004080031f41c00c081c2d04c640c0c000346071000081c0ba800003d404044141035521300d403403010700c8880352901d45440442e0445581140304540900801c15074000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 747889226 1250 747887976 747887981
    0x90c0c020306040507030b010e0108190501061a1b0628060306110c0d0912150f0504030818010216080702030a0506090d03050115021e16090603120f0206060f060d 71
    0x149104d90050a962421403620040b26441070304411620a00780005201e480e000149400360880d10314682c140360680b501c1c0481c0940601d421015584001039011070300030311070502412403910008580ea240034010210300e640d8120403914044549503c2e84030117200038040010030810300308440301080ca5501c0c2d45445041c0ea20040203128544c200040700724940070284600b150101052400c480d0310b900d003175502c0e619511003110140150b81d8207120704818000300d81c001140000e030280f080c0708601d064180540600302c210340c2003070380d001c006001c0c02c0000010b03c00c07112009640e212180d0640e00680300e660458102d802e0885e014401c0d00074820114038100070a80c4940b00d0302d8010002c4405014008094460680c0101520b4031000e0704400c0c4280c020452104e030b040c4007080c0482504100d0700305450b0481841c203032501420001c04c00714803209a034001805580c02030685c54548111180c08a907442c41c0d442200d401130700170070003007481860040c04601c00245c000701482c0c2070100f02e003c49401c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 747890476 1250 747889226 747889231
    0x130f0b010609091514060a030f0507050424050f030402040e07030809040b0f061207090b04031127010b09030a14010c09080f0303040b220f0302011113090c0c020306 72
    0x41542d0080070080000035000d02c0d00c103002000308004455203095050950441c41611aa100c0c510100c0c510746c0d2203201b6840440005202c4900348010b00700048082d00c4ca9010f0b00408a900a0071402d1255001d0038a91030300041c8880c4d0369030782c0b0b80161400715654a82010380704980c40343c0c40c0c9280f10880e21040120402171400345510a80d9000844200710403115a8405079010703010401254519542d1442507034051501354911918550b80c1c504211914403c940080d40c1c0c10001180101c1405440e42400414aa00303a0303044010084240030105071454443ca0103030302030741110045c0700d02c082e96000b500030050040c0445a01003095038a51700d02c0030750b0852a55040c0e644103480c21016521900710b000a020030001303402b01b0006800c00b1074480c8002040981002480301c003240c1c1104121800c0e5800d40030003030340061b403002c107450101000341c010341040e0b005600b846416003403503c546003140e0201881021014000e840c02448130f000c3d00c1e4110204090003003813000301001d82c42c240070147c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 747891726 1250 747890476 747890489
    0x7061707090b030a1d210d090b010e0a0510050f010c06020927010b0304030f03090f0f05030a0206090102031003031d1215010b0f040e1302030d051e0f03130f0b01 71
    0x55607103201d080c540c01015400d172490080e81e0042201302d5440380d030300300100c01c5940000521030396494a4185007010b44030310303200108a2403148000042031900f9060003802045620824042c80d12910f5085c0c0d01200d407801070316401741c1d0303043c1800415800340c0254030480b445404058100204a4009503d6414009180722070380d038044c206074030480602281c14050f2808801c40c500750f08064800400c01403802c04074206059071a03003c001805080f01240c84100c0d801515a10241428070303005459400c440760b244050700c03070744002c90300500060081e82d00c82d031035500d00901200e04c0e40d201100d0f50034107440d9a241c030752a49180f12003a501ca40240d080d8180941c0001c0403035658a1110f4805c2c010168080105440d05028107206505000100d800b1035080204c00d401989600d0485180c0c00314005000b5810321400e0341c2c441409820038080d050340d0384587c60746407004804e8407002e0460b21440c40080f0003010104002450000302008684520b8004c42950700c0107609079440322131541d403e81180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 747892976 1250 747891726 747891731
    0xf08030c010b030d090b0d06030503040612230a0906061e03021003140103060b010e1002060717040b0a151e050f010c020d021005130f0806070207061707090b030a 71
    0x504248024014820761160680003003040818440c002080c01105d80245200554001548034102c00b5980104018580090680340d072203a680c10064061091840c000354003d003001c0318482c0c04207100c01c54481c09924640c14408070742d103c4206400425813110100c61a0790707a9407000c14581521400b08a079009a601d24512035821401040b42c401c020042080400d03003410501704103100311100c1941100ea1000020504170071900050720b5000001040301d4021211030703601002c00e076000070a207020349840d40360020024110b0400b4141800100c0e03000d0044000d080c0400d00003070096204400b4268180000d441c61900c4805480a0f440201e000c1c007203900c807858050040b0310700400328000101d000d0030a1031074003a9590109100f0090002c1c040d01c039850343c280c0c540e1368600440440b501c8604031140400d21a4440c10941c41c0346425000f2444144103c40014244600006035002900c1d2551100c60718202000d403504d02010300101640c003007003851240003a01000302c1d000b0b140140c4003d00702 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 747894226 1250 747892976 747892987
    0x40b0118030807051203070507020f1302070f0b06040c0e12010e0d03050106081510080604020904020714011b050d050403021c02010203160302160807020d080c060a0b01090501080f07090f0803 84
    0x407172070b10424030405515503030104248840b450700b010032640820381c16200d00249551000016650110b1451080c000e180006a40d208106640c0444c22070288603181c90303070140d100c0c20b0601084461640740440480c4042a980419242c0542d84500030440f250006c40da82c0c0f8a00c10450800c3d1940010202090300c0e0300040c444681c0040e01030758401c01e04c1c94540c580400c07074800a00c2c1082040020310500040e000880c034141c423103804403015074901900540da102d5007880c01d0194040e050110503410351800d4204400607001003d8a40c0760300c941d40d1902d040c850002001c00c0140381c027600c21400e61240c681c403107151061165000c46103480d540c00044c0c50785012629540320205c0c20304010b0826204108591140120b800700c010680e402c035a909071115401c1c404181402404200074064100c0420050020500010b120703126580d0148140401c5012000542380c0107094010640403812810008022108a00e441c0360b0000451814151141d030310010590546000d800280703054000081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 747895476 1250 747894226 747894233
    0xc040f1a0d08162015030f04060e0f0706020c04020a08060631140904051e1905010b100810030b09011b0e01090f140402070503041a2115040b0118030807 67
    0xb0913095021055a11900340c48a003918071542c1d02c001494003100318040f101240602c0120303440041f403160418100d51540c14041c031050350302c00301c511a00005115401913a8802d0810340240c900c07580454440035501d0b282e0f44200803082d002060400c0c20006901d181a83c05600304100f140f4001c0e401c07024108a90501d2801e0030744a07180014180100078bc1d10502000034030000b40f110b16610175100c022003440c54903541c603090444413420007280a8022109900317111040d48141900b4a040710f503071000e0080c2e8041964044022a0795440710306c01a0804c00200f804d944846a00480c56000081c01c1408003d40002c1403924031111400143da2009260003960002842c1003e0809a946c076074026291403c940e140b041030442d0f82d8007554000c200402000020030a460240c0b118002d8581c0c410074084518055070042140a809480c0c004a540845940d2012040c0034420000b034554507061100140805001c00240c0d0904001d1182c440803680540180e010b80a0340c89601103a80d207200740e08 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 747896726 1250 747895476 747895523
    0x121515150d0218010507050606100903050303010b0a02211e090409050c0f220b1903060225050c0d110301060b03240a060e03031b0c040f1a0d0816 64
    0x600130b060140c20040c02020600000700103034042400c442041c40443c043c6d8080300c07144d503070780d00040484c40003200120300e614500340034100b455080d900b01c58500302035409650641603080040c0e002100304204280500b56492142c558101e000c4002c80d10301a00c003004a82280d001c500c00b5941a00718440d84003452030500c3c180801001c0403a5140c43c40c80b403400041e4000d6082c3c8a046001c0b507681e0130740d030700c841d00c50900b9100d081d5013290500002c03d50707905000b400b80d131081621401c51807500c4918585014840e03a200901500003008150340850303002401004401000e055601003144910f49072a0f81d801d018240207803952807800c58a03814800b4032000c100d0403001c000342104c50303556003180f529120000e5a000722901460300c5c288020000d4007181c114030421060140c00005038a51411703102c00001c8000010609a40030400d02c5c1030045210700326020303086484254680c0c84444441854850f8001c1d1816018011640c50100c03442904103200d14100c2c02184c2800030801e00c440703080d4140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 747897976 1250 747896726 747896767
    0xa051b2206050d05010e010b04140a050306130311030a050301030b0604091707031b170d0e01020a090302010f0810090e0106090c08012405040303030203071101060b0405121515150d02 80
    0x2c003d04182c5504000032003145010300e002cac1145080d0380404045060b540c04001c040182400360543c2c10f5408d000b4000815440e201c0b0054000c100884804c4104600010807146200308a507521811a400c5a442c2c0007120800b0b012598040d0b2550003003400300300c0c03009058908000c1aa001c9944801b01e02e07000d00702c08401a00c007030311054013000c5140490010b107803180d0120003150a40341d03141c050500050041545458209a540c4003103140d000c540d400c08013404c16a07000340c89034501030081c2c1c03008035407403003007114080b00021620308104035101007500251020b106441c00480c0640d25001803108840180814a00041c150001040040742c011450356003622030300c048000015207518040c1040c8074602c00141050350020020702842e21901401c04400742c0f11009008059403546204515000340c0246403103410000e420682100c0e0004010751200e0720309046c5642c40d030310741010000801301700c1038180d04140095400c0380d0f04040c0c1c000400803080ca84500603112010f4840e0301c1c8114024 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 747899226 1250 747897976 747897989
    0xf0d0e0307150c0503280909020a020d2312060a1502070303050a140a120c0c0c0b0a140307021c09061709120c03120a051b2206050d0501 60
    0xc0700501000d0514915040718041c1070a14801d0404107291030b0746103205115442c051030700102800c032090f8000e0402c1300c00740552543c800c404652521007000c1244146400800581c0c0000802c5000c0c5014040480044000302150710202c13600c400d01214603804003c0e03c407a4000120b08008042c900b88650802034102d0f034000d0300304e20b40c03c0000695580e03254080a0240b00d404103424600900c00d85801043d09103e0320301a44034044402c0141181c040c01000e504000d0400e4500c50185200300c83c0130000c035400c000c041c0903007443c3c04041c2055034005840c0c0d1041213013018441c074240640500940c00742e03034140d0003000011080311203001c07209010701d540000c1041940e41004525400026040a21841040080700303031581d40707009282034a0311940500c107101c041045a513002012014000290701892003114a5444c519880100c8a045030700b58050501401a034a1400800002c1e000e013049519003004400418044408461015441900010b600054a801c0442e0038081e45004210 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 747900476 1250 747899226 747899233
    0xc1a040b040e1504020409020703020c0405060a09110f04120c08030a171f1818080703120e150103060c030614010315050a091b0c0f0b0405010902030f0d0e03 69
    0x400c40540c4861081e4492084001428808a00f04002d803031100d12503a0750040045680d1540d40c40c103840650070064040d03000d4010b810000000b8140f50050780d01c60b0b45c0041401c2500fa091008000080c00182070705144160280080070400c450b000060001d01110a00c545415900e4508880401c0140d0000401f6070001e201c0c140710b058100340010101981043e61082503550b002100343c840c443c2071009000a2a20328000854940381111428603110009041c000c0041d040500240c01e4041034004040c45000c000c04008648606007a010700c008040340441c0c041c2003017014516013910b41e48540075000d45031004100304403039840b464001500300e05061294074030344030b604950040001400c0341410384910090a980c0880604ac0002c0c0c08001d00c25920152502c094400031300c04803480482e2014070094080300315005140000c0460b6004c181c0700b21928681d070358110305100141045446640b58414038005030344c240442e011100302e14004240407004844018600c02c0c44404083c0243c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 747901726 1250 747900476 747900479
    0xc1302070201082403010c050406020c0a080c0108070504080106180c0806010215092406040b060408070519090c0816030603050604230703030e030714090a0c0302040506070c1a04 78
    0x343c01c546640e511041196000d1254110b030880c108076844a80c1400b5403652030300d69a015920b03004000340054030340c10b80c01c0b0742080304a02c044c407805490314080e04d03400343d200d00e0000f1090341c1304142c050740c04071580c980780e82007642c2c444025007910303503680021500019200d8048904540e81c86400f14103075461030203940c0303400c1c8500044d480e6603803502001d5450200100007182d400080015094403890550b00c1441607940d4000c0d901801d0040d0f9085220f2400c01c8407c0d0035500c0c010095406541040000d0913455113000101b04080703807100c240302804040c07040c2c00030304822284280d281c014400d49a5104170329107030b44107001141030403400c1c80605d4540351003032011070800684c2640c0994045880182003008245804007452204007420303140c03044002c08800c15138403409010f201442641160b035155105c141c44008116042e421a800c075010100003403501040341c001c600d06149608005240035152400700c2c500ea0b00280040e19980c107a40400c00014514040c49030680804400302800c19 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 747902976 1250 747901726 747901729
    0xc0714090609060409050309121e010e1510030b0705090a2403020306030f1f0c030c350c0c0705040c05070f030e060d0e0f0d201009050c13020702 64
    0x103002c080c0000303020750b950760000400c106081040301e07404034009100c04000090012101da81e00c5481807075030300400c1c1c050f0314a14000d40500560005100b024060001d51164040d03440141d000180111b00412550700000b010941c10b00348613000764000d944240d6200000401e0000c05401e60340118106403000074400c080f003500d91054450f00e201840c015940381c84000c006460207807030312101ca140d8022407410011880c25242c0510860072104000d00443c00e0015060381100c04031030600c40461656118400040b0350b81d02d1500c01b1500c0428079030360601c1404980340c84144110341d001b22440c0001840389030b80c10208070803801458125000c1c410580c40b444014080d01420302c0040c40d45a0f02c50a007000c0501076560f11b80150701c080c00d080d88a111002880b00a8038130006001018010b40c03814110141011500f51a86042d54864000c6526850f0030070030300c0030f00e00c240000240030700310210f800610750f80102c1c0d071114050002481e41c4104003040288404445c02110120b40c4104840d4005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 747904226 1250 747902976 747902989
    0xb040521060c0a050409050f090607020109110904060e060a150f030f06150305030f0304141c050a230c06012108070c05060d1a010e01052205060c07140906 68
    0x8084480c5401d61144003001c0e00707440a0050360040d0440c1b03400c1408000c0c84a00000f1014416401003044a01540b5004400d03400c980e0380c0f550140c010803440e4a0342c038107810b101c80708540041c86034100107a00103907260301c2400c000341640d03200600e644407403040040302c41c00311814000d0821140c03805046443c540d59481907800c80100103040d280c5076034108450080c2d590b9010000c0d40c03c807054075075407124990b411034544d20071101121039500c0035003031406c0000c0015880e403516000b040c581450300714214050b98182c0041110004211644004100001d41d9100110602c034480152645940d10401003e06204050700903949500c4500111074402100300341c00022940c00c100100c0d9260000d00b8084e0800200b41c03c42c0e60412000910402041907685c400d5407010b040f42c40400b4007140d18001104c0081e0080b801600080040c00b118002d824140550a1040e00701c3e107220607103a41c2c1c1c401251498000b00031890b480d810078802002818010b1040c501e1610080f82c04003814500280060324 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 747905476 1250 747904226 747904231
    0x80705040f021207030606140a0e040914190501050c120a02070201020726010f0c021513020a030503030f13022b172104020307031b0905010b04052106 66
    0x412620344804111041140c2d04070355100b16000c18602c01454500310241c05007034103109000014001c5400c1030710a6090310f060742c500c501c0791390b28400021904000c20018106010f01665a07540410840c000c0c40010010444002d84004502c0105401400c1040c01c5940c024009a03203101c003042201035200d00c441c006035100c00c2c8200c0043c1c4602d01800101d107825a240c04c440e21200d100b041c0c0d603910f0f616415103e100b0b22040c6c4000e011013180e02e4162825070303020462a4000d80c0c00034078105403828002c11259404004100380e01d0503202c480d00081c61043ca90b6100f03545907000001881940c0d0b483d0440c4580c000142d0403040500781c41c550210301a840300800703650b41c901c1c0503026085003540c0740c01c05011700d6400c852494800132865010f50219030054041c400c00107001001d0760b8207001c1d90442d940c8a55001805021854a03544170320102410a103600d0740070202603800881d03200458403680d80a400140015521a4140b02c280628090b243d00e03501001a54804950108070f0f0000d043d50703 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 747906726 1250 747905476 747905479
    0xc110301021c0f090c0b280c140c03060112020f090a0903180b030406020703120606020c1002060f040f08070510061d1611010605030a060e060609010f0e150d0b1807080705 75
    0x70380c4c540b0800c04060134000350320b0080d1f0007108003920b03510b00c295024403000076150140100c00130328014490300342d0b07071408404d00d0345400d60000d4004200004a0f5050745240900250001000c4440400081c4100e0f0081fa81180c1c2035582d11031020903d0b5124148500c41021843c021101c00d0502c1c446140342d01008000a01090300050b00904052040c2d4840c0c0240088170b209000e03c92b140d04010707403240c40c80000c02c0e00411329a4400c200840c80003030701d030780503442410082c43d05071140c1e11440070225162034143d401041c100914030004404000342145240c000f44002409410084032981d14588807420024440c1558103001d0b01c0c404032420074650794528107000c10000341d060300c02400740603194045689406107200150a110098024000050480c4261a0340350b8030541000440d00e400c0c082e442240b002540f041c0069600a0070054008203204070f42079003d00c41c83d0024080084107081102c10b0010b2400f031182c050902141480d0901c9602d000c1c1032010300b0103410b42e9407004140f003080d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 747907976 1250 747906726 747906749
    0x31707081609030506041103010c0509130b0a080610051507030f0e011b060e0606150708070204060306060b13050f032805010204060f020d02010b010f0c110301021c0f090c 75
    0x1140305401142c0d818015035218007982d01070b02e0f060400751866000e00d41c50038020750038180c0c2a00940e21800403512444001032461020f11038490036840104514076200b500151003840110f026041001110b101e10f5110011864146c280b0040c0310389050911070b2011211024440a000a50003075440d41d00d0558600d0940001c4840c100100c81c2107030b404001e400d803112190b81080601105800024070715080710111600350f110740c0c05001c0d0240c10488460101c400a004140c0000d000c03400070840980004c0c80850415100e840710700441d1b8840d44000d9490f13200082d01c089280c4900c01e4040102411204001c81c1d050b0200420389411380e45850200164081e441c11007407d210001410b030054101c0021510b07940c031000054070f003000000242d00035102d9a1a8281150303c14007811194500c182c1d079034203074520400f0081d111401c402030b0440314401803d5404206032024405803003801030402d8100781c6144031001394412514068004120941032030550008900c900110b4004c860016446 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 747909226 1250 747907976 747908011
    0x8030301050f0108041109150109050a0509070809010f051e1b0d020702030109060c0807110a0f030305070e1009210f080313060608061b0c060621030706060303170708 73
    0x48542c02e4060506c42d54080c12003c1888106264114000351140c002c0c0c030f480c1300c542d490301e040180a59591144076803014101d0001111284030321882c5070400c00030030011841d0072a64807100255541142c030b01940c80f8425242c81e501540280b2440e401085065840d400900c1c8000207500910891890306000c98000610744110f403025400b8417911900a20208001e801c807130030040c10101c0585480002a140c0c0550008410010030000a01c0ba4805525410b0a140b0741c0d040d00030340307001031003001407107501c0c55944070710380341c081070b59242c203826a035543c1c010b50410b4120200009840400313520f04c44000210b03000141e4010300d0f800401d420103007040d203940d251074074501c1000b10110003d242a0a0020004000600280031070142c102044101c281d03c2100c2d40c010a24080c5154192540d44034030089412030800000e01010240380312100090b8080b9601010300d55403018070201c0e80039964050400c289507000300c07601c0c81c03c01b520060700c003541171400c1c000700480d0740030723000303003110101d0741e46 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 747910476 1250 747909226 747909233
    0xc032107031a0306040615080105010f030b090d0206150a03120f020708030a05160f20090a090809010f05161115040b030a0c030b0a08060f0c0a170603030d141008030301050f010804 79
    0x443e41c01023003014000d01003581c449451143d03184691004842400c500c03000700b0b6881d480030489060307180841e40108910360350008a095003403551b00106400482026011001c074803c59031031149041039840d007100817030420348003d1030b00800754814002504140001442d55038060100c4101101000c0c00402c0e01651707081600a0b0203450341d00501c8110003421905c4201c0e080d40e00110030700d5084a10030004c3d502d180c000000d60359900c1c0e004001c3c110801410a543d8004c0b490001c1c071940a280041c01d14101903c1c040d014040284180c540307000850030781c8071515103441d0084041a200000d0740c10300d40740501c2d102090001511030054541c03a05000b17441c0520071b42c04140d10f0080203000054565580d40a01c1d1600000c0c3c1d001300ca0084114005140e082017001141d60000044d82c55074484110020280480d8a01400141c0e2500007000310b80e90781c40185c000e040c0c3d80100501034082a0410300031000b001405607112040940007030004100a40e10140000e00d401428280b080c050760f11442c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 747911726 1250 747910476 747910511
    0x22050d03080a27110d03051b0708010e01020d0501120201080c0a12020403030314250c06090b0a2301030b060f040e0609060106090504020304050c060c032107031a03060406 75
    0x22003c1041140c0e4000d01e40c1d00da540c010288242c1c0c2d01030040d0300301003100035050110304501c01da0003502140007008820001412464005c040401510503100f81548541c1024252022554040c01d607a4000c19041c40707031484d0384940c1d8010848540384188050742070b030010b0310105000b07101020021020811140441c001c8000203007562102c2c5c42103645030344034500503008040d0306c00c2c901f88030f41314540022100c280c1e03036880094000c40d2010074080780c0c261940844041460100480f0700300d81b180c1c102c600082c140101c03a4028450140c0108a82c142030384070101c24030404102c0e044c054600c100400100303010b030a41642041040d1910b01062100c030002c2006480300d444d04018a1144108200e9120030100b8814145d40c441c0d603d40c00401c0d0340d581040182d000a4601821503000f00000082a207040001400303c61800300a072400c5c01b05000d1142c5d41c1d01110080100c1c101c0f4002c04210080764540b003690020741d04104e09540039035503140400d035104001080203040564980c6020514001e04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 747912976 1250 747911726 747911741
    0x90a050105032a2b080706050109020c1b01030b130c021510050f49020105030f040f050a03120b0405270f0f010b030c040504050a0f0204180822050d03080a 68
    0x482e949289004d8510701000f1943c800360b0280c40d0035182c58008520f0f0101d50080340d41002d03a290040c0401d040810846007000441600700c2d0600d80e459982e8840c2d501c0b148060014030882c0040054a9181200c001c2c0c10002441e61070702c02c68038018100261202442d10030300a40300705131014901a410303040414006480368083d60321944408000a0100305041c544803240b48142003c20320720900114405076580d0180c100a02044040c0002100c2512513521141e104c1d004030448803032a4919181d041c1401c2501c4c105400240716224000c114032400d000700729071080c051350100304a03d0014803e02038080c045c8500d80401000428a80000e04204441d0310710044d4031055544101d038032501c0c079009204540140b03000f4026042c200142c0c0c40c0511403e84641e8000010f0302d2551043d590b14651400c4010007240d002c1d83d111100460b05011118801c0058070580d0320316510000141c05e1641e80e18010102e00401e81251030501ca10b442d041440c1e21107662500b80304000343c5450440c50b026103040c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 747914226 1250 747912976 747913039
    0x30a06091b110303270102220e06010905060702100c0b090a1a010e0601080408071514100506270915150306220902090a050105032a 58
    0x24040d524004040c440303001c24056210b61100d088036105803101075140e0108683c1804901813200d00b611030042c6440226007022803d00005141ca000d0b050881c10040000030700c940c074114400000c1c000d00c0c0c0da110116802c0315090900e0f0355503501d4203000803928414903100900a882d010004021540a440c00401c2c05502c04c03801101c034a041c00400d5521402c070541030722505401d6a015030709255a00c4c085060f646c0b08035041ca801e54803840196501d07803005d0022a11128204000300102d6100030602c101d1041c84000407622880079040c030078001d440504043c01e00140c2800070465a91003100302d07119126408410712401d64055100c00c00080c0c5a080c164024000708104403040e00b5010071040420030484541e21865090484040c0c5070004465040d01705240b01400a0f003144025601c81180614440200b040c0d06542d001c035440f86000d440c038101d80da0700c501c0144902e14080c0029003103800005d0b25006d2101114080c3c00340d1070400800f0b41d0107441540128012103449425140040c02c9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 747915476 1250 747914226 747914231
    0xc03120c0c130203090c060910110a050a050c0a060f0c0201030b04020f04030c050306130b0411040e1006091107110904050a1e03021501030206030f0703020d15080c030d05030c030a0609 81
    0x5030b00d41001c010354400c8070714000c80e000c0c403004c041d41c81c80e041040c1c035846100604040076440d134902d820748020700380d171003611010f1041c4086903000a6040107801c0c910b600c80e0001c1c11a903001d0720180410200143c00c00d00510003449520400039030b01170880c180c41502444d000c01c00410150109009105121019002c200000380c0441806071a40060003150015011101030b5996001c1e80c1c4880002000010300407031180002c1000704114031301c102001d003030007480040c014898592451806260003010010140c80d41c80802079808144179220340341813030300480392620340c0340e0780c581d0340c110381ca5020f19115001003400f00d4107005007041542c0c44154803e162469a00602e010102104401d0804500500c21201c20040c90056048018100c0b68050905030850700c4400e402d11048500806d04010503500b401256a000c840c3e00403405014019103095105601380409035080c00c50414100303020740d00c519003d801c5a90b210f412264401241c0101c1c64407510350ba2801c80282002c1c1d4009400c260 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 747916726 1250 747915476 747915499
    0xf0d111903031107060309020d1106120423011b140c0109030c0c050d110f13051501080f07050a05130317030603010e0a05120a091a12090c03120c0c 65
    0x142c000707983c0e020504a100841d000580d80e85000c0302a180c1c80c88000303411144c0c0703110620000320a0f81a400310008020b04450070510403440950f003c2c002241c0641d840c5044074981c410b80c1c95064008250460800020f02200c1814030040f07058520140700d070410040740845c0341106030300c5801501c018900c400000d2005920504000b0166000b80b40300780d0f0001c0181e10002aa80340c034180900c14036a210100400194407242003108001030481216080306100d0482c2d40001c1035886203034403034620940d03d4034102d02c12000041250b0001040b800000c81e5002c180010710340c010781950300051702403819035520f50102c0740705080f60f096540f004080901030f100c0034286484a501440c03081000344c000b00089042c4140850381c540c50207034043c2c00354000c811850505504c0d4030040427144240e0030074445055460741000200403c018201d1307040030000c81e462904c010703198011030f081a000801000c2c43c002c03c600090305d03030301c043d00d03c1c204a41c1d0020340944414000e01041003503110003004003ca40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 747917976 1250 747916726 747916733
    0x20c28030813090b0a09020d0e0a121403150f0d0b0f010303170709170a140f070816060c110409050a060c051219020c0610050306060f0d111903 63
    0x30b8200080d242e00070b03001d4140120300c01e0014420b001309440e00a21032441c507460800600029440740e080313000f480341c480d859003d45060801181d60020b00c00c4581d40028001813500030507940c00ad90390116958010014841100c000e0301e84c480a00c1d80c2195048a10001040040c081140d48100104450060401c01c0880451003d400341220b00a40361310300c0106a80e00408000b1004413034140200300500420300c240b81200c40402001640b8408690b50714070b0540326200b18801034500c3ea6605d0f88410840c1e10080d1b802e20120380203001040060000f0640440c5105420200d40501c00c1003002094250040c03018101c003011345880081c00820035030300c86040983e16004680016140300703041c20382d4526028070a504503002c4561007540040300340c461251101107003d511001303c0c0c1076502449044030b400d80134045240144040e62105400380d1030401454100780c00100500c1c07094500d03100503150b680790541410166a4400e028003041c1803074000044142c04000280e90080000d000c0c080b041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 747919226 1250 747917976 747917993
    0x308030c13060e0f040204030b0708150411092404090b180718060e0312070804081609060605032806271a0f01050a09120b070816020c2803 61
    0x8000130b4400a540c00d00c01c3d801d100c164403462100030201080b078400549250305c00d02da003d4110245202044100fa5400e0006043c0d0f081901400e09850001030303203500c14134104041030141401ca031403920810361020032617019030259114440d0200d448414482440d0b48000041c92040102c038144182410055001044203600c0c0802007074841d0010b00200d9014003811422403c0c22000b0b0040c1507807059208030050503001100211003d003c1800049888201400b5900000c02d16244803280c5070f244c58051000d039840d5600c0310043c04010400d1240070307405428100780450342082c1003525440800320220040c4051350050301c422031060482c0300e40c4003449000180c00345411200703003d41200d11400c1507000180d00c0c1d000358806803580441029502910160051802d40c1c246120942e030b40320407900079803000080480380c40d1890020420b40c2a00076000d182c200e400800000141118903501a50b030300051480103200340c058010b01c001d04184c070720008803034240040442101980e80e1030301000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 747920476 1250 747919226 747919247
    0x1312170a030213170c040501051f0c0503041401120207020303030a0e0c10030209030106050f0a0e0c1902031e0304030c080d0207021305010503071e0e13020409050a1106130308030c1306 81
    0x130315001c0c1038000b03070041c41c1c2400303018180c900060210b64103c147e982c6849121105d102d43c2c20034094000003000114030140058002004001072a004990040700010101402c0c442e0601509105110500242e100041980d030f00042581c2c0000e011840070602c03615040300e640107250300041e85010740c2626541a00584811403040c4c000740000d0761074000700720750341041d000d5442c1c1014203070108001003807070349840070340040321402024039061807400358040c40a0a0b55400d07015a10001e0321103991410001848619555128100c0c15030903c0d0340c0041c403400721780c0c40c0542203800100303d103008107069a040340c0109078000c10005072034001600400c0502024855240f003401103110009100000c0519143e4520b00307414103000203824040e6110101700c3c003500d40d0000b15084d015200040e01e9a1040c042003031700400c02000c2d2040340340f52803d520404004c8290086d00c0510203466070091220240060342d0303100401d00d49950b80c1403104102c0e4041c000302224600d80d034040009149412111918 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 747921726 1250 747920476 747920519
    0xf01142106060c030702040906270c0b040b0a2007230604050117090705060c01091230091b030b06031203060d030c02030d051312170a030213 62
    0x20075510001041010301512941c02c4840d001009a5001803815503c1060304901c80c0600041001c0388010b40d001040f106010718410388841c0304440244400d12003007900a000c610004c030301e01420300103850218010ba440000c1489100d500700b91028030034041c2001150862412140a6aa6800801e0703200781100a06114154503d004603681e0030008210b80071f440c07060310fa40c440c100d61021446415840200742c500c01f030003407400c00300d00d50f80d902006000d41c4084200208805005041c0f03a00307805035103c46101800750064841610401d1107910a04c42000c8000c60404569001601d00c050440c2200040206460342d650507038000c030030300c0c021090724040c040801c076076901e000070705599140005040030f00351800e10000c4c0d1585400c038150500c13144289031048070f0758555030229140c56010b400c41380103d2000f02d1407003000030f130f0407a00d80014821012203d000303071400d80b1441044012020801804080040e0f580d200e40d00030703011503204101e1000c01b08100c5584980041c80340c1c44400003076 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 747922976 1250 747921726 747921787
    0xd0f060216032a030c110409031e0201060612020c0705090406020c0607090509181c020303070e090c1206010504031b0e060402031b1803030301031103060c0310050f0114 74
    0x2000342c0103440c080f100f00d006850062041c21140b0f030320f050b5510b6806130350440e0000d8541500c80400c1d2118005e001c1550700c00e4032440280300000015801802c13080d0100d800b16850510200102c5070700017034101e1440008440180d03101e21500b410ba043c4126604400c1c0c00940350b2045c00104200c0b039004019000c80a426980641c466241c03c4804403042e02c9900d5000a4030b0000c61820420320008140804010003206c07680b502e90007590803c0c07280d9003054005600040100840d00381c111188540e5414229581d2002e403501d05004645401042c0369004212403600000e5402c1e40684201e1303001d0f503044030010600c0d8818003000c3c488100c0e54020142e422000c500482e41505050082d039000784005407541c554046507003100720b0030350070903000d511440c5000708414903251402d000450182d4040c418841c00148030710185803600380013400030000349404004200c021443e00074100d06841044030b0140d00d10504030012910f10784617039280b00c0c190f84d001074079110211200c03404450303680340442034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 747924226 1250 747922976 747922997
    0x7110f01140a110c0c01030b04020412030903053313020a0f0612020309030d0b04110f070210111b0102072304050c091003020912010c0206010617150d0f06021603 71
    0x140040f8042d140131016540e014060000c80c130340c000d400886d040c14010340b0040c18255111500b503144000d146040d8041108030307509205008040c0700140070307038405d52801c0220760014400006107140700d064041000803803e000c606020710210140c41d644d074000f0040c020a5488102a040039901031080c1000b0070080008801001035500a40e8030841c145c0000c0c60605041c1a800400f40034151005035000307684607100e1a001c240203018040c1e041c6c0302d24090380c81c0d81d1b2610500c2603420260054100b80080c400503032041000c000b445a182a00e52080f800a080750000180c1c640900354005034440210b2010100c005034241c0d40c29800034108480502c03080d200c05404210512840c002c8a4210301e4002061807298001d40042121200c06480b1010044d145d81446007151428140310300140c000600400a00d0b60029000000d000c0342d158690759130404110552240b400812020300480c80304032000140714034520103800c4d054000405650301c0341d60081c1074801c000c0c1d5030000c40118800ca450f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 747925476 1250 747924226 747924251
    0x406050d050f0d0810030b0a060e010b09010e06030c040519120f03020c100206070f050f0a0203090907030e06130f1a01151d0f03121303030e030607020607110f01140a 73
    0xa8180134a1240c045c0440e03050958480580050300144202d4000b034840100080519149444500030a905000300303898a001c0c600040280c2058031a10b880791a0a0003441814011f0b030088074102d40d42103039030f20103000441c0302d05181461550710144a21562040e9503040c080c101c0c14501000d0f21907801d41c1d2410b5140010031182039049503000c001039000e2000508030a00942100d0580005070402c142080419001d50919610590300400183c1011880c0340850404003400c0d60440d03030508041c00344200c041051513440000421020391038020208113001c2c00401102c000300150014010a4200340504079985038103420310070f034010049c41d941e030908014420f64209914802c040c0100d0800f422010400a070301003840e501640c140600c802c0280c1e10009400200400f101c01e41580d0482440c50401a02d68612005a540250069420840040c3d4081603480d84442581850100b00c615500614075020161340e140c14550b00e0070342c030110500c4041c4030440c41240310311001d2003030076080d44 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 747926726 1250 747925476 747925487
    0x102c04050c0316031d070801061d011a0304020d06050f0f091933050601080109090506280e1f06050a15030f1d12270406050d050f0d 58
    0xc40050240004900c140326080c42508441a17802801d00c41c6001e001154000314100249070b1f00c0500b5a03035680c00200400324003c0748030190b07a8102050229158035000d60603c500000c1c1030706211407080007001408541d42c4005160480d50404000c128600d840c1103140784000e82594002c5d80d4108660000e5943c030400035803212072020500c90313a884003072980d640085d60100045038005160f034040c0741404a1410028400e03414240f544086403a062140c0007500148068110640e40e606011a14010810001b405604110f01005d14130084540300c46148401010f020700c034403424107040054007802e01c001110b02084400d0460028004407030310450045880c1807003581e4101d06903030010024199655000783e00c001d410304003c2506a851403003002150301414895868210000c007841c11a10300300009054000100c1000d85484540c8040c1c21001c4c01e40c018048808001d40768803d00c2c1d4480307802007002040d01411503030350700000f803402907201c038005010008d030b621882000400291265 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 747927976 1250 747926726 747926731
    0x309030d050a05240a0801050f072304060f0c06020f0d1521050a054827010303030203040212030a0c030309050313080c0307060e090105102c04050c03 66
    0x894070140d44c800400005201d9059102c11580c080c00300000001d002c6021f0141c9440751540c2019a000da1420181c080c1c1024800040e8403640807001807042c0b52401c14000700d4081e41c5450030076819a17446000700300d4005250b04c20003400d950000c91071903141400a03016140c0c1703080309001804140044400c40c6801c595522522001200110764a104c40e003180049a000328003c40a80b03501800d00e858540c900518051a41100c1d40c601d068048000308800e94900f007490f156511030800004508010700d900150f4044a2240c502e21b551101c6840384c02411300603a01074030054645940e0350b33081c090000c1d041201c2c10b9009440090050403104404003c40c0d041c0b0015840c3d0304020714440c0c400720028003015404032050b110400c14220307840b030221080c00003041120003d00003100d8500501d030a04640354012401d00441d00c44d088016903424841d0b505462058030802c02c60609940215445560802d80d06110705501d580703000c001c41042d07442c16182d85c05a80621070340e151000c0d0311800c0d1008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 747929226 1250 747927976 747927991
    0x1e140106082a010302090a0914010509150307051c0506040506070921080a0c020d0b070e010f020c090405070b0a05090103060e0402030d03410603070303120207030201020d020309030d050a05 83
    0x96070b0000c000e50701940c007410402d140500008002500e90f803440003100c0350302c22488450f9401500400c11440c1c440d804c940c0c820f05480040c01c14031041000310f81c0da58041c1c012a131140615840c0c0c0845410300700f070701861040d0800119070722400d280c20300a80f01c50059a41400050001c500403d120341c404c410780c50180014258180540c176161190402078004224941c20031005140c15000340e84c130103a0007801603000e800842024284040c2c090a00b8488000b542d043c00045030310030550300e0300030414103e00c00d01510b05000560b03440c80d2403402c1020701d0b08065000440851104c10659202001d807102c2282030301c0411480c0d4030b90070501d5580204503402540741e0300403902c103508203210750007807000b82011f46104c01250724020010301c4030442080050507a059145000055852107240c0b0725080700007580074110b03003030450720010400c18508890404d4250000792404c1050b200b5812105020350b451070864590900300b21454496102d080301041c850300300808180b8004030744c1708241c021043c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 747930476 1250 747929226 747929293
    0x1c0c14060618060d02100305092806181a0405060105030604210207080d020a021905010f05180405150310110306040b01020f0d0305040b07020c09041e14010608 70
    0x1503074807103500001c0108400c1d0000c2240b031300c04005803560044503071141025240803446141207e001440c04401e040e500548a03095105030b50380c80001212041c40380d80011010070a503a248541507040402c9000040002e55081c0541c40d4542070080c101c0c1c0698810ba0955942e030b6070f25800c05a0f20078060b07401820340d2007808843e080c1550340407500e840d4405d0f00d0043d0b0f03228a6846050300c1c00c2a5640d49a000542c101d05030301c1c40ac5161460050b9004080c52a00c0d1884504040c0000d1250441441d03600c14032100090b51500000913480141d0b1001d0b001f40140121b1415410701c4a9400301841001c3c001e10030303c102801c07929082d004542c0041e2018049a0441d41d814042001800c0e4181585056021b056401d040c2c407441800914a940d0a9031808212401c19140501d8803003801002e2208541089407400c10380d5603814201d46c0c215030090782c1c500e0071140c00d1b00101c03503481080200800d10444440760172050241034000f441100c0c20300341a64050600d100d14ae146002c0110042808002d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 747931726 1250 747930476 747930499
    0x12110c01020606120a06060b03070f0201020408071203050403050a03050909070219080904020c0f0f0f0706022a130e06070309020f1002030903030403030914040603231c0c140606 78
    0x13014000c2e921181440d0049419401c2203460703050445140e600480f403d0400002003180c0181c00038440e0a860800380700840c6000d24104d10303107031202c009000301c4c051001c501901005241c42141590b0207150090161006038400f0b04e005400b5600150030b203401850320100182c9150300110307061014408421982006041c02e9442580380d030f000d402000e612642c24401c2203403a0320104601454010014001c10040c00369a41c62842d000301e81d4600e400650000100b48056903001c83d286546038a07002e0a100d0884070704101e26910780d4600c0420350403150400e0210407050b07494001d143c001c040c1e42c0075501d941e251101d0803020303242d070355101a400c0641e1007e54100d80c248100e8803840740c0c01030b1043d01d0902501e100000d095600c2a40309034000385071418207201030054010359004482040701c00f08085481e5981340403105110000901d201101c519100d40e030803030144840302044000040401002401c10800f8100c44400c034025a044200701486c6600900c1c009980d9005240c001c14210f90746 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 747932976 1250 747931726 747931729
    0x15150108061504030302150105040204062c0d050c0a09020301141909061203030501080619150e010618090515060703020c0d080a030b0102010b060d090c0b0712110c01020606 76
    0x1034401422890708807031950718414440c0e038a4400750020310312a40c0038140aa01c511072565010106800c8a8400c1d4030400007004403503009582226040c21002d03440600503804444e400d2440e8090040d19007280d00341e5158000c111000c2109580c60608564a040e182c0c0c50b11400c40481c003090140c441a0301d0f008401d910246840500c0388044c61b900080180c15a8441c08504146c4015602c801003007070441c09100100764040c050507016000c2d900050200340b500002000c0100c020b51040121159039074039034041440010541d0740940b100c4030120105595440d0020200510103003110101a03000070041051880c9020380c5009660b030002580000c5000303010051b131a804000110250b2250210748080c54541e500d00141300c40c0913690b0a500c1c0d1440e450060300750751903062245c2c11640340000300c060a590702c1040d00c3d1401403400000400c81514508200f040742241c04c071082116000ca8404100527a884201204507044d50b9400c00c40c416000000c1c1e07440362035521070381c05a002040020f01b0f5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 747934226 1250 747932976 747932987
    0xf051e01050a0e130e06040314030f04030f051e13090b060f16050a1101270312090929090c0f03060f060c07030203160b04170a1703010305151501 64
    0x148070002c0c0b600104c26a103600030012a5001c00e403040301600a00100824150081080b1000303400407039400e4a18075201200d0011030f88018002800c0c00810500d03d004140700d0340c15030340801030f85e0315030620111036a003c0c00d05a4100000c907250501028001088903211401910f11141c805002c4c03e04013401d000588485400c507204107a00110701200c00404500101300c2e0314403050150703071404c0500821400040c01070400d0044c40d051f09410a81c03c400306070358002c00c0c2e021650007501c01104002c640e071048640f03034041e40c4859110b81c03e181043c0d000c5021a04174642c2c8860003400c0526400b2086e0500202d140700300d0303c1c101c0c0c0c00428071600c003211682c4030003140c1c003202c001c00081c160620307080052402e070003c10440c4c0141e40b02c0130f424011400e0400c40c1401040c07590302c070704c504a441c0c0184481c0521440c01400d0403010004480b04024000300000d0000c0e0b40d111102590140484012107807907003007440305032401e100d102d221500d04101c00d4400341c0581c0c43d80d48007042c180b4152005646 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 747935476 1250 747934226 747934247
    0xc130c0813050a0b01450c03021908091006050918151305011409100b0301140403051201060f0f05030423150906090c09130203070f051e01050a 63
    0x2a140124000440007413403000d2083d028000f00c48a4500c440e0282242020075241d150700c01100c0380140005a6014407020044000c010318414040341403c101c2c00b04030041d004468074104440c100380e0321180d00710b800c1000c030f6110f264070b80300f251020801145c0c4203007912500c0c032401d90440140008070703091506044041511101d16000c84400c210900801070007110106c84030000840181821407c000d000c0c0030359181040d40301d0a03031200b030409480c12600d401c84907080d00c2d91650340d503040c50410344084d00b220903069540507880c101891305041c054040c2e80a000f24400304820f0f240003103040c41c0540e40d94031102d9540e60303075107010280b071500c2510035902c040c000b512500060301d1281400c2103040f20403010761489402500c844090107500000003d00903021000d41d401800400681210008840302c41c2d5108848084c05034540002078551b07855014000780d01805064070110f84400c10504110403940c05a6400f580c4c0c00000881c1144860080c200c180011000c00114500e0340c0b280f140b284 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 747936726 1250 747935476 747935483
    0x91a2b02090a110f03070e090105010e0418051009120c0c060f17010602100f06050904020d140f0303070912051f06050a0e0603070e0c0f0a0c060203090c130c0813 71
    0x494140110301c080340d42e0131100004407210400030802c9003075a0701015400b1a02c10580711b1190f40d504040020b4100814892041e001d81d41c0d03401c011260340c0d034164840700c2c140c1e04602900c1000c00c4942c000390241902c14000c3c1d420030b00501c00000410721804004802c16000060365066505100080f60004001460342e0200644509040c1c0070700303c52001c080c000c003865002000744d000003991103001e485221004c5250b0914144003004251601000c41e903100b541160301c500b07400c1c06850f00d1480038602ca00214194402c41150710303142030b0000000d40c0500842c0d01c0341c2d125282c5e601449a10004000c038020030a80101c1684082c1041c00c0c690f40d8800a828031700410081d8071a00440d074803079146e07442401900d100d6010300919042c2480f03030a02800700c1c4001c992080c61700400701d02c800d2151f40d100680b006800260883c00c0c92084101c5a05554491001e41d640c0c00c01c8082c60350350318403003803180b84155240031401804188034403541d00d05004a07240c0d0301c01c075a00c1c00c080f1400c115080f24182c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 747937976 1250 747936726 747936731
    0x70803040f0606081504150b1e030102040b040617151c24090b09030301032402040b0c1b01021902011b060903050a030507090b0708090a091a2b02090a 66
    0x704d9a04d40030310030104007400701207415101c0d140504080c034071081c48013112500c0720b16154002d0718649941d5004549001d64000040c1c08425900102c0c0c0240b1a03035001c913031080004100440c1c60356010b19001c00410008480c0106c6845900990b11400c1c0c0c0026034503880030400040c0000c19a01d81d0440c00313001c1c0210202001c500c507641c44440a4895240d015030025921858032041113650071586030800390000081d415981141c0d960480d12a0345c501b81030841c40400b1a0207943c0000d50120360280403042d0149460349856440c444e624000048c0201120403841d4402e0115480002c81e010100400340c00356081101680041d100030700b18003920705468400a04050100309580105940c0c14401e50b9156624155007000808554002e0550300400412140030012040000c0035542250380089035681d0380d002d05000a0508551907004e18042410201c800004d400380f00d44114010205650400807103488084c8a1601501903e0030440c2c201482c0303041001d4100b40000c1c40d030124842000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 747939226 1250 747937976 747937979
    0x509010b0907020321060f06030a11040927031b020102280b010e10060807110a080a0210090c0b0c0a0605151003050f18030f030907030c0506070803040f0606 69
    0x1c100321030700445680340542c1c000034070444a00040e02c40454001d98100801c0440e003403410001d21444148041d641c81500c0120200e10601c100b540f00d0303184151550509a034540d6941c072908007406106c00c080c0c0e010303600003c1d035020086d00481c03404601c5034103544034642d21074000d01c041e03442d0301c020340260704500c1041c11505032118408102c00d010080c040300c000b03c0c00d013189000510314805030000c1c1e5004505a0910440110980550007030310a142410b4000d680c64103002c80d00740c814a007400c3d91520a087c04501404107910042403540e42ca60b0907960640f42840f801800d555155500400d940d042003000c012258122003c1c082224914013542d0750400d068480405442003601c4401b81c4060054488500703242140c1c41d99030100817428144064a0400d40c1c0007405500107248480c00c003007040e0300c0101c20a00b44200c131213910403600c82a40301c0c102480003d0303860a00d40011111041000804101850720b5802d488599900000540c0b0303669959540e040f040d12500c2d001c44820751035010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 747940476 1250 747939226 747939229
    0xa15030204050c09100516060b1203071406090708070306090218010b03090106060f021b0f0a031104060b0408250504060b03040302160f0509041505072607080601030509010b 76
    0xba650040d42c8100c86540c607111428100082d403100f0108800c28030104118640b806081500c1d03c600482c0c00100c0010b0070403900e00410300040e1042d41904043c04009201c0c41044180e20000100101c1139046a0300c607555100503907540c0c0460300588080d030f405081c003000080d04e01e8010801043c80a803140144080c041b08001043c6803e8010700b01d030120120030003240c00000d20074a00100301528045808000511029448042d5500350b0442c992991000038180c2d11072080b04071900c08080d00540442c1d0b5070707003080c506001030044110302c1a4140000000c00c0540c0400307031000c1e02e192038060841c04220703d408403914051035040b109400c0c215180058a5541d51240b800100700150030740da507a1400345002410040c20b40e10044400340050018440c2e0a80180100151801902c086d03086031036506110700711260000c1c0150406003080e0810505030790104010020421002c0c4c40301c440c45503c6914032300700004841210015030400c0001c0c409611076003103103400801d17a030000a4134005040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 747941726 1250 747940476 747940481
    0x100b0d0213031212140105100309051027020a06120609021306030b0a2619030215011a0901050f1905030118051e040c0807030506011a120a15030204 65
    0x10310a64100300d012030000469508041d40500d03488200c00b0800c00040402003081700644180200341c010400d006544111a010754446600305400a0854401ca007084030150050404c1803142c039289103c85001c60b6561500800490013030f0790040c0060320b480e003024001c40354050700b4803d0b142401c2c0c440c0340004a41c222031000303140c0314401a2220b187c003410610090240c9207076900c42030280000b00da01300004141030524169404c001642c1c802441015100300303240038501e0b241c41004e500e00c4c0841038201038000601c02440d110404960035140e90383e1044096420303102d0700c48a030b0104c04101400e00782d88139000800c500703c043c000081c1080b014038034102079000030300560800710b140000180004114040c60301e00c01c59160718107200c540f0b4030352841894424014445201a00b04e040030070204944109404068206a4103c80c0c0041e500d0174100c0d0f4031a028440e0800061444078403200e600c2e8400200c03160f1040145102204c0e8440320709000c010316040140f080001c03160000400165900d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 747942976 1250 747941726 747941729
    0x3130b0703060f053a060e031801020d050924030a0b040e0708070b0901051207030203040614070206071124010f050910030305130506030c0c01050f100b0d0213 70
    0x140c1d00080d86604001544884004640020344110000082d894a0441110700303410640c0803000c1c01c1035009484003400004005048000f4215814881e141c0045000040986000700c072615141c0c20016507074006a84031660f40c1c00b07400c00078004000310341c1942068149540d0300d10703200300c0341d18400004901c5000c6075041a02c0400030180c9407562100581740c2802501ca1468807100a0501c15141c2140c10741c1d2400302d40700f16240c40ca070115604220380e01603820f440200c0b980343d550841d503107400c01008001398422074040b0359651602501c0344103200c52528191040c00250001e1485458021059440e2020204454020f21842d0302419070340140120030300c80700b0301143c00008694140003400b50780c0311450700300c503029210300003c000001040514001c116500750504641c0e948020360350011400440d0440c1d40c00101c000b090003081c104c3d07500106180411b000082103140c8a0400380034901c94290b0b00351380340109448040c025440044010a500c090904005203045801e009012403d44203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 747944226 1250 747942976 747942991
    0xe090403050a03110f1804024b09010e0411190219080301050603040602070b0c270108180708010c020610210326011403070902030f0c03130b 62
    0xb00c0d01c0000180c05000e9003088407801e283d00c2d0705010b072190704034040e030140b403440401200790310507101c0c601c2e01c0d50360440f160310324290b10707003081e81841044112030303402e8000c02e5445c40c3c06075800c0ca80c924a4108800d0080c492549100d070310700b4255400440e0401484600607a10650702c0041c006404804030050440c020654200341455403400d4000e401c00f12600210040300300e40c486040d00160305801120b056400444511741c4030b854505007040240100d410051070798080f0802d0150401500001d08000080700044514500005260f00d00c00e2040030305c42404a081d0f500855103a07044001c16007851046401201c20040e96034001c42c1c01e4031407407000440540c0120007841006000b60071080080e1020143c00420384580e1201c0c0ca100d00250100602000f50004880d00242c0d00c44610035968852a41681c015584071072a0b2848880c0080f00548603100c0c00c0000a00c0f92054000d0700d100c0c140c880f41c200550350b60300500c4105039100504c402d5048010000f0200041e441e004582e024046 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 747945476 1250 747944226 747944237
    0xb040b030919200303160b0408071a15010e090703021b2406120a0b060103020d0e070503010c0e01080103061a0d0503090405060a05130e010605060a03020903010c18030f030e090403 79
    0x1040540103e0740c118440140b8081d80040000102c0c0341c51504510f1980c0da071061946d9440c4d0303554103241d1218000c4001c02400605003188030a1a20701d01d900050041384601c0b048a4529816401540c0041c501260103400081000c0010a03080c042e501826104040700d250f240360902034038409040c018442c0c05d80e1600501c8240c641c0c0c800d500d0703505196001d0400e850768490300a88800c540e6a83c0d00c00300c40107044014200000700d07642d120742c050781c1556200150500094050b07540e0755032540340034001c542c001d618103441c4c252030f503210f0140450480c0f01a192040380780d0a40e103408000e04035401c0009600c190685030b0100c1d07520754004141c413a80c0100d001c0d6803580e100e4010070082e101c0240a4074801e0504820074051070380c5051070165a94044000065206444282603016060f0303a4010b0794002d05c089007074048541c05030010507020800724000c10061050314801d40e03007016030012100049050480910001e400c1b140406400c44c02824448060303008000000d0311006e041304c04030000390 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 747946726 1250 747945476 747945503
    0x40201210b0d0515010f0503030409050c07150b031501150516080c0601090f0911040b01090e15040f050c0403080c12040605180306010302061909030b070f0f0206010b040b030919 78
    0x290f004c2c02090140c02504c802e00d015038540380010384c1d24051400768054190303540c03011940502d00c05c8110740ba41a449040482c0d01488010450000d10200b80120300070f02804201861002c4480c90540c16561648646c41b042d0b20003000454030b42c3c004100e003840c400009106200491005009030480c950008000c100d19030408013248280e45002111000103400c085500c00014071000f102000d40b00d0696001807070300c4082c00100c0d480c0903540d010316800c0152030140190b22160121545a40200340d0b001c3c4962134412048008454044a001d03442c8a4180310500028004000905e06c02a0074811900603455800c4078800e264000e0344032801040c0b001802c8510361a072260b00001946040340604605d40c9980c002c01c41a2007411aa02004503441c403135070042d80e000348002005150400ca000100d0700d003103d4060201c0d0151150000030414a001b0400701e14400200c05041e241070b018000e080c10f150103404403180d000a84190014083c1c40700c0501c0024044d114031006c1400380c1044040300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 747947976 1250 747946726 747946753
    0x8010c0207090e0601121a0403050c121201030305131703040f05030d08060411071e0203150c0f13090507031410050f15070206130801060e040201210b0d05 68
    0x100c070503844014039506001241404070b1000c146a411528401d0450f0b2101d05107103000482500801c2d44540f805001009110a1562100160800f00c060f10125252040060105c02060040f000708141c1e1520150060001900c60b00c007808280003c514400107490320f5120300790039500b00b91160911035002040c1044421290414207000782000d6010b805030389200c0e440140f00380c80082c03515015a84508c00c540e0714400031400c6a0103039070001408400050321036a9150040c00051069101e4420307084003034113040c4820400d0340903c1e80c040b14585003a00484400d047c5401038100001e285070400400103c41a0318007039507210f8041594005500052110342181e11300000e0040c05081c1c15014051049450f26428540c2c502000c540e0b014400142c1201036102e0701ca01c00c0003e40207903010807400441e0185071654800d59511000a221041c2ca0f0615101444021500a80050300404100704003000804006400c81120000070030007085200100300c1e000300a0100b11210f03441008281da20 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 747949226 1250 747947976 747947983
    0x7020a03180b0909040c08030a030b041409100c0c0b132f0409020301020403021816030c0e0f01030608120403230d05030c131508090a1218080708010c02 67
    0x303a21a40d400021030714240701400e0024000c0021207402510b0400205050000450403c0010f021800442c3c2d510201894000c0181146c844501d002e0790420711098114140722482d41e106030007a170028040040305100480180400b1811803041c40305412510020981150000c0d2243d0703400700451241819624149140002030340c00c0b0311190480950341034940c480d402003455041421100481e480329540000703402840b072580300030b61000c0ca140b098200c10018162040c410820707000204c0410941c0c04007503082d40c9000c212800083c1c465905240c1c01d1504a00c132811409061500007000c40d20b0390055881c140b85102041040c181c0031400b0800c000c20640840c1d22502d03c12030f00781c1403846070036100b40d8071031040c2040018814048005a0100c1102c41510b058174481034030196500e98811171059501780c40d0b4170083c00500201c002824603080040c0c2c4c402e00c1a0302c03180700c000030011250203c0e106039401602600d03411170140002100b020410198015040410002601000c465000f926 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 747950476 1250 747949226 747949247
    0x70804030f060c180806010b0a090b0c010504031d030624040603141905030906030c13061706040207020d02041a0405090c0906031c0f05040302030f01090302010c410307020a03 77
    0x1e10b403048a13010300040c00c02144c200d0460707045101460312024818425240c00c2c0c11600234102011012604540001c41500004c3c0a03d00039100e4640c942d01051020101c11031402e64a078156100c500132801c501e2940448100740b10010034640354180c00c0f4000038007603a0140e0300a0324185506c080d000d03058002800401d04286a0031524881c0b6580744c0e8a00d034403405003c401c54070644020000543c0c0000c9001161100c901100c1c48184461300c9100c0a8080c03104104030741c03c42c40302e0500250b184e0406100700c404058008014662000840d420040504800000001d01501079a088005601c4601030382c1e002d00074a00c06098002c141400340103c1e104000c0502d8866484200d10001290104400c0301d81c55207280781040090711811001c0d515445141c0c8000d4040c800c90041c842e584906503c41103084d0b2203a4000c1c00016010b110072103c880c00100c07a81c8062104189a03028990721030710181a00809481c90141d15003130380310b194115001180c1000158100309010010154814000007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 747951726 1250 747950476 747950507
    0x9110114070215030403200a1205121f05040609020903010e07060512151f081f05010503130c0803070507061706100c080301140405060d0b0c070804030f060c 69
    0x50a011075500081c0c1000740110b0711404103040080400c041c07502c280b1118000368000c400a4000da511184071583d1100581d2042e0b0717051301100f0011941a1150007210f00d031110180c81d82106899400120080c107030384140504c06406201d20019058075940a94002464000001620340013000181030943e08921460907881d000400b090120903001000e6903900104540da001c2c0c10750300d0b80c25085461081c50300280c1d0007a10741000840b0380c2c819218030881d0072902d6079070216646400112407501908140a40d9464030182000c3c403055204d040030f0355000c40040c01c00c403100241e0741c0b61910341e0b800c2c9410007003858000140080030701c80304000b8000180401c0c0b821020420100e42910b0115201034595481f460007a12408d07003642c8284001a0a01d0304100c40ca40d0381e5039194804100034515030110342c050760900001521518000c0312408405412508202842d42c42c0c89500c0347d40d0f840203808031450b280600c00840403520f00f00c40c00d040b1a12980740081c2d0803040c00b4010304079a4900101c40c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 747952976 1250 747951726 747951767
    0x5130c0b0a0503040b132f090606090d051009030e2b080f272103030a110d150f12020a0302041a13050601090e0702070b03040312091101 60
    0x703044039800011650302035001604162103480310b0080e400406079190f030107030806e00540c03420b512481031002c550442540d041140d8100024440074007280c240100c0c5d2181d4890310600075102507091071200c00096510560a803031550341141405022200c0c913900640000b10300e02d400d59101c3c1091800b41008105042d842c042d0b61302112100600a0a4004d0003001d5040104000010710b1402042e145110419800c5010080703603424008500d03200131903024440d8612070f8030700c14170b0403400000440c0d464501010310b140d82e90306604800509aa043c1d01501c1c5c1d2020414043d1b6410907105900300070b484003080014851421801c0b0303d0301025504520602400c09503000c00507681c96010408481c0e040d1000704411640d0300740080000065141607800c840915031020040a142d8401d034030130102602c42952003510384040e1070000001300c0c1d00501603807000c04148521720a54001d5540544603240c600f010112640d840820341c3d042e950f04580c80da441da060324080f5a00116a60004502400314 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 747954226 1250 747952976 747952987
    0x20a05061b151f0b0904110f0304060b0406060f02150612030d1b08071e0302040522182a0527010b0906070b0408070c030807031103031302210105130c0b 67
    0x420b0144101c3c1400d030b11890387c520700100e0050703c03001501c1c100c01d11b1000c403d8481ca028200400074200c1046010f1007a40b43c0440400d030300c2d0040108003142e800c160b0060103200080c1c80b0340d500a443c0508042d5002d0f49401512500010070401041103c00c080004114020030901145a950601031040244807400c1c0400400a0b4000341100320349280c08486400c801a40c03205900034411600903a0f0400c25007080302000444039942004485008c40302004182081ca554900c840594030006000d1007807000d55440030101c6040c44128907403c61541062943e4840001d034241c1e004401c03050a0907205000d452544441440003401440030114541c41c1154250010b030052054010081444900f036020500b8172445505845882c1c0c0d002c014402e005480742091314081c3c001c00070440002d078405001c581040000300642e40101c40b45110300c50090550b0b402c100c42e07503900ca040e60b010900b00524501221200340501790040e01825042d03010102c0609218848411039041594445020030a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 747955476 1250 747954226 747954239
    0x120325030f022107150507031d030a0503040f080903010921110709150305010603080913020408030d05040f060c0306060e030a0809012f07050901050904020a05061b151f 74
    0x1c4401d0b46051950802e540394210300c0d1400d8800b0392003d0200c185d510741030401007103d42542c44102042181c410040300604e2280002c0d650b442a031030740383c00040e010f01c04680061000c03001801d916101d04e03801404c00c2c0540c1c01003804c41e5121081618000f440310f801d05103070003142000c1031400605140070204c218101204659400b164032508040c2a80c92042501140b01000e190000e590302030300902003155a810045910781002131014800c000c1c80d10400c0c4207054034802c03141180e00c10405141000c1031488068000c1000030025500000440b00240c0000c580744500c1c1d0440c8426180042d0481c02d140ac000d041040c1094064000d50220b0150700c085042d04c801d491608400746408051401055514140800c240c0c1c0010100b24040341d544030508001700300b140651700b0943d0b0801c0d00d60b82c0e9508220008800707440194005464950038003072800e12600a005502200000000d01c49400100c1840c0410b0403007082c901103010010700003285108800c9240740341d90091140e503814103214 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 747956726 1250 747955476 747955513
    0x6040e12090406080319020706050a0909183201140a050603030405120c030606040606081603020f040801270506070f09030602030f1602120405120325030f02 69
    0x40c0c24902803500868032590564860b00081e001d4520407080d00d4a5000c2101e0201c0601030800c0254054003030520045541e41c407590039240f08501c5944c81c40d40c400d14041e40305c0c00a0020400029100046035081e9000c00c0c1100c0e54001c144041e484030450b03e065000f0b10201c8200160172019240c3d041034100e400b82c0000c1c150307007600100c0143c0001202c0d11880e00007891480b840d4800c90304a610800fa20a00860104070f500030380c4420b0b07090300c1440d51060f0070402141c215018030404101d201c004101c0c00c0d6801203004030034280d070b42001850102d079100760707190541160b842401d441e9107498210204801340700390000c0d264031b104540d84100340107550f0940c40f24001080d11080160f105a2016518480d41c509030007560007000455403401c03c43c0e465005800201c40804050b0200303100000c0f03030b0b4030002e04c4170601030b106c4281e141054100010001042c0304036120241504c01481440399280f52742c00703503070300415458940100c254001c0c030b4003400308100301c0d01110554010490503400c440651 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 747957976 1250 747956726 747956743
    0x203100b4b0c0f010e061608040c06031a0613300b0703090816141b100302070206030a1e020a080105120a14030307030f110f1c2306040e 60
    0x40781c0c0c440d141c0c80c800803003c0c504680868a480150700304100e0040d812404102c007400f610304140440a03200080d0402e450709142070340d00500c0054140d00070000c5921a0340b2103815141410042881c2e182440f000900d41c6d080b0300051081410402c0080017002d0002818182e13524040ca0b00780c8001154041c41c558a60f0000700240411214800140708141310382d1080d511140d004d05aa502d034009042d00020b0460420800c9550003244000c0280c514400940b202007c8807401e040002d05070301009100301c43c1411920001815001c0c0020001a5900000355118000c3c205000841103122020480740508e6a101d28030603c2c0304125000c036160b0f00000c1641500c006644504a0707448101005c2e14001c100000a08180d000c031014030440d00021000b1030044e030640e5424068495003001130012100741c40c054495400c400c001845002c4207100140070829602e0501c210112040481d00301515a1800754a036294207140b02d0481c443c148441464001c0d0082c0d07400c0243c50107031450303613a440040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 747959226 1250 747957976 747958117
    0x16030c090f050906031f020405090702030720030c04020309010f06050d0b01030321020c06010e1e0f090703170702131b030b030718050f06220203100b 66
    0x58009000b03904c08104003140d081903130720002d11059012002000a4108e406100c0c0b0408040000c00c0350184000203844ea05900900290700715918015080c02c00624608400c2d0107000301109180039a956101952052400f00e00100d0951419030031384040717882540005104113080080d24022501600110781903e6142c10540541156030307400e04020b040002024140900004a034650050040313001c504032140140da000c620b40b1106d2a089007148800c2405069030304510020304030100b45440603800450b0300301030782c103080d45036150340e01003d888150648034101c00103401011401c0c02d1000d40854200d416040040b040c80d0f00c03040b00b03c0304810782194101030302c07400018155a024040d100c0148070104090511031603400c0110003905007100d0480c5d45000c5030b40021081c0c02c01030f826810b141d107082c0802c1c0d9021912401e580094002904803580034814840200c2e0011600004182d548400c40390f40030003408403000c013005001c580044902d0103008003a140c0d00420302c03010b842c409800703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 747960476 1250 747959226 747959239
    0xf04110d0804030615050105094c02060603030406050a0e0102010b0306100302040b031504021009080703030e090702010b0907030f090506040c0509010b07150504060b030616030c090f05 81
    0x192540051000c0364011009481860002400404c000255000303031555010914031050b401e039a0001580c1c04d004201c0c1003a00041906010080b5440c41034641c0c0c0380c00c1e8482d640c7c10030420082c58904003010f03207d0130203403026580495040065010841b00760710000c1200254a800d061041c000c0c494041d49c040355042c00307030b90305400d0040c0e8000c0d0002c1010a1028049400030302c2c1240e0b03490761810389848140e024a1a201c01c5494600b0081241c1039881d0b141071410340b42ea211a428041d030301c00700440d50010800000700c04036128006100303010046010b5941d14028035035002c01c10412010161034801960304d046502c00094551032013a0f9846543d600b800252941c0075407803107001d00b8a820b0010510f01441d41080104000704a5800548005540b1f098080c1c2e20b4481c1e0900920a0540180c4100e0b000c042007070000150350001035219200d4007001c2203047c0200e0119203010360039103003810b0b0101440880359003d44d0520a040d4030400700d10348a40e901c0d1801001407400f10740c074010700d8003401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 747961726 1250 747960476 747960503
    0x151a121905090c0120030f0901050d0c0503040605150d110307030b01090e150915060a0e07080402040b0109060509040c031d0c102d11030a170702060f04 67
    0x2444140c5036440506a20144514540303094200d494006402d4500e02013405841d4400c004c10a5a145600b403801c600000c43c6054a00c000c4580c09400a10f03400b030420000704007034114038500780240d5841005a440756903c9041c540f07000429208010019402258450140c0a240e6550401040802d401141c0d0303c08070114071780031a0030318209400140011240c3d000028414210f0fa11292809240b9400ea841c0c2d190b0081e8015a14030003030750f981d100e641c41070202071000c0c4000c1c682d80b40c10030070080600603001d0b0780c0c2c19000303c0d40004440a00115840b1410030055003001d01078041c601c0c00910349024285d060100c0900940120191540a2592644a04a2075000f94819800704038811001d0548401866099645e500802130305409002c100644000c06409859440030039605851140500081c940c421002d0002c4424103100304111709001c003001c01c900b4030041131045190360b02c0c014003100c13003500082a080041e1460701154402c208000400c05c21250154101f940008041d01c0072 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 747962976 1250 747961726 747961741
    0x1062a1b0f1403010207031d060909040629030a0605040f051903091a040b161506090605032d0a0b010f0915030804050d0f0b0a151a12 59
    0x21110482404004045500070808040040344901207071801d201d045000030048040c035080c0e010b2004020003141a102a1a9450078203040342ca0b4070f000007030410f9080c00d540c17500064080b4001e035000d4480301d9482c0031401c4045003808495040d4594003101c07480400c0480c002c43d81c0c90002207005001607035030300041400c111850f1403c03c841c0e5044000c0396a5100d01100e402c10007281040f0403800318103e603100003628102900c030101c6075071307130030740c01c3d50800d1314103220110241d0002070a0101c1045041c00700000500c0030308a0111601046c000044c603508040d8884119a000c2d0800c0f0f20a40c031804150040f0441c225503000301044066081d043c03030b10074100541c945911b030040284508185400030900716070180c002c1085807440742c01400b1400a82c04c004402c042c2c140005000c040c0c08000c00c0c402800c040c00000b08940c4120480715a40e4542e4a078614040350a03560081100d480d140c01e0345503c8003800000000e0071102502d40714007440d20b5540c0c441881042c0414010361031200c0000c0c0392 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 747964226 1250 747962976 747962993
    0x190506130804030c031a0a09050a2a1e0e10050f0a09020c101803020703030f110303090705010305071d04090311061e0108070e010e130c06080f01062a 66
    0x460744444100ca0300350300c03891b1030410301501c0c0d205424281144030010b1f40c2c0921900400d00b030300d900103000d48888000b079208c50400c90145c5100b0b800c0514402c14046070f00c41b45000c030034018252a030104111420780e0703000305004034665120100c001d46071401c2c09007800c0f1610b803070700c1180e00032140c50307050360329403400700710300041c1544076101c0e49102140c030324540400400d4010080b49407500420080440c00c0f6414410440c010000c1c0c0141d0080c4070900002c2c3c0180480306984a11703081454144020304000d901c3c60340201e07104280c1e84c10100040050396058001d85e038108180d801c0017165440c0340b060000c3d80400002415104a4403155682c0c289802903a40c41e1030103000c24103a070780901e00b605241c40308041c41d549088102c1e003440b000064005011907058107890085140510700c5e442c01250340001c03034014105080300d0707864242e080001002e44a640005041d580c442c00c000e8a071044441c03003d281c05900c07003000c1c0310b5482c0924007101d81c0e000c1080e90221917800c0c4a41c00030324601340581c8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 747965476 1250 747964226 747964229
    0x507140d200d0f06060e010f08150603010f0c0c0c0f060c11010e04020d0203101512090501110c0d0f0207050d080a0e0a080309360c12010b04050102190506130804 71
    0x1080f00703070410100134820281c01c4a016a1105030a401141e60b0b02e2000391880c0d82c81d8072414041d82c104001508440e10440c810f070b0381209000b000451148200c0340120304842601c0f00500101c0c019203030711b03020024610904801400c030049070f00743c11407800c4005030070a502650005e02c2c02d1500304c070225440e8003c000301003441d00f02070011901c031120841400b000350b10644290038103400710080011180d044400d0005414106ea036452803041c07001c60510043c00040c4011200d9548030b450045003000200052301e6904c020744000c1515140190000d001c06088040b0316045404c03e1105010036120f1480a21003140d124102955818110b81d044400140c0141c901c0d03400302e41e07001c0010314207000002410070a9000c80d64200d402c1c4604072005206a144d0001100c595460200d0100400c15400d10661242c04607403818a0001c0c0c10ac114519010240c0241440c40340215050206590420643e110b10082d070303000040d00c0500340c0300c880e5030b000001d01c800d20401c0780501c0c00301040a001c05550 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 747966726 1250 747965476 747965483
    0x6020d1b08030f0712050408040623070f0c060305060a1802120a0c0f0e090a051918060509030313080901030e1f0b010801120209220507140d200d 64
    0xd07240e0400c1d4000d8032031101c043e141308000414138800c550200711148615130140754892512803429243c04402d55000c25180707210620414210340181c04d260391070f0003d2480511485402511802c1880c00d290004910303040303d8201840c02040003c5500d6a034060f03030595502c02d0841c82005c5024003000045d2240788820032150150a09001e07100d45250003140d10060141c0b581480c4c1b494284044a075480c0d1210080d03800f144890200e00c1090702030380402d4000c0c100b41820300000c41903402020035285189102c20344480e21a200c1c000b4440c0e46d1041640003451040911b255003419401c1900d1f503628a0000b030405040000e008405a0195000082c0c1c10000d906448000f040c8444148809020f603911000c0d89003404040140d6603c203120b0a410ba5200b00c08401c00155a0740a00064050041c0111002d071032204141c0090b01000700b1441c0440d200e540103200ca642000f52000e41500310010440c0500041d050700340015409206107202d01d912424200f00d2203c07964002002000d82c284040c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 747967976 1250 747966726 747966743
    0x14150c060105060f0409090f0302100c0806132304051b030c0108100527071e110705040516030b030303150d0c12050319021203220203070605120f0106020d1b 69
    0x2003005001044e231501c01d40203400350f40064015699030000d03110002154000501c1c19400514149400201495807208000700002c1c0c0d0040032914080301d4008030454101c0004000c2008100b01081040c484055a0f034548003140d0081e14000c00c1d6107414004030707103050020003000a80c3d540c0214412400a01c8002c20700b03030725848030f80442d10307141e401040c4110420052500060005000d02001099280240c0f05e00e0303450710800c0411120340050582c3e00b0040d00410000250661f103601a940c02003c1e11320350314401001015001c0c08440c007600e61301e4044d81041c0300300706d4250085000c0412111003914400e4285a80d03180214201200e50004c00305031000a42d40014081300001400000e041502030f2080310ba1109000d0365100d00f005000250340900300000307050071052030181e2a41310341c00300e00985840250341c0041c1c02c1c609943c00c00c02c000b80b8003144146040c0d80c0c96080030b03000b032090102c21910f0350401000944618104040c0c2d0300340002035110195800b8501050194281c101c6820f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 747969226 1250 747967976 747967991
    0xe0a1805190201020f12070b0a14070e04150605040b0a1101050405300d020a05070512090414040209040204050601020307080706151d070806150414150c060105060f0409 74
    0xc015036074000d1001070f40117114040700403c030b9101c00603010340b03104420b0040d81e060a01d241c1d510295130100410000030707580c0310000224060070703204005004250300d444205a2411400c05e01044403c040302e9041c1c4540190b00410190b900082150181c501c2c9401c0c00c4d80d42c52011100b0744018600344208981d541c6020700b00300070300c0004541c8144860802c00400c00020649011000c1d41e9520804c00d5444002000103500074126607000304202c503107030708089051443e15250300d400e10640c0d21070200710140000303048289290520400600c0c90303466100815604090b00404c2090b100200000d01079513076000030904903030003041a01d40250b80122400d80e00d051910340359025141011041414040310500400c03203c0c03200040720710f00c00356181080881c4d5a820401c0300c0c084005032409400180d00140c8040d00312061000f000034101c2d01560a507101920014055503224070344440e03135030000500040f041e4000c00b04600d41114022940c030354030b0702c840e80998203482c07007141d004400302d91400e1030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 747970476 1250 747969226 747969253
    0x2210c09090705030127110c0a03080108210a020a0807080703020c090c0901080402011803030201050f01050a030c090f0f06090f15060c0209180708030409060506040e0a1805 76
    0x200450a01a944040c807621022015100c0d404280075481c0ca1035410346c16100c0b09504502c0071049070400305404925164010400207080e4400d60682007103400012608050680002d0030074014604140203151108003181e5600100030300c0c0c8000801c01e8030005000164a2081011965160708040040c1c0c0d00c04080c81c20a905610a400c100c000d805501b440c2c0009140c5030071014480c904641d940740c074248107900112469680100201d043c0f201034000c02045040c050305010141d07202e41c0000540b03013054964105c690105a2005101d81141c1c001840003400034440c0104640f40c4101c0840d5428400c0e0408000c0e00210b5540540076103814800590625181c100d00194900d004040000014080034101d004440340210008278412920240c010700b40000c50f95440311086410440385021803c0440c10f04446500150040d4400300341444170311618401c400060070201c5040f0314051400c507114a40315001400752030050340e41e808000c07000f4111040e01c80001d07070042c1514a00c1c4940b4a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 747971726 1250 747970476 747970501
    0x90c010e1905030718060e0705030406050a0908030a06170c06120a02071a060414060619020309041506080a020a0207050f28180b18220f140615040221 66
    0x6002d141158101b002c00910352580382056400365103da40e405203903a89685032034002d02005007030703003c400381d6581d02030001c03e604201540c0a03204000000c10280d1900b10010750760754080c001710b2001e800500603100580c1e5040d00325500300364100c002c20005c3c4d0b81c0c1e0400340002d015400b4042e006506ca0410191400044c2d8001c1d807183e401287c080007500100c031040c8101042c1161981c0e0418030030403081000a0300700c42c05168298051040301d00d8105070758040741c00d07154800034500d11009103007001d01005810406890340b107104100114101415036100070f50b110a00d1003001d000f1280741030795907400d0f2500c0b081141c00101c0c03000f81c4039180f401d0b850400036064132440703500e40c134003080358400c2c1d0003c403240a141c0070100014050303042c000400070203031241040601441d402040c00400040c942400c1c3b8405034400d130164cc41861590305504010600d0140c907010010f80360020420070001c0d0b0058034056004070003c5e01c00688031a80c480040c900e40000410464000c65024100605850b800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 747972976 1250 747971726 747971759
    0x40c09030f151413171608030103030806191e17060f0a0905060408090a120b06010e01030902031c020f011a03100c0f030902150a020c09090c010e19050307 68
    0x7404200144a004000c098032400c3c180c079004048078240f6003000c00710f081c103000c07000d0403240420440d00d00004245002d03031280c415181100d07501340c040010414143c216000541c000c1082c1c80d00504000a40705002182a1a00802c803084d0358220f0240d40300180c009000014100758202104118206070a00746d84010450300c2404075458000003c034840c05501501140c242c0c058018242a02c590341c0c4d002454224083c0301350001f0b06288005400b00ca1016a04242c03030003050100240e0620800041c0f44000c45440e541c1454106001400185c4000400f14003260041400e00c000c100359807402c07818001808002c491560a203004002070301c0c40c05103e0030074048101e0486031008400301d120400c3c1c9070258a41001320f0207190101e00154002e070013110007244001c14884210a08902402c0f85420440450006a0115019034224145500d2991b0050851801040c82424440009040c041e1180405004010401d90716034503100448940c0e015204c005c0c103039109191102503504c05103121 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 747974226 1250 747972976 747973013
    0x1002010902210307060e0c06040609090b04060b0f0706110307021516050f0a05040503072c01290408060c0a0f051204081b1002030108070f14040c09030f 67
    0x95a03612418810b1201c0c401404902009141498155101e1000400f03000c0b42295090282c4041d100d0b1036952200240040e0005444070000c2500f00742e01c40c0122a1a1072000e80600d140032001d201c8905210141d68002c981034a0311030703568190b1f240180140885100d8044400004411300128035008600c0c401a00d419082c130264030368410038600b0ba2010241142030100b0010040c400205a408000704242d0038103007840348c50310b130303603180440c3c6404d009501088260f6140d03070310700803000440310541492000d40111029030354101400524910440060141d483e0461200104a0500001a10010801001607800902d4045a5001c996111481400000f0703140b9120044d00ca02030010340d003441090521441c40c0741d440c1d5890700155130010705290301c00e00f010f0310003280c110400c000121001214031737070260312549042d070010300d0401c55401040031840f084000f80402c1714800407010403514116804910444042c0341541c20790341581024082503000909601401912403840000304d10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 747975476 1250 747974226 747974239
    0x1030309051302090a081e03070803070c2f0406060c0b0604150b0408031b071505030a06090c0f030c090303021b0f0d0b06010f03050106050d0c090f06030f0506030c090f04030309021002010902 84
    0x1080400d2900e078271800c5c000400ea01c1c1d003400402c0e40140f0034201060041e10485107410740d810040304500344011001140528862282d50f5856981004d02502d0014a0241480508043c45070344894403050000d0215003c0c2c0c0da18026401c0b82203a041e803520085c00b0729620103680795151b06005881e0303030007558007517200202d164814410010000d60b0b40d00701d4040070b41403404a503401c4411542e50b44058420b01d0960349070600461201c02d00c0c03082c4040080142c60311418090341040150688800102807801c0c400740c0181040882d80200c1c2e2605040511000e61b00c0c61021040000c03c109030305907010342c024660520041c1007004070781d8220b018040036255034800244400f01101910300034002e480003d02e0620550900a200b0f4000b28640111070912500081d221042da1040010942c40040040e131141300700e0890529500c1429000401540902484450034000c110721140203441840c420b60a000001c0c14584603910503109a5801041040c00d0362400e24002e02810741550241c0c811745 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 747976726 1250 747975476 747975523
    0x130807030b100308032e0e07120507020d0503041401090b04150513060e150709050a0b090d2301090303050105030c22020a03061503140c0301030309051302090a08 71
    0x7108202d0481180d44c00f8000314615078406015908054200714140d10420002996074a12943c0001840181040103294452031401400041c14005142e2801c1c4490380342c0820700010f940d0107e541d006090b42e90600607031307a80300e514041c8114020445a00d4442d4a8041c4201c20011a40c0e20180114041c04c03191910311014030038502121000c1e40e826001c1c001d00030b065800039142d03412a040700e1501d00c041c0c0d0f40034200d0002c22003031041d0455071040020001c5100388007510f08642088090200400301604242c00080816002065228054403006800981008812104080c000824180c1c030007440301950a00c0c001e00a40300a00505c0e00ca40540b540d040301a041c171072030305a01409056220466002c0e0089044003e5009415120030951220740101e109040c1205402c146582940c00080310341d90040140c0885201910114a5032000c05c01000820f505c00d00300d03000e940d402c40d0035816010862000c80d000384101d92090741c0000d556072000600d1007020a0300356800000a1500c41c41d82c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 747977976 1250 747976726 747976741
    0x1511090a0905250c120c0605090c1009030f030e0d0606090903140307120f1503050d110a150507050c0105180d020328030e0307080a1b02100806030102130807030b 71
    0x1c8900c998001e0006140c503e100011030220541d440a171511410450740d01a501e40b1088107940d000c03580d40c0556071001e0208603490400d860b42110101481c545100e005080d5590740e001184000b0001d420030002d488040641d80d10407614946284d8403802c2040f1807030b83c0794010f00240034007500030360126014614270346181c00020700300c0e88119142c0d542c03440c800145010140091421600104406130388510507030b15901c035a40d414010714014070003403010380e030343c081e00900c0c0c2c0344000c401c070401da08030740003081c001141c035400d1b020b284122120110b81c554403141c04840318003a480e1000301e19801c180510580c40d0404890112a56060041c3c90800d4010301041c1c4c1d0780d1140400248445511024296448408015046285030140f034040351480b004404a4a50f4103d030f401030300d2240c4002034006455400c21200000492448030141220800340c00180c81c82081850680a10640c03a000840ba55002c5d4103c8281024102c6c02c01ca07019264408281d60784064003088407005118800f080b400d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 747979226 1250 747977976 747978031
    0x414090c03071a030703050711030c0c190b0a0503130204051303080f060105090f190308031501020c011205040f1b06030b030c031c050409020f07031205041511090a0905 74
    0x20400c0300b281803035611340640480041c1401408c00b0100040084580c1151801784010000860381a0042809015600030086042d2003c10718803c819075905040140c2a240e0301640e141031454206551695101410303050103802c402802540540b508081212100c1e0341d0041460b903d0007540c40d04210f0b500d05038560031f0b031300f01a41c256022071414440c0001d545002c550404100c003014118515403c50502929400c030002d42003282c00300780110401901c00a4140540c61000e0b0900c0104800c03194140003800034080c100d00100310720b480da00020207010003201e5502c1c41035840f001d810a0f10021407003950881005028101c0024144661446e403880c0000d040f06080390000c02601002622400c40154124001c000b9424440c003448000b66a10562000d02022461380c5169660780c03443c0d00e4020b220541100c0020301e11460801484080740c0040100e413542d1040e0480005d041391000d032441c900f402070300c2115501290003000403034407654680042d40114643d407001c020249201005c00e45 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 747980476 1250 747979226 747979259
    0x11070602120a020a0b0a061a030105100c1b080d0207080a0804050409140a061a0105130e06060f070606061b030c03030533010905041a06090414090c0307 67
    0x60703201c0c03000d00140110490080c8114690740c011582400b10903034581511800881c0c0c5c1d40c2e800c81d5034103030802140264610401c0c0054104040c0d500d9581401d00040340c000c0342c600b644041000300d541d80e408100030059240a400780c40358a00d2420ba41c4c0300d80042d61402c01d080c80800501865030006000c000005603610100d034450700c0c0c5800c260400c02880001c0c10340c844143d54128070303000b080610b0f140522608200034080c0c040842c2c500d031504030b442000b1489170317640380c1003282c01c010000010b030138110118103844481581c24200c0e2604000100c860040701040e803d514030014002c01041003543c000741c00c84a40340c64000707428050555114203100444401384c0840d40b81d6980c9800a8860fa0200346d009400744d4001c0c154481413008081000040b0843c000440c2055040c43c070250b0304100590010f0404903800e001903140034914900454410910f580203280c0810fa000403039607030342c0240400c8103603c0f4110426240c5524103996802c4007031103c902900a210000c43c038003041003035014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 747981726 1250 747980476 747980489
    0x909080405040b03031201170d08091b0307051801092304080a03180501150e010f091503020621010e040f020d0203250f090b030c060a090915061107 65
    0xd040600d8401440080d064403408560f05010800940070042034440881d400390852003c1c6030304007004000070398500f980350000103060000740010040c1a200000704c000c007a174200302ca90b000c408030880100b40b0300707001500015840303c800c0e071019250400c900b035842c1c121682640b09126030540101054249102000b2021782d4480910006020502d058002d282070149894001640305c0c0314040b4418070141c0c840708071003e0351034810034040406e2030a000b42c080c3c0020400300b507840d4507082d80d1056464080c428444550744030080440b9101c542c010610040d034006d450740341d42d070380b0301c03d00131506802c5841c544150810701c00001c12070300c0010406600c42e9034000f0454480764190703001c0062448000c40101d07854425840e020007499034000e00c87c10b501d080d6107050311005080040704801c8002d503070002c0d25018601007041102c1e9038001029525101c0039504241d5940c40520115034100058000f040c0c01400c02c070020500400c9100c0d460210b82d100e42e50b214070301015030581030b1601d66610515 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 747982976 1250 747981726 747981743
    0x12141303020c3a020a170d320910090f0b03040b0117010e0d0203090a0e0f0c03100305030c030702010f0e0306180102070c140306010608091209060408010f090204060909 74
    0x1111160301e0020340c07038841d0110700181116043d46030b000404841359900000d0b5207242071046000040c004115801e00c284950406c0250314510012010380f0f00d9225207101c410988800da40050402c4030800c03248440005424138080ba0020301d4094801d03111403081540303259140d02d0005402c80144296401903600c089080c801c0e0740382c50381c844c0c00740410b503910c805030355039942038011000010442150a00c2c07554001d1b5449109880c100010240e0640c00322000c1c42541c1d0411664440900d00b8070303801104110360a46a8a60400070207981c03850b07820045c1240f200140c80c8520040005c05032000b207200343d075140201014001c04950760708901881d26095449540810004001070366902c1d0329804800006007054400c2e141c10303100e11095800907851032140c900c3c91a4608007800041d001d003071103042035409400c00004096503a4074007401c1502041022071007455030769610707046800070594800248001107460a0b80e8004250402c400c03032103145000b00002d80d00c1d605001d480e6029402140a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 747984226 1250 747982976 747983029
    0x90307030309080f07030c050105060a03111215010608091911010c03140706020705010516081506160b090d0e01021504020402040e0405030d1109090712141303020c 72
    0x1903001d000c40c0302044a545005100d44c00c000c1580b540a0500070b4020360b50500014040e003000740c01c403000505038601030030244000780003007000c072161942814019682c0740c10038001e80c01c000f824206104000000e0301c0004000183d80c9074000d810300d0051380600255a07070042207401c11203145245070002400c8541410b071a1f800c0e0b40c001c8100314001d50281c1090034a0416044480301c55a00139001201c0e100c1e80490f03040f0a00109220f681c1e801441c460700f4141c240380d07104001c1d182d02c00003055103000c000c81e1072181d04561103107019691440424902c01151100754a8a034050200c22a4044840e1007051010095a40705440c400c480f450f068001d1304000028218409070264010410f07038100d50201300000c1c4101c00c0d40f400a12581c0544051510b0fa0003c0303c641c000c0d112940018400320100340107003259035840303121403500711900d41031a5032150750708a0303c080500104201c1d40c00d01a001c07400c1110842c8100d44c020030091003030b4241c03100c68802d00200034100c0c610615080d1400c0f8075056 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 747985476 1250 747984226 747984233
    0x5090d0e0907091e09060b0909011502100203070f110d0504150c150204031a040c061b05070311012003040e100b22080a0201080c0f071a010509010608090307 69
    0x41d81900301242c0d150540020352168009203003480540005007511002501c100030003045441000c000c0e000c040c0030280f5000403480000d0038640c1c10701540704084118001038041c80d008102c001d11002442034150340fa45056080a404640004400700100e41540014910308101054417490400d82d0b444090030719041540350700c400c0d0100e10002051107030054446c8042491624800854041e003070300540c2d124114906880510426200b85003480d2041c001d22000800c8244540d0940d961071030040e4210704000c0300701c0c1c60040c801c900500240200d14000c0148a4000c0d00202048001e8035008401500901002940c4c0800a1020200c1d0801d2000f40015130301c040781250440300000c860b640140d00d500944180341c2c009160881c1c0c4a20b01c0e0a09030650508003401802406108058668201140c0018002c404010b100e00758980000548441202108003690405a0048803100101003403064541040c0c0c0c0a001d01480307074004000002d40329100c1c0f06078900c1505204055030809110b6034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 747986726 1250 747985476 747985489
    0xb010302160b090114012408010602030405090a0b0603130c2c090c061b0d1103030f0402040f0f2703021b2403040c080c0612090703060204060c050105090d0e 69
    0x2807143c0c40319501c400102015802180802e0b01800c0c481c459015110300d041e9603000030320386036014801804031401c01007020b036401105031421036900b500c071482940d65410b110340c000d000e03411703125602c00c03000300600a24031440d460004001e4420302074030104035200c1c8062410754082d60f0150020f0b0000d10001942040303a002a990407015803411950071140030343c001031580d000170854070065070b032a46041c012450100b003610b40001c8142080200b103c0136000d540c1c4c0364440184050f05901e0000042030843d240c55102d5070912440c0b2004100f00390300d6120f600050803849405505201000f2443c4046921010140140310b42c59001091500005403c06500c3c0d00c0c0441129030040b81d0b42e0070b038030541e60314200541040c1c0c3c400c0012a501e00d401d1421180320107640d007048206030300c00200d0214540320070007241c03800c1e0041c03c1c181800e030390740c1c5960f585000380603000144250700100c2d0000d2100d41100b24018858401c40003480107a942c44140d9903034201c0a404500040d101e80100c01560400d138 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 747987976 1250 747986726 747986731
    0x50129060702030f03032a031306020a1e02010204061403090c1203070f06270c050105090d0c03030806120105100308031e180d03020310060e03070e0403120b010302160b 74
    0x3c2c0907190342d20b00c141c41e910b080d5001216003a690a0451158904c0307050020389007003940c500030381d48905501340545000204541c0010003000d2903400a611030b500c1c0e00500c16514030300f41c000c0c00d0428042c0d514100074082d410a1081c0030104071495400343d100d0283c14192407040320944018200071400c01c08010f801890b11002480c00e002c00c1224030040780c02c805900428038015080842c6a0051001800c00032100d001902c1500780400d4218000400400c1400101c1d082441c0c60354a0301b82000c00a80d007407109410080009600003000070815400c01901031180350120f85001c2450001906142600d0007114071750900c1c030a50f6400c2c40060403141c05140c000d80360755820351030b000c02d081c004d079000d0300c080e03900d054003950401002c006d0000c108980030313148689203415400e504000200b0001c000d010b000d441e0500603070340c80501d0140c504000042c01011610050074040c10181406480303407002c10180001c0c541841410640c9500030700031180d80c1001503101881c5110141c9420580b074501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 747989226 1250 747987976 747987979
    0x80705011e1412240303030f0a0506030708060906072303060d03030e0f100b03071202210d030c090918030309060f09151a0105040b0a0203120a09050129060702 70
    0x61100d40014074044502d144100d5a0780300f1500d21355000360b0305030003c5003011400ca210350310403c00c000036031a1741c0041603040707222001c0125681d11100c000074100280f0f43c101c41614400c031400c203c000074002800c2d40c01041581c071841914141000c04446002c20111001d80d04103041020030203604021119640041c068500005c680946003d000d042a0741ca5500ca0300b1a40915031650200d40c1031b10428148140450040c031a6a00d0040c518503039210101c0007a21806d60b242c1441c004102681c44004003004503400d03101c80904000c0301034020f208011002001a180c4030000c150414103112f8040302103c41094004290401d6a046029100180049802a4481c807401549500324014041070318440c2100f00c841d041411074680850700c3c403902c00c005031012098403c0590340c1010859050310742c031505003952031086c03800592952142c0d080d646640e440341c008000222440d07501075400c0034860002805210700710001240e480384080c0e51840031400e1510030004a140003402008400e10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 747990476 1250 747989226 747989267
    0x210050c0102070c0b0c0106210816052401050102071a0c0c22050c04120807030e150d200415030605090403030902030f0a03080609040f020306040c080705011e 70
    0x103d9982d00154407030550142004c02000309541c90104028064100540848845501c840500e85000405484242001b0b0701c074040c00a13480348601d500c2c84d003490206810100310b8400b6a43c880003643c400900003088145400c0403000443d03191b1022812104460f0050700c4c2d1202c0300e202c1c21038000540c0c460180041c8078481c03502200d8072911140b41c0c48034000c00b080508040c0006401c101c0c020343d40e00801f0303200b030008204414041c034080c20590220158004030b0300e0f5143da4075440c095a41d004001c07030769a441083d22a811100b20765181c0282004075091000744400c08840200394038400040c0394010b403490040c0800e00130325021528000580783c1503d00801d40ea550317000810308100d01500c069000a46501501c015030904000c49d000554013000180b07100185a207004040d010040c01017441035000385d01203000d22049541400c0e403160000c0a40715181410b2428200500c3c1a1142d01e0b094007603058001110341c041c061801180303010340e44500d143c0b03600000c220b9003450741030f4202e0400350 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 747991726 1250 747990476 747990487
    0x50d020f15161701060e03070803090a03060c05120109020a030c02010b01021b18010e180a030e06090f09160801050d150e011b030c17040317091c0e04180210050c0102 73
    0x5a1644c0c028103042d00d0324102031108105140c00e0007010b40040b19958400c00460b1099180d04200b070f002c03281c1121f0009410301e083d010459003071103601424841e014103000003060091896004221001050b14100040e904240c404e90031f0340c0b0480302040c0503070860054a030100b000b00e92864005100100b400c0345070200700e030300c50744030328020b81088806440c6a010040c40c00801400902c0d84410a0000d00c04501c145e0750003010350943c0e142150040ca00441c0b408030b00c1d2201c003014551079100810051944c80c1079441400d15101441149001800c440300018403820300303c07120f440e1a0340091ba4901c40039905010180602200c52150340590b40e00c00c44410003000314440c8000c28034003590007007908000ca0100510109004070f520b01c82d6040d54080c0000680c01013a0180b900d42d6640c9044066a20008032a08081180b801143d0004203c1d05400c3d455501c4060b103c2c00c1a0129405c000d900312880241d00d0340d0741022402508001e08490380c0c41128060005001c800869000152404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 747992976 1250 747991726 747991757
    0x10201230622020a02061b0f161703010303020a0201080a05010506071707020a080d0f0e0f010c03090504020307110106141008040f05120d050a1a010c03050f0403050d020f1516 77
    0x84e03010161000050b003062080c0525060304000a01e031040306001c682e414242c50358080400e601c05c240359140001c0c0007c800c03a0030004200c0a02841e0320000400d41d480350307521305010f5290180c09804a00042500e0006090354000344540c03416554042c00003420042d040d44e071089070502580411b040100103214800050307503a402800084d10034500906200d420300030340070b0b0800611458105c1804204003200001e0303103d40100034000042441c14040c1703c03d0b40e007000d9880074040d80081e80c01a0000041100343ca0b04001003100e240781c03040c000c0003410f0f9180a800001e00103a1000b0b0340c044c58040154040910848442e90006d00400111088146641d91a40390041c800c4241e0a46500403c00c2048036406104050340b0110103041888240c0c200704210740c8290803402c1d80c6052080340103280c0d0a062081c0166400049031010480c0d446480b03047c51991003402e800740400612a0018a11500c41d000c07406010b4841486020603113070b00c0e010101c1048100d0001444100712810740d510504 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 747994226 1250 747992976 747992981
    0xf010c050f01090b160c1124030711030f040b0c030d06032103090c03020402030a14010807081c0903150e0a030801091a0603010b1b120306010201230622 67
    0x40d0032807000003a04245500e000001c0800c01008011220481c84565004681000f00311034250780c0321550012a080c500c0c001042e8a14480450354601140300132802c0c072007428401580078006940f2000105007905803100d9803480f520b00b9484101809120030000b442200d00039200c0030001c80b00b603038104140111510100c8800342c0c0240e41c40c80e0180cd81d1807214020f07880100003050a4502030058500c0c640f91151168601d01c402030050750f00000055282034950310101e103400034099200e00c0c0d96515180165540401e015981c064040c4c1f804290159200c040c032181d0301140c948442c4034041c6580c03140c0c4050380b40d034845510310303c1e16200d84461a5005200000006200c0c0c0ca981095504040c0c0d848201c07a071080f4460305850340701c40300300d1442c1e65150640341111001140250744030300c02d0920501035a4403000640040c40760307041d0448122852005075108001c00c2c1d001b0008140d02105900e85230206140c040e00704401381c4040381ea941400500c0308000c1141c03d144460750800603804204 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 747995476 1250 747994226 747994243
    0x402040e120703120b100f020106050d1a15150a0c080409020309070b0f0f070c05030304080d17010303090e06010e130f0f2c07030c0312022a0f010c05 66
    0x141ea1100180c4002055040104180c00000a030000c0000b500e241005c1101c1e041141c2c4a902400074084118544a100b508090042e00d40034100e000a41d00c940340040c1030f44400c0102d04001500d040014800e12802203041c00310b43c4c8004d04181c1c1c001d11060b0041c0b0954000e42e0040100504156040c1c04030b0f171302000500090071141001030741d0340b401841d802c1c1002e160360007040060008000d0703a01255024010780d00c280c0403000d403c40d0b4821040c54040c4108007a580203d815000c0031a00046520010420080c00040c50f00d8184028600400d180c0c4190b80901004003c255210340500c582c10b8005060b0742d0007441814224180c22140d000200181201044403404039191a001c0c0e901070a03e0041d000020f54800d030a0000000a0944c18001681c416000451902443c0842c450702c0003002214011344d0010341409180f0340b2810280c24184042c8055005445141020700452244c1e14048041c0409034000d140c0e2090202c01f04584202d00c4404a41007191111116000c1441401800c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 747996726 1250 747995476 747995503
    0x70218041719020c01030c2a020d0302010b120109020a090c0e1f0207060509310e070e010e070909020a020102130833010905060112050411030609030408030d050402040e 74
    0x1080b030350440030001c0c5000340d03004429040504001704208170a070400c1c081c0d080004100c502c08804044040701808201072048060350000200308600103140e010750003088190816920b0850402c1e09a40d541e082c0c03440404000d400c503c11150400024200b9805441403481e54030341003c0700c2813610005401844440703101c071a40180038104064040c1c0402c8140300078003007810710b203007416062800a01d8804894000440350711101c0441c290805000200d10b18855000500f0442c003040c48509d00e607100218050790340d0500080c000402c40300d20045855210300c0700340c0d0b12403500034101505000603401203e102425590240101440c00110707800750340181003c10001c000140c0701da15410b0720140304000310243c0349520f207000d0710500744803508541580c03000c20000c80d0302d440e9180102d0300310502d5000080420715180c1480200105503c800701c0481044088038500d8440d4080c2d19202d01c10740c03140300940c2d401000002080c9040e0381210350322900080c0001605803141140b02d0525900103981d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 747997976 1250 747996726 747996757
    0x3030c0c2108070f0e1005070506040f02031009081b070f09050f06150d0b0a0e010806090d0e0307050405040c1203111014010b09210c13020702180417 66
    0x8280e082d40b007450540c0c003196070f140c25140c2054020780070303150011029141d8000c4d1400c0b0080c440003400744c2c0403292215800700440b010b910f49401c0c10018110180400c920138041c900128031640741c1030145050b11900303d0a12071818000240c0d405e400344111352a51520300610400242948508000c14000c048000b40440d441ca041182d2500030035000f0102c910904840d0202440304004506036001c218025200041c0c80d07410b0707030000b070940041c0d038081401800140c0003c54207003408a04507008174070f010200c0321f100c01c080c0c8040d0761001c011155180c043d0300820040000b0718003038000c6600b203806070714100d11041d2100d0000c101424509070903000310309041a034500158040242181841c2d08800c1001170010702030746180155018490310390106000308840303040d6a2102c3c030f1000755000c00c1440781e54107000031f402c25850354440304405114401c030841030a007440311402201d038026030052110b2080d6521a006080740e1350041c00594040800c0030b8422001c6144030000c00c03240106003141d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 747999226 1250 747997976 747998033
    0x11e17012304240e2d121602060405060c0a0c0b030903030f091006030b0604060e1b1b0601061e020a12200102120a150b0703030c0c 58
    0x2421040100c0082616082201c10300b04008190b040038100400c2284080001d03054424520510103048480e9140403203010311413072010600040e48841c01c0c000140f000c69007008003a004c8298841140c03043d0002c442508004005202c250a01044211440108a41e040540340c0000c243c0540140c80d049000c1d50100319218280a04551070300018512402d0184c550f14283d80840d80360300001d48141039006036000804c644040c2400f405003003001c080001c0110a5480c14400c840d40c40075280d0f50300851070b000c404142002d0300421544110560b00c0d03406c0e00580d4810b0560702c03d07072206240306400110700119110003041840000c1c020403c958030307014000c00e1162a941d0080e400d40501003994007006803180081c039100a01e1004090320b042c0050700307100424180c03a0310070303210452901a5100040080d07448030800c840d40c5c00781e5400c0d80100403a034011000b07103203214414058820010000c2c032078000001d101e03401148403403195140c00c6450b10722944d0340c0603c0c905100501c0008072000e000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 748000476 1250 747999226 747999251
    0xb3612210c04080d0503060a0506030721060f03121809020c010b0d120c080d090c090c03090b160905040e010506150414010c082a120a08011e1701 64
    0x4045070001d80618045142600d0051556582d0502081d01024408007100046e826515143c6d0003006240282c49259a458541c9000701020428803544465403e080a01c1039086400d20490060317504180100801340d0075919070042c550025100d82081100003103c007010100b00c000010001c02c03000d68007503126608414080e00359802030b42618046c0c49004001000b09456010540f02c0000c2400c2c2000044490304181041c0d01c0307400d004440003030401d00003108203e4400814002c480702c5a004100042c4a00d00c01c81c00d0325003014003d0004203222021070a00600d079550740d61010b8a60800c48000c0d940d903404181941c20034100380702603942d1041007080505245940801102c88400c1887c075060a104a604240c48140c421504000f25041c0100400c441c1030b04484200780d546012980807441c01105080d41840200000032078000c080100d1080c4d00580c1c240d07000f101c80d6403070703500c0c007a82010300d40c14078065410782c0c549803a88500d90000e42d5503120100c4901c1c1c04804800030034003070550203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 748001726 1250 748000476 748000537
    0xb100c14060402210c03010c0905030f03191d0d0b091605090c09030313030c1503060602060705210903040f0e010e0a02070516120b3612 60
    0x303941240c104104110060380e032801840d0a001d2401c0c41608880c00d25000d0615203a01c0c4104560103610b0140e4817090326800c03041c40300c01c480301107084866550a40011503120701650203110030b0b03c006410440041401211951840c58100e40005504003950000070b504000600e0241d42900c240d0701404026502802401c2c00030344102140c1004030325082c082014020700602c50814060040360104203650240f088592840041c1000150580c407810000f0319128540300b106103111021104411440c041d015540c02c8400c41d03000b9003ca5903c1c03200540d190361040f520740c2c030245801c8040d0140c44a00c05062806800c1b004015070315241083c0081b982a02c980e003103001a000154010400c030740750030480320307401407101c41f0142c2c0701d030b515203405071a00000542d807080078101c1c00c01c0840c00101c281141c00c1e000d4022003041c1401d403034101300c5240d00d080c01c2d40c0300355000030403c82d400d194620894000d40d0402c002000c40b151100100e180010a4019151541c5150040100c401124007030f007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 748002976 1250 748001726 748001753
    0x17010e041202030316030509030f221205151905071d03010b06031f030c06020a0605073e01021201030606050a05010203070311031c15080607140d0b100c 67
    0x30b0005615504244040c040c1c450144001c0ba401c01d5162800240b2000b028401da07106588400c0500d62104035182600c140c40c000c80d00070f1034104254920000d20407889000e4a546160020086d201c03014010b0244104100300500302c44e807208005034074500d80340c0c4611956100e00d05c203544d406803103164222000e0120170f0f05a07500707100b80c2c1050400680c60fa034181c12280c000b1a10407440078283d281c209047c9080026500103032040b64545800100a40c01181c0c1100d01849044208030640e85e5a6040d108003500b00d01c0e681d62a13031a0800702410509041050114112420f00030340310075868a4940d0176a401580c0229100a64100410030801030380501c0d80640300444680c0c20f11410000000d68a000e000809410424002ca0319224000c0500880300420b504101400b01c903041088440058041080043c905140e1104005103c85000c6407448c080d41c29582e80141c002009100185c0d103400500d103625203150b40c0c10548006580c3e52181314504111502c1d0301c0c40520890400031240d0488 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 748004226 1250 748002976 748003013
    0x110306070f020312150d0305031b03010e0601261314063105030a0926060703020c010e0a0b06011206050f010c030c020409110a120b0402010e0117010e04 67
    0x14224141e50080207660424140440c1d20402d0f035624074146031015140a035140d0011070401c40d40e400d00d0342c000e0045110b401030f180b1019608011501841c0e2511007441030190088091001c80e07215840341c206007801c0004000c00410b4900b40e600d61404000003520100003079100c25000d1810041c5010407061b214051601400c10b510b8401000600d4a900009600804010303000501d01841070f100d00080c41ca800c203086907102c1180e02c0c8080c1400103070b070184150351250504602500310040107003210b080309400c007074075003911107843c164041d400202196020303540300c00c1c00d1109220b0410041400710702445500c1c080b410503d00151030303042c40108100c40316092034000e00c09a2105000440e2030802031030291100c0c411400e084a400080701d50081d0702600305802e5000348500100c1072581e40c50101d0380700480c40c0e500c00400a0311010040000c041c070024000003009580590b02215074900181050b1640e0101114250a450001d810019401310240140824804106202d1465010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 748005476 1250 748004226 748004237
    0x108010f0b1929030f07080105061305150c010906091101020f0601030b27060601020c0d0308040f080415020a0c050a180c03020f130e09061b0904061211030607 70
    0x1001e20702c0d0100941e440c00703003042078443c42c1104030310480e900b50510310110090328900d480342850500c054041c9010707648140090b40c3d140c0081850714181c0308071407000a55a00c0721400c0d0380703040203119480d0140705259584410511110704101d200380194821140f00b2000080d20060a1804010803442020481c0c115801254540340003000040d1035810749400825401d15a0b0ba450503040404d400501b84050300404039445a980303041c0021020700400c1c098094414800e80c600601420311031501004d0001000308000c03401266a0f0840180d185028184440c078090f00d43d41103032202e0740182d442c0c0c40141d01880c56a820310070307001c40b584040c0c5412598200241e282c0000080490720030958441c10603a070b1811a80d00394041c0d0304503030035002000000394440c0085c0001d030b11081c03071034458408180e440c1d60000c1c500c8030011840c01d119516010485ca90721440d00d0140300160804c0004580142e40c07180c0201d011a4914034000200f444cd6071040c0e04026402c00f41400d260010b40408240078 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 748006726 1250 748005476 748005499
    0x2b0615050d050304031208062b0c090c0f1806031a10170c03040c0306020c0120040f080708120d14010906180c14071a010308040f0e0118020a170108010f0b 68
    0x1a13469468442027070101402c0180007400c1d4880040004102c0708c0149484011240014000100e8002c00c400c0340c0300d515003a5851445403010f4941c5420f00c8081400c601410302d0030311415000740e00c018a5941e180110b41c09000d11500442d0818410003189400b040003020100844ca2681c50241c1e802040a01e1103401c60406503242c0011540e40d001c0101200c0c1c02050414102d2007d501ca481501e104102a1400340c203071550030980c640c014000d8460740880744d040401c200d0400600081280c0880f401005010501a102001e0782c1220101c020025149c404482002220f5191075011303140e0800c0001d01d283c6004403071301002c00c1900044054604011781006220b8111030b244040a802401d56076580102d0b103801c062502000d03890408947c6104d00100a20503840007400030780350409011444a511445005504207091051404006442d03549400c1215035030041e00044806090007040042c0440c02104290307400d81042d117041e952800101014000c0c1d00800540d460262891030380700 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 748007976 1250 748006726 748006729
    0x910060806040303110c060c0301090f092607080a02161409011809020303040e04020a051e150405041e0c0509090f1e0c04052b0615050d05030403120806 67
    0x3854010b00143c28559070341010b07072159494804803503482034120f05030b58840c5006190466140c0082c01417a540d103251480310f1300151041d100d6151801d400c4200031180714400741c00402d182502c038840d0596054140000000503540d440607008041040d00600040021120407132003c0f42c80e83d10030800c2d0910004010601d440f0a03c180c0d0648804500e42c0000c80e00c800140c10142a114000a4140c40002000508006420b4040c0d000da88211014243c059403035040040390440e0030b0041ca05c1d1403000c1e456007640e1410103104d440300007656006a04003580ca90010303040714030b40d540540c451490344c504028294003038401c030024052942001c9081003664404200301e008001c01c0c400c04a80301c1d0300407804040840381c600741450010305085d0f01c42c0c80c040c01000d001d03801a00c982c40c0180039610300f4080d462008286131110100403105a010714255484081c0a04048291112180400c910105540d00d03019144113082e0702a1004540c1c036031071441d0114607140c2540c08002000480002c3c803406 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 748009226 1250 748007976 748007983
    0x30305041e080909150613050415050a0608061305090f120337060b0c010507050313061a12011a1207050d05010b04060e0601081503030421060e010509100608 69
    0x450025640c11802c1e80c0d0317030380c0c040300500c1e040144d0f1a0b200d0341c085011241e003500d805800381500c90544007801086010113000080b01d0103802030541c801c4010406000551080c5240c4d58042c10050248141e141040e1418003103600940d5148007582028030341c0601240100103400c0c02c5040b9410540c40c51420400d070011149401c4e00d10940d0060b02a02102d40540049044d0b81e001c034120001c00855680b00312207491540042000401942883c1c001440240504150b901c02c010171b10303010070040c1403640c0d0711009040520000d0f601494042c07038020581c0320b094060500012050001030000c480c103c0d410351148500242078800d182d020f040503680c1e000403a640b011540f06441c500350a44462800134090051480600d03040751408400003641d41920f2400c0380181001e80b0340210315243d4103081104c1490b04919030b9010b500c100410010a041080302051a543c2460300d241042c0140d91014141c9001d00100f994981d100d6080c466018405d01902e540e44003018810046c0c035282c065080d48 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 748010476 1250 748009226 748009237
    0x3060601140a02150108011d1c030b03010207150519060b0a032a0f03140411060a0908100906060602061306020f0405060a020a0519020a090209010318030305041e08 72
    0x440303000c0410614003160080111101c00d131004010105103607114200d050003409100c60b451034034078407414400714010001c602a80c40b00150100a00184c1c03000318103401501c1e21f4121035406650810202e00401c041aa5400480c0c50045020682e8146610104a0072060b011400c1407907182480411860440b00200c1d10740b0941406e000c1008400d8161400e400440440c103d0003a001038010150035503800180d0360f0300f1040607102003254400b41202010a0b01c0c040781c0050030316034050215012840c02c4405410505038520b010705a41c2c1d00e402020f4181180711501902d041c1c1c68011b5a03007004018003d14001e0700b4288001c041e90300e0501480c0138041074a940150240754001070300910035500b00c04880c003601e4064449580e46111a90003035642180d954241d90078006c44061182c10b040c910000302c00640c0040a40b84c1d52803d10320100000d5028101050516985006070090900598044608a0f00a440c00130300d43c603050900c072035404402e014015444001d403c1d03002c00582240700366403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 748011726 1250 748010476 748010507
    0x70305090f0c040b040e0a080405031506010203030721020711090105060a1b03022b02011512021c02090f040519032709021c0f020708041503271103060601 68
    0xc44d0301c5000d01150040070004461100303800348a007540d00340401800140308407441581250940380300b40408070003504040d1180750040e0010008502034a1241d41240c4540c1c0341240b5000046d481791424504036801050102d07403004100308007a1a03841c106000d80c5c010801174598a2070040e5606006024074403895044d040b802011040d4000e06108020801940030080e8000b46a94902c07408000c60a0325011060010f60030010070046450040c800c070703070407240f148610207940c5166508005540c07542458081b041d103104810100543e0f81d4460b02c5001b000070460b007450310300f031508080e82803500c03504241d0880b0107085400000254000f8050605c1816602e49004490302c802c20101e40e4601a071041512500106a800c0400c00c80350108000c215a0281084041d00d0000800c0c00c2e07009400c0050003180301404108040f548012492501d045645400071710b0700440c00d180c0d6803100070440781d10100407100c3c0e81881002100701c80e0b280602c070214000c280910340100024120107445680f903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 748012976 1250 748011726 748011731
    0x70201021c0c030e120604030c05010605030114160e030705040e1c0c021206040f06090f1b0504231b04090f0903080106110a080a020307021c02090f0415021c090308070305090f0c04 79
    0x709c0500000394819000fa0030014000c0c01407030341c06011020f00b4030381070321228130180b031a2010101150003400324410401001e00501700c01e40c41d110810000344003042c0d2482681c0186040c00b128001041150710b2501815260302845000d2401441582003606180542c154803560900c800709402a900c01c2d00325900c070380041ba030304156241c034182030120154001c2450034656042240304c10f161515106661064608202001900362006403c0110741c00d02c03402c5440c4400071450003d02d44107003e22081c04200b010b03181641d5110443e08580801c042c100e542d650340d2218408150780030189a00401d075510f0491072102e01c1d051555114410108001c1101d0b40000380f00001600a2043c5c0c0c000f650001e2040701a079203140c3c141d07842d0740d418038412407042040500040044114040050203507803c0000402d0880011070740710000d5100c1403000480500002920b00ba4070814003c4041ca20310079942c0d08582e05000f40080d06443c0050310b00d050036003120001010701400081c100b8075880c0b003142d01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 748014226 1250 748012976 748012997
    0x30c0d0c05070206120a0f09020609060307020a14030711040204140f03160806041101181505090904140c060906091e0d0f03140901090308070201021c0c030e12060403 73
    0xd40d01d82c80780c0c40740250090750200b02031400000303000c00d00388680380c20315080c0525034004000900325209000c0c0250300c50002d21034a60142408800366070b01031010300440344401038588600018000680016a05520000d0300408006101d941201290402c2c7d070254281820005103803821a00401d000b40204105003800502e40c3d0f04020f01c103202645207206800ca02d032a03d1005489590840301038039580c06c5a00600035551003181b0202d5580240c6400d03400031400d05200045104940300c0755010403109200110803544d4045000e030103148686a00d100707800d078111a40c0d083c80e804042141c4201411702c800d0100303860b0340e021510381c000c08485042c0f4106080e0310701030513030115000503a08a0070702d50328401004008400c00d0945402900c82d410001c1d451100c09009100741d081150008000400410000300301c50007910002d4414010740d034030781c2c0d030044413038010100b007038241800150025503860906400800003002903030300380d8200c443c0214101405a49440c0078000600708046001c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 748015476 1250 748014226 748014251
    0x1d0f01050c15100e011a0306060a030608060c0901081b0a0e0307090e060f0c071509231f1505010e01110607020c01030b03010203040b010b0d02091801060f05030c0d 72
    0x703420710074840010644a0f0900304111450040d15005182008400c40c00115041ca26001e81500c01c000680002d442c55403558113100454020320012006e054817400c010643c03120074009148a80f254849094950140c800010416100030340301e22900088505450141041c040c01c81c1e00c24005401e20042c001b4032800440c0c0781002a50084c0910f03440d01096031200000416114010b80c4400b0504945413501130b02024580b0131400010300c2000652600c1034102e03002d40140e00300034003c01c1400c0303000703007509060481d841500d500480e207034220080c1c00142091540100c074141c041c244041012a5448214548502c1d081c0030740d9060040d005e858902c01da100c0c03032600e041e0003810785c1034540c90b040c01d25002c0c3d61014071103240c9001c00d04000765810241414401d40e4803880e04450345482c1646040c103614159404010800c2919801f00301c2c14203280c80b0909070006202c00312034128043d6241c803e0003400c642e83d144103e405c00c80100b06009400828030305503030b90081c0b001e43c00200d1342c0c0e8810 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 748016726 1250 748015476 748015483
    0x50601231e041502010b0108070e0d24050a0606021b040911061305040b120a030305040305130f030204050a020a090b0a2a060609020a1209020d1e031d0f01050c 70
    0x10000545580c002902044406091200075030f446101c0c0c00a11094a80304015202840125140030000300c1007074152040385420303218800064001d0556800390b1104c01c000b40701c541804000b000e43c0b01d48841c01c0c040c49a02520446001784010320262111400c140000750009410200591140e51a42c0141c4103114081600c40300001d0000c0c0340542d0f5510104d40340000001d240304030b51250703181c420800301e41d00b40091510ba06040c40b1024011304801d503a0164002e21014200fa010030500340004e0039441d1545441d4170152100300010340e4014a10320412094483c0144604100d50042c00f501c022150800d00003010b4600c338480c0591180c00c4010111381441404501807084031001409114086100c0144a04a030155005001854031a04640243d21503030009030002010a00803483c800082c4d80500041c0d072004007280003010b041d07200c034005100700422070f8103039462400743d0310109a017201118080400b00d40080891085000005900e03403c0e4030015414817500003001c0e4100300050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 748017976 1250 748016726 748016767
    0x12010e190506270403020c010906210f02040b040f0b09100815030709060e130b0612030712023d0b010e0301091b080708030f162405060123 61
    0x5a005411a401c0120710032074a99040e00c003179025010b480404c8200c0d5108006070410f403000d9486008007040c0c000610030901200028bc03450090361075120309620075032030005100418181c46a1500d40341044a88844000d1584c090001c111080180760789035204d00510940440403828043e802c0c0d07442daa030301d01d208141d40103440d038503004031130010811000769030107481039602041800030315940b02040b0758409101c002024001090b8100001c0302031506001100c2c1802c0c0c010156810020a81e685401002040150303002503008215200800c0c4a40d03070164aa4800c440c000c50b841025000c19501c840700c101e200080b072161581801265640609170306444010701078001c0021039518140704c1d401c0808a03108000407040900005400716001a040050b10001809945443c407400f41c9907410340d020304800840038000503444000304003a007410310143c510954030034004c034146840a0040b00c900802043c1480624020605100070b44407003040c20f0004000321b59581d608041c9076280300000d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 748019226 1250 748017976 748018009
    0xc050c1801362705030a11030a120522080406020d091409060d1506030308060a21020d080d0902040f05070503061908030a0203090315090613170f12010e190506 70
    0x4181c1503070b04010f0b0005c010b100b40202ca503070b09503044200650003074032845000700120000300580201404108154401034102411001211014400b012611003c640808095070703040d00220b02003041c550140803143d100350316464a801041d0070b0505501c0000e0142c10290f00480b0310400207401d513291039951544050700704c0b181e00c520701001e0b1142c01c0600140d0100b14000382086022406500700703222448160796010410030030400c3e8400b1628008a6000c10076070b03001e00c00d9003900001c942902c0003800c40d6403260001068460150043c4400d40c4c6000c08140d2071146082c080108450380304c82030f43c0c0c000004460300c0030b56111103590003445019942040015020004998a082e600080104000c4038240d09540c005048988105400310003181c0c40300742604039a0014405d00021030f40740e400684107400c00510130503020000780395500031194850707102c41d001844101d009600781425004042d2203046403114504611042c4290b074040d11080462901c0e40c010460715500c1c078ad940043d1105 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 748020476 1250 748019226 748019291
    0x4080c010c052109220605062b090b041a01050117010b03090709020a050406120504030c14070f0312080f071b140307030801050a09090305030402010c050c180136 71
    0x1080c001706507804080801c6801c0326407902e000054141011401c2d07401c90039240c24120000405100160501c0b0391011506820a980c1c00c1402c0c001440b0311569806903000361703001e101c1c0140c519200c0c03d02c1e02060704039505201074a0502040003c80c0c88006056480114030640c4035141e0701c540920300402900400f200c14008103901382c6003a0711001500440b031460b41c1d004903905100403071324100c5c1c000352409000a8001e0300e80c0d0700402c0c1c2402001010000540444030a50b546001c1800f00b100d4035042220420303460420b07820000d9100d91039079004070f4040c2003141e072420141c0d006001800420303076000800c511101d0b00c20074030886c0e08092620b2104082680ea40755002c0c17800402c9210f00740a818420903601e400420510485e102e40424654181c840c40e1441c2c540da001501c04800b82c8404503040d102300120b9072100d4680d0702d50141e082c8224820202c0c01d5041c43c0401c402c0541c08000da208400041c440404103d03a144082c00c0c0a0404a1000588a00d400b241c04841c060b0038610401ca0003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 748021582 1106 748020476 748020499
    0xd02060711010909050f04150506010905190e090a23030a0e04110c0105071d03122809031e0312110d1104080c010c052109 54
    0x1c0c0141090214aa0748850040035200c00b04e41c4e0000601c0580700344030401444034609000828030b050240031601e80070b00020400303502489404d224850103503031100b40d4034440e100d103001340005c0183c20100e4986551501d1b92105515800c0300d8880d9101c1001d203410528080305890f103031401002d1031904102940440304e195003007c15071381c0a40e80c0d0f4a9280d155590704010041501190004681494111070107840d01106d0110303c0ca1402c0b040c0108441c0b0355001c50707a40d08030101d0380e284944070545015001107030860880c2803c88095840d03020304045400c0145101128860410b40802c002041c200c0d194a0721405c200078085505032155042116081e0000c0c02d06682a050260400a440720352500f920900750555980003800a800e1041c154140214804843c0c00e003005900041a9910982e54000454000207442c20808402ca88400356004551070b03003000034400030451 = true := by decide +kernel

theorem cover : BRFrame.Cov 747841726 748021582 := by
  have h0 := BRFrame.cov_init 747841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 747841726 ≤ n) (h2 : n < 748021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
