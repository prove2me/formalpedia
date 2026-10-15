-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4947
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:14:44.607134+00:00
-- url     : https://prove2.me/submissions/6847cf82-0af9-4e06-91f9-9e89d2a07ddb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 889568345 ≤ n < 889748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 889569595 1250 889568345 889568357
    0xb0603011a100c1a0f0603070b0a0807030c1206030c06020f01060f1412010f050406140709090b040608120d0c0809061f090f0b01031113090515210106060807 69
    0x5510000e503511680140d0a03201407643c907003403990600500d40c0c11817041d07a08076842503843c10701009044ca8410160403041c9105802e101804000e0b034001c4d038140c1d00104528000c5100b032010032090b1681419110040309060401d00040144101c24401c00100d030781583c05c68403000d100404107400c80b9203d019a02103841711600030040c200c00c0b42c000c3d00ca0307203400824800d203207103240e101203086520740b00d014842c1c59181c42c00c00051101c240704050a00d50181400c00ea00e01c2d020500a0100905004010480c0e60b1011600c0c0c4030344941d40400c1c0509120002ca0350001c88003406258207404c560f85002046041a00d51440c1900c1ba40711039001e446c28070010107547d140c450781a000e00600b440f5000c41c84119140000c2d040c501c502590520300005480002c08040e4000018140c404105640c1d65001c400c11109401c8850304020504071031002d6000030ba140c030b0304002d02c180500c2480b15542d22072144500d5030054030b10000b81c0654200044020440e0396510b490545030901c04440c0344003c03a031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 889570845 1250 889569595 889569619
    0xa111f02011e0b130c0201020c0601030f0b0f090303281811030304030f03051c06030f0201030c1b060e1c120b09060609090709031407060206220f0c050d0b0603011a 72
    0x4c00c07900070801d01032440c0009030605640416991600409920903641d10f00d0403d24001070001280e55107030403540b84815000c10b0314184401650702d00c0040c0074800d00200804560400d166441c041700b2950030020414840c05128800340038034081200c40c00c1e142e507110241210414030b80081190102c07a40a0711860310750045440688007034000c4020100d00e41c904038410841c41e112171040c41c020390301c541690400003869000040c100c440c8007020307206112403940480b02414184041d445000d07444900030030603403981840641414a440419010745605500d4411665000450702c0003466400c201008002034000411104450503100c29411180401800c0d1a0741080c2e84c54a500044604103100300c141d407681ca0855041d855280400c441d0004102070064940c1448901d8000c099050004004030000c0c4400590a601c03040c02044940745d10b00610400c00010b0141c4001c00c40104a0f059110f00d608000107200c40840d00c86100303501e41240148131003c7c1e08200c2c04202030260904110b00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 889572095 1250 889570845 889570879
    0x1020702032107050102030403050c0c040e06130f0804060e10020606010507020103020d140405030318070510210227010f08060909120309010204030c0f080a111f02011e0b 75
    0x200c880b101102059020014880483c000b40011409144a9500d29940e00506240c2c1c0742489000154144a24103000b03581054040009400b0781081d8a860f4484003500c0a20f000174900c1072101d4000c0000700c01140006146d50030946440240400b07941814506600200480c0c8451049513558045101031041c20702552207035010349089140404001690320795603000f50041030044cc0c04440940c0b000040000316801080d0080d02c0b41d0300c09006103030a500b0600091035140c0d450700400208150b0012280560f40200c02519040511000465807032000ba02d0b612618041840205010010100c02180552207008030004490550ba900c0b18251a102d003005103000014040d0701240c032841d06e9845c9100d011000070350081c10450001a40d4520394903208083c44015801510071442209003080071303c001003080c4101c0743e40050040c2c400480310000407200c21029240900c41310a0000d59144150154800c1403c001c865802d030440c07500b51104030007903901c0304545681200c09090510380310 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 889573345 1250 889572095 889572133
    0x1200316020105040e090d0e0301271a0f0103030207060e0619140a05031801050103020d0b101a03040c0f0f0504020c0a0b04240b0a061b120315080102070203 69
    0x100e8414034140d481d0540c3d03400442c15089043c0d828250741d4200d40b00d10b0420580110030300c403100c5001e4000344590b8480984908052080711ba40e4105900c0b540e20240800c4105001c1c1d58624100c0301811019040c100c442e000954803d000440140c0710703082002ca00c0e070380500d410315205080206064613103a000440e4000c0c5101114054040c407240740c0c2059a01c6080c0303c003902c48018560f69454903072401c039241d511034500782f1390a90042c0e40740400503c09a121203040c010750a07081560031000b5143c0321440c1503000d155a100c462150f407071440000c0104c0300c00f07004500840c0107000101146444040750581900140301e07001001851801c2040341c0c1c10550054180d0420f0312085e0703044103c0c1c81d1559081c100c411102120034804030500701608941070007030382580360700100c0100040c5000b1000b140e80e4040d5409094103100d8009480038101c180c48000000056108070150340c0308a13080170140281c0300a1090309840b10b8000070100351f0748814402c1e01d00640d001001080f85186e0100c0c56515 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 889574595 1250 889573345 889573387
    0x14060f010e13020a030207050c121905120307030b0f01170117210c0607030c090302040209120f030c010606050c100b15190909020921010f0f0b012003 66
    0x401e034142d420700480c220a20241540d801c1c141c4000d03070f0ba1280f80c90958104928031800c00d110307000342e007440c3c1c001600c00515170301f0008039029803030105540c50600a250400c2c044901d9140e80e0000308000c512681900150140d25042d10060200b114000041d9044401040801c80f44112030004210100300e140c0a01881c050310000d64bc3c0b40301c0700381c24500c40403841c20b03d41c40e03e240f0002100380d401c05d010000e459005405c3e150400825800710b10042c45c1c0d9000b44006032090740c020a803004113550302042c2500c000300d000c0c00c0303502030710b060310130035450b0342003040d6240c0b11303501c0c0003c00981e060184003101d511b00071b004068104456154484d0006145400e02036400c2820f00380c981c1d0024100c40c0c02804407841f0960005400b08001d1030003005a4940e0300000c15207401807008806030745030300d2190143e04a09102e5503810071440d0300300500401c0d105500200c00e40c206504c8240d9640d50b40e100250700902079031811006201d02d03400c020402c40e03003100c07411f290380304006001c2c0a020781104010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 889575845 1250 889574595 889574599
    0x3050c0c06070f0e0a1d09030f09210607030608070605120f1008070f090c0e031506031014040b13031b150c03020d0b0102010b030312060a030803040b090114060f010e 73
    0x354060051005c00c0c000d0107a0303003084100303c2690466400524000c0c580c951300070025802585403442641c1d40c42071600444004e10f01400900040d02c000d00451301c4d1141841c1c42060850b40e5914100d1001400381c1050f03c50024a400350354000b10b0300500c03035421103010722403140060072151a0007450451449004002116281c0c0521000c20030303138414411389006100040c04090703220304000880d021506826a80824407010703402ca14201d0300d0105071201c0d0f0071019040041195035120200b8103041d245000c4080452030120520078100c00c1040c013500442c0a000d447c42642d41d201040c1c7c2c05540c0d84800a03000c00c14000820840207031501c01e01440d94491084440b5000c40301990600f641c0a1180d54000300b5004180c031542d8440714843e030140514244024051551840007190301c07031080e003000c02d00c00c0d602400002c5041c2c80303031041d007401180e0041c1c40d281d492410341060b451400c2c05440e0301c0813035401d001302c0d800c4502c0300300074140c0140310003400e40148004010041d101d540c51807000325 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 889577095 1250 889575845 889575857
    0xb09040204240806100e0103021804050a0c110303040c0506070602093016140604030c0e071701030c050402031815100b070c0905060307080601090c03050c0c06070f 72
    0x101c1c000301c000c000e595980b92103024103981c015040101503c224801002c2c54020508480800390b640d6001844500412003070034016a903074850401820080000e0b41040e13000390402050090b0355990307621240d1907240a035034006e10142000d030400e441c0e100a0b54080c3c009140da141c2488140350041c01070442d01c1c030070100140780a04d220086008074a41441041c1c580c0100c014100710416484170340402d1510000203059141c0200c103040203040c066000d0b0b4000c0021540014a41d52909400c03900516005210b1580c0c5a40d00c24242d104d0744012a92403000a503288100404050801c2005050742d91010050303801904240c1844000d400080000140d2600d49a290350500b40c14000c00c43c0d03a07104110021480d01c0c01d218aa10900559031003984050820030080d40070568114207501542ea076124041402d0320391000080c504496900300a6040c0107110002030009019880b8074a9440c0a441c1400355964600c0d0003c00c1d40100803800c2e01d207420000000300120320a0108002001180c1811 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 889578345 1250 889577095 889577099
    0xa060207152c1504021207080d050912010219050a11100218092823070e100c0f110310020a02010c1e140d02160b0f01120308070c1202010203060a0f0605040b09040204 73
    0x41c600e0427000e41d01c0c001c0070804c005582642d03130070540c078403442c10f0601d90700a614259101c8241081e10464403501d0040140205051042c0da11540c030020f41069640308450203110b10183c02e2000390310819200d44240c2c0000700c0c8065900f03000b516588030320100c5140c0512002c8880c3d115072040c14005065117030030f0b0303104c9620503000b080180301145003402c0e040d121600d00d040b020190021554100035441000c4015500707420716444203081c48441e40c0040002c0c0c95511038a0a50342c00315540021503414064800c40c24414041640a8000300031241d00030302050400a005440000c00510b218187e00d03010121030031200e0042103c0041070303459030f2585182c13801901e1580c003240c00078241e04520341c4400da289024090456401c1c0d8000401d5240901036524000f0b14160300f5584900c010148048100054542c034000c50180d00c203a604008442d540000c5030000074000e41c0100c400318030030030600401103840c04003011640c1c260b400c00e450b01c920f40340c24140b154640307400c8201803d034003035020000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 889579595 1250 889578345 889578359
    0x110f18180c0a06020c0a060201150b07140f48011e030606030605090f06121005040f021c050c0613050a0e0f09010e0a060207152c1504021207 62
    0x4150040c250f41c0c0c0070708100300300e400400045c0390047e4460011681801940442030450380c100c1c101321101c03030440f1342e070314a214540301038000c0360b000030001c0d03d0140803581c0080810228035a040da05041003c001c5451410011800c3d54045090088a40c9100c50742c045580d42e620804091651050410300c0300302e031851080c070745035a00807040040000c0d10b4007810480b09406003e8071000c0e200031540c3e0042840c1510440c0d604407001400184074008201c0b0000c0d00c038500b84601800c0c0d030400d0038140282e01d4542042c2c1e07203641c46010b089000d0704280248003080c00b005020242c0082e84030019000c0d04542400300a407a030800c1d00b20f174100055101d0001615a5440b500100030112041c0c0e6040700d20f001d180f21a0000e80091116000d070341030007074110309200d0100382e03080c1d025446000141c07202e08900348030200d1003010440091080c503180700320002c690015500041d21a024180c40c0c012081041070b03030703154401c04255030328080c2000003040051400c422881220401403040342d51581d40c8180d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 889580845 1250 889579595 889579609
    0x1210b0a0515090106180f03080a05070c0b0403050102030f090f0c090603030405120c1207150c151a19120206032e060e1012050402040b040603110f18180c 68
    0x31019010418002042c41c800503621061402444241803079007a1f9032464444030054070a12090740100280010300d0420000303030b4000b10020300b81c0c060085403966103a1070094000c0d802078402c01000594400001e251003400142c285022040d88082c0c4014004002030142007540030700701c598140400d00010030140c45020b2000710f4005101c0007030034000044030511a02d81d2202e01000c640380c2090205000c0c00881c114080501105842d0120480030386061911036020103054000480c0c0c02c0c40c0c17511240d0031a11aa601c41e101d1300700c400640307030f92a42c40e180b112006280b003040c040701c807070700306550244c03401002841d844006500000f800c13680084582340220980000742102c7d000310b07030301400100c0e48440740c0f107120303e001d0722209018214014007421107005201d081040e140c5810008046484075003104d600c915014005200c025144c3c94004003010015803014001c51502d14040e200f880c0090340e4824540000880303009030785400c5a840042001c5560903941449250340301030007030b03c0d030761 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 889582095 1250 889580845 889580849
    0x14131a040c05030103060c111f0603140d020c121b2e0f0f2f240a05130803150306150103050906010501050a03020d0e031201210b0a05150901 62
    0x2d5641a42d070740c118a0080207c0e40c00b82e500e8420010b2003504803581c1400014850103e00607610134424512690400740e01405080d0070081265104007820b20307001100040104e141e0481c0d809885584204109103c011140c03891011041e038000403a08850940c1c0c49941c20395084060881d041071510300c04421480307a62089803c91700d051b254180140704d64080d801c4c189800d00d52802a5454501000003015040c010030b030020300302600280c0d201d40202e100103800c04080d60505440d5044c24124404842d04c00958108510810000006034100d034280305030f80c46440d4192880001c059241c0390740019800007401c0c405d0b210240000c02031283d5040100c18030441191409175200840000010b06841000d000003601d980900d0060142c0ea800006036100c200041c5030041c0c803203000c940800b01420075454900042d0000042080ea031444000b0814180c901d140401040c07500e0900c1a845a040c0b184005448840c2d02004511203900c41c1e00150b8101540d0700c8160b441e40c480304001140040c003a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 889583345 1250 889582095 889582097
    0x20307050a0f0f0911120603031303050f0f03070b010b070c0e010e0610030b010212161401050106020f030c0c0918030c0a061503020906060a0201181b14131a040c 71
    0x7151041000001c225240006003944da00709000c010350105100b42a40100304180781032409a000052494408105448216110041c000001540d07820155200c10030f50b05004254016400b084210340c03000811506156400010105947c0c6000c98201e01a04003102c2203807030f001901e1001a040d45e0604aa9000c0c100f42070004480b070812030f0400180c82c0f541c034544410b00d420490001c907a81c0c0c011070940700198500d24170aa86080504c02d075898412030300001800c402c100311105006100550119060360100e4003104c604000700f10080d075803409148910040d90303100a40406050605403c0d01c0c1d0014030308840790709544001a2650f01796000700f8004002a40400c101d035052144038042c03400155669010000050700750340200303221745401800b1901804000842d1b08290b8400d44c0240200300c2c002d041504900e81c185414901644032401d0140e100000800101c0c64420069000c40b4000d0024103102c081600c011006c1c016005014042c2c18a0b800784c4420705498950b03000c2d0060720501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 889584595 1250 889583345 889583369
    0x1c0602130f08100b120703050c090603121b0a06061d0a0612020402160b010b070b0c0a0e01110c0618040e030f07140708030a0c03080a1b0c020307050a 66
    0xa0821680c0400080781e00000c854003912404012544002c00d10204003c03009102166406240340071400c41c110006440006106015001003801070104010300d4141c011100311071561281d2040580c4c0d201d01c20b45801100404000e180b2000300c0e900c034626841c94001003600c1080b03500e030700c42c07400721400c0b544a40c034006c2c84110185905a00c1c031490641c404052402000340701d003080046101440d860400900403a40000c10a4030009590200d1a41c1c03544000408403d41e1070b98046030072904200c1d0101c40c040801404503100780d81140c180c0b5916035441d0b0701c0c140d490f180c1d000111644150010072030150300032009068010340300c05d4024440300c100000040340030350402045c8000c03142c240305201280c0d0018000c201d070382d6010100701c4007071540220420608481110b01141001040e61128129100003d0000380540c1c121000007060b80c082e0315200403070f07607030b481800701030b03070410241c82001d000c13000c6004c4030403030203024608046030011f800c0b90b035240d4a96020404042c61a008034900320b413 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 889585845 1250 889584595 889584607
    0x7050105121e13170711100c052a030a0b1513020c01140a23040f0b070801080c040e03121801050114090603010e06190b120c04111602041107020603040b0406050c090a0b091c0602 78
    0x820b0b0ac4000e1042c1d04158010401000f0030b84900c1003a44018103d960b0b0256400d00c400f09a40d5050b000203400c283c640c0d8215640e0303840c80d00c914028120001e2801d00821a8030000f88075030f2940c401c4113a26112994140481c04450741a203003035001c000c108451a224004681d4081480301559602c544100e49441c0c03099410b041900d03181074051060603102c2c9007000d0301540d51070808000d40b1402507030030101d841d02d034440007000f4000090f106004d24082d841c1900018013001d0001c0c010341d14200941322820349881d0b080c141401d0b96074800304010703107a00c8040452012041c107070b01410303690034170080050300c03031154400070344458441e000d50074481e40a15100c1d60549014801d404501810041c02c0d0325000b045029503546114403200688280c0d5150000d0481c40140400c68000f41c0d4024092a503c1c42d203863300d00d4a03180709070340c182c40c1d107441d141c001850501d40e41c08550304114001d1115003540d1800305218425440304410f55004286060525601000000340c03900043c4900300140c2c840d9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 889587095 1250 889585845 889585903
    0x6050306060a0b090d02030c0909071a0403121d19080d0206071b0201170117070e01300c030807031107050105121e13170711100c05 58
    0x310090012403041a119408124421241c03049070b00c41d540c259582440340030940002400c1401d0341180b6078201c4421010031180400119490050311100400843e90303999090410000d4020740c00b00600200341c50031000407203801401c0c201c4a003215035107005000b0003c10081041d4203165038400440340d80d50342c02401000c2c5c05104040404d1200d200038040b03460f103e4401012400e400c130f0168a01d000c410350030025a485808a0010080900303940d0183e941d4904403086c14038032880400019000b00e600100d001070b604010305040b6840c072000841c100b500e03881000032004500074110300c810f11113600c1d50001303030700d400507400114010f009098031a02ca1781400b40051204001c40310711604441c01c103210907a0800705170b4103d00c42c00300c7d80000f0741e56413080a207180080e03810110410f000d03000801090420011284480501c958102c4103482103100d0b100c3c1060041601c02440d1714400c100d080356038140706501d240090145d14000740c40180235164207040c0510700507400c5071721140c1e0004912803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 889588345 1250 889587095 889587103
    0x6120e0706050c0c0402070210051e031005011805011202180a0303050c10090b1803090a09022101030f0b10031703040201110303040c060806040f020c0c0924040c0c080c01060503 78
    0x119000c0d41c046d40380140740d9001407020441080c880c0244000403800d000f04005e0307180d1018030005c0c80c41055549091251a08040140038425207000074811140e04c00d40e9080e40441400301c1e039046c1c5501c0d9001e110200110040d4000c8030102d900d001440c0d000a8841e90781140e4800154041e8903020f5450403a440c1160074420406503241c1090304001a0b8000070b000741e11070b070b13503c0b40b003411143c4001c0e00302404580c2548580c428442c3c0c0503002c40b034003181100311540184862030048401c100001c0c100c10a62030300744c4c0244409010301c2078840307250300071130380b84011194002c080d60b00e40e4204c1900c0344d07140c81c0d555502e031040400400010007000110b5030000c50700b2481c0c0545500075400c500d042d943d02c0c0e0804029004180c10000200041a174607210341e00038002c4a090b0b42400e40d200c81e010400035594501b620121407280b044000420749542d0107411109511020490141c200c0000c101408046c043c4180c00004100d40100b0400200d203c8001401c1045540c20000c0f44c11750be401c0c00c15141c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 889589595 1250 889588345 889588363
    0x321090602070b01141f0503040c121203050702070f0911040e10030b100803030a1d0d11010b090402030703081e0403140708010e0a0314090603040c08061e0106120e0706050c 76
    0x4c100550741171001308003007140c2070304145081c5440f82d80ca565900d070030070200452f603000c100482803241144003000100c14500d81e03050500d5800b040656034544003284d59040600c500e10450800800c18040d00d016078214280034480f50b185140f4140d61003800f0210200d00b100d001c501d401c0c000344103200b0800145820f070341091200f42410b034450f040c80452505c074880646000070f076079900c155103442003001034101e03400c0001c00170642d0780c075010400001d4458010f00c5a07098565182002040051402d03040146c040c03600500144801030940d5216000741d444985585000600d1951030780031685003400a0000c0c6114090308004600203001c218644145500107030300d2a41080c884405000d800285244115014908424400d88412040216104800083d500805c0001c00c00090246501c00103046422002c00c40e10a6a5041c82142c442c00c3c680e5842258001c481004110851041610502510300d540000818225103030f4928a40216603004030040740002c6441118444240300d41c50f4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 889590845 1250 889589595 889589599
    0x72d050c011809150b0307031a040908041205030f0409021801080408180a0806040602031b0f040b091314062d0402160c06020a02100203070321090602070b0114 70
    0x4104004022200c030214414050700804950b502c2d055490f01851300700d4013000b400464a92552030604000050180c045000da496070814000c0d18500c040c00c16105031f81000e60050304007800c090500140003090f03a90071006450720f10060008038107492240c4003c0004241f40080103076600e902e4940c4540441d1041105814801c2040c104400309039200c0480b2401010b000300c074070500181d400010f0400000c2e8100c0c3d049171089404100270070655600071b500035801c0c40d03001011603003030305e00d05041131048190003003000b4000c4c0010841030b070104002c0c00c0c00b410024003040a070041c1031841400c8a00b00c41d0b4400703068410406118043c10079051040302014143c195200e040d90400f4039255143c5503181030b90149a00113040c1184020504100c444103a024254640c0c403a595000203645d06000a002e0788100113480440d001c050000003200c040c150315464102c0c41402041405000702202c68502084541311340d4040c0000b1660710041c040786206041110495041644d0040913041003000e542c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 889592095 1250 889590845 889590857
    0x193b1f082b02280b0a021306180905150405250e010e370609030803041a0910060509040f060507050c030d060905070c1703060a091a0411041a072d050c01 67
    0x10b248140d90501fa101600c4550078101040e041c140d150101e40d079134540c8010f109500d02410700061442d9404030100d4184100c4051105441c0c0414112568400300b0041c05400c039076100a518480c000c0402d5803289005045c04001501030401154100241e40042204a44e846101d040900200c80c0e0350361422109801031302005081c400007600d00e130200e00010301000c4001c4005010421444a1102200b4982e407603040c142c140010f1859807814111000c840c1e460602c2404106070601400c1c0034400d0750018020700b020010394a40e00c00400b8050b0540342044000c10030350610b44001c00040c03018010381040000c0051600c0420700031648040d0041080100b9600c0da0b80102d541c90764202d800000303c0060710396a845010004030034401c0c030f41c000602541814000400342c0156841c40500c1c6005075403d014801c01c2100002440c403850207140708203802c8110008111200001424145114008030800302c110300000e500c00006003080ca044884401c01c114007004014030800e6201c200c00e003850 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 889593345 1250 889592095 889592107
    0x92d090201031b050d0213050604080a0507051005031513020c0304031109100315020d0c08010312030e07060e010e0909060105193b1f082b02280b0a02 66
    0x181184111003c40380ca954021801920340d41c48007c0810017480002c0482d5910fa5a905c030241e01c03400f54071010748250080f5040020142080c3d03840f5014110541c0c0c940d49555a600000501008440fa00e180c001c0c402c0c21442c02016024401030501070100c900941d10b039844c61812840c070401c1048414098002c0c4024824585c411100b0704040e130b948424492602445210420000c0c0600e081640300c070780c20042c4039202c007500041c40e241a00e02070a80300c0e402c100e0306034041d8141c5015444a01c242d512600d01080a10b124004d80001d2990514000302105004400201903c605840000072a0042001000306280c1036030f88912210088443e207105620300001520443c050202d014091240383c1c0040c003082540308900044140e059442403514100445000e080041105c003c18041c1015600400c1041001402101c0415282031110710f0300c0340e050065403544d07a0640e00c4401d5218906c42c1c0c19491501c808a07800a1007082c0303264005440328100f4030420381000d80f19559080c410450 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 889594595 1250 889593345 889593347
    0xa0b0a0b0f0d0b061c060c0921060522080c0f121801090302030d11010b01090b0403110a0f2d140904020102070b040e06100e0901092d090201031b 64
    0x2c08501d40e000381d01a40640d03104804586040c0d68211602036440d102c10b84d1104102c1c0340c0d4820003400c0c16079615001e0040d1154244140041c400c20b00318240e5944240c1c403800680c1541040341d100c07148014403080e1400d40c410082520902050454901d18013240030411440f0400c80fa911120b00d00004242400c4c0c0ca0044080038400c01c0301981d600c000308107420249034042c000034402194081d0172203800e44d50307001d8020141d1002c10000c2c8915400c0064140046d0311522a40056552004626107414556038442940c0107001e03080d40e40203504658001481e40e87c041c0c8001c000d140c03101c072600001a8100824014000c081600e411014808a06003c10400b0414040c000b8000790340d0740040f600e0300d00040c1d02d450426030010b01c8206000801003049200c5a505500031842a107a400c0c02c040c0b0443c05503aa1949440002d402600000040140107071540051840c155841e140d034800030210070902d0000100c050a0030200c4d43c13501d0702d00046590621400d401140c4611030401c9104507400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 889595845 1250 889594595 889594609
    0x301050705120901021c0b0f03061603020d0e0319090b041d040516140330030a020909070f0e030d1d060903190c080318011b02030a0b0a0b0f 62
    0x200b62010360110001071a140c025130403240c0740e5454210301c5020204610100019203180501d950041512a622035058100001c031113000d0141d840c0e060a00c407068a004400a400c1040c0003100c5940700c0c04d190264400520051102d861640c6003c042403000076400b4040d88a02d602543c40c402c0100001c000d040640784c44804c3d100e031003610004076a1038604080d490008269180400400690000140c0c0d018500340800c03201400d400b0748100e040c0c060241c000344a8448141d002e5074641e800c04070f0752000d0b041d001b1640b0540311000103040440b0540400d0950760b007140c00801041c403c1200c0c088a5400400700c100380a0102e004000b080c02d03c941c0282590a80300c3d0004180512200700318065840704144e5444180107011903054520117014081302501010f81515038103a482c10206100781d001c011110420740c00c0b05c000360a46e0141c0011200201c1a03080681243c0b0b80085010043e41c0501004030054011701004010381428550340040301d12404482744941c0e82c40a125183d512004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 889597095 1250 889595845 889595857
    0x240206010b090a0b07062c12131a04030818090c0a12020901090b0c0102030f090d0822050d030c020d0e0a180e0307080a08060103180f050c060c010204140301050705 72
    0x790005d49900c141e00d0040041e10900b040c0006440100c0e180d0601e450480c0120000c064886040300c0141001407d07210042c4142c1295440c2c040e8001c1040c0503440714892030b140c0c56114629070320714042d42ca44401c11603400040280380402c0c18101c0d1818140b400412094102400181c03031880c1190804000d404603542480c0107100315004500890940c0c041c0480700b0040900203045a50361540d641000d000b5401112000f0030b00e401c820203d4644800082c0c0004103110580360366055840d2000403c0c0c0c7d018000c012400c000a8100744880012400c1c080c4801006858401154803041c204010b401c0c0781606001004008541c50010130302d940350210070080342c241206414041104d24040310107401100b86807403152000040b04410080418000c0803000000d44e5907042580315a001181a00d000300f2113841120030b150805d801092083c0b04003002140314104896140c0140300104031950400746201c0796595010408100181c0242100e10040300218000c110900e4a103c000c2d009000d00c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 889598345 1250 889597095 889597109
    0x9150206070810050315190501081b0f0409050c0108011703120606070602030702071811120a090611041a030f040f06060b03181522020a240206010b090a 67
    0x40e00070a011000f10040c03c00600303400b4040c1c0742034400340044c007044c2c80c205035400b0000c640c01114140b48112a80708990680b0381d40000b80451070110011180e00d00d2496601d66404003025220110540d50b6120304180c4900c034a002d80000203184002400c140c07416480500d00c4074404400c1d460ba0fa0001c000c4404e015080c09018500792581808603499001701e000003014140b002003481051500014004111520b6010860702c0ba41d030400182d0030340c0c2242c101c010705080c003407082503050240440a298004c00742500000c400c05103448238015a0003844440498550008080c00005080c11000d141d4507007800010f8907500f024060400d58030300040000d004d031421709603400100415500712b0030050100c461516141c2c1130102100a6201c0162408071443c821400c0340c0306000300ba00b84080c440c2d407041c0401032a01480380d02401064848410490b40001d039140045864082008041e8628092600c8011038884001001e40b800c201030704a4654041d00340811070280c1c0e211724011007500d0701 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 889599595 1250 889598345 889598357
    0x16062906190504121b0f050a030f03050702130e0c18060111150f01060f0c11060f0c030304140d0809070501120b0301021b060c1602120309031603030915020607 70
    0x201c007a04651030300558008284038865280c1c11020300c52100d0706600042d0054041d12103c5507103400317449481c0c02c5072190700c3e0403461010381080030a140c0300744511400d010b802c01341d02d80b0001d90300160104082d03000740c000c101d64804a401e130f9400100000391880200b41e40d01402c454180790f116040303210003051035041010700c03804007003000f5080c0038840000c1d80f000880700c2d00303080902d031060f1040c509024010000d0709100040c165140300792405800310b60480424807041d00144103001a5610140301c40c110280200300c01c54504008000035403040d402000c45120241021050b2818068100b01000401c4440002d2140703102d000b05010044030b07000d0070042c03a2200d81d07070f82d0074020702241d000c4180d0651010500180c40c13042140c3c08050408560b05540440c2d0300e151049406006a918401e03002246104078801400d00ca04241c20700c08113a1b04507800c0ca8900000289080b80b03448040c0f00c05044d1035810010181c0004d40c3d80064081e0315503200350900f030000700940e22200106410f0400c51 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 889600845 1250 889599595 889599637
    0x10603140f0a11070308041502040e060415080f010501030606050303040e0703050a0615050a020d1b170421150603020616020a030c120c08030403080909090316062906 73
    0x2c05a00c195034400107a0f9030305446404606010b416944119825103554000c00c4400d00f00e0b00300b500c22902a103680c04140d8103607468072002d010003000c0e4002d00103902030182c00007040c008400c00005020030020000403c0960542c50132000742e940d29130080d40a64018441407215080d9828100c0c1c2c0000c451400140650b030342e00c18030000e411280d01c0045103c220701000d15007d68030800030810201d0b05c0d000c0f038003650b031001000c854400c0c031417156056820f030a60a050014445a0002c040700125100a5040985540e180d4481540303105070240a54142074810782081004070030724242041410b4104246883e44e00031602d03070301c5144a9000e101d4114040403045650710310710203001e56041038001400944840f10080712242610080e241213014503400641e421002048400792544121340601342185042800300b400e0010340300f004540001d201c81c92210060110a241050040801023030980c403144d20b044200180030b0000204602c4604084490345440c01210344468400e80000010b40d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 889602095 1250 889600845 889600861
    0x10e09040c0506070b01080105070f0f051c050106050306030d020109020109090203130f050303270705150f16110d1a151507020418150f020d1401060206010603140f 72
    0x756a54000c15842280030540a05000f40540d8950591318000002c0041d0b03228480d003036958401c3e241c0c00c8030001d9228820f0780ca8070b501c03c40c003824010781c800103403107a80c02090b556442611400d8200000103140030003085220f01e0200480c1c580d00c1b0860008100040842e0002001f140180c001e0303600c81d58001001c5002a246080004113054000c1c3c06203041020f286007060b201c0d88181c07641c2485440e40300c05c0070a41602800c580e16030601d03140040c000355240000b80300402040a00c6503a40c05021f0000800010083c4001e02c9400310b840030a00b04440c4c40c4c80c2080022140c00c800c0b600a002e0000744400241680b01014030600000e024032030103680b00c040b11090582c1c102c4905401440d5040704402c1c8004c52000340040303a100f12000d00c030140c5400020b0302e0b02c65107040003400038511380300c50b0254044103074040d0340350940c8807101501d05410b00240c403040d0785003419941103044803040104001e5a06002590162030185801d0107103d0f1076081060081c103000e003600c40095206000b043c1e84d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 889603345 1250 889602095 889602113
    0x60f0103050607081512010609050a11030402040c030204030c030507290714070b04230f0d150b060403142505090c160c090605220c020f0105010801020a0e03030405010e0904 76
    0x1d04003c10441c3c03104c0122000314048c1159104010690f0300300703030114002d030f080d43c0180c0200d203010520150941d51143c0801020f01103480011040c913508000200110785d00728032240155006034020142c0f9882d0040400b00d0426441c09200e09101420031500403c1d509001c564407240c025204101c1c3c071128060141c20702a232580818440100058001341c0280c000e40c0e580d035910000c0049811040381d0300c0c00d20203400b540d405040d0780701d40d0032801100001e14150180503031b1009100000780c905203020100e03140790305c80d400c241c2d204c12504014095104081100300c05440114202080c1c2100c07020491840c5011806603521a03482c0800140c43e140250302600e000f14904440c07943c806000d41008002170080c0d00031580120309040020071142080742c070740035070b0192683c07030980000790740c80061004207143d0b010305046000f901c0307000d41e0495090140d540601840b42c0010380e507815605000c1c0ca20f01c0f0f03400e1694020b40017480100031584e0410109c0320320060030394084c060303661540742c46148 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 889604595 1250 889603345 889603381
    0x7021c200109120614091f02070203120c010b04140402120d09090f020c0604080705120f030c0313060509030c07050f03030a0e01120e071401030923031209010e060f010305060708 78
    0x1201045200f0801c0030000003400382c47c02a006480310340d40381d03180e04980341070384144e25000e9050f9101e4042a0141022603000300440c0b82c4050000550543e1413000509a540307082c2e08e1804c4c60583d000303120551500705c48800b14403031407100034a000b59030884060310345102032180c3c8150700c0d038444080e82340031b64035011109000d2008c420f40d5014a41071512030056040044295014816001e0040300810203904903800c120076902d10302d04654070b144080c0301641c0020321802c41110f21081000c0011b8050280034005c20307124000d1a1a080c0d1404900d291429070391140d4403407030035001c3c80300c4141c80c0031044807640c48007880c20480e04110351005a4050320a00401c3c0341c91403404840f040401008034a540a507050880c9604070714207000c0044041d5400f0250280c0100c6480d6880e4540c1004400500d1540c04d81c1c8055a0a0592040402a0000d030499171451941d460300d92452500800b4042c00340d00c40c0da40e400c0c1030580d5055883e641d507039050007020b00c0e080c000c0300400726036801c040e003025000e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 889605845 1250 889604595 889604621
    0x141903021302070645060b040e031218010212041e02150301060806060703021024082d061b0d050901020c07060f17040807021c2001091206 61
    0x10144000304c000b207076000c00146011000c405000c180300e442c085100141ca11405e0802c1ea80074080e90701d030000240001240140d0040d03996a01020194040c030150004076802400b42c03d03a454140d90507601d01c01c0011031750420b40d104010000704404000d0405d42c0060b04680002000c2071485011100b4031011000a503010f100c41030700c2c0040e4621040154180e658641d01c091040d00c992092103898000c500c002005038001e14040d0024075000d40c4580030b4220005040224116401010102c0b603100d6000805540c100020228400240f0381071030a048003082581110100000c181e103031501e902400100d070458420780340e400800101019a2060010703036504108a050102109000b544010030803000c3d070088801c00548503006034480b45601d11161212000d8101d2644c509804010040088440060a101c14805a00e40e07075040b10245480d8a04241e025080f030404500d402034041038003080c0084510301c2c14050342d120440d403040710882040894505150701d4000060201c6100483c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 889607095 1250 889605845 889605851
    0x204030804180c080103120f030f0c050702040b09040c051c050619050907050307060e061903051b0c0a0303050a020c0604030918061d040302070b03090105011419030213020706 77
    0x42944058165040e00030102c4440411100589030002e8408120901c000ba01c5584201d4034941e102d40910402e8100c100e99250000740030805000750400c8034560038003000015030105c2e24100f182454458100640c000b150058413a10b440d541e451640002401070354054003a494444294020f160307249500581d05c103040c4c684c0d40c5049503003060204031001007801402d06100110384607c80218850040d0351000d400740810070709046096030b0050100a0198002c2401c00c074840044c1041a00180561902d60380440c42c1e0402c199a00c1c803400c0300300314014982030200070900c1940030014118200c660316041c0400d65036140e08000c070083c0513403412402e0600a80003000701705507101000e80103441c490114444054106400003044460b64060118240c548403915070500412111042d4814802c3c812034040ba42c480310424141e8200781c4080301243e4496006000d074440e45201030a150130140e803a0680d07214260841c2e40307091610700c0040d0141d0850300c250480703c03145404507600c4d690070440034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 889608345 1250 889607095 889607099
    0x3040911131409060f0a03021f11070609141c12031a091b070203070b03011401050f121f03150b090103050616121109040605100c11040204030804 64
    0x803440764004800200504901900400d072240125031001c2440e00162031014150303038690030b01881c014107030f200c00d5100603441030010060f600c452607270010302c1c21000c00d011900301060020b420030180e004910000d810030030b024000945d02030242c500b1146201c403000c1009000501143d20350340c520f4120300250061025801c180521100c00401d00d6065aa081020076030206031103180c00d04001010741d0010513140492030110320107100040e0072000c03d90032450100250300091504140d54003036107000501000400c5083c007010040c030b40c440005c1c2051854003c0030b904031080e502c030f80d160000c121070401020541078443c080c294400c00c040c02078811181f588034200a0840c5d0380019412501c80c3c1030840502940c242003072968100c076071000c01040c641e01c030b03ea5403c0300540c58000040810141c40344481180d4004c0c0035200d0701e0300420314481d0755043c070301307041c001542d0068000501951a00303030000722703003a8051090181c06401041a40d00062050000340280c441c0d40e10240c04d07401d003c0b80c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 889609595 1250 889608345 889608371
    0xb1b0f061e0705090d120906090623120f0a0e150a150f120203010b0a3605150906040e12160f060b0108090109031202090111060103082709060d0302030409 68
    0x801c143c0301068845c048581c1d41c42c07030100ca1680c010700a90b4000781c850210581420b818002f04009420150700050805403641c86043d01140c0031250300040304000790520400c000f0a00c9400c42030040702c03001d4a45070102d18031a8041d00e002071701441446588043d581a098044580d0402414032820b10300740b00d9584983e10b1940450441e82684254a0041c9102840c501180729404031080b84050490024640b42c1c00100030440f44281da24031180c046982c66010440d101d4a372284156440e112200d079000c0047c4800050300174100c1e0b01843c500300c07802a5034000003030f034058101d42e540c084c19901c035074101016010554185000740450045418882042066001803440304400c0c0d071603402940c1e6a0782c0c01801d854205a0181c040389221141c84640304985e0010840e080060400491f840782840c07525242c100c0c241e006a84045003c00c2d9000f1400e010094000900081c11030030a40c81d040e400083c1a100000e0b2103213125284111490080600038400c7d1801058a10400c12035802c100341 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 889610845 1250 889609595 889609613
    0x51207030b2d040209030a03030b01200703060c0201020a0905100c0f0b010806101410110a0320030c1906090510060602010b040905060f0603070b1b0f061e0705090d 72
    0x101c19a102c82403800300c6100e003454804d4071082da400078001d05007a1020f440a07030003000d0410702181046404a03010031064011703803c001074203c000004261a41c42c50400f541107074144654403045900410003580380c1540641c94105440d0200c0c0c6840740c0b6403c0308815a004005003200901e00e03580512841d0510994003034060488541c0b800390795907540c400a4010303000c1b2a500034020315a00a20b089841410320103400005030001e820007450031483c01350014036100003100110009920410090046030059031000d45000485000b0f43c2010a14021651207610100403010306111240d0088180910780d0400d03260190000142c910f0740262030b80410250829000708000366092141d0703011341d41050300c2149031f0301c1e4105014108907200d03000381003010000031f44200e60601c02c24101041280c810030041000c055944002180390b010150030b10304145185e0400d01d455000740f010002c0391082c445030f400a0b076001c40c0602140d50b8544c04140c409025803c4050f411121030a890030400605003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 889612095 1250 889610845 889610899
    0x120f06092a0e060423120f070605031611250608070c080307050c01060302100203070308010902040503030405270c0a110d1b0f02040207081209010c051207030b 70
    0x11480c01c42018054400b51030a110960b03845030000400c00c0108140091200c8040c034040600d64450840e014400004aa41c0036040d4100300d16000a20b41003041078003003004000820407030a00724110710341102d01103c0340300040c0550f020321030f00d502000305d01203061000c54005e40307003048240400c6644c080350042d138801500860000c18000e0780840e40c12405800c483e841e4540c452080d51840d03583c020200c0712608806805015503407502000300040e91107110b4580f0140340c50f070046443e4011801e00501c0c880b410ba00070401188100001d200903180801142d05442d010703214038000300a54203400c1d810b4070154020b182140c400c841404504040340d4020440740303100b40ea55840110302100c03100c4e1505012506000800c3c1300c000c0030422420b1440c840d92410340225505503100c1166000b00b4242e0380318007421200510001044071801c5505400ca1382c02907001d4000b0440880e0000c00603041c0d00c00c640010325610818000962102c5c82608a070500320710181660307842c809205622000c100b620 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 889613345 1250 889612095 889612151
    0xb0703080705090d0f0219030602033322050f1504051e06040e0316060c1412181506120c01120e070e090a0201020d0906120f0609 57
    0x1003001c141490b00c61825a074440070020140719101c0c3c00f80d40c0300b910300c0851401c02c07038200325030500303903001410420280c000941c0150400769892820203000080a01400f980d480e40e600703883e00c5014608207240080740302801c103850348021950b1841c0c0000400c40140d0030011000d0a11003006004030490140c42d008003020400c019181118800300416608111400d585404000c00c0c0c200c0304880da07404581c0c00c51005000082e8205d5141e600d1400d643c04540c52406615102c0820b0f02004494400e01a050000345040500c00381c00002009540c404e03402e6000107140008046108104603c4030684022003640071039103c0e041810400d04a070000311038040c828980c0c80456086528007042c1080110016035424030288210394210780241800742000301c161262010106580f44850441402020340031300429207001c82d44002840e1480740c68006003008403c132010000c66411066524174601003450118400004082c1c61b0002c0a0550002103c1414602d10345000110103050f10320171001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 889614595 1250 889613345 889613357
    0xc05010f050304020f0d0222060311010503010b04090c02030d0c0c0317010f0e13020301150f14090126060c07060605030606331b1c02071206020706060b0703 69
    0x149103400c0d10540000c0710042c1d0402c419466030324140ca081c0c4030740d1400a02c002c08000c90312030409440d40d20994107103031110100380c1d03c203414801d0052a5400c1c60790203400340b074245c1ca5903047c654045c00c00e02031445000180e50300d51003c07100441c024025216031848c0c4134070402c0340302502d07600280700d0f000804050b000314a500403601c5060900781c9415050303880010740070b54040e2800c0c0250181e100028240b004180c181002c100c0185e030f0a001c2d442043e03031003090303200708641011841e682d071900d43c0d40700150800d51642d80c60140e8444464450441d03a0030a4080c40f840603403030043d1070861802180c0c62450050408001040c41150301400783c1602070300040110580780c00506584aa0035162140d000302c2500c018040204c000400d00712030b8444440504440406901c0d50306580c00c0b000d00820058000d034203005000004000072588040143e207107001013481880040d407582d40502079601c000b0030a800100501c034840c1c040704d0509500000070414141c0c0c0300c08032599074100c5a4114000b45d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 889615845 1250 889614595 889614617
    0xb030c120a0f230c0303030613090515071b0c05063001090c090f1a0f0301090209010305070c033e10231f0504050403020606100c080415020304030f0c0501 68
    0x83d00040c207001681016004501c2c0d601e03400100151988100c1c03403c01c825488641d00340c0040d00500c02032101504400c01049503090605010b0700e00842c0e00c44040000b108642d41d1804135071800d00d0070702260816940d03143e45284044004000e10840c1c2c491a2a14210b507a010b0030244120310898102d545844c010400703440c000e841200c0005061081103a11080074030180558000d56020f550b040a016000300c1c507000003100883c115400076404441141d41c0803406111a580500440d54042c900d840c00e6100d407111564043c00d980b40400f00c0729040c0c3c00b1213941244054446170014003403505021544a29001218516030300c4d0044001d41b0300d00d07403d080c1c0e10000c400b040301d588009851303600d80c043c0c0140c1d00d9803400e204c2010106010b40c5015032a00001580b92114400d00380034900990140c5003074a4048248100746032100c80000c10058030011910100d0722a605586c00da41c400400d4030b07145210020203e1650081e078002070580c0b0349a800000c2042901c01c9070718100e64080e00d518030410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 889617095 1250 889615845 889615913
    0x50a1a0603010e0c2112030f0604020f0a0f1206031514130609020102010f060b070c080d120b040605150706050109060308192001021c0b030c120a0f 65
    0x80c00300502c10780b21398880042071010386841c090104400c070100c1e507018010090b20f0080c0b403410300b00c9131100400c09400003d010b070001054460b1540b049095406514040007502d036801c0318450440c5250400043c2e0701c406138454030806004c008181000024404a9205e0801d486050311240c8810760071490a0030001041403440071b024400c003111166442c60b44103984441d07000d8400410100c3c115540c940108506c10110b00c40d00c1e000c2d000c1c1188040e01c4910601e8004030b02c6542c0c1c0c000c08416840310b20300303541c501d5001c0c43d03c2860302c25210020a102c1c540b030002c50301405960300100e502801101e0352400108885010380755640c0249404e201a907030310070900302142d0007400060080f86003007103070f9002e05401400d4002d100100780350001010b03103111285440094044400c8100d4ad400107581c1600e080b1100204001540341401000b02400c0140025920700740621f12900540f06000084003220701400b045a074281c01800b20420754405252440380c3c007056007400d07100c844004080001c1c603 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 889618345 1250 889617095 889617101
    0x80f010f140708070809150c0405030c15031503010b1206061f020309120f06010830040905190207030e10180905060a030602071a0714031b07050a1a060301 68
    0x44a40d80c5900c1d10f07035120301c1c200b02d031a000c00410f100c0707041c45003107070010b6103038282614244103020016515450f1400d0000705410101c09a5a0724403407079030007032014070b00352484c07040742d400000c8400441014814200030a01500101d0701040e80205003165640c10810081000b6100300c1c0704a07805034a10001d144110200203132558074400680c006c1c01840c1d01d41c141503040221380400502150743c5501c42d07500741464140242c100ea0b5858011b082c0c07507002405101d104030032505000a050034003151081001000d030045200d9100b1194544c0b01041c0300e07948440c00d040407031103803540943d41c40c945420040d201001d80000c0a01943c00700c1f0319440e0051080007011210219000c41c2143e16107042c0320701000d000050102e0f030f0b02401c200342c00400110b00d4070003010424071440038030f40304808100300a120407030010300d01c905100c400c4e011001495081800c495010300743c000020070750f40300a11032041c18055502c00402a2003280e055205001090140280024080c001c5409680ea503405150a07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 889619595 1250 889618345 889618351
    0x120a240b03060907061b02100905030d05181009151701050108060306070c02031e0601090b06040803040b0f130b1b010b0105071e0203071805130822080f010f14 70
    0x45a00451028040240725040c9070401d0010001c001b105034140f40c002417407080e0a032001c0404116134003804c000905051100c06000301c005e081c00340c2003000c85004c0400400920721110300c07610322240c540d41d8031800792404002500f00780d103282c1c099100c46078000e4061602c0d86500c3c0781206030400009030561142501510899010380a040940c6074404255103d601461080742c1c54004c0c00c06c03000d00d46900d4080c1d9600b030b0040c5401814194501491103040354100c00400d409200304000502070110008200c50031561494040342d03550140304e10303600c01401b800305d070656000100b01c0e0016422000c48082c15004480d140c0c0004031402520b0030038200e034119602c4c1804900c0500900300403031414440d0f03050310101d0502194001034640d000904101281e080803214000c005c1c4481c2c45510039100d0035600400c03a02c6c0300004617005894603c81800b54060140c215012000d001d14143c0d0711035400c80c024001c01084540000d00d03049038038060a8403101001401d07160a0b11310301a20740c20008580 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 889620845 1250 889619595 889619611
    0x708010213140a0b160218070c0b0a0e0a12020c0301200a23031f061d120f0309031516031d07120c060201021305120a240b0306 56
    0xc1c00500d81010380740401c21815030168401c10540740042c00c090b10380028040340b0100401d01c103902c0081d2040080c4000b2000d074500d00140c1150402118980015400d0800c40e00100180a035503101d02010004d800c0700c0c000a00d02e40161b00c170300e0f800c2200340d00606000b980c1e19000d607001540c629082c9822a005500307511a41058510100c2950b04004010500f0103a913241c0041e030003113a035145440008000306207520b1400000f041000114400d00100400070b44007503034054040c54004005c00f40302c420390b545081c085908484840955500d41302c80b14075030075075065415000c070851030719480383c001c5158607020b0f0196500140d00320017002201803285010781e40940c0c4540d0007900803002030038406400300e03140c040e0b0003c0008680003003140000031702070840c0c480d503600c8180c0340400c5c141c18190300003001d580c0140024110085020181000d544c426101108500d0700c07010345500e03000f12454041c02d0b12800d0040c0c401001000700309142d100240e0441070010381e14250500d80d445108450400c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 889622095 1250 889620845 889620877
    0x2030d0c1b2910080111120703022a06010303030e01062706030f05010506180609041202120d02030109060b070f0318030b0a020d0b0307080d0c0501151707080102 71
    0x8400105a28000002c00c10200a00240e0101031120082d02000540304068002d4804608000703070321003401000d0300900002d4103141408001030174281035000180040d805c2c540c000c1075070a032010009076450b901c0980c1c20002010035440a40369621407000b80010f90000341007101c0c140905005020300c00c02c07100c00384d124142d900c0c42020f004a0609003440c00041e0682c603000c0c0080811442c0380004409406400000303007504020003000000c9035504a04021035140e0070400180d81d8603410503952058000244000c1c00b40303500412400d0114a40325030b00b06802c01f04142c9045241c82d030145042e02c406007810810141c9440382d500b480d019251004050800101301080085e200d09900c803079203107190011a0100d501d90b61043c031000421a8030b002205d602142800303640c696401100103a220540141402d68100401140c5506000c0f80d02c5c0180007594490800300102544400c42900804900300401038a0721030742d076030303411491003513030843d01c01d417030f00414540010b200b00c850070200c0c640e043d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 889623345 1250 889622095 889622147
    0x9341d0109080d03090510062310120203060301140c180307080706110115090915110f0c0a1401140c04150c0204090b0f0a180203030f03090a0f0302030d0c 68
    0x300d02030017042c0421a0f545c094102011006051802440050002c2003058540c81004c60030711440000d080000fa4400d00300115441c083c41e8020884118140d02d47c100940c2ea65a207001003405400142140d480d681c0702c0c0020040d90050400c0680358001d02d184043d0312100c02c0750b0805a4422160003804181d810840c3c00b0807401e07005481800491041100208156001c080c0305c0b15000d40c1c545c80300c4441d0b501d070310b42c1c41d040112003c004262080e07070341c00030442c88030f00c0b8084d640c0300c2c01342c002030b100c010000148500700c04201300107415496500115a80784841040219406030520b601d01c00800500304001c110098032050a95040c0c175124181c0002e0300400d07030030484611500c2c0384240d030440d0340c0d0340f52000440d07031544019100e50400e071400c071020701704600000c0440703801000288001200b1006500107070380103c119501441c1060f03455440fa118010702600300001c00000426030030070031040f04101a0044041d156070562500104504010007009880b10240392181c42040c3e80c24580d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 889624595 1250 889623345 889623347
    0x150302030115110f0f0706030c18140a0e090c150f071704180c090915030615080318030d0801050d03120e1204170a0209341d0109080d 59
    0x48010003a809508441c9140780191a0b1410f110301170500c00543d0300404400d10400d90940903024502c09107180103081300f41490000880400280900905c4026a40d440a05a03480e4183c0001804030310881c0400303410700d020b07001d40e1290f04d440c0003170051078410f03800508000740c001038032800704c841d40c0010701e00405d540e078260141629a00000f13010030103000c00700b00307500c90b2901340160070003101c8000b403840c0300c0280150600f2860b5001031901820046c210382110003104d81902244e9204402140c0c3d5a501c0005d061414a650462405c41c030001c42c1c110304843d007504201e00d6244043c0c0980b1101c2d855020221540700d024010319810800b19040780c00000e100305010032400308481d0300090300b002000386c080c2c00c11056143c80d82c0f031464089002c0c8445992034641d4000100408014448a90141c0c04140c1e49a401448104052105640048001c001c082c81d211000012400350381c25054428010307140f0541c2c100b0400c0b0b0159901030b251400d500503001201503072910300040c2846110014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 889625845 1250 889624595 889624607
    0x121e1214010308120405121c05150618040906090b07090e040209061201090c060c020111030a08130f0506040b250203030c0912011416030b0906100e19150302030115 72
    0x4000c95151042c02d447d401302c200c502e40544010040700b9031080f500a0800704410540f03a001d000c060040c9403605104400340c0e610700031100c1404041350948040050400010014900d00c0b8000c0e154501302640b89081040c07038519a0300c5000c198854000464403080f812542d15012180203420000320400724403945000076800701c01e008141d00104000301565160305401600781c0c015800300b1000c2c40346d20115038104a020b42c2e030685507801141408810b041c02030072480060250180311b1440e100322400d000380302140091483e04001204d10500b042d26080c2d061000c1260382c58002c000c01018640c40707040800e1050b604407039071341c019803c40d00c90303114005403a400980c00c07030b0b23000d031b560018bc101502c003e00030903001491104070902c3d40d140808414444401c0048804109480e1441946490307039141c07807054002c513040e21401000d6100c0070702901d5220344460120344c44840310360303e0b14a0407a112120341c1580c082a6106403d8890b205041c0c050b80428003c80c030103900044030411344544030320 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 889627095 1250 889625845 889625851
    0xf030f0609050a150203010510020105040b01030b040503160b060405060103181b09060e1b120106120603081201140307051c0f0b040303092d121e121401030812 70
    0x5064400306425962640c03800c28140d030813183c001d07802100422041c68601015544003403240006d0046207065070764603c0f80b41050100801c031019800200b024400c0410903940380281d600526055a8102c3c1001d00c6215400c0380c03480e100c0c50030640020115407081c010340381403904206111400201c00c2d42c4280890030302c0c170321880c2a05c1c161140010081a40d0203202d0040c40814000640c6042034807034540d40a49c4003120310986c01080040001070410f1800181c1110000d141c5401152054503601014220719400500f00303203004180d0480380c81c000e211850403030307500e112014080b6004c42c0a0545a400760b2040c80d40c8014201d01c412059480840d40c0c090442c840c607040d841d004c103150345070206103000351803e40010b40e96000302810064003441d20643d41c2154003500320300e9881110246181c866424004044440d2131404003c1540245000c000240c0c442e1104512032800144c020030102104c2c58282c1c0b4036041402420ad002d402d038070024141c9421510b92031406c5501c0d01c1902483c080a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 889628345 1250 889627095 889627103
    0xd03021005090f0a1511030c040b0d140a0e0705030105010602070603050a060302100f0809011a0f0f0423010b03091e0f0a03090e09070e0a1a1003020c06010f030f0609 73
    0x41c14080b41c01c3d0081c0a60740009200e01c06121100700111505000c650390300386000d885040c10414030004861800684040b10940c0944a075506d2848003641c000d088602d2149940c0f0322003030148140c0c000a50006000300c1d0400003100c40d420380d601704042c2600c101b0321508000d1782002c0070501546209401c055803000c0e20034001300e1415547ea01140051405a003400001015242c1029685500505260704101d25500a2210703410030042da42041100440142c0703d42c0300900c461003151501903030034241c4000140200003c1d0500c188001081440002e50800e607031a80002140c400c0280f41503a008072a048001c29040607021040e02070300c84800a02006407013825841c0840c081d04112004046100e41c2d03074828081c0c80c1102e5400b00b203502811aaa0700e4003d883c0921140303042000c1e0303683c82402900301040d411001000f040112109850f8190410000383d0307052038854041c1c00500509000c0021142d150380c0c1c070030105040d50f6540c0401401d0300394174581840481e9240d04020300031801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 889629595 1250 889628345 889628353
    0x70c0c090c0e1f020d09030c151107060302031902070b01030b040804080610090f020702030d03020d1503110f0d05030d1505030a050d180303050910230c0c0d0302100509 74
    0x4142d00258112030058080818084404403101d44150305018a00f030380c17a400e0429801150641d99070000d41405401108603540010400a20040c4207078a5a0b41c900200c500303940c0003603180da50040c0039503c2100e141c060314807040000480455184200e0741d0141d00010210304a0342150365542030b0381406070041e50b0444040c080807d03214424400745025443d2282040c00880c5411200320a40750440400e80d8814418042c034000740c1c5000c40c00d12f402c000c0c140360050f940c0980500705001004207414401c0c1140c0c07001d0000c03040003803004041d40003240c11a0444801e185240801c00840c0507040007c0564100f4800740d8840302003a0400e040104041d62400308051700c0d4030200e4680154104103a4403603000c17880481e4420b0b0809641d100c10300c052040b02841a0860300c02912501c9520791860181e103490300c0f01c0c10014440c8071070743c8420310310303030350265034501c40811804030368000c2e41482805010b02d0045090500e0203d50240d45994160080c00b0f41d0003882c0030b40001404002c1101000303003d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 889630845 1250 889629595 889629617
    0x71d060d150806090c100e090702010f0f0603150509030409050702190b04032c0607020a031a0108010c02010b0d06020a11031b15060609091009180b070c0c090c 70
    0x101c40120729010746801d400402092409030f950f545020000e0380e0301c600445a400c800e084450340003c50600c80700c01607851211030748622074100d0052941d88046034070f007480c090110909140c0c542000084901a485d04002092010441002c80f0402e339100c00c2d060380100020044012107411060b40302000380141ca1289035810320620344401c0c200c004072030488989041208054100040c02108a0111183c1c2c1c40c080b07044020744d01d00052031100034410080440c121085664a04c1c400d0013075980800c0c00310750311941c1cdc0035111080ca02030060492039420040107162403403051064102c05000140303204c00d20b0740b4076102d5800a5100713030041010840003030550002c3d0b24007040109100a910031415034420402d1404c3c0b4100044020a00140b90300041071115035614041034070018a002c445890761a1103110100e1458040c503807141e5241030600d504001e125180890301800c9500031308002d84c690b46c1c5e00703008503804024150000c018080c4c41030113002c1524030713520030f602c290310a0503c2c103c054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 889632095 1250 889630845 889630871
    0x15060c020d03090f0b1b01050103120e0d080a021e0a020f040e0a060c050d0c02010506030703030f1119020108010806060a09050c1e07020301060501110a061a1003050f071d060d 77
    0x1190416003150b000011010106c5424a1104d40340c0301c2c1c0350000708540c0d415540c51419018003400312008000d4803034101440c83d0b4942d1840541258440c42541d9a14144c1030040c0d03c6144d0b5440032580d2a04402c1c0750300800401041c9040b2540c1d004100d000078848003410030008052000b15040b0358460083c1881c005116445460f0318016180c4541c1d4641c1e400381d101105482130104028210390401d418001d160300e0014042007900d516081c030b0b541c0c5e58000e03601220209490703d000f81c414032032113034600a242e200e40042c2503094001e90b45c0416580e00e84602540c0c60030192001600304007104404c020160169000b40c0c2c101103018001c0b03147c41040c0e0202c44078010f842e0740c40d01c03580c1030004210301149024810807000306001c0c2410000d40819420701c0d45c0320108007034040e0405413625404003550385620400c0d804054001e005038801240910010b009200898a4000c0c44000c0700218000e14001c1d80c1c20542c020810006c040101c0050301030280941100401c8800280c540049000318 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 889633345 1250 889632095 889632119
    0x204030203030d0915020703020712080705070b03060103060b0301080303070e19031a01080a020105070b1b03040f05011419021305090c0307020c0607120e130e01020d15060c020d0309 80
    0x100001030f0011070031201e54107194614001c01e010b48514140b0410010f030010b5004981c840403074840f46003030b0780303000880e003060007a62150364402402c0c2d000d040c001041301c000010113140105001e030381c00c102d05515510321000780d01c000c1c000c810156009100083d0039602c0b42c20300820020000e00020351320070601d80a480f2485840e0021a04029840a04080d07010342c40e42050040000c41c00a21807240d6680000c2c250344501c180103081c5080400010300d08203021640760708100e20602c1c82c0d6a6038981800d111100c51185a4202c5595080034100d1282404111000b8001c181c90046801c2140a92307220200960242e400441c4440104800140595a0030001882800e17080d1040d5943d00d46600000d0404000b542150f05c00c1405001e8240810102ca03981c50300c1010a04010034001c16201c0003da0309448090001071282c00d14550500b19201900a410805032810040c01012610b851000051286002d480300003241c0009040c05440c02c80c0c0f1050189001c0d051242034161070300c60766010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 889634595 1250 889633345 889633357
    0x13051014040612110a081b21070305130803060d030e0d03020a030215010f12020d020306091b06030921070c0e01030c0b09030c13021c06060e0a080606010f03020403020303 75
    0x110340303083ca44110f48200342c01244148100c042181e0b203400304a00c0050701089002d41740d00705c0003080070794801c000c0000d001240c01c44c90030036000b007040c5040180e2202c0480c1d01203419100003820310f80410203204081c0640e080c0c0300c0d44100e43ca421741d40d0b1a411302040c140c2207c015410880c101d600780807540c481c4820742c0c0c2414045e9028059401203401c01a10300110420051489103115004020195403203054000390740c542243c07140180b9082c0001001030304070740b80113581406204144662090b0006205d42c04070303108070072800c001030000100003042c0021038520b42c0742d40080460000b1020305641481414248104060610480d903d130f0a5072412642c001c030f02516250b5005200380030311202e0110003045240c100c0c42c500300300100400e85590900390b00320f000d04041d0f15124400a5103406890346541500c00c07546181d03440c004550064403a83c822600401c804030510144ec0c01c0072060070090f41d1224000f02455240c400c0111041413600b99260101076090002200507a824401001c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 889635845 1250 889634595 889634597
    0x30603011503110405010e090c041a18010911070f060e07170105010905010509011d0a06051c0b0a0506030d1b0f12090501030c0215100f030c0806060402130510140406 73
    0x42010f030500288001c840043e000381c620144030108000f02c610340040c580c000600190350201d040c03103041d00225208580300040c5648544108002004001c044060b28120ba40007070b01030010b4184542480028031a050b0094499651680110041080ba800415002120604880080d641c07028100b0700c44800301e55090290b519200100101c03a12030080f940074003012030707100c1025490000120709100300103032840040c5850000140b0755000950000009220150801003800c0d00ea81b0800c0300124044012541010401c0c04180c280000d48074807481490040e006169040540409469000341d000d850080c080e02802808001a0389130540c0d0140b42c0305001030040d548200d074011700864050b801c01410549040b1440d08515070000e41c170baa0080d06e4035801046501d80443d5244a002c041d08640301d500c030360070303400410017445200040444040c0010355032603403940c00400040c1d116082241031702c00d0070a28203012a2410070000b20148201d03040c0b000d19071a420780707407104581280d48520 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 889637095 1250 889635845 889635863
    0xf08070b0906070804021003060b0a05130b1806130b070c05100e091504060b22061814180a0e070902031b03040311030c0c0a0b031308030603011503 65
    0x2008024515891582164440014020910b84004000c000030b10040010740b0071464203034034824840c0203500160291000590440c1d0380d004240000c1e0496001c1100d809100c50000400030b183c1a51400391000003c0e0100740e40720119000007008216007020307030100d01550128200040305da0105c0700804a041c4500c030020181c52404040004121301d8901e64800c1c09130500100c5010341c1c0d4400400d0348014000c00c800d80c0c040851001c10010302554221500c5c440d80000d40908201d101420242041f12507401f1007421600d039042100c403d05000c0492650304117000052140e010207105100b9640d40103840030400340041c40c611038065405503405000c29640320146003034480c0901042e00640100c400c20340c51414030b4160028240205601c410280d98044003150030184200e40c1285412060320440352201124260203481e20f0400d12950b205480c81400020443c1c6614240c1c0c0c0700f4074a807001e150303120200b501d422040e46d0005100356499540d440c016145403842101c041c010314000c0840b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 889638345 1250 889637095 889637107
    0xc0a2306091b0303160b0f070e0d03050a1b0819050a0906031e02030f0702070b0f0909060a120c060e0d0503091e0307080102040e13050604030e130c0c12050f04060e0d0f08 75
    0x81a000b501c40348c20419420309072446911440c4005d6823880e4517142032076442080c11007c031410b800300300c5502000804400710310107008040d0041d007403041d5500d4100c4200200f1600a840b588036412148012130f10a030b208202e138034060390000e1031145910f5040421041c02222180480c0d00407242149411800801d1204a81e81084000d01500d140d403500e40c038280f0007440075041e60240025082c8a44600e600103201d60301d810107207000800c203a06481d00d41440526145a200000d4015640010020002301e000303854440d80780b0140070340050145152800f0081401002c10300c075241e000312100d00122011680d2810480b000043c4422000140c485041410000130380d00c0203800100c0b52840142007401058004c07031856000755250902c2001090800041003042c80b4036115040b01510300002e00c0405504a440340400510501030420400c403000410340d1540504070f500b404490382400180321050085403d86803d04004245136a29251680d40648841c141001262050310105d45 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 889639595 1250 889638345 889638361
    0x9031a0c0d020a1e022e0b121005060117010303051602031c17010b250206070605061306030b16030617070e15030d0e0103020c0a2306091b0303160b 65
    0x1800c43e403581d1034405803103600260b04400c0000260500306d0f0818810000da200c50324002e544c048041150040c0901ca03004442181a9403100e82c0030040c009818148000601c041d84510020081c0810b0a40c561030302e642983c80440742500068403180321040307215800380140e5010490001118101a44400083c0e10307520300070206084055a800b16480c18001032003103002503000c1e40d00700c0c240c0b920a004500700142c0700c1451440c2c1044041e410580c00075010060003220341155100e100300341c4408441c0300050100380c048611920015009200c40400b05400c011480c0c426850000c161401103500c0e46c441c03e00d078188250000341d12800f40d10940c010003681c0182c000c0c13591321007851700c031800e54500d4a50229803581c1403507500c1410414040554800d60780243c4c180d03a02c0520000444031441661f14240404411928601000010040409441c0200001d010780315601040c064000d24540100c8004d106c0d944044a41d81400180003203502c1d4400040c2c0c1f000118040c40c000611810314a003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 889640845 1250 889639595 889639637
    0x102a05100b03010b0d06060614091807050d05090309180403170730050105120d0507020a03050604030320072001020f0607020607090605030105030316020a050616110109031a0c0d020a 80
    0x40c002c1e01804103002107412a5180c4404036074002c2c02c26400600d0760758cd0f10003201c16201d0f030a0409031261400c000c1c00219880003002c1e150044080d100304802d0301440000380c1007000d00302c0e401400582c0303440c41c01407015485140c80e900505039050040d603820b060341c824800601c0c85028044a501c201e401c0104026940c002d05004280a0320350503c0d0344890f46125844c0d88407520740388140040010344c0001c546458000c2c40040d5000300030340d541e6040034034004024001032000100d1501c09038004410f06442c400031190900d0b80030035071103003400e00751001803a00f0380520019410750040d4444007540207414003c2520a01e03d5a019103421b1a020501409008168010200b00b04060005010b5918004100c50b0041000718580c0500d51b00c502c0000c81c0040160400d9030450808203100e481018a80d4194202620941070b00301e0f101c003040011030b461411440047c004d03c00750102c4054cc02d132180c00a5400604c0103c0c0e42d0b10301034203051008266482100e6a070005075520980c011003a042d04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 889642095 1250 889640845 889640867
    0xf0a06090215030603070902090d02040216030f050408031b100905060405060f07082205030c1b040228030f110d0c02120f090f102a05100b03010b0d060606 68
    0x40c0000b41503007401001721740d03155028020f012005900080c2105155103601ca000995a80144255a80c400b81c0c082d1640000c0c0c030785412000300710b2070311510b0f80c0c0900540030780741a150540e0045003042490704c082d0109881100305000030b0702502c018007138402c06d10300401003005e0141004080703600385031420518001000300480449000542480741299001000b2a0082c0443da49490308400781100301c11002103060004003179210000e00e00d80039a6000c201c2d102c00e454442c04d0146111510b1003072005a100341b080310401e1b025003c0891010300c03c04e88040003107c00b01d15000511442c908058070485020760841440d40d070b80401c624120078458020401100158400743c0300380d03003030700c500c001c01405090a940d9601c18041507410040c2c5942480030114203004081402000c4000c00241c0308942c48807031602101848901d40085072103940c0e541c0380e441c3d4040d000b0009621125014002004095050ad80c95503c82020035025528404e0b050006400b503140050500e00c1c1900281800c2c02d54 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 889643345 1250 889642095 889642129
    0x3041b0e060603060409080c1e0c010306140103050714070c03170a02060412030e0303010b131a250503030f090f0106180e010b0910060f0801121101020f0a060902 71
    0x1160821607103480d1441543d4212206540104600d182031074141e0490003032854010303991080f0b500e141c02c640044207060405866680c03d44440c1c02e880001181520601d02815034050300740002014a54030030340c00709900c0583e518182d0001c0c4211130714412a0741c0035080594a1111b1341c80248280030024080d51440150b03030202c20300c4d000c0c40e004040e44444004102030196001d1182007803946002c2d4000f540d42d000e4203c00d0340d90f20368455041c40d0381600003090000015000100c0400c0c50342c0000c0050920b510408900c03402e140101c3c0d035101600308419188400c0307948454414000030410009903002e01c030503510200b070b00c2c9041c4000c1403500b03500e1102060030340c0c1004010000c2842003c003020741150302f480b005c2420243c1c6500325014003505070019403c801b80302d0801c400d00100c415800e06880065a81034462440360700d0880700040c0030701a0541c0507646510324400651901d070708096541040c015600c03501031900c2070504040c15100180d480c3c9480791000411840c100d00a20000c44e0345e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 889644595 1250 889643345 889643369
    0x2010c030209030a0f051e0f0c0102010623220902012a0201050702041b080906010b0306010e060c010e1b031203040816110a030f060e0c0112110f03041b 67
    0x2d5800070741d45282c8180c3c09007039803081582803404e010041c043c0a4480d1541041011a81c205034072055480040381c1c1d4007100c501410105d220740c1d41c41030007000211600e804540744e80701501c0400b00e0b0311140c5294071960001c0002e521540c0c800c040300004c05a14454400041c041401e40000740c507124401000c806170b036002c4400001040203424003401c41507020b1038055102ca070540701240c01400550a01c041c0704414292000c0341c1503102040c0d503c1525000191541c599139149582c3c0c072400243c0e6034502207070b60a4601c4001c1d00f4600050031108140d42c00100f03101031b50f003c0590400d420503c1c4e5842c05507406405a00034101001080c81c4501010700c000e2851801e0f4903041c140e4003030802d54408460201e180641070260406144400807402030141c1c543c07580d079140c0325000d886509801c9a0440c1031015580d2a81e8003c21000c0c441501238440e8104420b820200500409a161421102900520039a44500e1000d80035522452240400e0741010801c004031901e0300c00541d0209030580706c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 889645845 1250 889644595 889644607
    0x30d081909080405191a0703090f1403100b09160302070c061218050c011809020415090e0f0109050c0f03011d0f040c090c090b0d1406060c03220f06050301030302010c0302 75
    0x30010744205c0c803040246c030f00e40f501c2d20b030302d0300d02155043e400d5404100070f0401048049508900007000341031802e0203d003102c40c00d10311000c228050300d80d1044540d502030707400b100041c0c40b1a20040d400300c45041a140040c42c050083d5298505201c07550400d000003480c00d20400d020344154806c0d2413482e80c10ba404100b290104d9030314550340d000031005680c1086107005c840180c00b0038020180c0040c110401d400d549a50b00c0301c940d9070000700349644c440c001440240b40003c00701c0c0c0c1550b0300c5020301c090354110300c0f03280e080c4801d0304003802001d080b6200324802001107001a003e260003950203032101000300a4817510340c9098003d00e40003d44210380800010051000144074240c4400854000b03500110b20135250f81070940d9400502d60082404010002c0d01c81501c44091b4000001010701c42c2d0402556103640d03007440000c1c06040202e042a031300421005c6d803504040041d594480078401c0083c070f0303280c4d210a0001e52140c069440380c80820300101c0140201364080c02075140c034039664a800c5007003503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 889647095 1250 889645845 889645859
    0xa020f030f03031303180305030a09051824030d05030f0906072a02040609050a14011203050702240d0b1f1107030219081b030d08190908040519 63
    0x4440a00964004013440c40400c04050090342010b8055105402d491000c40c2d036400c010340c0340e5000c0c0d410744000071402d41740851707980782501180100045440c48044241c1d6010035114000311480703035030f525030303c1041c07041a900d5030108041a40c0c50380940d1800d4507402d101881d05841e040c0640b21038050f070031103010096061b501000030307a1469000708040006480c0412440b440b5168400003a400900b40300001c80c0920554015600810700c8803000c12031142e80a800c4501c400c1c080c0101d0b000354410070300e414040f81c800c002030041280000c01c00341110101c45401003985010b01c410520205001c92100c14502443c42600c88458041e25803110f1114907080032084403501118000600c1207500e206000468200300410142d64050b140d1030006030703003500d100e0401d01d15214060061051082e64030300e40342d80b022491070143d0044c0003080c0c0241311034410f6a0002004085160607030707030394000c42c680780140e0080d0722905000d0041c095650b410b00007401010ba40c07003001b02103a1591508204020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 889648345 1250 889647095 889647097
    0x106080f0f120a051c050412090b0901030e160603050619030201050703080a180804050307060216030b0903071505010e0c0a020d050a030e10062105030a0f0e030f0a020f030f03 77
    0x12000c1154400e0380d0301e50000056030140115100140d000e100d2071240c0c651201c4603817011380101e0052392024812150030804550045460041a21491040c09514481d50094020940b414007070720079120340100a0b60454407440d5070b907000c2c1000139254001d05c8aa418085002500c3d412038a4442036150f08603000030301035201c1c6120003000c0105040014281e060144d000702e00440010003684081101c1c0e0400e038289400c5401414824000d400c030000d52140001140700305100f09612480c0c0b880d00d1505c54010200c001800107045003c1000b041001944103440ba140b80b40040c14001415418400b0240d107000c0010022964201c081020608241e00050510460f51041c0742081c0e9a50b101c01c0118042d0101d1040c01c00030340701d010034000d0100342c1500010300350360316500d91340c640d540a8580020720070702c0c0a4001c5c01d5a0410801c40e4459480340d0381d00c40700f00c2c2d1a03003070015264401c400132074070b803001e101e40080b401d40011400c007045181c60006e0010b072010440c010111610001d03030058a03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 889649595 1250 889648345 889648363
    0x6020708180d0c0b1b0a03021609140a1a0d0c080c010f020a12021c0c1502032a0906040915320f0301020427021201030201032c0106080f0f 61
    0x201c600070580e00c10007402040c078400118505800c0d94072906d910301e40a0340d64408006441a180900c0314041501d42d1307103121b241403c50a02c1c90f913030840e4403a00d807400020100718000d80c00e51007800c482c01c64240c03202d20311044014407500b03540455900c1d10605608108080300d1030350400403001d03c0314954a90000d0322000b05900500c0301460190b13980030517880e00740c00c1103640c08030780c1c4080303c4029855044011855643c2c000e4000800245011800324202d00c41128002407981e2038003180081c1101d14110545114829282240303402c0469000500c80c2e003007903010303014543d10b86000c0b0095110f0b041c00e000003410060021001394040035044080d074040d07038108101c8441040e80c5103903550748240c02b0201d0007101800031542c598450501000d550b245031000308440000d4000014450f0300780c401c0710440288800c540c540d036401d550044000c1d040342414525042e1111440981076050f003812101184205030002822038500359041d4149030b00906004026004a1160564401c0204080348 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 889650845 1250 889649595 889649609
    0x180d0c02060d0615030f0e01050c07150f0603061a040504170a050702090408030708090c03061503160b18040b1309022206030b0112230a06020708180d0c 67
    0xd00c61064035a02c800800719540b00f45441141e08107603014064060b4018040007070001c100b403065100505115081c2c940a03a00050018020490103010514045031000005010a8003154440030070040c41c087d500646c0050741e034a0765070000e200700b5541407060781c0c0600303605407001c1c0800c0c98943c445000c91000c540d2200c0c9020400030390680614030a0307048a040310360050400866080c9403e0007a45600102e545d000415034100c081180c541c0000f406002621008000f4142a036843e10a52441e4030311888054141c4210b0912101c0015903007800f0380a0100300c08260f44854203100c1901d4409182d1008034043d524215046010343c07078031251036948101c11071001c40c0b9181c1c544080f4003000564120400711010010007890001500d40118003228001c0d0252030300d590321b64031a0365882d1800600141350803005c140034000140c08103100101d81005400381c84c0e11160ba43c94840684c2d00a0300b04480c061070000d10f081e00c10402000c5104851015240c0080c004120703601d0300111999801108 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 889652095 1250 889650845 889650847
    0x1122c0d09140303090a091508280c0305060405210903071719050109030806040c0c1202030f0711100306080a030c0f061a1f301103180d0c0206 63
    0x90b059072410030407a48402005801001900d036500c1a09004003a006018010400348800c00a054000041c2e41d90050080c200c039150980c0304010728065141c01d002c001c40324920300f02000400b1605c18008a48902d000d82e0141107c080c0129100031140400b8111440060050054840f5078030005424025142885100704444882c0c003102490404e0146900d008100701051a004008064105445184c030a40301c1024036247c41c2e08000907551010070140c006044e051240d800b20710704948003c150859801541e141c400b442c01100210f074000c0358281d4070000c0f85946085c85003040c0d01c501000820382c0c5070401c0540d01380082103866204040300601000728901a07082440180440c02d10103c2d03208408004101101200c68400080c6110f8548100f0000500d00741005c0d91881d901c0034044240d03100c4141c0c1d4802d4540c4150405c04086400c0724084622000108002500c1070080c03214039000502d4a0740351910760740e000104020441869500241150144960000c1200883d907074110354072 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 889653345 1250 889652095 889652129
    0x3050603012715021902060105011b0807020d021504060206010b0a0203070318080703060c1d03030a0507030e13060806131e060e01050f150d02091501122c0d09 70
    0xc40c6040440d01603483c00d03840001c1e42011301c40c45480c400603d4046800380c1d2102da0781c0314015511544982d0480800c1250f01b042a000601000010807600d4402041030100d1015a004200d006600e034128452000700020240040e64040020703e00400c41800044e01e07000040100945034000c180c1c004040c04003400482c1c3e45112040158006891080112a03000da5641402005050345c03800c01c0c030101c1d143e0381010040c00d1060300c1048d1103190183c002c501d0b143e014002110654018003042e000c01510018030041a5640c14a140304424180c03c046035541c1402c0c201c03800d0034000b400a0081104015005000803800a5090801002c542c0721302c0c0f01250138101540980054140201c83e940707000b00700900e4081e410402030141c6013042d101d06100c00300c1030a0002c0c0c1904200e001e54051445000601040d0001600c0d10350300070185800c014060054504005844074812140200481c654000302142e180102d0380740d001c1d003024018111040740c41000790140f41c041c011340c2100c09001c007070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 889654595 1250 889653345 889653353
    0x20705122d071e21030c0c020d020603091014090609030c0a0b25090906091401090906090210020c091e1501050f040b1806030c0d0911100807030506030127 68
    0x21002101e0708134045400c098004202402c9102002c042e039804289016440a2028810710383d4120840d40640740c0d82000c0121740821841c0e400080580c0e0145c0301c5c4070240146042076008074003545010300c59040141c01c0c41860a418200d00801d02400c1d41c1c8207100800e0186400900f8401e070136004444045541c5034442d9000e0b1680f04c0c0d400c40500c0850242c0c1c400b081592010080048500d485002c00010351240007010694103912000c50001c24000018270044481e03520004c071082c0f00d50310008a807101a8045510f43c100000c0d07100140c0c116020641072400c2403140107603c0410088100402c80e1080d80b0054003020140c11040b0000c0380c3c1003803100d264082d1003143c10b0315101e8260a5181d69484028038483d0703101801c4140031b016581d0354104642882e1003968050343c4451402420080e00c008010000c000c0f01000390349034035503c00314440780c0c0c9840d4180101d00304070381e0f1344000740d20701004040c06030352000d0303d042d000360f00d80b440d42802c0342e40b1400410a180842081d1420f84111828 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 889655845 1250 889654595 889654643
    0x9091a07081014060d090503070303060b03060a030312020702151206090112030323090d021005280209060423030f031c02071b03030909110319020705122d07 69
    0x1a10545841c5401b080400b40100007014101161003540d040c0702c0381d5124044c80c5d2241c041a260350340c00074900e00c02440000d0086004c0421040c40140041c02c009840d0001307250202524a2008880f1000800c50320761280360740f4442d40104240d811510551400540506102c901140901010381d504108401c03200003240c88055205124005103181c03e103111607a4541d50307400f901001600c07039009a0020000f1500801c0e118003500c00720340030341014006894001807a442040d44c0c240c0c0c3d003041011059074507607003d08003400800c640022080030070454503100b802c0d8941103d02c0395200031007120030b807140003003112051003030105181c141c4402c600d0480080d00505000400d070a19903601d0403507151001140e002224082d59070008a103079030b2000142220070440c1149240c010820015416626010b000720200ba8064001850901d0300c0e00e41038104203c0741090704400c0c40008245203e54040c59230581f80001c004c100341001007203c014405603208035030700101504440c1000715041c1c5040c40c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 889657095 1250 889655845 889655857
    0xe10090f060608011a15030411010504080d200c130b060909160f1b08030705120a0902010306061706090433140402062209091a0708101406 61
    0x10074144215501e40c2107242c0a04a0080e0a0802000c0308a000109103003031545d03c40c10700c5401e141030b481d58445890709401f41c03101030001030510404100000c2c140404004603443d40119031380b400fa48204404640c0c0411201d401c15402c1da0f440942503c401b990b40515400c21112201c10000303503040301102040150040611a952001546041104882d44400f1116100c1c0d070642d1088951150380c1401d81d9150303c504513411041c019009010005007642006541001040c181141007200c0c076601c0804c204422100000c6880d12050761108558040c0142000f4010301d007090f404131040486652281d03031000b0081881f40014202007814400d95003c3e9174900c43c400700c141810000c052090351000909060803802d00d500c0c00d5900198414141c03c014019580240b0341840d00003e590610b5650040a82110004519520000d00000c89101c5d80414520911420700088404d220290b5480030050aa00a0085080c200504000095400c0c0c007076902d6200030075104810307180455a140112 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 889658345 1250 889657095 889657103
    0x5180102010e0a05011b09080d0804020609060301030303150b040803252f0a0302010503010e040204060906060e0a080d02120c1002130519031110020f03030a1b030e10090f 75
    0x48503c0501c40113400004401100300c0b596a01c4c041980400c03100120507215178010b41c0c00c42200c03001703003a02c40c969840c0c10034002004030f4200915100000d41c90f40c4207900813004640d4418000321401d100181c080010b01528060034142850301c540c60307440b4418504001070b64911425031040382d05068503260038968000e041e4071240100000401842010b0152068180381c1991820b107031480d066560a00f034a0741a594141564600070607281c0001018000b240c1c480d48a00000c520400b0b03501c600401804180d40c0c032a203485a440a000c041d83c0240c008072010340111300a124100e40000b008906525095011030f504c6008000043c2021150460315084d18000500501148070311003119003552000c850212181c0e1400b00316031100e80c51840001d0980d41511414845464950480602d0b05464010340300541e0070504d130142558000c40340c0380b804a50b00d4111001c16001c1003844211000c00782400c00c190414901d405036200303151660600806d464840a10800240780904400c03d584 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 889659595 1250 889658345 889658353
    0x15040c18060206060a080a0203071a0c101d15060f06190302090f24131d1e01030309270203090c04180206040e0a1103040302060402030c0a050105180102010e 69
    0x90340d01c02501c03604207a461a100e1001100702182c201030200380c510f026a8020003c01140f443c0914909003840d4116071403030083c60500a1004221060080d0328804254550001d1030851201810b111072400449598140e0711000002c4d100c40e40080d083c07504640200c82e80340b8a510408001071840c414200ea00031003100d03640d1a009540d815402030f240488048484001b00c04016003803202e5100c4a4400f210811542864000314081d000024204400d1800041e00c003a9100c5050055465410828442c04448802003006404079091405105441803070401029451034500902484e00350103030324032064040303070f00c01c107400798220303500c0282c8a804005540340d182040b000340e00e52298100d41c40c0a14240286c0341009001c0d5114510300c50340c010f103424201390034005c00c001100782c010450f11805542c0d00c048092040d41401452290b4480d5008010070f02e010f2050504000019407880d005000140040c0002d03a000000e0700c11819030720301101b501c450804d0040b405082185450007207401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 889660845 1250 889659595 889659599
    0x11032403030408070e0106050307050a0e060f22080105060a090c1218020102070906080712080403020307030807120e01080c0304051c0c03090b07050c0603040c05060d020c1515040c18 80
    0x800403507180100d0f403005d80010080da98034103050311944000c503010f40c00a90100160f00340e060145840b41400700020380321034105041045158082e6100440d403104001030400c4c141f60040d01c08640c00c000d42074501c000c0c0000c0c20a4804902a00c0b2036008180e0030740e45410803000035510900680c80c0d040100e60080c08000d01c03c0003013050300110f900040c0e006000d545408182c441841c00b030b2904550740305000300031491a0030021500311418190403074942504010000141c1e508114482c080d50103980b486644091601d131006031101c2c9150450144406007020304c03985c1e80c2002040380d0094020221030b680380e45a280640c20206803103400410381c0c4a021038071120319880302d22000300500c603071181c0720440c0d19003199880354003881c14000e1890b0b20020108003d402e002e40070f941c1003449022440959500c0704001146030b0400e501d40704200384e0101e02c6820103041007048010f414038100c40308160303041000c1419640b0f6150301900303018586490415910b1403044007004c4600481c0c05482081a0f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 889662095 1250 889660845 889660859
    0x2d0e012318030f060609061011030c1c09030b0a051f060e04060609050a05061315170f060d02090601140f03060f0603250c060207050c13110324030304 66
    0x100c1c9500c00750281c4554400080200c0c40043c1e01c0c0d0051030000d18225503a9190030070480048601e07102282000b00d500d41c4044408020409031180e0380103030001d07018400cac4181d450500c07441003007034800070480d154800f0800310321603802141d084042c240700412075607a00d40074042011103960002c0043e0a02c1e07980001d0082c0d00c40340803491204100e400384943c90f40c904003282c03440080c0c0034050b84542200420805850300e0401488502241ca0020100e40c1d030f070300e5445c1c00d61620354004030302286090384c1c0303861242c8017204110b0340003900c800d0305901030620304c0c00300301d03281240c0800a010b141a840800d4140e800360859042010102544a517661f03203180403120a40c01c00d840890041003401209051442c0403c00d0b82c0c401c2c0e100d0181d40e016030808000e0034009140448614091005400c072030b2012405500003041e03140c3c0110b000b020030256420074441d150b80d2685011160071301d4a005e80b400b85071142d048030b4000001d030075107011300507041c51032400300040c1c400e43c0c17645840700290004a0f4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 889663345 1250 889662095 889662127
    0x360d03060306151805060414010b07030305071b1101050d1112060a031e020103200c0c01090f03022709060106110d05090405040c030209072d0e0123 65
    0x500d02c90b0380c0520800320581e24041011400303000b514144600038081da2150802030b404a540144028004242c1403043c1c50543d401c401e080c0c1044400010010361001450b406010300e03a04020140381c00385c00b100310000c5c02c24208070b28440080c186c5a0503669040268843c000365450001543c3c8200a541d0748217501d1046035015a245074401c03101341d030000b0011318100600000700d03900204200110032524220412a01c54894201e0500d40d403a4249100116401866000a20400d0b444e40d55040e000007618030341180c4102c0141001181c941c20300648110b039900c00c04a81d4142c0f0300043d04006e0700180c2c880800c1045034620960103003802c00070700c0b22000880034101c030307465140c0c01080742c4860450b0351214001e03e10140807807010814030b1100c2c1081d038032840c1c0c03140c090400c02061a86940c00100141e40a4555000141010f001c040040c0d546140f001d0818003c04250003203450040006080d0f0742c035421009041c40a07840c6040300005a50b40441403081f80070f0100c42ea00d002040800c0c03a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 889664595 1250 889663345 889663349
    0x18190c08070303020a1401232403120c1011130603020909060d0f0b0906090c0a030203100e10020a120605181b0705030d0b01080f360d0306 61
    0x1a14a001401200114518040e2505a0301602c1c0c20a81d945034031031000454940d4180d40c0d0742e0b58a0300b4480b89000a030405c01044100080d071310038200180740070603c200000b442c25100c640710102800a6a0003d2900c9410060a403880d86882e070382d00074241029452040e01c25003600f0502c810b1810b0400000401e224071900506034101d03511001c045003280100141a90081c0b5000045801443c02c0c0c0116881c544c400c29200843c4c00803641c910402003004c1d284410389501c008203000607040306100008901605035030412500340342d40c002070b6903407514042c6010050707070754201195030a805104084007524181c0f81990b80ea800e00b00020001144261549c0c14940742040c08201344c54441c9801080b80c200c440460742c03980390240b925550406a030146c025005040140e000051070501c0a80b200e1180050b0004101501c03900142400d41c00401c4d0036065203030003080000580c0356154211008031802c0054160075030200070601d4080941c0b007070f900343d4441e40d841c81124607419003100003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 889665845 1250 889664595 889664603
    0x50421090e1b0f0a0c02031c0507060b0d0c0611060a0c1e0905130501090c02060601020613030e0604080d0e061e0708040b0301030c08010e0303100e1819 67
    0x85041510201150100958060750715040765090100b14001001240300b0b03101920403800914100d0400781c0300d10f02d64880004d1501040400051600798903080c030070007105d15501d44e0480342c16090404c00400d0b604c80c07004014003590752041c1030340301030321003440f41a00c0582c05900c00c9441ca459007000751003c203094001000c01e2140e00001800003881e405003051007409070315100890b103201c4102c562900d0300001c684041104014000034982d50781c0304522007000810b1000142541071107100c40a8800c1c25000354255403102083c440d090341c2c0050490780c0800c060522507082d0350b85103001c50fa698600d6290640c041004980414020408140440e0541e1300d600e0301d000c00a01a000d01c00305000700140c80341d0141201e2803da8000178544001d0404178450840189001d4032030b485610741d5082032f0010b882c1001c03584418004148240300745200581c801c8001d60440c41d24001d5085100010f0140c001c0384410b510104811440c1d2000c1103402e2218841030ba00b0080700012047c550403815402a1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 889667095 1250 889665845 889665893
    0x7060e0f150a0c1e170c04050108060409030c170c12040503011812050a020f0106121505040809060a0203070501060e16091a0c2a040b030303060918010902040504 71
    0x580b004603512820030401281e895207840301400b004105102c0b200200c4a80a0180c072000003400c0000505125200f440d28010558940c2d0030320000401740c03035008000354002d80c40c0c01001000310340c01482c0424100d034003481c90783c0741e0707042007109004074007030808040e00350300c40c002948403210080340c0907000340e078004c1d80208001042d119000b440745002042c05410005d0300240703c1711251141c4002c0007a0900d5004644614801c50910f030300b100d0440d80300388006910103030200100410355140078030800802005100504298441000610980029900c10000004e504240a00a106860100d03030424020018a50355948800c0380c1030f8203c40d01b500c00c3c0c204484100045001c1d412440c22b40d02d008621040941c00c1000408180c2d00c01d500f094024499041002450712008840149010702c50040f20010740c8928140b2081d101b11007081407007a0403d100304001d0362260004998807000440c00d030441c01000c618070600524400801a4005041c58100400e200c007001711810b1008400c1241 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 889668345 1250 889667095 889667101
    0xf130b040308091201022a0708060103050a140d0e010c1e0c031712041103030c070602150a0c020a0b04170708120f0f041b17010903030b030609100207060e0f15 70
    0x1360300301c0c0b0a14072801f00d60302400100900e08401140c22868040c4001c045a03107d40d01c0d00c01080c9801c00c00d83c42120700b548810310701800c0003280062000801d810700f000304501e00c00f00718081d120712080e00c6194100300301c015250040c0407002d1910700c100400b1084145000b00d25041164091085010603198070011000d030349090000d05c4201c07444010a101000343d2a02c0e155144c0c41509036540c078083e4588018048007503522380500c2441c000b000203800401554150003c2641041c00052246002e540b0f800040c40300c00740c0118a040005602000f100c1480d0742d18540780202c0c0041302c2058024007000300f84c032410008050300034150041034071044509643d60a00c0040c01e86001c844500c0d000164030085000203515605003000c45142c007a02d516030710b0311a00c031100e00039140142c99840b83e46820003c420b2681611035611103880030350141070140303001d107501035907607a000e074400c40702c1d07540062401d0607c4516404601c004080405490510b0130400c5203aa0741e488030349a94642410300004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 889669595 1250 889668345 889668379
    0xc030d0c0f1409130b032e0b0a06120f090501020d090221030f16060c08010e0f0c04051002070905070504170a111011060c03070f03050603030f130b04030809 69
    0x41c1c50360b01c0001060640f45107280144400500b05020314541c0511803400c0d40c55008811140c0c10560481f9070092490916500c0411710035600c443d24030030b019440603501484465401200035101c500b1050000c5181030038041000000c1160040143c090351020640101a580941103094554000c03206615403501207141e05c80b1030b031080f1907008400c0c0c3c0b0411559804506800207040081d841549008001400e505d42d0019580e0a80510000883c0c0000500906404080d0349400c030340712804c0d00820340350000200020f0302c075901410348030f80519195444414030030042c141c0941006ea00600139400c0294002c0c140c0c0d0000d01070703500681c0b043c58224402490002c3c42284541d007000bc0d22644015802c240200e00301203c00c50001c00454900300141014200304490007118000c42156030b900c0e0841e80200f041c1045400c2c54100b6040400340401070350000241c62186000700030143d03446600001c100102c1e89940d0100c18110f1000c41c0000500c0721242c064071840c0804c0d540c0354451015040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 889670845 1250 889669595 889669597
    0x7031806110c1203040e073f02090f040e03040b0d0c03050c0a020a0803060a0e090601031103070f0b03250804020415050108070c0c0815061009030f080c030d0c0f14 72
    0x1602d6441d510500040051580010710503402080e03604090030f0701c8616000303612110709490720700c0300459640c81c8d1140311011248602c80851121030411404c0803510701c0010300200e0800002c80c0300c1c64541c02c4102c070490040c0115401030490724910f81da03500c2e10081c1e42c13024241d04203048020910b0080018402e41200c0c04a98000b809603010705905c118559501c44107810142070103400003440c5c2c201041e8840003405440c003d00502d001480780e5031541c648000080c0000007502c1c000c3d002034008125a007010f10b881c10540b080720401e02e460380e07076151a190140c0da42d07240d6885240d010181995107540c12105130307405035000f03440601485140d030030780540e002014450a8002032101c0005540c00c0e10580e80424134620500e2803040c01075030f6402141c0741a503401180290389040b403007072041c40d26115904015800440c18400d01162071900e411903000c1e036240015100d05800100346111160900450b030019256200400c90003440140040c02c1c4222040c0c40ca0100e0304101c025494000200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 889672095 1250 889670845 889670869
    0x3f01051803030f040b070306090908092d091b03010f060806090f060f0102011508071e0303080718031704060305100f060c0204110f1c18030507031806110c 68
    0x1d1a0f0901075290740c1c1e10344905036001022401059514403001c22445218014002c58134002d0504580b075045c5a4200022034000c0545400c482e104540c506030410340b4070358180601c0b90102ca8030546513440849400200d513440d810044030742400400412502108540d001c143c3e45160350381041c3c2d0381c0b40d900b4840044410f80340e54080b1410640004c0c1240b0b0560b10070b402402c0184000b107888442100342555140040e0490107068000480600c181c1066034442e403408501075032802d80b0249951030140c40d844026010104011a0490030100c10340c0881d09040115403200441800701c8440c1c15241c01c5400500a9000003030401020031400740c0d400d17000000352500151541e000c240b8000701503920000c07000c012a005921201166055030f000c6029007807104203119800e0362031000c80d0500b41818100c00b21030301d00502d03200581003003200c040307415240c00f42d00d17080150340c071081401c0584039518050b02da050302109020740441c00c541d0010001c02000201c004944d51400c4490400c101e01c4528 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 889673345 1250 889672095 889672111
    0x11030a0c020f0613060e030c0307050901120206190903140c150c011e0506030d020d05030a02090a210b070c0305160c050d050d120204053f0105180303 66
    0x10304040d0054030b08901c0361001e90740024031071460701041450340d59508045070301c40c1022a0210310195100d0400744083d00309450110041c00c2c2550621000868459040c0030f004410411541d412045440d85022204107080c0c450039030b405031600910042800070305010460b218000c2d84d10321814800005117451041c0401400d441980850984840d4141c1041202c418a036482d03107807801052000000d02d0301c1c071403e852004113461815105051030000c011542c14119408a21030203d0a036016090303039040302d01d000c80584da40402070001211541e072500304a00604007050b441308043e55070307801e05011030310902064540c0e0381c82c4142620500b040100c040d001c9041000240d448204c000c1c0c00014a44c4100ac1d003110391074691010804060344103a0803100c1e5488400c1c0f1880158105441121070800b201003985011308100200d08074540401c100c9a4280862002d00020b0050b0050314000700ca83c0c0d0a00060300c900a0340e1203020b01030507075400c1c0b98003054101c112800740022040f01d01c07030f40720 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 889674595 1250 889673345 889673357
    0x70e070c1707060b060903030a11030d15140a2907021c060b060a0e040905030706060e090709051006110705031b0910030302121e070b010810091113060b0c070611030a 73
    0x15241700b13894400500d2b00807602c5d40000c02c0651940443c510802264504070180901c001c0e0400c5200883c1c0c9101000e01449182503c10420440703481000d0204912082c0040400d225040b00c000304041c024014001e6001220382600c512051080c254a001140039000510003d40c0e030740d007072050521a116241c00003403e00c82c003059090415810800c08988079030112403034461261144400c440ca03070741000020440080a015582030100a050094081408100301c0d07400c1011100203010803d124200c103001c1d40845c0485040002d0290700c0082c00040c054514502c1081549281389581581c8640300d0102c8402088140c0d52001044050b26030580041c8200d1215400380c1c1c0700750f0842c2405d8a0f4448c04040c1d040c500707580032009003030910710901c5808000d50400070b01c00d0030b1070030030103c3c116114603003080003011900004964280000644000543d450101002d0001d007185420107444d2540000b0f84419074680018000111403090769610280e101d49840280c0b41e115483c180f60009035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 889675845 1250 889674595 889674607
    0xf0509131e090c1e03080a0224060f0904020105130b03060a0602010b0a09050c070807050619181202010e0115050108131104111207121b02070e070c1707060b06090303 73
    0x1600e40000c01e11114440c0c0b52904207a490781d6040a42c1d11000c40300005030002d03e09240c554010703a0302c520004907279502d51480d9282c804c0116002121443e5121311424022000c5801d59000341c0488500d8211800c07280c00068840054200c46d50082d200c150040c214094009252403041c42400903c00c0018500410f49150240000140501030718a441c40340c400c104440018000100620000d84500050b0a1074905010030761362214210050905a50400e0f24903000480148a00030525a00c401a013002c40785100301207004140800c92003415600c0e00c0c0e0103809420070202010704491099071020601c1e6103604a4204050503848010306010920b84140030920b401d0700982c00d021108194130b0f0070b190503a8014012180107803248004110041c00044841c4414010003414140c10700426801c5032030702031700a5803005584500100100d00d40003040c2c00c2d510a04e01000000d4008400c0d10360b8414240941c80e072540220390031070303034503103410210043c50a000c01035411a01c0002e0240d82061 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 889677095 1250 889675845 889675859
    0xf0902040b0d0b060910022103040f201503090d020102120103060b1306350c090603070e040506070801050a050604050105160b010b0d0b06070b0105010f0509131e090c 73
    0x44800f20000f41d0001d42031004c0f0900ea00c5803180d142034840d483d401040106e01c420301c0414281403242c490b00180f5010802c2001280d01200718042056000050741035011100c0f11619000001208251388080c200800c949864007000146028140d107509643c2505c1682c6010f034200c0c82071007100403090543c0300041001c100070307612118101e8400391070285105078001001e403c54103035810411103407048440070510213018691b50010341c200c1c2d09840c00c00000554406580d0f000030001140f040b81c4000000e00603480500211006041c00510340e081c50919150454964108403032203000100003000000c3c851408280c09000c48a0190155107058200070044840c1d40c001000b203114840c43c410300c000090702983c40c2c079000b0410900e1403902d44505124010650b44c803000b400c1c2c4162418003034000800d810504041c11110242444090401b0940003941c041c050500c1080e40807111000382d40a03035909400072000c20701d400c4c06c0507410582c14000c150440e0000b1801501080e06142c0c188a10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 889678345 1250 889677095 889677101
    0xe0103030c05070305030d0504050c0a05030c120106030501050405030702100912060903030e0616020d05030c030c0307020a060203041a0121082a1b011704021e04090303060f0902040b0d 81
    0x128082d506803209103850f078541a24541c4105a03501f4559a1a03040000303104003440043d00c0c403901114084041440c200010307a5400c04110128802e0240c02601c2c543d081c2d00358001f40042d6030080c001d00a0b03280a04006859801c18030099000e50243c00300300d100c80780f080f040c0d0000d65070110802c40b183c804940302c84c8010b02c18a1811000d055032088480c00020081241500c075282502088801204104000703040a10300c400300424030030300340140840a042c00f0140d80d8081d40142180c1d13205c0e95400d008a02d8000c480c6c4e00540118400800c0c4414481e0402982c0c205403254581e110340c0340d030395001d440078203461821400d810340900e4035894000350001004101450008001c4010080d00c0d2121041e1038481040c0d02003076520011070851440021982101190303801d090000f10300283e010070420071400204020300c5001c0c0f01d0440d40c01c010710b00028810f8008090010013010906d49000303402080380c6e01440694103a520400102c2c40424002ca8055440850415003012200030b034039009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 889679595 1250 889678345 889678367
    0x120c122806060f08100506010e04050f0a0606140304120c0b0109020306040c05041404051f0603050103110f060d0509030708030c09040e0d05160503040e100f09020a050f0904060b041d060303040e010303 88
    0x1008000b049100558ad520f000d824000c20341c400c1c00300e90a0424410381c00440c0c0d136940c012000d100c004079010b0906010041942d074405e401001c0b2480c1d08810145c22203049804000c000c00c854452400800c550625501940c8519015203003000032001c44503054949020b41c1c130450500241c449c06a43c0c150a103904140d0f0404404009d030303040702009200460b0b42840c1074000b040025920740040051051a0300300082c20341c030075540c0b61b40c0d0842d1071000c50342d54030408000c1c2180c0781d154400301e41502000c02c111036019810000c0b95449040503410302869902900c0018841c0c0d044c60315400c50851b000c21003132028816504d4440ca00040715070220a80c6480300000e4815010038400010403500c20100c03184160030b0502c4048d85039003016a80c13089038515070003172015584148200c6204680140032034244081103040c060311500c070680001e02401c2a60040c0b044003801160004074203080020780010040000d01c0f54040b56500014550b40b40194482c61944640c50801000468018014041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 889680845 1250 889679595 889679597
    0x50a03020409020f270f0c09150408010615022109040e0309090a02040501081509010605091c050313061b0201050313050f0d0e120c122806060f0810050601 68
    0x80303040480000346014104003151700d60b07001d190140d80c1c4003061035891294004509501c00415080c0403d078051140140400c0500549042c074140b51400300c52016100204401d10081c80040c0d00c40c80761a90314840d0715034680143c0318203960380d07010400b40d00c410703204003020009441c03c0c4040c00c0b040102a11804409c84108e0008015001aa48030075024500c117500341c01c000346c3c1d150f1910700010502d0350f00034400c0310082c136812801070b216600d01c4185811902c030b5141c940e40754010f03000000c15020041306101c0003148000e180c00200300002c400391180c81d2011840518490341d0b18004d03125070500580b040c003201d002c0d000d41001136029a0145401008584415140d10010b41d41d840c94508070400b5203440d40e202c0030700e14400c1070b440ba14400c038800381525042d0314204407044507642c0d6101d00207054070850380c40240a134000c42c2008000c02100062480e03180801048041d500004602001940c5450925001145c280c004154410440c0c0040e002031222520b05081c550040c41d000d0030242c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 889682095 1250 889680845 889680859
    0x31b0c150d111b0c03120306010f1b050a0b0c072102210c010605180f1b0d151d0a0c170a02031510020703030c0503130e0a15050a0302040902 62
    0x84420582c0754007030246001800c03000b0254619106a8600c0c10b031405126a1095015440b070202082540c1d05903604800d00382801d44c5c1711540403805450102c120725000f81034410f8446820705000001904d503000134018104040e403500d40e100541220712901202406840f19401507560900311090603040649030361047e03910020b100500480b8082050018010144000c41c0d902901d0100307201d4480240390445031140d04001051110585030401441030f003080601b00005404d0329901d84015120485125207946c0d242000142c90000b8812039240380302e0401d140c034010032a035002c0d12f2a411448020f0340c0c02900c958559a0030300140c086049207208002c1c4000e0780c0c21031440d014807038a006989442000d1b880e031400c4581081c0b0048a036603194810000740c5104403d0039004180311050b203405203030442c44d017109070520a19611860600003414000c24100140241514030080d004441e1104140143c4610134503401d02981d45000381a1b10008840303041006113000e03400001007a06c060058 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 889683345 1250 889682095 889682111
    0x2190c0509070504030b010902070c3507063e0106150c0203010c030614130209030f2107030212220f1d090a1e050f031b0c150d 56
    0x10441a00742610114045040801c0510402c51501c9103a805445021421410030000d9203400d00100610312525000c641c1107508440801d00d01003000044545c0600d00e8582c2c0c8003101500c943e80d903030b030780304940015401400410f61002d0204000d21410490309091800d1025406846101c0e0581d0007940020343d0388002c00184a40e6013141c003214030050362201c01d00c019050040c142501c8000250a0400d440c29000b4001c0c4110710070307042c94624059400d203c154a250819500a214109016074103119010101d000d4660000790181d07680c2003180d03407207000300ca404010030403409107520090158100d016144102060344020300400d205a80011541d4002c00c0410b0800d452560420164454a0b65091041c107442d00c54140c112010240e4804482c50011102d80d240c41100000504280c84207154500c0c0c9000000845951130f088800c0e11100b02e40032001a0fa00d0344108403284940070120080b188242e000306541100200103402e500c185402e21054100790b520a80102c1542a0b40c0c00403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 889684595 1250 889683345 889683349
    0x1021b041d0709060f0e251218032303060121090501050907080d0c0b1f060203030603060f07021e100c02011505100203071509060504050c0108060a0602190c05 70
    0x31076002003a03d01000a812418658031100300500703031b080507001c01003600605c14022001c42203440d00000c0c00d61801c0807240480c0d011034041d1f2200c02e2003e00700d404e0900101c125035500541c01c5d0103901c41d0300c0713006103042181100001c404c0805071409524905000040c40c65002c0c084054108140e0a09884030081c0619420119401c0500c182ca0aa56680420004c408100501005040580014080884001c00003044001365a00080c1200081c102040d0340015940e601c140c1101401c0810700442c0e01c80e200250740340c1044580d50b1182c841d140101c4ea1200e112182d09004141960140040781c01e200f1301d01103260480045903005101c4e060558594584521914000d1019a030010400c400280040c2c4241e1010b50486032103000b0348210310a400d5000011111001d9000b03009460141400015000030210108050403080c01d0604010400c00c0120715000c00d41400d88030343d201c588555051090399900d60294501591148504030000c21182c0d100c000355500c1515410403994840300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 889685845 1250 889684595 889684603
    0x2010b06030c070b010e090a030e06210a060e190b0d061a0901080601081c0c050304260c0a090e16080706111203010501050a050c060711070501021b041d 67
    0xb6030010342c440302140802c10484c03000c06042c01409140b20302c007094200020707100d0b1141c40c0400003e00b0b00001d01214a03064582c03805a801c00703081c3d0400c107402180e14030030090404808544864000b85000e402090101e4000d4805001d02c8010040b00c910b80d0800c02c4d15802400c24010480d0b0141911901c2000100e0b2801412240142144643c00d0740100f0010b1100d5000107030800d128a411440c014004003200003240282a06070048010810b80690301c251030000d1a2503018002d80800a404615071201156486002c0090801104250349540b50b141c1c585592201e5180d11101c2c0003020030103038903d500080c805a0300501942c0d040e55600c04603110010042e030200300542c0080a0820115801901201d240601c40c009426481d8440102c01c006100500581e814040c001c100d00704080e03c105c00382c03040c0362a010b00700da103075003844000a09440510340000103a4401c110020589520109180c07940c940d91f08600031108032000d0410004c0c02c00340c80f40c0c1c602d48401307000038400d4101c100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 889687095 1250 889685845 889685851
    0xa031107060608030406020c09130f03051b1c0c03080411041806062d05090a0608010c0206041203020a080c0711090a02030702071203020d0809071e0f051507060c02010b0603 76
    0x10f40150740d110324004010b030501d03030300303d42140c03180710300c0b104200312000090746450700f003544008950070f184001d150540341070040840662618140700203507410240001200e070342041e08042e81c501e8101511008558490b58824002c0c005204200400c3c00030300440503107050004000c202158440300981d41c20f41c800c1e100001558821346a42d400c0091400c0c0e820031100310940c4443c1080c038421034800c41d002c424410300c600350061300c5100000300e41c0091a40020040c1007140020b100010b00c6110083d903603d0255002c0e1004a005031710700f5201e41c042c1c422180b00c0041900c030881e4941e81d000020405800c04241030344e14250024130340301503603078841c4400e11510303210f01d00688900b02140024030700800d5800c94034458020080c2c100100e40c0018500d100c0318080c1c545a03400f580c3e1001c3c0c55042103401c0d4030052690080500d0842034211f50203000c400d498001e03201e40d03101940c45041001081c07691807510700040d020061000419038a821580b041c2080d030001080b1184c0a8011420360341c012 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 889688345 1250 889687095 889687109
    0x414090a170409140a060614040b0a0512090d1419030b0f040c0504030c0e0103082505191506060c17070b040309150806030c040e01060b07050105010e070309080a0311070606 76
    0x180c0b0030031034485124410700029001c01c2c50410103001c0d2344410070f10300b0f11650140e10f40d83c080104405a0395841102102d43c1d103000003c0180c050b040c8410031076512034030b01c0103802c0843c8a141024200d0000001603400000100868810710030801c17000f6001001c00100180d0840086101c0c42483e494a0040c054a0506079030f03400d698924504001d059202150000480602c00700010008078944c00e0a4540030303070308203a00100d501a2031030711540b481590b0b100141207000300100c21200403015260002598010980300c00c40e0940c5100913000c0302c02d03900400300880c000c000c1580118401801c070313802003e41083d0407840d00203181c032204442d6200b214201d0000715000c20078850079001081501e418841403c10244a08010f40000d49038a9104000ea010b41d070380d481041d084460035008000105801411700b03503100001d081ca503001e40303401d00070801d050441e0404504914440d200d01d04030103801841460402004030000c0b40034144510201131b0a400500042d0b001c2410351154000610745 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 889689595 1250 889688345 889688381
    0xe0f0601152003030c16020d05011d190f0c0812130506070c0306050903090618040e07030f030513170106081b06040b030403050412030e0414090a170409 67
    0x7405500400340d44034150990254001c064000b00c02620001c19130b60402a0710141315151500860802c650f0700d004d52003e0740c008080900c0c0c5040c0300c0190702000340702904d180e0410b0741081e61417600b9690305800400303000c0e640ea04140362000c5412038108001f482d1003507800c0e0084036030f9000c149260503042680700305c20700c400140d9500c80d007541d0203c080040600b615030604041c5180c0380ea0003081400d1201900c01600e9800141d0301d44e80034401c5030b698142c001c020b203445402003100c0b9114030100c4918540520720780b20300d006800600140200449901400501c06580260350485040c2c12158524201d02c2c2c1a90700403429900c002071103000300c41d2000c0009940b510349450756207030001c1d52070740700d0719030380140003456107611480111400d03520309040c1c540d901c0e00c0f185400c8800d48200c2c0c3c480300020492480c01c0741011343c41005140c001038102c070140715100075800101c1c2c0180d0141c61000d46907000782505000107003600301d0091391070034604ca140d080964442c1c0b21401e4500f0f544002e0740750b0003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 889690845 1250 889689595 889689629
    0x3090d0c0807060f0e010f0201020f0d02070b06030c130e1e1c091a071b06081f060503130201090b190914010c08180607060912080f0a0e0f0601 63
    0x4401c100c0d07078004101c3c44ca0148042568010042e00c0c44806450320703810421444100d604890007501210111201a41c82682e81c1321a81000c030001c0d041808111825080500455614580086c0d15145800000c0c0944050090f0a006030000c080306280e20419000c0c2c2100b8110400d8030204e666502d05000c00540010a644c0180001d0668a0300d105001e00c0311012050103016000301c0c6003040a00c001c601c0c55a03c084500f003415034030201101c1c034061f01e6506080070407131542c4103a20500840f44240300c81d120b8003c0c050218420001070180c00006401030001500b403519a0310400061030041c100700b01c0341500c0c0c150700800380e48200500c01e41c4500348401c5a1100c1d61200120340140300c0050090310381c0c0d8010000800703a00c0d050340098802d203804500c01010607030f480142c55031000700405d0169038030704a1600e03c001d091558029101c450300d1100210b54240912203040c0b1810744881810100d40d151007414004107496141807000388984007046404200410006020300b005012501c0207007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 889692095 1250 889690845 889690859
    0x2a0201050717010b09060d05010626150603060609031c020d09031a0403120510030308060d0c210f05011a0d0c0303050f2505011d030f0c03090d0c 64
    0x540040c0c01e0404001903841640034142c0400c0a107819210981201c95461480d2400201c0e176016085031204079034584000015060f80290302c4507200980c44c500358951001d43c502100c0c00800c201c0c0c48811004c1c030000d40c807a10f40f50200055a00000c028802070031320001401003032070545002040c1d0070300c850800301320186e15010402e424202c80f107850800072203411540c1d441020b06402c50300c8a915614140400d00305805140351040c101c1680344100310900d011145001d60020324030045e004a142400400c0e414203040e40310845071030b0485091003a503407400e0300c45020400d20f5599643c0c40d02c0c10128041c001407200c0401c0410034004c00001c81d180460f10761501c5513080224209202c1e40c0581e044400081105d040d90b411203400d0304242e520340079100d0003000036100d034030007907144096890f8840300c4c51440940750b0303100a4000d5008001d00e20103c3e0085003540d81c4901d03c040c06230300c18050310950741c131900f006049074400c803000c1e03e0400070b00c040840c003400095441141c3d94100840c09010b02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 889693345 1250 889692095 889692101
    0x12080f180112060302031f0204031a010e0f01050d170f070b010302130603050a060e1c11060a0203190f0204030204050f0403020609030f0307030c0e0918070518070507062a0201 77
    0x88000480c0c100f09403451980000c0d6600259012142c0310000d500780504a140242d05032170041d0380000c001e001c032181204844110603800d010fa104e26100003804030700306040902403c0c0c1602d4003d40401c844002d50385841802d0900444007240e200401c100448048034514050202c66120310f11180b0365505510400c24126103203e0341c042071601c1d100c0108003103040094100802c94000c8c10010b900800c0c3d110707646c100304003400f110b03030038061000a15103000c0d84401c1c061040f483e003006540d11038803032040c040c045c1d22050b1800d060700f81038040c0c0000003070041e81c02405107022040c001442c080c0e8941c04101980e80843d45445100c2480080101b495018044103500030042e00245140500d66580075000b80406003a410400d907554880c000218010100b40320031030341c000d110211074642581d800c1265450354900c26894064014002100c0c1001d00400c01c000070030034010200c0c0e580d18102190203030811780c02030320320765142c0d807500b0342031207146084078450281c0303801c51703510608100c0000c0d0079 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 889694595 1250 889693345 889693367
    0x501030317040f2f04150b0d020d0c2a03020709020c0114040303021209070e1b0c0a1127010312120f060e0705030421020f01060e060f03030f0412080f1801 68
    0x6076090007115280341b640c2c40a0001551071a450441c0c551944424400027402440e0380c481d8041e180c41d80003500c0c160440d241001c85200d506900f46601000318410620b42010040103015a20000e07081c024103d030b80d0082c0805002440000960145024644880c1401514180d010075800034260300d102c0040760f4400d920100b05402010394034940b514952043c0c20003483c1c0180da6540310840707201c0603115001c41d0780d5520004101c40c1341c4a804d0a10400c0030400081b0280b03e884002d0026514a50395144400c1d040c018003ca015a40e1031511841d04000ca0300c005407040002082a5203030300e203941e00c00c1c111180c00300c40380090311a0409500c245600005000e02c02400ba0500400000a4000000c0141101c40c08600e040d11184007038268540b00086100d1105542040c1c0045414000300d92424842ca108880705002e415041c1c040c10340700c0c4240764801401c22030401c070521860500d419113240c81031081c100c49281188236003c054041c3c01c1185000070ba05a000c80c00d080560740306080c416 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 889695845 1250 889694595 889694599
    0x60518010312020a051605100f0c0602070f0516050f040b01120b0f0d06050717010524040b0d0f2a0f050702180a06080d1d0402040b0406020f0f010501030317040f2f 72
    0x3c142d41070700c9d01c080c00303c00784900010682e40c0c00050800030051005441c0d07901550040803202c0d1400390103803401c030341d90f120301480c1d002e444000c41400443c6071a01440e008990107031600541034a64104441c06000071800040e0400c0616441b0201070302c0b45180c2c2c00c01140180d9000515041c018402040d15a03400383d40b01e0042c00580c010b1046645481d10751070102c41c00048082c1c00441da10100115019640c4851100c030710205066001c0143d0b40c1000840b032051000c1040f07000c0801c1e4106054402a000200d80710400c0049118254064800d4010030102424041e003082c0c130036070021f4140345089804140c02e46510303040c03010340c47e80da00a48018101c0c2c00060f002e00000c101004002c415600c4803000b05549018480b129500d440d8100c0707014096180d101030b51030307840d041c0107035a4101c4400c1807240c42c8942880c0c1c050040061050a058a91596803808100f00084203412170060152040e00e051070240340a1000410782584c5010000350003100d8038802260005c50840303e6655a0034078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 889697095 1250 889695845 889695857
    0xf1c090f0f0e070e0a060509011e052b18020103051303021b010c020411120f040b06010c0201021623063a180204060518010312020a05160510 62
    0x40400c1da0801e9000e81500c0794600204500c1c0d460350390840c0c998000d40d0380582c00c03441c0040c02050780c940c0440108030b0326600780c88003040c000042210b4400424007803144400120b092024201c90b8140a40c80d070500c980388111416002d20140c5000b044840d82e402c03192510322650750340313011035030540241035200721944d040041c9805940c4010303450700400303034240c001c2c80c41840840001c0ea0082d00700307030344454024004200004002c00552110342c00400e4105201100100207010f001003164214807903944001c43c1606921914015501c01410310f00490650103010b5004c100c02c800e1640110041819215500903900f03c0d200318200c41c1550101a8004c00e0200b010a8500c040480e0751106c4d4200308280284400d0141d41c4190080320079a8480061402c00348902100b2000d140c03c1300751a4000c0768200f00d803a950b0420005602d001001c410360201700500104040b9012031107d030130100241c0143c0d00403802c01e1351000d0600d0761911318403d0450192500b48170301c0c00c2c40b81c01c2190025480c2002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 889698345 1250 889697095 889697099
    0x801021818041203020309330c0f0d02030c120f070e100c3003020a0206100503060402040b04180507090c0504051c06020d060b1c0b010906110f1c090f 66
    0x21503072400743c440d40c41e01031580000c04169855001c0042c0c204004414141c66403141c0c3d080741461410806840c4101c45804034804a2604030a20044500e0100b200368420300d04181d868141d4042e400c01414001d213120284120694058008078091003040c10308070094052034400c0b00a04400103142c000c03801210029050042c803074200540e82142504884201c0c1d22007892100d80c14020900141c0703202034120740210b2815107405402030031040c107150f0282c40c500e5465000948000080c0d101701d55042d4003034030102c6d02506107640301d444054000b0300041040104054150340c0310380700f0701c0103c40c540d010f40c1c001c100001940c0329440b41c01c00039144c514030b000d10304000240c0d140882c0e60000401c10005d40d8103410056180e04886054492440500c1101d0341d9101c443c003540c1000552000001d0348410903448541e2901c035403090500305845441c0060b00700700d012640c1070181e0318910101c0c8210f140d135200301c5a04004c1000480010026800a1949103a000304120301c19403011050203015001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 889699595 1250 889698345 889698353
    0x16060801051804230a06050601050a050d020309070b0a0f031a060301060f050909071d09040827090a240e01050105070203030d051801240b0f04080102181804 69
    0x10707a10900c40b8045409000c1d1603e080060b50311042c140e44445041400e000d500d084500401c2980b100350080a0821440d511000151000d104070b44004000800c20041c0843c80410381c2e020750781000303400c01202c0b4100c0d11003840078070b00d521940e20f40c0041961100c1e4074001d02c1c1d040c05000170a84100b40c4030156035002034041a00d500060007040180014105100c0429100d80180d501100000308001010704020350301030b2115010b021204c20408030940003d80505020990500966008911a281510a2034041142c445d405500c0741d0306111000880603983c1c410180074020003000e00005006229440d06d1150104c0d00c0300241d55600b01003070b0400120000a118504507802030a002d0350f01c4020344006803c51142400d08420b980c609018000c0c0c1c6047c54020f0740e43c0500381802089100e00da144111030b10198012400d6040402940a00403103640c10003414155040d600c0990a0540b5124081d080e6007040c0c0340c054149100c0711202001b8034007843e100400410032a1240914100390325 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 889700845 1250 889699595 889699609
    0xc170102090d0f020102150408030402101b0204051005040f0605040c020d020607050a0c02041b020d02030702090c210a0f061203050a0c3e03062e171606080105 70
    0x81d03e8604404002c005590091106d181507102c00e04402100780b4052401403050342040d14180d02405540054a040300d001d000c2480c03545000030b5802c040b01c81a82d0030080a014020440046030f000028000764a8659004042141c030040c4004960307241401d0500c0b085503c1402504210b41c007109005002c07640109d602c5401100519200b03a88030380040d8152400009114000e4000c2c0c0350528103580b000d400d040c000e401807829409c0c0e404c0e0b100746070750072170380c034014240c02a5210620802141242101600400c0f01181e1040015405280d031036400c462813404645c02c07501036071640c403041b09292041c4110406811140800038400801e40c600504a00400c0c4502c424000b040c02820140005c611340d203690720522500300312480c100d0000d00c0c004c4041103003021104210440c030010380c1c0e02d00400d801d440b418040e807814000c061203400340d44d443c0e2140f112090070f281c41494089001c103503182c601d02099424000408039212404404022000c1aa0203a000c00c40e64500501880d44c50603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 889702095 1250 889700845 889700869
    0xc0303080601020c0d050d030606080c04170a06052d010b0a030513061109120a0b16030e0a0c181509020702040b030303040f20030d110a0c030c17010209 67
    0xc40d0526031a030350840140d1600201400c159484003400e02514204400040c040d14100c0841c0c1e024002142e03655000c0e80c2242c41603c01d07410755001884203029000740440050f810a0303020080710301400041d110602114410f5440c40e0094651814450010329400020790201d080c0c004e107058035624142010500f4001c0700d950200b055140d5010500c0c00d5185840c0903501ea8000307170200410b0041136400000d44d0f0250001a0050441c50945021b400300801d80000c4943c20117603040c91650f851f110510400c3d291030407041415075135289041400800c11042003180c1c400e000e0000100d05111a0384805690300c0b0b00091014141081d048800280101100848105d80350158551410303100090150240e2080300c0d0b00f5100c048108014080001444420b5900a00d40100c0d0608a20050440d2000700c40f44c803034059104002c44d04c0c9084c414195112000c80c000190b40801000c3c2d0380e0424102c480d0b078016101121881428054412a20703010410221580000c514214a800203d032100102c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 889703345 1250 889702095 889702097
    0x3120f0c090e3313060906080307020a1214030a0930080901090b0d1a03060f010605160203031c05011202030c120c0a060309060b01050715050603030c030a0c06180c0303 74
    0x198030b0058600106a092048043d0001d00003410001007201e1100101070728402d000d503083c04c0c110000b5040d0004000c4508264000d0302242d24141000031800f40d581c0d1452085035041c008480368500d0003014030140c080410782d0b648111074035240210403038884611400d4100d601108005014003000d003810000c4081345d2082415458460400050b81c010110360300502c840540000c2c0c402400819500c40c409040082e507034000e55100c5c210a02d2741c0c5034800c40d4000401001c480040c4619030042c2d01030818202e029814078680b6a4030342c0840c0c11900300032500550115004209002c8010f41d0040a024110880c1c540040c192150002035481c54810281801511241e100185888080c4021801120041d029152450b65500018004c0c00b160005403580f5150050141080d840341003110105500001480710000c501c1c20309000070079024082540c103100420103861400d0042c0040c0c40303e07039030b991140b551070300301820700e0019100b655000404402c000141c00c8002250842814140c1c1c0d01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 889704595 1250 889703345 889703401
    0xc07152114040f082a1531020406140429040216060509030316021203061002071e030209060406060c0f0c0f03080d0e06091903120f0c090e 61
    0x1440c2098a030741e11500c1c01c01d101c20b54290154680175900309008218030074803542102c0007800344901d28440071009a5500d03090060300a0490800b04076000c7c50070082100c9203800e501c150b1282d000070b040303031800d50090401402040022640d49450711501001800751031012042503610540004003a10070712803d80315550200f03400549aa002641021265000c8400c1000382005e1180c140d9940048031000e8030079a80104c0701840e1803004c80c240c500d503450174850a0558407a002041403100b9410494002c510812900094440e41207102040304c80c005400140d140d13040d4014001c0c03445004210343e019600b000c40c200011a8004400d02e101904421940c900104d14500040c0f45091640b0032940f10005040100c2400009401080104404142007046980406507503071690411030f10440150407080c240780000401e03084030184144a0700d80076070b02c1d10701c0f441600c0c100d40801d110149400d68454410b08602c1d0071541000c081c0105804120952a00100304101c00c44803175810054a10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 889705845 1250 889704595 889704623
    0x8060c0d0e0a0c180c1704080d0c0f020c0402070503090607020a090f1b0c110103020c1908041a04440f0705120709020c0715211404 58
    0x442036015603050780c0c0a0007030307034180c81e02424400720480c01e5000d814101c42860b9041e0f018150140705210384003044c3d45a00300350490800ca8007844800040c4191855074080119440e07290b014400d2151074003881c1c0303505400340441d000c000c2c0340164089040d40900e104000c4400803450000a070340d480c0310100e840641e110110310104802c2107065006440c00e80c1015000400c50800b42c004825031050701c0002038801d00003103000c85695000c4000901116080504035020754400c1d001000c1d100f050404031f4034032803058001c2051011002c8007d0703450450124040c406004500c02e800351441e002c0c0c8550741890309043d500b5411403440c45100745509101c2e4a2925002d44d0340c1010356a070100d6014854011040c3c5c0b66003521142e200c0f001c00c09030700480001180d98a022146518401006002010151304040b1a4002944681070307070720301449110b8000601d2030485005040444071569000704042144115000300381d01d126120341c200d4140036417038204101c51210b4030f40c00380c0c100c044607014103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 889707095 1250 889705845 889705867
    0x50303060613080d02010c083919051c0615120b0a090209120d050f03090f0601030f03020f030a350c0c06060907020c120309030604150c0908060c 64
    0x2c942d80010254041c499090018a80643c041c5c0000c1c0c81c5a2602001c0ba40e9000b0703da119200c40c200183c40c001310079000d0140b607021080d00389007500c182c140401d2822480b40e80c01c00c010400c000c008000500e000683d143c02074100350110609500c10354007072161500340507511842289050188081042c8000c1c916035005c03440d044401d04402c05041c0e25419038a4200c0407002c2e40c42152000d0050822800035004e10800190880520344c1c0395941030704101541d6241c1342e0551000c3d000010714442c21071614014a0103105190086200d8008200303040042c4c6070190802050303804260b040e030818894030203001d800a282c5091040c18105228520046c0280c800303204000c0124044a00710400411000461a500030644005050101c0e04c107603448800304030030403000b100c0701d40c0142c1140c116845d10b814074003c18100c000005041e203051030720540209103814000c0300c081d148080e40380446409552a4070801e005d0400e07901d4451419400e0003d015031703c6201806000300b08100240d10301d0741e4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 889708345 1250 889707095 889707127
    0x303090e042a080d0f020606010c0807050105010602030901080f0601201908090109050603040f0204110705010911040b030a051f0b030a050d0311030f040b07030902060c06010f080106030503030606 86
    0x107035a80c4106030b9440c04090060720141203080c080c0200c984038040c04202d18601030028a20b02403090790080c501035807944c004607400c02601c4400c4412070000d00009000600a0040074080e141607801940c4070f03440742000500a402c0501104024081c2c201805881e991001e000c0544011840c0d098014120044c075040c6860307880707000c0e0510b841c03900001c1002c00040074000c00a051007640c03000780c2d0f15100c0c0100495840b00b660012701711074040e424500103080036040303e556080c1004540382411140e071112829220207002c110795115140c01c107003202e0320b4540f01e02d4514000030380003800c1d5071083da9500b42c1e807085101581054040704c480d035081c40210039044146014030280698580381418078001da65202041a6200400d0030010702155148112054030f120301d24404261507907460329110010b90a0f0080d002c1020140c48404e80700150711244010041c614950f401005039604d8264001d0100d101508140e6a59040030400c0010840000c00c2d2600103404448040e0b0310000c440d480086 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 889709595 1250 889708345 889708373
    0x200a0c0804260607050a120b041e021309061805150607080414060a02030f0a230912030c0c011d1005040e130b010905130c080123010303090e04 63
    0x18950b06103035041406501102c030340c801c03003510b0440c1d2094640c61419101401042022800201d007801001c541d2800ca411102909101400c0000d4400c0024240709400000c6070840000940005007980c000c90040c140c10700521100008100c01d40c2880c1d9554110141104803902860315100840c0d40c1d0109000c411601403c0201104d0ba1b80c0c00c5450900ca07140c001e4403440c41218296814482c0c103080c10004c03a80c40002c82d50195162010303015034007102c1c1d0480c0840c5010024000104140a00c1c03460034949500c034128640784d214180d0380200700c00c030f07540ca03050078050b600240582d480c82c850006443c00304803002d00b0001942c0310080b12048900c184020329982c07155076080d07135104040e000b074024002d44840341c0303403180d055898070911042c0c801029401055804074000400c01c0c0340030740d841a60002c81002c094540e211244d00c400c045442d2903040f01b035646c0d42da004286181102400c0710340d003089550144054075032460700c0180403016144161811079002e0340c0083c0c1004030011800f41c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 889710845 1250 889709595 889709609
    0x20120071b080708070e0105090f090c12010f060801051b13050319060c020c0f040c032301150e150a050910120b1804030503060607080a0e0a061d060a0e060f070303200a0c0804 77
    0x35542c107900203c140038140840301d00f81c0d0fca107014404a071641c01806500e2207420b00b00407402a0400c000040d40c05a0312141c00e421803607145200106055400780304e5001e288055884c40c903400c01060400c84200c991210662042d0340c0600014025a101e1080c3c1c3c421401044500140c958044c0c40c06501070301e64146040d084000b21401481c1c0c0c0d405105116050f100c82e030441324584103203d41d003960300040d85500207502c9110520b00c40b055100c030346c0050200005900c1c0070b50a05080002144455940190322000700d00d210100c080750f010203101d0074800f800100c940d940e601d0012001a003207914090400382c1005000130029482e84c42d0030003200d4003168801031480c2d0301c441c0440c000300164a8502c40d01d2180e0158800081e5852140221182d0215500c00d030f82c0c8213003081420040154440000c40e4113000d034091030181e4a542d0301001c1e160040080715007580d03031242c40c80c2c020b04581d41c015481102d40049001d00c5c2c00b81103c0e000f6580b03049002d080020b02200b40d070400c403a140c001e55100007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 889712095 1250 889710845 889710859
    0x601170d2a0606030807110a0308030c0306010c0506040303290a0302040908071b05010f050c0c010c14070b030a0c1b0b13080307020a1101020120071b080708070e0105090f090c 77
    0xc005d482c0c0300a00c00c00b40100140b0002070030810421021070150711020302043c4080c00410807009034500111740206050400306001030b0a03680d82410711000326001d0b40803960312100d15190381d6104214400e2030821101d1201903001c103200181e1201010700011b0701540e612804242085166000c64107116080884103003500030084078101e0480c0300d4010580003c001920f104c1407103026034256801140e804014100e10301078000110340e51100c507001651030044c0c0e030186200100007480f6040c080d04807450583da40b4074001d181c0600341c5080000310010032030000c8110241c1c0001210130030550b540565200700c00d4441038449506510044c2c00501241740000c184251560000cd8540300c141c40349035002c5180d28150011ba00b21400700750344003400d8000f03035821803040d00c0c900d0040c000c4504c2054008005031044442e01207503040c1d0341004c141544280070070b00c0680c0d02000110000c0c84038900200f5958102030124594034009803000034071806450201d28034410605ca41c1184080c050300032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 889713345 1250 889712095 889712099
    0xf030a06091e0c0e0d11180a060801050f01030b07081308130303021b132d0509120c0c0405070507050604060c18050303030f0603070906080601170d2a0606 68
    0x80701d02840a0b24403001c06140a20f46150b05004612100328440000c01c030244000c1140c81c2e00544440120b039466000300c3c0380281d51040c8204801960282c03000b254002140307414200701d542114805428184c404e02c0403c0104000743e080102c041e4407007260314103107030241c40c0d00244002c1c280311168021300c2610003243c1000700034100052101144c1c040c0d401c8900200c40314890070071040d00f03180225041a4100283c1c0100503803908a107180c503401d41251603681100303400c820b080c4d4a854110f41000381d1158107110381c10f18100040d04003041d1881c1c00340d1404202c0c00700c0710350f50b0344c0280f0b07242d0280f5240c8001600d0903002d20300380c4e1303942c1d034212050300c1183c035240c60031000900148010b000490000c90303c40d03904420b82c8840c1000e5440c0034008500c2c50b00c60750900c8441000003842c5550604c1401c801084d900d0080c05040000c1000000502c01c80d414428601182a000e10b01000b0ad03600041501d51059440f0050340c0f440141d49c000f1280d5492170a60300381c1155000a4041e00e003505060300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 889714595 1250 889713345 889713371
    0x1905190c08062401050a0f36150f050904090f080d0606020f030c1510120b0106030f0e06040f0212030c0a020a090605030706051315020d03050601020c0102030f030a0609 74
    0x1d04400d181050000c0c0c00303d424a03401034485008005820001600c41d00701c0c0401b550107000100c84c1d140900010001f6401c01e10000401601920000900c60300821810010b00c0c0d014500940c1300c4030182040140250020001007aa001c3c60303c03210b00c60b40d164010754080c40603140e0120045078018520580d10301003150100050b010f5803190b0401446000344001507840044190350340d090101d401f07490740c1c44402d0035000200c3d20140102c80398a00006000500302203030300410807018491802c451040d85000009400c503a414400e402002d8141520100c02003c04240294003a0b800300b20100d441d110381c0081004083c104500b010340e031000050003500c9103400a06403010a108a800724007168031010a0005ea030514440c00e5099030000741c081c84202e0284000c1c00364040c25558103274141d5942c80d00c030601804203046071005600401c19480707003241e0500405038011004c1c001000b007020a140001c0da24468061a9010b0b44008004209400d90b01d82002000b03080c400e0b0140400200c0c114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 889715845 1250 889714595 889714621
    0xf0706020c07170706081009090309031101030504020901030b040f0b360d0f031401030c0e09011a010e01020c032401080d122307111905190c0806 64
    0x81d01850341c455188001105151420025840307841030010301805440d00f0001d03102e8600c0508825142a0b03c60700200320b0407038920540140501903a501c400081c135508240c0c1c1005510300c280c504141c142802c200140c2c84441c20241101c0e40003010b04010798075801e1402540d02d6400d03009101d40981824490702000c3d1079042461404000c440b4091b418080646010856491110203110f421584171400c0312400b070302120b0140000c50501007441c111000c1e600302c1e421000d81040b14a105c0150051081c1e44000e0103840d40485000c008020480c109103400364540461203042c1c0c10403601021480c1242d10a200c080741d003034805005c4600109003d0fa0800f031b50542c8959421101c2c00394000010711001c0010802a044290b84547e100d44c4040c2da010005007458007541c03243e16004088002c800800114a503204414580e00d44414510f1902010704290145440810503e100d54811010aa003c10390031f000c01c0312f040004e514500c4c0c500d480756103c7c540d580110014050a4100720361206049 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 889717095 1250 889715845 889715857
    0x114360a0b100203030921070803010b120105060c070302061c02041401022a010c03051b07051e150912070e040507050d030807030c05041203021b030102040b0304060f020f070602 78
    0x10b8814401420400e41281d890004441101140d4000c43d84602d0115039002405100100403100340d142100c5500c0d01c00d9245e0003a400000e80a00000b9a0280004071166441c0034000884000e45415203403041c1d2a42c2c4c4146e800b01034800c0d8000194904c80c10003c0c101c519003c00d02ca02c1c25903e641d50b1384595160140110112030160081030380b5010041d00382d6412042d04080810901221007046004561806a010088007031103402c22250300448407190002a094299400800159040c42c050001c0e40c11121400c000c61170044200d00c6041e6100d1016048499003002415100c129081c00144501002081040399006041c0d000ca8106104801188200e018004881140d50b41d10f05100c65902000c6001d00011481404504030342d01c00e400240b201c44180c502581402c0c1c03207410f41c05080e190b0801c110056441a000606100101180882071a20450086003424502803481c803483c80300807c0204459510003000c1850030081e8181d64002102030b200e03a407504800c4c42c10f9402944030b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 889718345 1250 889717095 889717099
    0x170d06060c110a050307060f0e041817270a0f03120e1f110c03120a08160c031b05061905060901050619020a12020102120114360a0b 58
    0x115400b8040e90800c0d000850888402800078100c051a10a084422082c40070506040040c410070b004001d5449014403d00f00502d4032807400d20030900d00e81508882c06419500340055003d100c00d9802060b541303540d1241c20004040200c0d0035200d44006501c91049400c4810700705104034002c030030f04c0041110142e90311034944135102000d103002c080280101d08590000c50240703600541056861007020b0341e13660f0503c0c1c80211004400c00b50300190074032350980c00c0400c840c80d02080c944486035000340f86682000911100c401764294046005124807010315000c3c09000d00c0ca0140300c40c00f022460031256054005051b19032508002d0348400610140e918454491400d10000c07401600c2c25260035412200700070041c920340341600e4644a00440740a0f4a00258059803500c1404070f584540d00e804403c0d9154001640c1c3d94880036200241441030b00560b0340d40030009101201e40c1c892124103807034900e40441c0c03480526401245c0441c041319000e41000c41c0380164090203150b101a4204106582c1c3c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 889719595 1250 889718345 889718363
    0xb01020609030418090f1a1f050a030201080c13060207050a08010b0d14100e030702090106090e0c030406110d0f0f0903051602010201060803070b100f0302030a170d06060c 75
    0x41c41c1c41e825900d00450290b180c00040742000f10900c001103500a580c010310075031b24082854240e40b18203a4090086109032180700040d820484881c007544054602c0301d10241647d000503003404086803912480f400000d0500040d100424202d103070203800d030340d94801d4680c804615030b0345501c0000e44520700c91003000d0058820500c00b140980c41805031918000c3c010701402100038080d00c520cc1803052205500705240100c41c03030610448000d0142c4d1500e80d45120003150f982810380f0510201d24016800f10b003c01c40640010300071408074220454001d45140384803a00ca864504141d00201840e10501414a10001d8801d200c14842c0d040781c881006050390402003001c40030401030940d6500d43d00100080d508000c103e402e8604140380001d61401031000041480c3ca03428281e145912883c025a44030609408014901900c40b400f24080d100e140307015005240356a01181e90f5040c0480010b10a80815a85c0c8100407400ca041e211041c80e003a806009150b55800d0103400d00c41c01c481d003603803100c403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 889720845 1250 889719595 889719601
    0x1d0601080a11064305070e06180c030718270e0a02040906020906040f0e01050d03080a0b01210e120405010e0108150604030b19050702030a0c150f0b010206 68
    0x6000c0d010b45200080850328000c01c2d00ca18040c8400c400104070010380d500c1200c5000c043c03010104d01c2c480403114450701c000c3c1075040c109880072484130b4000340198802c4a1a500001c0c189407003590721038001d460040070701c5c0c6070386445006950031076807449002c00309a0702c2400010003000a104842400800440b039504080c1c00c842c8803016103200080c40700e081e030b120303400380c10050601c2c0c0d000402950080f000142401100c000062a0b988540e1060400840308034050001d0032a4103a0f41c0e0042c141202d0154514030340b99806031a01100901e00c009460380c0700e480e500070764080c2c040c211001d8194900400d190b8200100e500003084040191000c910881c84030f0340007000d03030004890030b0300c0d03058440b40c0e0600714450046540b620014510141000100b400345101d8542c04080c101451003158011424503242d040c20942030820303440750502c1428903060000c0e9540120444001c40f410b4500766800c0380d41070500c4000449106031941d8407a03d0160000360742c441544c030040c1001c2003642500c029072 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 889722095 1250 889720845 889720849
    0xc061805100c12091a0906041d040507060908060601081e18070608040b0402060304030516110411070222061707090506060310090507121406041d07091d0601080a11 72
    0x8803a005400c07002c01031040045c50260390502820fa168030043c001440d05e912036440c031500003c417400c601300e05e1200105000802000b032110b000a44510300d403918200d890500459a02d10700500365606001064003c298084640d52134100941c3c40034401c0c120605249244602c082d400d148511400d0080f0003000c04d10b5482401d000c2c1c00340390040302e202d050b030325540c082104681c0054401c800f0b0010802c01c5611045440d080d015a41c2c0c055829801c0c000c1c00d00d01404103442c04200e900304101c004001e0140181e990b0029031904002a10076450420700941c401c03002441942c00441d19100604003005e181c1000188100544041100611050b1120300c10b0181e00d009c1520f842180d80c1259500744070512061f4441c0d42d2220345450500b540e2483c02e2400402c5405000c410f407100091413080110a080501400420009000400ca46a600400b441e5160b2041d400341b050036035141d602e4249039045110a0100401c41f070000d403401940d440714006d0f664054001c044480e00034201d803048244c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 889723345 1250 889722095 889722107
    0x20901090c0503010314280302010f05010e071124011809030f0f09030f060e060105100e01180e0903030910020306010509091b1c0f090c061805100c12 66
    0x1c081e441c0c071203e0941c1d0850342e0b002c0241d0743c0d600721030400d44503c01c0c200c9142d5000c913822440c180c5a951044540c90501d050082c00d5540104100080361700300720042160400300c9504a50145151a00e0050480040080340c02e140604e00c804d91420300355420b1514520800030f00f0341c101c801c0141081141c114038a241e1054034020308000c2c010844854003a580140908011242c0451a02c2d1607040c0c1c5460790342c0d1482d403000c00b40095038001d54504000c0183d4404005407405041c0071940140d600c5100e000003000401503007091030400181340150349520006050b054040c04181041001600c2c1000c41c0b00d94a0300304079080b10951082072001030141c281131003228007414041c3d40b160b1401c1d10407414017442400107854105d601200b006801540701d0058068407150034681491113911100200380400e50b820065041305051400510200149103c202c0b07908403000c600b0800341c40403403083c1d00c0b1f21040d800d601094121418501010545901c44c84a102661080201d80307490303ca1000d0480d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 889724595 1250 889723345 889723361
    0x4180503070213060506070623090304061413090b0907030b01050d0b010519050c0721060c05130807030308070c0f060506040b03010911011e051215031902090109 71
    0x503001009403401508001c86001c0c0f044000d401e012a00036a11008540b056003e5402580c3c0c0320b503140c1680c02c0c03840d200910294140042e80044070b9606040251340e84070f00c6140700f41e074103100c125100540d0041c0000c00b51600b40342c50b0448517081980d114010304c00750807a5041302d441078040b0000504844e009200320145004180c4d40d503820000d454000c580200200c410243c180001842141c19124650212241100e49540d034a0b03103507030325141c80038902421a0010b400010810307102c051065103071503011544940040c0c003c00c50481055090300d1034450001080780e01a503440010030142800901d000c2140e210750358850081d9141401154a032a00a00c000c01503a00c05a07440042480d0b40c0100750007003002040090312000681c0000d0848004240488085d5094084001e280d07821043d000b003010894108000c118a0200009003548500c15880340610403010100d01d44400b03100d4080c206c840c02804860313a10907405080c441d179021280080b80300704c851200102d00b4000e28090106 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 889725845 1250 889724595 889724603
    0x603060b0c0307030507030c020607030e15070312020a0c12080103120905130c0203040b04140f0d12180e04151505061608070516031b0e040f06140705090418 69
    0x209242013a0b0301103d050344201c1e42078040040198400c0e0140c3d840034020b003491480b07a111b00c82c00707401d03100600082e4200c9010202c0040c0782844080f01094102c90075079810102c04100583e2900d0404007500c0590100c40702500710582400e0124509420000c454180d9018800c4031550364101c1070b0480b20041240101c642240c584420000c50b07484681090703204154500649007040d031500d0650325682c0090307210040b03081b001180e018250a11b000fa04a00f4013082c0c0329a0170042c007588139651000101001d090410801241094982c2c0c101c807000405031220b0003500c4114181400c014000203005800e4040b070303d14092103007032a003030114101c2d822100c0260082c6e0401d100715041c074222100440064428800400c00e00c00001e2060000010a030266026400d0326811410412050803040409201d072007031218007840204018003003290f210b60301c440182c03e001d16034904100a403a07150a292100c000d6103060250f110741090191803041001c0e6010803110b0034840800214200b1054068 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 889727095 1250 889725845 889725847
    0x90c030311060a060b041832010e01030b06150909070306050f0901062a0813030510150e06040e16051207031502071a0403020105010f2301360603060b0c03 68
    0x719a07500c003c80501201c0307050300040ca03030450000c05607050034150140110400c0c0303511202c090323140600c0c0207014262124252100d58103542d1150454440942101e220f0303c8040000800840000b00310761050a002e48020000d040001000d0042c120302d00610348100c40030343d056101030804610081c102c5030544c3e1481201c1c901d050300c40420780ca03903404580500e00a868190041002c4d00c0040c03041076071030b0480e86189072450030132a04141031885142c50041c107007209454001e90029016041e1031f5003031045c4505407540c900007001421001d101800d940200840d90754043c80c1c2c10019004c50344d09640d038400780d000e545241c81c0c41d079101c2c0c00001d100010601e480c580008c0706902400d5494840d05609075180c00c1c0040f544503140c412541107005030344503401032068070492400d102c0209200e44071071542086d00700d0200d21200300d440b141c0303040040c540c000d213841000304105001c0c0000e01404100c04910b604000c00c9040085010345404603080030360010310f084401e01169814680f9030099 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 889728345 1250 889727095 889727099
    0xf021204140a08280c050d0806010512042004020a051602150d1b21050402040b06070f02090906040201202a100906020c0112090c030311060a060b04 65
    0x110040780015010050902c01c00c0700c8003000a81e10401020501c40303822a10319001c4100003840300755011902d4680401001c0c541e100001600040d0302c2e1200c44203800c002d0011398940c40100c640d030203140d1610144045110901090085048a02814001d0342c980400240715038010f10041c2d01c217007080701002410030800780c1140421a250079406902c001c080040e00c848001403100c550b0000044030440551310250914624103684040b518000b01d803d0810789a0015105154100765900c3c41144540c4c90b94000303404c40d41e895100c60800c1c00020451910b030707013140c100f869414800070030807800f038a1180d004c07601c01e400000d10301d071180b0790595809078010082c02e05410b1a8010030040b8019215030584072000b001003c0b90000704801e00840300460400c600104140e01c0c0503050a5018440340310ba05000460740850510000d00d020b0800300d080426903460304000702410302c03010300b1407c8501408420503034002e00310b1804100050032541d40b611482c0d1001c080b110381c1d00c14028918810001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 889729595 1250 889728345 889728353
    0x150b0405100909060612030203030711070317090f030718060506030f06100c05060a1e050f01061103120f010303120614120f070b1c020903060103030513031209090f021204 75
    0x2209055130301c200400f0440c40daa03403007080c40c2da43c0225000c0b005600013104121084c0e40c030402d664420848000205001403840c0c40300b10000982ca98a04c8200a00003084050f81c0c1b1340780ea040c0c0180c44040e080f0351100d542c0e10818040300c03803240100c54819041c07400019161404034250703809080540d044900c01e44804041000b4030881e03100c42c07401c2c0200304042c4030100c0e00622000340b244260351400305801c884254000601c000d10b036460280e05180805025107940e250a005045d01c41a04080d4130345150000e21034654042c10340403550000c008000c0008200d04420800d040764441c0d1107060340c1810401d0400c1c107440d0349000b51140f44031030041e039000c40e185c04036808064840c3ca605440c454013a401403241006100d07001050740b8040014801d00070f1303500c0b40c20950b8401014800b181000a644002512900e0611018041145c003080c0a103840f00200048001503034880d82c0c04029001450010b04503405921518070001d01e00314010019944600803038002e4400c818070504c4a580c2ca6503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 889730845 1250 889729595 889729601
    0xc1309020112140a050105030d1d030c0301330303050d110405030a0b041b030506010b1318060603061a220f170d020c011227150b04051009 61
    0x4264104420000702c0e101c0c82100d8810301c0140c02d15401800d0613840c00c0c1080c201543ca069008038041d601c00000d13908a1a80001ca0180c400136041c000280c641d00740001918282500035650380c15460300c801c60052240d042d4142c0b100d91020720403400255101700c210504903000e8400035000c2130040080404801c01b951240e51020321141c0c24904240d194408a85065180c0404440c00300742141071000f40700700d016030340152442800510b82e1075400d503610651a008103214031408880c010a241105080102c4408080c1440781c10b41d01014030b030840c0007400f40020b403043c840880e00e0034a010482c444d03603041c008904072500800340e180080d000c03003030809000d502e00250752000ca400d40c046852603400f1540001000d51031100f00c0301b42e42601d9181e0800281e0342d02502554000c03048a00942d0300640003050b5200b8081c0000390380401c54210750060202c8022149810480008580812500c0d4281c22050f0551031410841c4503074000078403044900546800000e039481c26402c21007809030750 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 889732095 1250 889730845 889730861
    0xb0106030f091e050105060a0b0a0e032b08060118050108131e1401150e090a020a03150e06060918031e04170307080702060309011b1d030c13 62
    0x90002d00d0b00da8030b8407010112440f1403003401c0d500c08060107080611000340610358114100300c3d603040055103030062035525441282403003414040d850300704140c80d94092201468000400c4000031a1542454600c18056a5004980003049003071001c180701d075206640342d0303d640c1030511201d00d2107401d10740190382005004004004140807100700c0d40006800704680b0000d400d5000031102220000d1030600d491a80c8030364010b06a0b0725101c07091a900150403840b800311110390085c519692a031010041c10509880030294125200e54800002c002d0a903110009692a80d0010082c1c0100c15413800d48034030007036a03050340c01180400881c001030740e522004d250044004003120b240449803564861043c41e0400354803d0998049000c003c0c0004070030f6400450303a1844069843d10f0a50390318803005001e07028019010345004400101007403030951000d054081d288602e0400740c2190b000c010400c2c841a100b80c116045141075114240c24000388090310148020a4000a03901013529280100211 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 889733345 1250 889732095 889732121
    0x70305070806330a0303021b010309050a031b0812010603141e1008010f09110306010303050d1a1e03010f09030806090717130201020114010302010c0b06040b030f01020d11070b010603 80
    0x108040310140e5107a400c04c0001394420b802a114000d099454402c1c07081102c00050b045c142081c4500e00000c802103030398031846925042403202480e04031001c4001c840c1104004181c40e0b00003c01200b0705060b020040d040b03503403e9030103000f212040c030302c0605c070b401d82035801d80c603005000800c0e030b5602d0f4800010940d100440c1903a041032507540b4400107094075020400d5452080e6a00644002e2107001c842110725500190000d11980d491359030010150b01c0360350002d5402c5640e40c1030000b0b80d00078402d60362080d10740c003c1154495004d0802600d1480404225045c4a0761a20080c00d8001c1c0841c002c0c8454190542c0341c146c4207a56640c00c0c00070240b0014404802c200c0c41090145c5e6400501001c140240304d40d81d0070710002441351001a0845090f821148420901d4500410060303905c404142080c5901131880500c90b2107020101d80508004041c469060190703980804c038082c0154080d100249843c4800d205d80c055104d4500c800d4441c5800183c01c80c0702030350062240e10b0098002016100913 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 889734595 1250 889733345 889733431
    0x7050a020d02041b090e090d170a0207150b041a060d02070c031406070f020303010b0d0c0e0406141905211f05010608073617070305070806 61
    0x1e840740c50300303a88021041c005c1075403484180840141d00018690100d503003001490030464002c005032000303014070542a004903124002846800042d010350f0440356100110609100d011003540703000d010f00340d01990142d0315044c0501d0b034000300394124890003103020303100c0b61529900b451034078082e6110070740503103002c0d04403c000400101682d14507001503003014058032150270055002070074200c0f8808103500310f600900061100c01007a07000c81c0c0c0444e903030070030000d42401480020f8074070313a0390726911540c410b14040c0c0000e03a03080158071601c0191011a00c049c500404090040e028804500480b0341141401103524906a2610182d40c180e03000340d000c80e00c00c2c619041400441c155100c0c64403900d40d4a80e0010004142c10450054005005040c0003001d544007828004c02d6800718424007082517540a4216885175015686801030400c0e0b14000c80c6c08003000f05425a5000e0034441110360b881071200015103402d0120b0398501545420b046241d0000a00091211541d10b0b14000545810 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 889735845 1250 889734595 889734611
    0x6032d050303010306050f101505093f0102030f0406200a03020702092a0f0c03030117060c03101203140307030c02072c091204030c0311010507050a020d0204 69
    0x11007000a036000307500c100d00105003803804072800d00c00c005016004102610000c5001e010114854601d40c20440c01850308039118280c00d030000d24200310040c40440c14128810740c00c1070360080420346a02c1000d14803070510040e800100d2541c03c0b03105c22078441c800c004140c0c0114000411710307004440140004415800009802a0031720724661111400c100460b500286100450602c02007a1380d2014a0207074032076410035500443c1c1c040c0c4a01c4c60b4925080c00d0001204604c80075020291030b103080000e400c4079103039030311188444c0c00141c01002c11056486944001002079a101c02183d100303039803050340498280e1400000c1c0704143d1281d481101400407607102e00c2d00102416000d9407207181155000300360340e140c20b50044c0c1481c0e40340d004514042c0d42c0c20303400101154010901c40160f04995440d50540c1e90340481c1e581414403420000165020005000081c8001007601c0c0c010741c3d006095203902586444010b603942d110328440284039030084d008080c00341c0303003100d01c40c01c04c10300207000888c1c640 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 889737095 1250 889735845 889735853
    0x160203120a020d0219030b191211031c050d051f0605070201030209130f0f0b010f23120f0a2304170c030a110313270903080f060406032d 60
    0x4a2164401d8000aa8881f110046858282d10008680b85101c01d6040141d007480d214542032542070f840900310414418105000b51010040d8103420f55402c407002d400304c2c1c0e06900c020461303800313140c130504200d0902d4081030303c510300c00c1c202c40717024580d000f10399034068039000080c0c4664001c0b0780c00f81e051590a112000321522040707295280c4080c000d20005035101100b40f0407045030785003c420781c01103103480403100315660002211a907a011034101521304010722030b80500c00d1608140d01024217180400c0000c12040d00450325805000812110f8a1503a92201302004980c0c89200301003080700c10702d5601050310f030503804050708680a0492590401d40b10107910009600074a5107112940c00010340010b243d61040d802004c502c9001d01561034080038031114100304039203014900700b00d662107904003500c8001c0940c2c00048142ea40c400c0c030003000181409030010008030382284c0703207200010003d00c45146c144603580a696010442c007903040da85503031b80fa00b642ca0f50300340014042e07503110844008c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 889738345 1250 889737095 889737127
    0xa0314030c010f090201200705010c06020904110703020601120506190b0a060e0f09130803060111010e030307140a1211160f02030d110307020607020d021206160203120a020d02 77
    0x1e04140f80010403054404d200040c00c042500c1c10300050810f04481000002202140304021600240b810741403103406418141d0091140f40850780d401854590b4440f20200c3c1907000e001c20394066020f85000b60f0303851001d18118108854000d0058104c000003131200c0b01001720b074000f0001e10300c6001600301044030200300c040e00c00340c0084000c900c040b07c0103c4e29150030380c03102c581207030182d07144089420700c000001c00551030b4800041c035216022000413010f034813604046407441d066030028803106001c1c0300407548071350040d540301c400901ca1000c94807080e52030300100c40e910006565034441040030000900002c280088101c5000501000078046070b640045103540e2007406002da0501012a40c4101481d10345d02110040610201140d01c2d03c5951010041c1c42805405035801640c0d04078510000d440501e020100940c07040da0000c168000f0711000480d0780c49440e01e80031844036a02042000d0740c3e02e0192004a1007001c0880340007912100c01a0090030442044107000f500304508400320303440c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 889739595 1250 889738345 889738361
    0x406060e1509070f0e0d031b0605160306031e14070608100602160317120c030f0a0e210f0309030a02060106090e01030b150303030a0e010b0f0a0314030c01 68
    0x15206224031140c10710700100c40300d402450070f04001c458007281304000350005001520340391107144142c1c5580c041c58012403009903801401000c200d02c81c03030b0614090000b00000d0fa200700304003203842c0134118110301034492031041d01d0b0040e0b0003415440c1e43c00c80c90740c514031680c8021100c40025000100c281d0034200030710005030201e80c80c0c4800d946044038456403070702d105038010005c651000001402c15041800fa000a50345c100410004000c80540700c01c2c468801e2030007148058003041e00f04040600520701a5001e408440d82d188040d840c0e1410000c02da0380b101900000030707000300c070402c0364018041e6a00c90600d80e4044030b280c01c16003c554200842e030011a52402a904001070030b0740700660500849000d054141010141181004498814541c0c14000100450000130201e0708182a050004c082d01500800301d0760303285880103291000e00344159041d540c81d800c0550054481c940300f1b5a03648000d038060121801075207540c071105070311401c51010140b640010442086100000c0c014688 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 889740845 1250 889739595 889739611
    0x30312090c03061a1e06030106230a09060f1701150e030d03020301030c0b031603020307030b1e01020d0903111c05010c02011e092613031b0803030405030307080406060e 74
    0x3095140d4203051005131400200e845c822540f400b5142c0004d583c0c3c46040d00e054a04034604800d04500d01c0c05280f039a2688858420034000010602c101c04541c090403203010303603100350f45241c0840e031070241c2611800d4a0340000e101c80d001c0100144010720380c4920303c0f0740c600d00c546844000e58a4450109040c00b4440c2028000243c001006000388500040400001c207006000c05241d4680101d05104084c62541000105a0000b001c94201ca1082d0400a00740000802a11404404503003003202c010b010056240903000c0c48248600340c501403220ba1048a030802c402c81c3e0600c426108110711200c0000e0a544c4030488400c11801052091182c101120010303000003420152100000090400202021240782c0c00d040a400008003000c19045804004402d8446980301100800c0800c2c098283c000c0c180c141c0c00c00c0c3c00800e001ca207a07041490512200e00e00701c150364942c00300b2034032480216000703040ca5104002203020140301d80d19843d4407a004090000c1e542d6111050100c241c00140d41c40b02d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 889742095 1250 889740845 889740881
    0x1e0e0409081605010e062811030a0903020d03060602070b0702041e0c030b0904020d02012a051b0d17070c0b07120215070c111201151509030312090c0306 67
    0x1c02000f40900ca0001003000450051a25140c082d80098404070f803171260b24410741c3c0721100b02c2ca80e0845500700c0b400c40420848a961245041c0405d10002d01001c80c3c19401842500c800740300342802485002d050b98520b50142c45482e0810704007a401d940100c81c200d030030035958509094106013482084e480561312000104540b9180ea400074240d902000180c0c2c45402103109000060b078034a882c84510550a0074000440303080602d848403021a0b2031846800c1e40e00958142c0c08114001c21600c0b01c08a2001168041e8040d0200b8403080103c0c2c108020b01740c6600da10752650040800010b0606c0c0e605c0b0382c00700304000f900c589c103840680c2c00105048074800c070300e584400d50403034050000c1d8482c00080841c0c1100c41c90140c0005084016155002d06001c100c0b81448255849100e80380000d000803200074444204c8076400388400504520600e80091500751007a1011807056400c5411a50143c0d41c003030b03070441d0b0035440b00c00810148400711040015880000300160450044044404c0c00740624 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 889743345 1250 889742095 889742137
    0x5040203132a1a0f040b1b01050f0a050a09050d0203091c020603180a020402122706130203031b0a380c160c170304030512091305010f0302040c1e0e040908 68
    0x652007c004800340941140d040400304141ca048510516a12070000100440e4030788a00006d0070042100e4000644240504807607003c01a070000010040028103440c04224482e107241c030492514003a010095100c902000130445942c28104640d07140501c2106544c3c49610941c00102280c0c01840790021300c07003080041280011100c0260600b901d034080322008030740400722160351100740052000d1888094a50340a0542d10b0410940d40700310f0803400600c48000d11210b07203036a581c4049100300c411101c9511414441c1c40e8141c8c6900d180c01c2240c045401c8002455001c9041840c01003152801c07460a01090a404801e040035801060150000c100c440b41010101c04008550b101500203030703401000704000180b400504900c02c0b0b500300107240d0301d4050a20000e40e02d07149202600c880c840c202000440c50038507a0400f181100c1c401c441c00c00184041c5403059550b00c00b07008030328421000701c05802500302d01079004140307040c2000707000040001e51903131240c03120380141719031040e01a079607800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 889744595 1250 889743345 889743367
    0x50a030f02010504150203150910091d0304061407061401050112090b0a0903090e0712180f0210110d0504080f0102090d0f0c05040203132a1a0f040b 65
    0x2035200009244000d204602e030584075641c12403009440c4000c400c3e40000014030004200c03c850300c03100303001001140d150408240e180f001651900450b03a280f4505070000c0b51380402c10399030300107019400026505052074001c003503610010b01504200e40303410410030880004c4c09803260180030744038140460300950511000410201e00c0000c002d84062514a0020100d207000d440d443e400f010070100480d100b070880c94100d070007a0061744290041c04010050000b5207030001d81d510b5941026810400c0041c46225007448040388941001d8200c000c54120700b07003d41400401412241c180381401e0008100100d000c0b07140610142e54400051070100d002d100708102403248422000300c1500940c140520040051006140f41000920a0b19103200b8202000f400f580340400818001748119181d01e0316a20354100c1803481201121402d0030301810544d801c904105281c62200308078240600d0a00306a001c1c0441c540800c400028110117010123140041403900400c00341c04500045c3d6264800b01c44 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 889745845 1250 889744595 889744607
    0x7020d050d113c1c02010b0f1003020a03151401080603030c12180d1505130b071b020306010308070510020406120207080904240914130519050a03 64
    0x500305400303070801c800102c0c000200c0d02400f00304682d00c0c146851900e000201120049446983e00d00d0940a40e030103c51440019802180e42c500090b0020310450b00c0da00100100c1401e40d5041d81c0e4030600161a0f4803a180c46035029202510700c6013000038003200d61901500c1c4001c05036100d40c6982d440d0340065107895074881714460300504250011410f0021240b440d86c1c407108403d00010641102103180306400f03030a0503500055030009451000c190b6171070b0030010100005030400401e0350b030130b040101d901800c00312001d02a2903006030f0214607070744800c80120f644600691201d04a03d200d40008005030390188074040c021441050429542e500f9132034a5401e0001223905418403601c10f0004000040e0010702140742003496890050f911707142440c0c41004c50042000d00c1d600685425032001c60144200500b0b0580ca0004040403007050b5200280b40695210200800383d10003154085909640c05a0078411900e20441c280c80f0104070b62030310302030308540010702640c0c01c0d40225420303400c1c960045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 889747095 1250 889745845 889745867
    0x5070f0c15020d03411f140f060a0e0910030b06120c0906040f020c011d0a050a081803100f050609040f0f05030c0f16060504030c0e0a0207020d050d 65
    0x1c1028440d4000b41159590703082c022520115000e510b41c0030303081024a01e60041024017680091115403814032880c0300c500808820341c481401da0000c840800e01c880c045264042c0708000400e0020300c0080407091180c0b9070000c0440c101440003410f500c441c2c586d0b40b0150188900c024140381e0200618600b00340c03440e21000b402150203051204943c00e880d0300c010550401c011130030764071860f82c0c1d02c680d00820000d0150030004180c5a2020a0302180000e064209221081840700c90240fa0200400301c80c1e10341034041402420ba40c407401c40080010803210140146002c02a8070b61801d00c10320000c01d08042c2d0303030000c8010580d41c9508881c80329410344241c42c0c00c41c0d000d803070640103440c0a030707101c00d80d116a0b68800343c907154140f100441004030410841c0d1700000340350f00b5a81f403076000340d0138140d40c1e82d951052040302a03421000800c50900c518151030480781c201070498001803030900ca40c0782c8024090402c14115408014000168948100c0070481c01c1c410002031090313580110004103905804 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 889748201 1106 889747095 889747097
    0x32413180201021218091003140a0b13020a030201200f0a14210d02070206030408040504050a0507120b01170106080f01060203030c070305070f0c15020d 67
    0x5000240d11803007a0201d0712036400c038001966071070281401c40e040c4c14003003401c090f00924202d4020703900300c039413074005010301500d94035820001c1d00000c0000c44242d01149a450070813201c0303031030203920400300c0c02c24000d04d0341f840d400210035035541d210280c10070032041c1c03030420034850800c0141d1071501e0040071105035845654001da15012149070655244c0110741883c410300e44041030038400f0980128580803804440170780e85841c1c4e0010500041038a6082c8030000c010785401c1d000311f010703e01440b84992954985410441561380007068601813a0600003840300a640150030040c51040004000c100e0340c11030380040703030104440c0d41c0e0701c0051043c0d0070000960a8101c18014041d140900b080c0c005683c80304401da80c0c82c0301c103880f00d940c410070030813230740d03000c0380c0702d540506005445905541404003450301d5000007240150085650901100708108201d60104001c0c0915038017 = true := by decide +kernel

theorem cover : BRFrame.Cov 889568345 889748201 := by
  have h0 := BRFrame.cov_init 889568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 889568345 ≤ n) (h2 : n < 889748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
