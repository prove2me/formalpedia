-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5260
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:16:28.897832+00:00
-- url     : https://prove2.me/submissions/bc29f453-c1b5-4bfe-949d-37f00ddf5032

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 945863309 ≤ n < 946043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 945864559 1250 945863309 945863327
    0xf1801020d0b1c0515040507180605031908040b0c070302040f022d07021e090c0a030b030105040b150d05010e0705011d0307060807121a030606060403170a050c0105040b07 75
    0x30303c4441441d4952000140c001c6151040c0e941d607607441c54001d4840340f41190800b20140c0080664210580c040080d444660708a030084507400d50507a190780880303202c0c00d003050803660005007800d401000104020101078008048080c01038007503640203900c0b540000c040c0c40ca4883d03c201180d030086070824000360042e40c1107440703085003801c013641707144102d5110b0414080c0c000064414945802800180c4480300000c0d000500014000c40382d52030111202c3d01907400900d41180081d20340b40803440182070501c47c0c00c0c095030300500d2501481d6248a034549244034020103842d0401501801c84001a00034016054020044405408041c1c200000100007449910100695001a0094040310340f0085404001e4500300c1c5450b0b1102d5030303803000540e00c032030703103024519095032070840100181001070300e07032041b0303800304030706403105521448104209405940406400030120a5030426201c442c18000c01002c480360074280c2c1058a1094110f085840c03c0f1001ea41138410101040000c41c0d00131164 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 945865809 1250 945864559 945864589
    0xa0503060405100b01050909270714040e010b06040314060f130b04110a03060912090605120603210304060f020a0e120a1b060306060302040501080f1801020d0b 70
    0x50640c1d2929842e00c40d41e5003807488a4181c2295150100801640300f5800c807041c40340050108101804c1103544203000e030290340311045801050f040c0c0180307002d80101d20001201c801c00d428000451264080200400c0e41c208180f03071300d41d41c40005040c241c0300d98014200560249851a103500b021058030340c2400401011404220500750403c090300300b540030b5003080300b03401102d401c11554561411180394544100d80303075807210b0703000c00000401c06290401d00e00e280c41020010564010044160781510690007007902040e81481340301021100415000d83c4510002e013110549450215200c8101d08071480c4a26030301c3c0700004100c2131010074002e9000c902c1c0341d43d104500c2c0180320f0b07800a00760b1101100d4603200c1e014450000004a00030011424059000689070103c80f003040304180c2139144074481c040210323080c16000101140644262401c070b54040c0c491182a5882d4008c0f40d0078550000c20401650b100761019051406091001d0400141044400a81c6000f400c041181031443e00c140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 945867059 1250 945865809 945865813
    0x31809010f171c050415170403110c121e06010806070f020c0405010b18030a0b0a0e010b0303030a0b0126180a050708030c16051003020f160c0608060118150207030507140a0503 77
    0x405000301f00c1e070001d0583d006815290004949900b50301040c1081702440310654400c1207010440b551400104490041c0300c2c03895500b600d1000d000c0c40c035a0b1541e4091140707800b01d812071000945920701031000052000e9462050340d80741c0d41c0c0900000c00b1210280c004090040b000301e60309902080d50b91148800c2c4d00210b00070032150300b4035079481012100080001c11017640318030008401840942104000120060036a89c136032500d4281e800c01003640300100e50024000103a00b2024500040c0d61503070402d2603a00c8400c15669055164141801a0a524070b040c81111194030100b1403d10074180900f9107270019555038100f0726400d0b4600b8903c404004603170140058200541ea407540d9552000102508000d070312013a0b006142002406000040e0415491101c509400c1210800d0f0341c9094400f55264071805844401c0110781101031080e100300004042e16080c454806203444180d0002807520480d20320b1038aa9480780d0410700554040781241c003004254803410315088040101401082d00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 945868309 1250 945867059 945867077
    0x80d050c130303180b03040614060a150c0c081009060b040c120b1c060b01090902160219050604030602120903130b0f09090108031809010f171c050415 66
    0x140d1900400512006090040c0440402101300c1c9120540000344050000c951302c80c03410b41000d10181c454100d00b003071b982ea501c00000e80340e45004d41451054400e811501482c80403c0a0180c800381c81103030301a500010408800a4010400c0240402d1201d18010115181015244c00c00a6410901d5007500c1141000000710040b60320003120b50040300d440034082141d641460200d040341226520f01045400c0c102440d8080c0b00130340c5c2014240410a0b030307982442d03650b2a01008124018684000303500c1102e50b15071005442c10301c0e64103131200c003c0350340005080c4c1e8610000d08035601c282d10844145130040350394040e00f40383d030aa1940c000b20f007402070341c40c003400403400303444c1c00c0d03098000d5890964000c00d115240d5414070b4156002c4c0607014204800070b5840d440490742c0e0360004001180000c07490254115035045c0a20803504a82810007015051410140410407500103100c542070310b8031905030001d490004c00100701a0100158466507503440c188541102d000b00c60040c41024042107030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 945869559 1250 945868309 945868327
    0x120c0105070303020711100f020609030304020d060213051f09080303090a080a030b030109030c0b1e0c0a030f09121205010f150c02030a080a111606050c03070b0103080d050c 76
    0x203012030300d100d941407900507583d4060f0714000c6500c0b0210056290417000130030707040c1145c0c2e42007034450b80d03810b6064080350403d503507102d030103503176880708582c025000701c2400850000500103401034070360307460358000c96545141c8682c040740c6400a012800c019004980c1c20380741480d86c200b94240e000d40220405103186240641c4143d03502c07200ca0304014200000012010612403095101c0722802c03200800034000c010482c00c00601704006054251817407007030040890000381c656100340000301c4209203030074138564803407241240b5504441c3c850400c0c1030b1584001c115250704c0d841000c0c111880359004903202c50400c00300502c400300d812070402c1810301d40300042c0a0782d04410f02c032004950000d1741c52090301902820032200402e049600a4051080c203000c07408120708000078082c0040d1658664802400c420300c600d540b0340d810a5110000030010b0002d1154921403030081440410950440b031828416586213500104261710503101d510b8080b4105986800a009240c0c011002c0303413246081c10604 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 945870809 1250 945869559 945869567
    0x6030108151f060207060e0319032a150b010810090b0604080105190e01090209150105120c0711060304330606020313060908030d24060e120c01 63
    0xc0c110803110301c0d04034006480900b207905030081102200355080075003580e4078800780d034512243c056080801c82000f8410b00c5420000754000060b0b0146404052948044e10180e941e0361080c044405c02440444200d00b0101c1c4400700103844600c1071000301040c5444805260440701c84407042810840f0035400c1c0720f079801e6082c1204055a82075400040c012400d4400101c8510031944020803650030401000f403842d290710441408104803850038080c082c0d000110074202c86000c0c0d002588641d200380810f040c40360300c0045c540007441c1810239502c1c01d2681c01c003010700c0600858110701843e0000880d481045030b15101000c04445c1a20040e046003401eaa403004160a280003245e48003030210030601c18100440c5ca108940f40c48a20100100780e00c56000035220f074004400700342d19020002c800501c245c4280744002c100d58083c8003071401c003816600500c2c090460440100410b04400800990540e175441c02c400090a03181c07602026210550140090b00610707803001c0600c4e41203e000c81203d83d0700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 945872059 1250 945870809 945870823
    0x5060405060603191b03090209061f051606060b130617010302040f0b09090f0715140a030605180f0f0105012709050c030f0c030c07390f0506030108 65
    0x1040d112103513915414420000030440c0740f0b41e8485107412442c0d1442c00c90b400d036010001041c02074500c0469a5100c000784031f9030807083c0140f02d03080b444901840c290b480c841c80c0a080080d66048181c1d078500c540c1d031641c0c0150303644c98204103070885000860b445c0e000202034100d4002c1885003805035407a91400c0400348c9903881444007a001d00e4a4003520030b010101948a4480000d009104003454201035601035a144101540b810007031252407004601c0f0b051500010801c2451a620011400392000f9a544030b41c1025658105040e1255000b01c0c40780d80364100c1000c1584066410f070b03c12328205a0120402c9406030940541d10401001401140d900c448200c03104510081c007440501903040710b40794481c0f80743d8050303901c10b03180000340003440d4401c0c0021801a10804452240c50303c0d0303040024040d100554404031106003c100e43c0002611501c50082c0c141d41400340d00041c5051405003002c040541d6400081e684000348003404032110115180014160a0b550b6034110760401c240309944042c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 945873309 1250 945872059 945872071
    0x715180807080a06090501181b08060c0405041e020a05030a0506040b03100c180f030b091b0d030c120e1207180b0312120907060c031e0e031204080105060405060603 72
    0x74568080170709200c0250407506000000100d28195003501e130a0a48602c00c1100c0d40104d0320b519500009a040e0700003403d2401940c807004a04d281c1450202000002d0a07030118140d5440840b91040d4103440701e501c09009081e0203610342980d2490681c41440c1222070003468203109500c4d1500b9043d007600c0002c0e00295002d00c880d000207510106150640d2040100d950f0404d0028004101181d8419095641400c5912034486081d2648072400c00355212018540405080b4403040070b450040d10349145480046030290402440451440d01e0f040b4080b1440c500090108078551031186580c1881c0c1402d0740350290f00b0000e8a081d604080100754080c080c4203031001080d8591482c0c64a85c1d0703050124041e0101c0d03882ca02030f50b4100d50361400e041c804007101c1c04003840c000da03200020321b14010382d1048801c0341d140c0da0388030600a0401001a045e86071102c1e9030f0400100c50706400c100d48040103200100b240c002d00841e01c0314642a0404d0030b459004281074051070800d030511100b078807008140e80c1c0001c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 945874559 1250 945873309 945873311
    0x10e0406050a0b03030a05070c0b091003050a0f050702060906071409040207110613030c050402070c050d030221120a0e1c0c0515180c031209030715180807080a06 71
    0x240320b14519102611210564680c107000c00102c200489030080010803142c0d2203401c07142e0b0b9140e540c036842051405464641b80c2c0040c0901d2080711303624802c0d44000d50081c01a0000601840d0072000c1da8100c0314100c038550b02580c00b51081c054110401c0024581c011107625000c04828140c004150707942c080d808245005640100d8190208480582c48203141c803805085039454102e558040348007111244425516414001c0c0017041d00e040c42e0003120701c900d4204082a140910389410b0043c40720348117006804600a00140c5000c038140507560241c5407140b0315480b9158074203004a22007166019091684591400c4c9290840d1000401c820744c003150038020340c484400e0001c00a030f034034498a41d0300800c04d0080040d41204520111036080c052106440054982c25801030785d16503403010000040c5d45640a8070341c2195029421004208801c0b0290036514066a982c21840940300c00e90399650104903a0701584c855941c403c0512001046a0340c010043c05107400e030003d4580d0022040a4055 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 945875809 1250 945874559 945874561
    0x270306180305092209060c081e041104021303050105070f0203121b0d0e0a0c090c091a04081504051c05070305030411120d02060a0614240d050402010e0108010e040605 73
    0x144414040c0c004c2400da02c407400d0000711002d14010f4000c0c070f00f1820b80c40100b031185010075003041c0310420b00180110100e14007003607900da80d1210110324100d4261258010380030000320038140010100d8900840c40741c00045003509150002924180308000c161045600030b228613104004844e045030b80000784c01a40d1403000d03160320180a000e2144000d140c0c41e942c1086640300031001e00180c1402c20794090a05001265110802d45081c2c07952000d260002401d4040c0a0005e080c0c0403054070110900e9650052400c0d80d100000b80c00c00c0b81141001c458000d40f00204002c0c401d080c0072050100100042c2190007180072078000e082c2d4064208054208040440082c041000c00b500b201690720303004000c0703c00740044450160307440000d0b860490060007041d0221b40038080e54000ca906807009000307005880d0440100340305c2c41d000c11015804080e100501c1d124030541034000107056503840304030080368a140c2400050075480b0444480307810400079000400014030220203054100307a1080c004285e0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 945877059 1250 945875809 945875839
    0x60d09030c080703020a02130221070201270b090c03060109020304020103090f0b270d140f040b0d0e0601120b180f030a02070b0304020a05010f27030618030509 70
    0x2081001c1a0010425040015540145600007680c01c0a55100311104111051100030b01020b034060840000c904200c1d418481c00101d00c031821840d4014900d100000d0980e81c41c041152806000400b240000402c2d01d0045080c01000312803180c2c0f0160b010000c0c00700400c0c1350086a5905ca0510034030071b1080c0e000c0b0114003168429002005a01d402502080c5240c07000c0c1084a00184103071408040c06000e00d68052041f03c2d0a40a21a44100c00d4003611020312030040603035280d011030070242e80d00842000042154151500a080a420f0b6018078944a002200451040b210006602d81c610390202e00100202c80d191070403540a644e000244115949814851640c018020144513415019030003200d09211000805003513000342540c202e400e41c950b1011180080e210595000c8c0d00403805803024089035000d50460700604207149014164006900c60985202c0d0814440d0f9400c0303a00d504040040c8204c031b01410080c3c90899140741c85c0c0c06465507004d4428840c1d180d405000313140c00d20042c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 945878309 1250 945877059 945877067
    0xb1c02070c03120306030b010b03160807081f0f0b030910021206220504150614062b090c0317181203070203010518060c030403020a0b0a1b0c0203070501030209060d0903 74
    0x200660303110000d0040ca5864040303e0342160030440d440c071210b4024402f07082e0b8080c494030b10503004082e01e13280e00109460340900d076000220a07490341d419070307820003d000800303c01c00800e80004003030780800582c81e0704002c180141060780075140070840600501c2400c010b00c0806600940290045070005255072000036071090584000850100d014545020041800074415480c10b440e104d04000304030030364499003010540908449a80d80004050001d4108e8869061a860032075418189818045550800750010740e8403004048034164489882001001229582806000d03c100f546030b08042d0301d0300740325500400403007510303100700c5040c000821444030034000c40380c515401400a01452a0030300c440e500c2c0c3c02120545401d41c2c460305001410407040907099034000d40e03141d0302510906055456002030380030003030302e02e802066440310001105010010060050310041e02c8404112426004240c03c00c00b256000d28181401008002110b642d580f00b1070f400300c160340c44001100c80c061b0038111 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 945879559 1250 945878309 945878321
    0x90a0314042d090f060f0801150e070c020a1d100b07031416060912140f13120615050301110a1115010816050f090103030f020f070b1c02070c031203 65
    0x1000b18980751310048416a80d400413810388003d40700940003d65940e00c294201c85070b944039001009011a003e204840c803414203d17170044528a4020b1041c641500000c18a01484d444902c0e481c8244410419a1402c10070650380907400036001c606036031420a10054030b07c61564005d080090340041481600c0d07000303007515900503840c102c6a040050340d180c00802020601d1080e280180c03042c1d8400f0120b44521600b00e5804850b00c140750411300c410302d04400715082080010248081640d02007000160b110400c11b5a0f8050200460a02281010300900840e41d07000340e402a418044180c0507080f860303084628a00383d82c500103c1d6401d1b0078090900f032142544203c4032031a42403000044002c8000b030b400c13607120364500e040740c5601d03a92030410030304200c1602d816821481240c01040030a0140d48081184100c50042c1c40900b040040490306080305600708229880c0301182c00100760740c0c20a0078180800c558402140340070b28503114a07409002a100040c01d20b401d103060810214400d811503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 945880809 1250 945879559 945879569
    0x2032e090510030606050301092f03011b11010b030613061119020708030702150306060c250803030c0f090a09090c05040b0f22090803090a0314042d 65
    0x8010710309006120380c0c001c091501c01500e81505158002c200c1d40b60601c01c80c400f040d4809049000f4141030900f110041c0f008214140c0440783d28801c0e42d40c41c2d00c00780903e86407501c0c02c0398421014000305030b0181007518240b0812440d40e1400900818a4600064458001c1c007491104076200c42c09103044800341a40390700c1c901481d840801c504240b449100003000c80c03450305400303940c80d850712138100950b01c1c0181000079500000c41c8160310490181c1c880210b070001000780245d490803410017503240c54400c01d03020001805601c46020302d480c4810140000103400c0c201c003c0c51445c00d04c0c1405003514003e0850f03031414054005000c0441e5614800141300410024606000c18111401c180031071482c80c0c03040d940903500304442120b0301c1c81c0116040c3c207486401080d00c2d403401804600c054110301340604440c90340f5601d00300000400c4641024510031101030b001004d4254031494010045c18411101918281080c0010702c5003082d08040780b0302c07410012130841c821144005152114005503404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 945882059 1250 945880809 945880811
    0x1a01020a11280504050c0a02060408090d0f140601090902010c06180f0b0106030c050304080a03050703060b1c06171504030203070c03110a0510020a290906150402032e09 74
    0x200d5003500c03415104122181294100705c90340d62200512010312402002000680298000600040e403080180210f04130103440081c0443c00741d0b2390100c070344040c1003041c1c81c0340e0b903111400000c0310420440c9034050301c0c0c112414820200140d00203403942c0d940d400002e00d215190303462403103148d080720725403900c0c00d070081600c586c1c0e81c69608150001d40828011200000e0400c000c101c4004d004034110703401032b075112240c1441c200407008120300904000e03020800301744c0c442c4000114035500b0b84c045e05020304111841d01c20303100da101002040302d14551140d4080f4443c00011914510003040544c0f12468002c21040d00784d81e20b140481c218840c0361401030103017034802408010f00c02c61601d8448564410340302c10701c0d4075440d5410000e2143e01c5103100001a4031002d5440002031380308807003103810200710707104420030710581c0c40c18200420221400101c56001c00d0400c0712001c3c51188440d20380d44161411491403c08000b000444100b009604a02851000788440c4a8102609480050070a000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 945883309 1250 945882059 945882109
    0x50322080307080f060901060c0c08010c030e0c040513080310080a110301150e0118090609030e2805060a020f070e0117060c1b0319020c041a01020a11 66
    0x150051403504181c0e402e40019004100051000e10003621880c02114003d10050450786006421a0090340001080b200c0e01041c400018154401340600700d86401d80f0344010400c100342d0100207280102d14220030f841982071900b030050242040c068019105c1d000305400341d9039544c0c041400c5809015a0004e036203489401061070a10a407010525416003044000380044400d8000400440d0b0f07880c0250010903550b00010460150383e4801c0c6810900b0841020850840c1910782c41c00304c4509070070030b0300800c10380071860b056442c0c401c041c0360b00c1c550a00780090000122059200545100e4050180510000140345903101e00802004180012000031255a0768540b080c415a21500b807140c0658296100c2c9900f01200f4085810f41c40307040140c1590781088001e2082c0b208000f00c110044c500c601007000300040d90780d20030200020200d180d8006000070000041800101d882c411340404810003100030502ca140c0e03020413503c5410350020f00c03880180c14158001041c080300902c51452581c2d21403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 945884559 1250 945883309 945883313
    0x909060609270a0f0b0f100201060302060708030f09060907150512040c0503122d04050315010501020c0612160509060a0e1005040302010912080d06181d0d050322 71
    0x500c10b680300350b41c4400b080c014100088142c00c00e4600310740129a002c0510070040340c15007041505813164640d0392002040e540c1c3d4940204401d41c0c044681a241c0700c00000c100320300b42c0301e954649a088214000200b00c0c9181c00f4042c1a103c040d640125a1076140352059a5001c4e84680142c1d4849030344150041001d050503c1c1000030b1880070704c036140c0240900c100b010420300510061702c0580c1d180d900010740c55081104900030035604c3e08000120500140008240e50300e08202d040c0034a14221382458595052400280c80d02540f440c2c1c061140c40b0412101e031240c00c603c85025080804030b40c09003140e00d241c0e0310540d418024143c03526002040402d40906107684880a030515140c11348040401010140d01105c05100354040030303002c2200b40401700403102110708803058141c050711165040c240700e00c0741c0f041500c20640c407016051440000381201005588a00c50180441c1c403000c03100000311031881600c686420a100b404d20202100044407040c541021151450020f46901d100010038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 945885809 1250 945884559 945884629
    0x71d101809110105180603100b0705070623190306051c380408160f1101020f0c0105071103060408071509150906090c031211030909060609 61
    0x2000030b640d0350451484540d590b5000b01e048032030100c41d07030b4500d48107002060140b000c075070700242808003a40c40240d0005141c0d51105e000d400c0d098441e501801d0690718028006100310440040c09003484140f507910120b50f00104201d803410444e40c000c1030001071044200b0340007030505500c82c640010000c0701d80140d2001d580c07410860320348101a000301c880d014010760030394150b0b03404207504404519010240c82d80701c81c070181d55000b4494054540b8100c1034410668220819074003c860400310f920380b5100300310000750000c0c2008000e10041c1644040f0704982e0741e5403102181218144240010301c9403c0c010389921411090102504840d403a0802c1e04e8104240d0b4440007043e12005c070400c12803e4007079614011a452207402110300982c08501002d05e0008205100301100e00665401d40400010050708000e0015401495880b003600310740c00c009070007440d1160400c04640c00811450085584151859130030600540e91a91244103042c0410351030130007074038442c05071840c0d1540d400d030070489 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 945887059 1250 945885809 945885821
    0x17040303051e01030507050607150e01090314070210031a27090d0e0103110702130c08060103020c1b03121206011206060507170409020c0c03070503071d1018 69
    0x10550b41c0c45903640100141c140541c0081c00000c00c01c5c0c000030b40400841c541000901030480c0120040c509d180d140307003800c2044030301d0b6a000300c1e2265194404038050503001212480c10380040503819103803220310742c00600c5044294124105050741c408480354405001102c640d600c020141c1800d074250355113401442d5600c0301441c500001000c3c5030004800003c040344501103850303103403200341e100b038030b000c00540141c0a003d00189206800344032550240c0c1e00d011400c480c00e540840c00003452440382c20010f14019004081b141030500400c00509040c00004444001e1501005101c0301c010554002908101c4043e240241c010400701c0e10091040c44810001d00a013800d1722005080c582c134611030000d40303a482c4034200204c0ca00344440d2010034541e42d003d03400b4003462900309103466100e0714041c0403030f04035a2311140307641d100d80080c08460034108440d00240c00c0072002002c0007490702c483e035550b03c0c1880e083d0f26a58003101d07021920b40380c0c01001c03000282404030325000070002c41000b040010b0038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 945888309 1250 945887059 945887071
    0x2091b16110a08070b07240c121d07090f1d0d080109140703090c0512010f0f0b0303040312030207300f08071b0507090902090a02190806011704030305 66
    0x151010010344150009448801c488102840c5406c0081946400081a084040120107103031000d075002143c0030680700d500e903043d00c00c1c1c641c1d800d1840b034448603204503120700251013524480c040e0b0099105200140c02030841d90081004030700700c04402002400303000c901da041e1084010485081c4005140860704020700c242c1a600c001607682c1e941850700985184928000400c0c00b0313400072404a0f4840e0f0010351b0307194002c5207898520343c0d0340e401003502c4c10400340070707005c059640e03014545084109008074421000c0ca01c00512040890790000380d240d204a03c002001e065005040010b041d019805a03107006401c60b4462030780c00c07144002104000920b04400c099118101c8043c2c0300e0070302507142003480d00b00c59070300c484442d0380d03144060318841803e5411103540c030144c401d202c1c002131040100c0030140260590108802d881481840381e107034000390185140c103005000e4a07900c415000e21a6419003414501503a1580340d800050354242c4000644840307104600003040149034264120f280109 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 945889559 1250 945888309 945888319
    0x90a090509010618050f010e2d1b0c07050d020d060f020d110a02070302060d1d010e010605010c030507080d060b0c0604140115090906060b040807060f0c02091b1611 72
    0x40c107040303420800c8401c1211441b8503907000c40d005110103040d80752610740c804814a440205984503640b03080c0c903040d840904026000601003004030084401022001c1500d9203a0640d040c003208a02d22501d6075014060580940c421703544210a550300c0f0341105440301c0d08201d003007201c1c1d02450540000303036214642c0010f0460910001e154031402102c1101e801d80c0301503018001c0c0c035007160700300035855202520341c0c0d04c0700d5201c942c040c40c43c106140c11b980c8080381d94800064079034441c0b140a400d48039140e01441c1405805400000482d030010100c030880c95108410aa41d1454001d40f030300109110b81154100d598040b415103011107000807502d00442c0916104102041a140e4180c243c4182d001d408814a07411081000180e80680001000501c14030340810a0b80c0c48949055164200d9840b250710784e449440100400c5030030050038641d042c031515081a40b201c9540108000500c0a4031800c15840b1028081006c07009240659041050164408031485440d050202444108090700703403240d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 945890809 1250 945889559 945889589
    0xf0d030f092c040201021204080604110109030b0109050c1605060a0f2d06050411040905070212161a0a06031e0f030c0c151d030109080d02090a0905090106 68
    0x1141c001c035019404603008582c90070002100500540c5822019000b02d05600c5180040d0107061105170240c006003441c43c000700300b00d00d45410484007612100d000740b81400303003078601030011840344000b060546480c268042125194504588a14410041078a0740728000c86081c4042080102d0824025410400d09122421000180074221006d800c030160611501100903540c1c0d00300ca803680410f4105164001400c03e070384101103404c1e47c00e0b1410500030210001000c3c00340c4100c0e40f04840e0411407505c01481c8803542410100c03420302c41c0340c9015544219041c000c604011100030b0402d1440350079600d008480c01d0000071071015088a000481c0d1300b04094a01600c2844a6600c0d0b8580540090400e40c10301d02c1a1000d44094185c6030007500c1042d04c007440070904c0d104900c80c500ca60b98080d41c43c00380d0480f01e02c107151000090261b02a00c01e03410542c0d01c001207940403081d0394035849038000050b42c2d8183c1000003124002d0b0f550019003120301f41420400c02000660204d004c49842d03000020b40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 945892059 1250 945890809 945890819
    0x170a0b040309141e0f0a21030f030b01210f0606050309010f050f04020405090a080c0c0108060d0209010515090a080d0908031c05040303090506181b01020a110f0d030f09 74
    0x5148041200540c4182502001445403070680c01c0c0100045c1d018026003005612007046c0c590010080100000c039104182d40c007010540d01c1803800805056524042110324a8400006d028500c241b0740e95620003050b83c0c001003190041e91003c943c4580030391040001c1c9507220400340c5282c104540106480d4a0700d1109241c1460341e0151502c03514500c0042c0b0a0f0740e41c0c5500700300081801428902442c0f1800c054000001c1c04007000b4000200f9150050000080c0d14000601e1071100410003800782003c1c0032104d00603291001d449054580446690101e1010801920075a000d100907240c1c1c01164003d00082c3d0420201c0d02808880050743c0d88a0328a440321001540c81c4661110b21800079400d4404854002c00c0da4008d9802c0741c0704c1d241c04a0400090b440d820300d80130050754800303070840d02c1003810707601c0e85810040c0382c050100c3c2d5108a00381c00c11032070001c5d444000307580c00903040e03842c640d140440545d83c1303074242101c1845c02401c5003061071040c2170051151004081a07800f041c074003500491 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 945893309 1250 945892059 945892069
    0x110d020f1c020304030f0804140a0b030406051816091a010203031306110304110301052d040c030c23030303010f0b070f0204020f0705070e0f01170a0b04030914 70
    0x21554080000c0107041901c42940d0003158803200c2080031070005120200000305483c140704c4981d4001d039040b5448900309802c164107114031004c22407103800c842034100300c11100c6000b070341d904c10b81040300020255120700e07000c000c06035252150f031300d00d0080704100c02d001120001c3c04425182416810845c030711344544141c0107500340c080601c0c05070780140001500240d08001802809e803250001262a03070480002c2034003900142c504640c20b078000d02e0301e0440d5040c24860a640710541d40c2107074a69014042c1023080076050080c0207440c1d24140300000302841b4520342020011039024821403031640e070f1684201041c0c41d440f01c0043c541080700c58002003070f16002080d07905a03040c0c01e030020100e615086001c11181d10910381210040b61040c641d60240c0da6900c0600f80c3d0020080041d80da41d1038902d071090030000305400859114041d4070500041e03100f4090858151405200401007030512407482500d0030382c80c200c00500d0848030034208800c00d039000c01c200c000c513a480d4888050042c08441005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 945894559 1250 945893309 945893323
    0x403032a0813051203090f0d0906030c0207030c122f011b030e28080c030f03130b0307090b0a03021b0d023705010515010503010b0a080c19110d02 64
    0x6031080c1e20800d420700b00c0c00c0c1350b00300440e00980014111038084c08101e158901f00354074007803403d010800789142003190b44d400d8060126415003c0c4042c9c0011411a52452081030707950003522241940c0a5a08040000103001c10702002c0f60403002003024010a11640d81e004900922640040d40c10341d954103840c0108219115281e61540310744411500c00340c140002d02e0860741c41c210035042d81e0390b034000303a4406001c041009401a00040c0c0721941045081c1032410040030490061580204810425083d050460b00150744c400c1d2a900c5d500e4541c040200c6003065160850300140c50000384c401c01c80c0d90507500415148900100c00b00303500c11382c005019162035404e014030f00540c0001802c0c10081640f0344c000820744503101c800c180c0c0c80c11405410061811480011525a9960418071080064003652140c046809180161556041c4107910a8a0051040000c2440381402c04151b80320b000780251115190f8449e01c955122254800c0209000302c400c0c4442c6d0b4902443d0038003400f291000c5400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 945895809 1250 945894559 945894563
    0x609080d05030109050406090b0f01030201020628020a05130b0d150b090f0301150617011a0d0c0e0d080711031b010804083702010c090e0403032a0813 66
    0xa42c1140c2c0303010165009840000c10440c1d901d9580c5d02c0400c005110414210300660952000024540c118400a8074100d0080e04600f003104800b41134250b0407c10329003038106091900030243e02d0310f5070108291464040da420010512146540100d4000ca01d10064070108440400a102a980c2802155645d07440c0d402400421030003000340d1a04d40c100740f0700220500e60041d0000a00d0080c50000d420280300320780001000130146824141160305000c800340c05000f08681c01c007050545189003400030322828880401154848032000c103030b035006094001c080d41015100d03030000c0744246042600e980c0090380807101700b025411240c0940c00c0008201d100402d019141800308008078005580210f03005104540440007006640f21281e03d03850041000080088005510301c0c451501d41c000c44282004901168036100c9407040303030b55010102d03808455a100a40170513441c0c41c1411805442100752589079050842040034224800c420301c44460b100a07910a20542c035038030542d211002601c100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 945897059 1250 945895809 945895817
    0x31b0a0503010605280302070605061f14130f030525050d0203010608030c070f060e0307060e01050904090b072604141603110f040920060408010608070609080d 70
    0x40c040700b1301403c020170a07242c070070241084440321003101c115003505c8904000c0c000f94020500d20300304105070103020340001044850446030201c580f001240702c000c1c80d00980820580c0100500368410700e00c100ca500c0c0c10300d003000790b800380d0700c48402d448000342c0c6101c1240d461248680ba0250340c0309103511241c0b07401002c050a17654510788010843c6118040e00e00b030340d040d5600c50000400380d40030401080100b00c06000380c001c0320719105603140794210325030285003400205140181c050f9800701c0c120702501c009081107169940d000d40100c0b118061442c0c0a070f002482c100016050200104038540704d107456549060b031031120307014881004100300b04002d054811420100d40010f8803540840e03850a4270000712103120884c0c2444600800c070030b92090b108101c220042d4642400e00451103403015809507014456081a0f030748407040e0700d44075000741c00c0901400078070051956450341150014800f030720090103029200c2e082940c0f540058400c14021a4510000042004001c90785c1c1d41c4064030750f15 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 945898309 1250 945897059 945897061
    0x70c21260a0e070b0310030203012003070c240515040204060512040318170d2c1207080705090a0c09180b0d1a0609090705060708120c031b0a0503 64
    0x2109002e0480c001002001d40284500403071100b0b076100c0618400c40249140f491414a5801070500b1128034034001c84240f180701c0302c44c03040f81e40b440040729000300c00351801002005480c02c000301d43d100c1c111000500503ca9a8421a107400705800c801e01400c1511042c4070b61100d42403c104c01c9100d030340b064002007202401024030320030520b5089a44a4001d0070960041460b6501d000030701421904609268000e00909031320840c42000417944501040c101220000780307280615808841c5000400141944c2115540c150f4030341701c4440607030b042410110781e0a0394540d1101070b290480c500178103014000810004c0d410f020180161005050f403515101c9409040c000380c0241d03c090700c04260111502c40c040100c0d03d40790b0344100c5202900582512410b10b100040c00b00511a001d8142441004c0a109004800c4004603e01d07041722030498003103907034400c94503000083c2c4c0503403540d61a408502200300610545104000d600ca495000552070380b04e1207100003843e15015032180d84c400200f082c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 945899559 1250 945898309 945898321
    0x1c02041b0905062116020c0f0913031e023a050c030f0d02041401171302030f0601060215070203071104050411040510050a080106050612070c2126 64
    0x11004000304c1a02aa041e0807626208070701c0891044156600e100c802020502240e4259050000310b0038100c0c12030742000d1005018001850165020f06458540401c4c809110704060150643d207490300342041052412410068001e52102c0030a41c500c80e9442110b01341da07003c070440c07800c0c1c40891820000b14003403a07d107458046400790802c04004c81c140c40308021601c220103810014103d1640e00e0302000d80d0f90307800d01c410080f1082c4001d0b15103042c13140010005408101c3c0c40c0f600b50f030080003035201803d9600c80d0300010740b40410340d003881100c80c000c4000108030580d0115601e800000106860445900c411030100e0f07881c45a0000948107002080030048946055040107802c01d00030307410101c9c195141c2c000034046a5040e11303500b00d5413505000810141c2000c2400034000c0074008020800d151a1401283d154030405c03c03d00c0e03899140f500000d41e61406070850506490b00202c0b02070892140003040f554425a828040c00490003200d030a161010400c035841200f100303c2000384100d61110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 945900809 1250 945899559 945899569
    0xf29100c05120a180f090b01020c011202090f1e01080601050c0c150403151b0314011208040f030506040516031e05031c05011502010207021810051c02041b0905 70
    0x680c03294208407003291103143c03081c91801508043e041d445422104e00d0310300441b060444002d000380c20306640210b000301005a8120096184003d40d0b4000540d42e6042c20001508490381401019400000c04814030210540b0a06002e5113090a888070346240c1c540c0c0c0e00555541c050b03502d6500d115845418001c1550600100e4a90650741c00c031030044c14103403295110f00c05040003104240310580c0d2041c000c542c004060b65520b40f10001414204101c4650001c2c101401805005800c407030020381c600d52007000800011240100703140010a034540751240703040f42d01c1d20310595080c4c4491040351070142d00c000754005041c085a0388405441140b404482d5070f1003c205281000303030f4041c00184401d26084200b60300c04000640580800100c0f90b040450640280c0c05091300c4a08683c81808118010b07100c503a001e04490300c01144049013550b0781c120070191107007560030198200701000d00021480d500031500c914460b01c21281404001c40e040b80c0b064406d2600c42da90400111a80420000ea00301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 945902059 1250 945900809 945900817
    0x50405100201110d0b031e030a08010b0a0c0809030a020d0b010f06080c180111010501090b09090a050c1311130311030d0f030f180503041a030601120f29100c0512 71
    0x1020b005d60766108806980c0f44101202c074525020315802c005901e400098ac4284000d0151103e0104103003001d01040c80101405003164008000100000d07500109503401c001051a69078000c000a4481c800d52a001c900e07000e0070b220b00c200001c80c000001c544140102402c500c034200107050941080b800e5504c108080501c001d2050500038180100e200070542030140781c0c06442c40c80c5010070340c1a08407081c0b2141d00401030007481c1c01d0304410365000c0000c02c00300e100d20072a041190410b4007510800880b400520310318200030008100007c01c07507500128020580c08030390182010400f0080350f48185900c0e80e207500c0700c120014580743c24101343c0038002c0c0d000e0032001000c11000030364140c2c0342241e842900000b00056a0541c8045020030a5504031101ca0343c0d28900901500d085050481c00608a004400307074000920361601c04059881d60680e00101c05002c2c0f40c03400c4281861a0102c012820340201003050103040a001e0b240c03072450140c2c007105038103a03120000b40104d298242132143c40d504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 945903309 1250 945902059 945902081
    0x1503090317041b0e070207091109210105040309060f0512010504020313080f0d0b1e090403030f2f07050c151e12070e0603131401020a050405100201110d 67
    0x3d51440910340c01d2000d228200003802c0001c0194410342086203011b031519981c0d078010041c0034101030560501c10720313030f009407003101c0c80c02d44000305030b41015200c00105034040207061000d50310300000c001c10f150b0b00002240c1181d100e5190340c500e4405074201181c8074443c01c0455101980003030010012030820740c0c02036a20410100e2011303000c085581c2d41407080e6004126000002c900404c0703450504045100d0b43c1c03903008003200d8a541011105100e910103000c6002c000b03104c0c2481500203003e0500a400821005100070020000e0403420038441c0c08039500761109100c0b04802188000030040c4100880e80c82507000801400300512280c01c2200c4040c40842092031460107100142c4c0000018110100ca5808030900071b440700c00d4401c2c1040c80703440042145c000c110718884c4060890302d500f0308603a01718142c100d601c0380450143c208090003070182c11000d10290701c0015a42500c5a10030040c00039658201d034221034940d0514822401d0781c841d15445080a0005c211303207030362094644d1066007100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 945904559 1250 945903309 945903323
    0x29010e3904380412060e030d06120311010e100917030709140618100201061a04030309080111090112060f09091a0928020d060204150309031704 63
    0x1984480d1405000c0b6006060b02c4480c94080d0010680702841c0c01801070000008515103007840d1a19901c90882c40351071038044c2c10180e8030310066043c807a041c4122901c440c100e9030288103490350340c009418401c0d1443c01c150002400f912014422650602440107244c281200030a500103000b220f01e030003401c16940331240004040890b1381c01d0304074840658030441998507808052441d050784020000c1c0005e0500b0301c1804100421003030700c001d0844a0342e501c042901c800103d030b580c100040e030040485401159121a44a20a0001044850003401a039100e036640c444016942e102d054240d40c80e4405010364800d0030f000c0c1020075403289980c1e070303007400388244d010840941d140182022554280c01108c10356494142d01818007044410002a182103503034013442a1402898040c0ca80c81c00c5100c00c4600544000b48807102804140d6403280940c0051001c1c4e4001c0f241c0c904440203501c14420500044020700c03240d09428042d1154003490360b015140c03802c2202c2224002c110740ca00082080300c5003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 945905809 1250 945904559 945904567
    0xc0117150f09090105090f0307050a03050a030f060f05030c1c0b04020a03080301090c03061d010b0c0a020301140402030c0901060207050112110a0c0302011802010c0f29010e39 77
    0x79611041010f01035a0701e100001500c2c1041d090003800e21280c07111420b50341e8020002540020b000003916400e80741c15182030380d02d5006414085000e03003828070800d52100d05240d800f1a145500c1c003060b400705c0e18110100c403000d40b550300a02ca0022400c1003040781004185540c94089401c28191643c064401030281c2070903a10396949440c5900282c101c188440c0e52140380092054040c800d08002c1d0080b40100103142d40d05851aa640c14014010880040008a10160300c1302c402c010307030127110350f00030001d10903079801145500c00c02c40101d400f80e100e8808c600c05640103040070b042c910b0585030719502901016060100540300c0b6405848842c111943c1d6080d10b160300404000030300759070040caa5400400300e12034180242946d0603d6840450350011200c1800144e80182ca4124042c1d480081c10070350540f14181904650f601c01d0142d441c00d103035000448007402a600c0c00034180c0b070030329034006460b844c0d00850b00c0c81c00f950b01300401030b101d4a200d05142040b03000b410a00f05120b1240c04180341c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 945907059 1250 945905809 945905839
    0x1a0306090703090b07030b03372102031201050a0b04210606030f031101060807060c050f12070c0b0906070204022b09200d0f260c0c011715 61
    0x4c65441203a452002950704c10000030185400e0000350500120008040f444000038080c0a0140c1e000c4500c0702c0c00e8001880b100c0301041484043d0010101c410300200220030710004020b502d80e072040c50000b04068140c000803415262000143d026666506c1050b4101402c1c0100f01401007080169a280c114400f170081001414900805000e50304c94081020405071624026046400420301c04d542d60741082e40a00c801000050312004075080e9107040408080710f820310900b000c043c03030303520041405002c1054100c1840000108505071241c551035202e1580c448441200d8002c24070760b6548500200130380c8015203081c0c0c000e0410b8102580f0180900c0c840710f904d20009400c0c1040034418035880f01185000d000328041d40b20b44e080c45c514180d400b1900000300046507058405070042c028508481c9000a202184810800000c403240075007100070100032480040d600181c0751014688141904002a54407581100d4002071800300260102d484450391180369541c031a00440e0000e00501420780303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 945908309 1250 945907059 945907073
    0x5030f0d0f120903030605010201051e130c09020c010c0909060b03010501300f0c0e030a0b0c0d02070303021c090b0609090a0609060203150307030302120d180b101a030609070309 78
    0x41c409204c0d40f000510f2910f004006400c3d698014400c1c4414007508202c156024900c0200f07030b03803195401e01d140022446600d80401802025002061840d00c04161404031920541c0f0581c04c42005441e40401159643c0c90b0f042541c07524003e060384001c081c0010803803940511210aa00043c4440d000750107103800310352300791090981f080300150503260070210341044000c0c400c510b00c1242c18505040454400404282d03104d442e0700f40208249030386000100380e00041016260955650b46042d9030390152810010047d401400c4203892030699044107801005480c0326a680e1079030b0104103101150b44482c10411100002407403c180d90140640c0e803800900a032241c00d01c0c2d03501c203510040c1c807810401e0700c20409458a00a05003e54070400081c0007003600003031030b00811102400301540e0b5403078560345d51003d0b110220b0f0402d40d54100007900341c00c0100d51140c06115004c590880d4040d19613030301e0444401070103910030050508c000c00100b486800c15400c0303a507002800b403d0100d04c0d1040d0742c2e100340d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 945909559 1250 945908309 945908321
    0x403110f0d12210c090e0c040e09060406051e0406090203011113031109190c1b0506070e06090a060e04140c0309010506010e0f21030c0102040f05030f0d0f12 69
    0x540041d140600301038464185120b072106403c480c09040110701c4009002501244d42070040481c0700080c0c00003d900c0c9510401100c02414480f58011468203005407402e076222420784046030b04030f0900700056100c0800350101d41c00030788181c240c0051a295600d80d0801003014040c2a60155201c42c0c9c4604034503816001045c0c014001c1c00340f100388902d9800c064580d21651114144215001000d00072014007801a401070f220740458002041e010155042d610350702c2c010681e40240ca0b103450710340c0501c800403038103d10548094031004560f81c204401c1207400c2c421000c14507408410041c0902c01e051080711851010b40001d000002c0d10035103031041c416038080c200c0702210990400420404603520a0080580100081c00c02d000440000000240d054800c640340c0e03401440400303003034808410070212004c01580b40c602500d955520384000c8a020390700600818006205503100007a42d403c000075041c0c207442c0c0010103840d01074400e00c0c003201c281c206c1c1c030304040c100200c24100e516020b2040c0b10b90 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 945910809 1250 945909559 945909593
    0xc030a0308281a1912021e0a1d070305040c0b07170f0703020d1803020618090a0b010f022d0a0c08030a030c030e06070809150a050f0c0403110f0d 64
    0x4014000c030749204009140c042d06440000c0070420590030041d03008008205c0002ca681150300310b51040f200280c0300414050741100d81e5200007004d01c0091200380b0307020141181d50001843c01320070750b10404180d080e00d0342035500410b00d229a4104110580034107014180d031610901190210040f2810140c1694015011002c201d40000540404054042007490741c0a80f140c00e00c0d615444001440012074100c511020707006910000ea68211610034040c00d14911100030501080c40c104203940c04001d0202040c024085000a0302651a440c0001448004006c40c2030720f024040c4240d00114205001d0030f0303101c10342841074140420009407030040380000350140c80025500c500741190300a00341d45800320640c0901d442d2004140c03114001145180e03200c1c2c02c80c246007c00341c40d40175429182c4084880c1400844c4a1541404040841d0390000740c000e603000450f5075010b4460203410f40c5144070390701c0022724000c42d1400c0341000d800c142041000c90b001c002d1075012540c600d510303040300040105200f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 945912059 1250 945910809 945910841
    0x62d0d05010e0915070f05091c200303070b04081608070624080d0f02100609060503010b010311160c030b0f0f090c010909020904150e090c030a030828 66
    0x20003221010411414000d0f0715014a144428186141c000d4001b206c45600c000400038005591503194540038070405072000040c032040282c5200f03042025200c1e603004104007000c170945a800450307140000a0f0b60f0980d070404081002c079121555000c0803640240b222881044071011600302007555003000d05403190103078102281c243c01e5091003100390802e0f051130320411340910000b481824800582c806424401341071110b0342c850380c000c1c180c0c602204040344182c224104a000710308110242c100c04115801a0028031481d80000300550990746561101c210b01e22081c04174407d00d05100410b048018022840103404a44070f48400000102c12590300b801d1203a24024440c0d4480007420341503000d070810010705a01046a80000d000c10414860300d07140325000300380100555610f51003c1041442180c003a8041503481a030404640c004440c0d00f0faa0f4003a0b114400070505002c038107102c0642e451340d20046581c0e94000d018202c14010303006d82e1803412200500b501e004556104580f90040c9801c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 945913309 1250 945912059 945912061
    0x18220803070305060d080427020d060f0905071e030603080a260402060301060e130218030610120818030703030905030709021206010e120a0f020f062d0d05010e 70
    0x7014081e6900500001d010f101013800050100b001d803010380341501d00c40154a031070a02e80c0204d000400d44000c10100c2417510004115800d2080b690196084070306610420710025520941301040f50012606000401e100c40042d111840304001544000c0740745081c00190740e0345a4032603814981000c1c3c18100410303600c1e201640384807502c5110788071000c0004e051031100e01d403a41c01700e000b5000611440052003000c0712101030301c2d0346407021241d10303840c08502103484003085085105003901d541e02e200e0103070081b80082101d440024030068203503061580052003e401c507549034030741d0741d01009840f0341103d22906211020780d801c0c8011001107009584007c00d0700e007400f040500341078582c0e200c1c0c2304281c81000a8108950840e94144d400a424240340308010740d01030116000c00f500802c40000d83c001d0a154800f0481d80009910540340240d900300343c6a080359081c0140d034450007201d081217010268040c028800e04100d104003100710624600d003055174000b9400d007998020781000086c005c501d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 945914559 1250 945913309 945913321
    0x150a0b122401050306091c02010b030a2901120210140c0f06070e011b050705180a051303020616030204090f0b1002010c091503060f080d030b09010518220803 69
    0xc0341c9a409000110090609403c0203c40346558000310180441a85a503540d40f1018500030360200051207800760595210306854034144240c400f01030041041f5290b04040c01c20700c0d049401310325042c1c8031382e10084c4005441640801c508042c01541d02c10400c0204003460061203505400b07000306529260041c0401480c100c4030501301203005040e1001c1000000d0030200701c0c0c0c0c1c00201c04031051403211700085c00040c14242642840300d0b680269802c60309560701860300e080541c4c0094130508007003408101d59244e9011301904100c440f01d001e00103903c104041084118801c90014610341c82e410018030f811f55408413401a940038064000e00c00f60b0714405800c0d40e00304040c4c0d00c80c0d41103451000300030000c40c00402801c442c803540503408415071220350310b210395406540240b001d03156840180c12003541c0c51444603611010440303000c0000e8107010008083d4201524024160741006014851856481d1100302c07613194024120a00a604007228208440c4800c611141c0907004410f542d650b45058 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 945915809 1250 945914559 945914623
    0x204050105060f0904050406020408060702101815050712061202281502030702041d1603031b02010c020a0803041d070909050c090a0609080f150a0b12 66
    0x5910150007000100040e42d643d141d80b0045842803042101e00041e03a480d80d041981c020300881c0c00c1216140f1442040c040700130340020711020b4444001c0030903c00b40300c24aa03d000e6458604ca0010140f0314940036500c00540c19030042507000d842441c002114400030503064055920350303408413207802414250a410b50a20126040f8064100c070151408424045405407890440e840746484540501501d0310100307209101321022180c00a00a01520a100900442d656032100441c0414407556007000d0141d64440e015004698150300c170465040c00111222000b00c1d07030440304a0400c10018007290050742c6d00744400307000e00804401540c07a2410941c00c50400310072002041030400342e52040040c0a503002d20f282c3c080d9140e0402c04203040e11050395801c124042d0b015034543c01800781c02e0105507164008007280843c1c9000040307604141c40d070b01c002030301c0e5401883d404030040d0454000910b8410a90040905494007401c0d06040d101240c122504017030a560b10440400300b28028100c900c070740 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 945917059 1250 945915809 945915811
    0xd0e0a1520070201110703080c03090a06030b01091502032a0c0316091806140f3102121b011805011b050715110708010b1018120f020405 60
    0x4070610800300d401c42240006401984002410401c1503182070300c03000000d00044009503440711001340c0300c0381c50b419801d4407038103c401b140380a18034035040052264440c0c041e003445100183c41da0f0100074107010482c0140c10b031a80b07581b41903100c10000b19180391010880c543c2500e01e0221600b1aa0040c00d2280b810701030f12040c2c86200e548850409001e500d0703403e003804200e0300d2080c1e00280c50200300c1d4002101ca40840000b4185510708401c0304520002403034010b11070040108400d0107581c47c05800030405099081140082c6450300c21103118441c107030141e0703000e04e000900c0c8519103408030104610f130005248116981c0401e5003280d403081d51304450300341c403084111000c26a400b0f0800d40024030850400020f45c0322103000c04000e006011050000901030303c1607142e400d400c644416400f41500c550541c6140c1d4521500714002005013041c4640d0200c490000c1900790040c84186e0211081200c890006414005440b000a4038400c4000c6903c07980d0b124141803410110b2500401c011a28 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 945918309 1250 945917059 945917081
    0x103060e070302370605030603061008030a0518040903090810020301151d03030a021609050c0a08190c081e06031c030b0a06051e0702030d050d0e0a15 66
    0x201c11501400141e640810030000808800005003903011380c040c02224080381040d00e810007502c0188080344480e4000029071140d1000e40c00c86905454004e6186040121131083e03400319041030001c030843c248a000203020400791411420400d19100c000541201d0014104902107603c40c2000c10659006020150080c286032800b181950f1600c0c500c0060f000b401b1541004105410b0150300c40904180751109074003c002c0d080740d031504041000a595204000101820741210f6100000e0900ba64060702c0d1243e40c11820060800340c520505403040c543c0940304155a03081d01010510359944d501c11025252000d5480c2c80301410250790300301703918817118816100301c9501c03010000103440020341800c3c0004442c0a180b01f25540b0b0342d04030004c204120343d069000070802c4001800c554808058600098406060401350501c1f81d030500441c0b2a5090080d0140c1000103d01d58060041d0003130000440c4810b4041020200100c1c018182140700e402280c030300da01000000d00e100300c903100d0510806 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 945919559 1250 945918309 945918313
    0x270403080106180501030902121507030b030c100c03090e07050306100f08010b0a0c0b0108070501090f030309032301020d0e06070f020606040c18091b090605031b210103060e 76
    0x1440d007541040d040c180c3e40a800d0506442da0010011504c90030031300da42004940041d140d00150b084d80728880001c0c107461201c0001e0130305040030392500d4040342812006034010004031003016040c1c42582d01e2000c594069090125800300000c00f107440c181c146210f0031007655407070343c0e03843c00b502000210420b001480c3c00300484400080450b0345c01001e070b581510400c0140b26200c003542c403011107180360790301d00c001d1061080100000c4c008400040300005c0c0c0c2d10988465100715150024010700170b206200c080d000400c54035003003001c15202c0f01c01e41081344101d07000d80e0f02407400800c7d040c26680081801103000741d17182640031407124148001034104000b40703020854020444002035861902620085c821a591004841000d0241402455034046041108581561001203000a015900801006450082500c4480d43c410307400031098524a45500d411030300c5d015804071203040501500c03810080100203003441c0f030300b04024440003903088181005040d030443c0703043c6042c0c4140c607000890329 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 945920809 1250 945919559 945919577
    0xb0d0f0f0501050f0112022104020f04020703050316020102070827030f07031e0c120506010b0301050907032003180f0613080706111308010b01020c0102030a0c02270403080106 77
    0x180d0745012103410b10b40000d18007060402c2d15851b400e402071103060000f0f520607032114261056007801c0615213205500813142c03980806400303010b1000340d109084004001540401c00507004942013203d6501400440c40010308105059480c08d606621103440c0c5040001c020841079220716009400290ba007000b603001d0002c07401561805991074500d07000c0100000382d02a10002603401040e400c8003125000400035108560350f5200c0450b1503121441940c2d0303800b0380c400200b001010407007241c1c101c90001d4440d80e4a0f5031780c05800c0300200100d0720310300168105500e0003076500c0c903154044d40c05001613056044120b90180701143c940944000c401c180f0381c00c51010000d464011040050f200c03600040700315030b9500c052070150001e01c5140c10240420030007051a1a100d011074580c1d00076182c41b00700070021804410016643d0721a481940ca005a03c100041e400c40c91262100703041480c4094240c0110b1251284041300c142c401c035900203841d00f12001000180355111142600400c01401c0c02c000e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 945922059 1250 945920809 945920819
    0xe09040507330e042d0f020f1201030201110327190b03010512241306021809070305040b010312120608010c0212040e1611060f070906090b040e100b0d0f0f0501 70
    0xf15a0407172441c444011390358403071410300302c030b0030380480d2010712184007010b82d00e541e04440c24030301354800c0c003080e80000c6143c100c204403200b00104840d51a8415022428401258003035454000302501a842d0011485140d40b00341c20f460303803610005080d42c460480d4984d0305103018000b08907009140e5060702d038021950a45840103d101c81c240c00002d03004a11031581d51190381c00b00c1c400c13000307600902552000408000c0d5074400c0d100030141d050201d07040822074070341300012001e0b60340a481c01b07400d80300c3c004010030001d03100380da607040c007000541402101402403614100c110303000c0d9800001665154040d803544a58180204007a100130702240364103f40c2001151030050000510131850001400d0740d001420780507a90102090040104603802440c00285140c0c4000c0e050b2900c00c0030078605000450010b019030441426a6400641c00b0309140c9803003140e840b0540043c1001409050344203002c01c0c2c1100c0c413402040e01c0c1e0f00700c2c400412341d20403141040d0103c1d0141020140388914140040c04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 945923309 1250 945922059 945922121
    0x901060612150b0f040e0f0f0606120612070f030c0f0605040f1e15050705122704090c0f170d0e06070c050618010e09040507330e04 58
    0xf0345180c8041d26440c1d4507400c40713060302031181e5089865524201c0e0108000c2060f100301d542e204081500f1202c0e0f45459000501159020b2003803003808a400e110b00041e52030403e40943c114040c80001103c6900c0d544070b0a4050403001038005407902c0032a00c0341400303402d604049080040c001c0d0b16215142c2450640c80c0c4002c0c1c2c52501a1500800101d183c0241e1f2705a000040000b409a0410000d0854001000601568040541101c0754090040364051089400054a103094409141c0d0790a04c605250042074482c0071440f440d40c03003035540920802050f068031080000d4000c0c0012400694241020754102008210844046901521034210001c3c0c1c080c281640c140420740e000364a503501e624000600342550341000b80c2110002c10558000111030391a0b628282003030309c400403501c4240e8280020b01c00200c6d00500300c0c2d800902c080103003429101d00307007040110401000c4400c60700301000c921602d501204080000760300b6a400c0c01c0c61b25107441120f1040d0401112a00d0280e00300382001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 945924559 1250 945923309 945923351
    0x314030d0e0a020114030403090b0409020d0f050610200706082410030507170405071419050609180a1a010c0506070e0d060e100c0c0c050607030c020301050901060612 73
    0x100c145ca901001240406000b45207000251080c4210a034440d529280010000d4000d007000d000d01904041d060591100b003441068064030300501240040307103020b241502e000c0700c2681e80b6800360a110140b560304080600100001d0841030390b40050030300745000c00006040761481101e18044055030785003030301e8bd11440220401d0602e400c01007500d03030b9120800d981e9001e000c2c04204a1b07480d4401004208000440c0038400d89844009841000c11504140210201c0006051000d0510000300380310034a4000003a081f5514001c20100302003610581c01840084203880d1401082e44443c0c02001c42d01190a000059101c00e1810b00350314152903ca5581e141c1d40030b4540030501ca0685405801901c4240640d11000d4024009000411441c2e800c180d4031450304402c0f1810318034188102c000c0310f21513500d02c503045401c020790304c80207070030002004150742c1729880031000d00c01d165981c90f006807401e0080c00d10a019100c00003c0140c070385280074100c2c10465034140210340c6082c0030000c850903903000c02 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 945925809 1250 945924559 945924587
    0x90f031911160302030f07230307051e031b0105032a39070e100302120307060b01110703061802090916090b1e0a0314030d0e0a0201 58
    0xe000311405001070340d0310505058000340d9030003828882c1110440d07011500e030880e0300c01c0c0e0466a44c90304046880e074443d0060700801410150240e5184500d644031000002500030081c20723540410703030310800075440704208840040351420143c4050590326051000b0340f154611410910350340d00b030820008240e88001400301b03214006d801195048082040c10b01209582e04011040d0344040203102c118070021201c092020a03401244080390a04044c1515040540380200030440c540c1400d0840401030300c000c0c4130000d403030074040000015035101501801c1c1501d070040a165030f002c641c20110b0646021150341818014620f800d10710510000441804480c1c00401c00100049090810807149144804c003950140d5008148038049001040483c0c408106035041303080b49950f41c03117040c103558007149001d40c00350400240324030365402d90301c0c55201c071240203151800a50b16a036410340c1b0340e042108240c19035030000c2000c101032650791140c5c03400084894003d210503a01540001c110b44003113050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 945927059 1250 945925809 945925837
    0x51603020715020309011a030c010512090312011d070804021c0f05060a0501060f110d08071116081218010c051e150a1a010311090d050601030308090f03 67
    0x550414049200808034000b40d11070019942c0c0e00b80b156030180a8800c40307030101c2101c841250912241e00e00040d022071603c00c1a141c05041000e0903424803c0307240001e10816a500042000d640141c0303141280c54045e0810301c485c038240c01d6078250800c81c6650007c0c403450a00c400c1d9002d000159441d1409211a484805803400130701d012460000001c62003524001e10511030383c41400402c840c80d401843c10b0b41d02e1960341038181086080100c4410490001484040c1c01211034800b0302440f5400c155840031176070903d0101041148011860040040e0707222480e510815130501030b9080502c00400d0903411b01821900f400c140e4415141d00510364980e043c1030100c03003280541040428020900d1441700072020f03200318000000c0c083c0d1205040e071070015940e1800070018601d08001c5c07160203a1808020020342910070600015401403c5a46282143c00020f1021820a5544121071089180f249000c1c0095500d03501c0c01600d000e20140005200c3e80290201070007020b0008107480c502424004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 945928309 1250 945927059 945927067
    0xa110606011d131e0e061e1b0d0606090803070309090e01111207090909030203090f12030c1006080d120c0903060e150603010e070e0a020c0118031205160302 69
    0x2c0050300c2c04060400360545507040001400340e003038051022900c449001e0300103102501c80011040e40742c0d982154000a040004403c501c00e0307101e010122588509110304800100800c9541c00085421903501e640050740c50780020f2108a88c8a00c0300001000550f0082d0f0502e1440e40d000b4003240035034040d10104980c2c9004807000314a094101c1341c50000c0c01701009035910180000d2010030101140d01c4408600000b1001412201502c901a92560942d020318101221602000787c9200503905403a88070564880d004031505041c00100b40002c201e000400d08194100c140c0c0064400d260b210503813541201d43c02c0240150083c10f0440b5001e0446000650040006001d4503041891b80024003a6441e1540c91000103800040c005040726400c2504c01742507894508040c241e603a0542c0001458004043c00c1058145501d20070342c10100d00302016003030801a01c08030f800c41d02d070480d01910810790240040c0900d900034410040c1440901c101b40300030300e04003c0c0d000040c0340c83c00d400020964001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 945929559 1250 945928309 945928367
    0x1e01030f02041215050709060915090e07020d230406181e03020102010f1505040c1413030c15360f0914090606092502030a11060601 58
    0x307811034014010602114038005001d0600422002d0701030700c2071640310b15000208a80c1c501a004071030460300a0b0f42c440340110b09108501c4170f0314090098080030b008440002288000410030946c2c0316460701c0d4020721489450b014000c10fa00c1003c4000b070590004c006601001c800207104076016641c2c2070030045008043c0e105c1080401c48940d1000c988c0b00342c02c03491660b4540425030400f0840307000368000c1c003001040d0550b920032141080303083c3c940c044800d030b420070190400f03400c0b00c007041d0200e06206640483d1151000425030203240c0030759600707845800600400c03c2001d0610013030705401d4a0398094204210010f045000d13a0040c142c84150f42001408503201211610002020601c5146c8030441d40c40d030a40c0c8000354180521501641000480d07007034404815122440b03110b4020044c00d0b2505c40340d050010707400001d00301100158810300184141201494581194445a401160358820340035000306040c09003030010000348c0010090010340d80c1e0010903401401c00c80c0e0384501c8566070038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 945930809 1250 945929559 945929561
    0xc0e032b17060d140a03050a0f1107030b060d14010906060b0c0307260705010507021011030a0902040603021c050d1b171c0f0605060703021e03270f1e01030f 69
    0x1d10301320380c03070340c822181d5160415030300101400e611519a11240035901c0b644000703682c942d09907a4000c980d54402c08041010820704507619811000140003d007075010705403039103400d913940f5a2130340b841a0b448a1810307040104074402c1400600c480005142015107869955407207114003c0d000e840d00703100b03500c404d44072079640d0040d5070400c018005140d80c07005d40d07151040c060700341102d14501500a0380c50307210102c8118001d6440c0780c6a040c11003440d40c2d40e00040c4030010f000102042e40c20541d100c1020005031500b10101000b41c401d000c044c603403410245001844c1c50401c56401c0100680c00002c40c0b0451500d01c40d10038081c4d0301c41e00745140c02e170b08469a2072480c054103d007900124a52039010071400030079401800015081c0d80240055515001402500e2062402c000d006a002d44861a884c0031501010060000d0003c04c0d40d207025804900305104824054100c0214400501ea075140c0d45046001c2130000e5206403800e101000b0191140c0c08a45028403810341455201c00e5400440011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 945932059 1250 945930809 945930833
    0x9051c05040b0703021c0e01031104050a06120e24240f010c0803010609081e150403030f0908250b0a02160605090610060816030c0e032b17060d 63
    0x14001944170307906d0310f10340300801c440c0c1456012404245403d80c5004001c3d103540898041d500301a00c8400010300c0c00340e048484107608004003440c990f0b150310050350700406020000341c11504480342c8403940151907500c0e00d504030242c0a403214200e81e6000326190801c0c182c020f440030004480390810314170100c00581e5001d40c09100280804800030001c00d4aa0300708040c03a00384c3e0140c0d000c440c684a8101000003140700b41d40b09c2d9020b107030b0101c13030a01078851403000010741c40340c400c0c540451a10b003040ea91905881d01c10307900f1100030801007801400310b040c160a49107a0034002502ca109111030762582c0c0748050000d412003415030b400060030008078030180c10116145038030030b10400c420300c0c00a42c0d441e21f4004c151080032070604c0c110000920b89100f0108240124504d910700100d44850000a400526a000480040c00300003940304000c1e54040c0640707480308404060648841c0a460300c082400c0c4042e03103408042c000d84868801e0307030307142c010300310b950100c401d035050b02007850f103130900c007114900b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 945933309 1250 945932059 945932083
    0x14070f020405010e150d02060919030503040f180c080f0717090d0216030308070c020a0902030f0a0c050708091302040807090e0c0f220f02040909051c05040b070302 72
    0x10400d000001c2680c04d01510750b1080140310b624418078040c59080080b07072044144065840032003486440424131f8059914082c0641340080c0504a940d290303038413815034020307a00403440d0741090744c2d08000680000181c2c104800251908010005019102030b100e0403015100320b40042200c00096940d5000f042060a58000c02c411202c2d6450040c0503155240c50600001c0010b020321095001d005c0b02d01403001b003d0700d501d600d41c50825a41c9250803545200410b5050341c1c0500f40c030300002502e803058402507009191501a103441441c01403403050640c0e40291500702004410080c140c00b103501c1000f902c2000303c4c00c8880360210402030032001d0107030040f5000130065000d03120700010b4006080e800858200c50910940f0745198021782001510102c2d80c0140b81c01c1002089850601c03d0318000c01c0114001e0302c2c0c000942c03080b600b40c1080898005411003404d856031011200c051043c200440c16801d40c0d5410010a1402d00c40d200501034095031140a4103101d01040f14400c140c02070040c40314002d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 945934559 1250 945933309 945933311
    0x720010b1203040312081006030e010b0616050706020609031206030705060301060c060b04051308031f18051b0412051903030204030210030e0c130b060c010e16030314070f0204 77
    0x3801070304216160750143c4001c503100001646521403a90152007028800c032000141d03542d0491421034294040c010002d032061070b0b0755031150f6460f80d40d078403d000b43c03450000c0c01101403821000d600d072480c03820180307030412415980041b007023010b400030002c2224581d8680354020360f09a220200801d10300050384d000940d100c0c030f0102c00494129402000205410f010b407000340212401b602c144822500140d5144d81e60038000035040c400b1411000c003e51700310150200c11074410900c0803858003101e0392500704030b40380c1644204000c950700c003501650380c01c40706491107105014a000001c074841d11441c401c03444081801d030074660600000b81f0a00c000c07405261042d099008142ca0b00070000e5100e80003c80c407900590100c50b454610a1050713030340e91450480100440c5401c0410424810703012080f44074803a0300d03084d4a000946528010304801e080700302c008200801040b0031f850601100c89540c0b0345d540b00000080011a900841d0003000051021906036250f466040054031800c40b19000f94002d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 945935809 1250 945934559 945934579
    0x21306080303060307090212070c081b0309030d1b1214030108011506030c080c0906130b03041e0b010608041e0f020f04021606110c0609010b01170720010b 68
    0x400100082d40300f2182201582d003d035480e40b902c5412401681007100d1102980c000003404180100c030b030080301c14003c0e205142003101000c00c880e0b00509900d0040d900c0d40010a500046003010000c07078043c000142095641404100c460a8a90002181c05403103c602d10a1203465203000303104807020114a81503440d520342c2c441f4000703800307000e030b103998200b048520038000240c09209115044000388555281c0c40952504628121650003d83c0e04560081d810081510843c14004204d0010259040410f40300c0c6003d0070001001200c6442554140e104000404c1c006100c088440d41503c010b800e100541351502d040c0070305016039000d032000441d44405041e405100c100c007400c24010b4402c64021410140d90b030140010f030700a071010b4804400b0b203040c031880041c4480c2c000540b0400010070304c1c3d0500a07254603240c40c20005694001d55a55907200403180b5580c0080c018800c01d1000c07681032014100400c00400340d01c01080b107424a914204581c01070b000081d0401500c07404000e05880c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 945937059 1250 945935809 945935819
    0x61d1e120703031e081612092a050904030318060c020a0b09011107060b0f0d0312050a0207020d06020d2c0708011503080c0313031220030412021306 65
    0x10740d41c11408140c02141c4c1040d1120360b1000001c02e5440c100c2200c1d640c904464840f10035099840044040c00030a1240146c1107581c07079150761088501c414041d03c0d03014166a400000e4141c80c071000c510003559414116020701c03103501c0b0100c109811076454640080c8861100483c8100c113015084010300481c01e021648446a07030010700d000001c0d000d5400c464841e01c44c100c0d094220f8a0b400d4002c0d001e0601403100703e0209055622118010001802c4581c0103442e80c0002402007a07040000ca0108055480c0f100940149100d00d5a010144420071403a003100741e0002224100601e100409007500000c060a1107000c90300700010418900d20301911036020344a03040c4d0b5080c0b480310f61440300d22603d040014200f40c14040c1d400c1d0550100880d180c200d0944e102d42e115903101c420104030074401004000c0d100100e60482d000254003512894285501710072000341084944640eaa80f5038240c0c038640008550040201c40440d1403541c02403101805078408039074141400c201900d6814134040000035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 945938309 1250 945937059 945937063
    0x715020306090a05040b0106050a050f0d0204061107120605090319020303220b0403050705150103030e0f03061b030a2408011b050712090b13030c061d1e12 68
    0x2001da4400c9540c2e001070f55605034140304413141210003620030031000004000c058000c1c80104504540b6107486c51405203181005081030340080862441107a002500f00b10385c0341d10090825141c1102c030090400703985400741d5800c620321500300141a141c0d0301c90205075903140c20021503140419035420300b60404a0759401035166001104c3e00d420815100c100400f240700c4400582a220f61700003100b4138280c4413a18122901d402981c400c617070500c5007844020f074001e45126041c0c003c521990b42c014140c00000180f01c100001e00854a001e54014824880401014007684507582007210441d91243c0d945101c1a016010700316880030f02031107494400490041c2013580394103403034030040280a8040c08103d5a113004a4460749807001031414040480002c2845254000c01c40303082c0707483c00e0155280c804a400651140000c4a00fa5041010400402045ca4020700c000d20700c03420a07107055800585c0d1000d80d1040820b281344140300441080c540d0304500e03c030144c80c1c82405060030341c0d8003604502d00b035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 945939559 1250 945938309 945938311
    0xf030305060a0f030f0803060f031516031b0f090f0308120f24030c06030c031f0503120306060f130303350745060c0209040807150203 59
    0x40e00625009201152114a100d0070038122031380400181c030800c0490322907000f1900041d200a40c000e127030b200110250340e030801000051104d01510b000b200d0030300c244500e40107418458104103141c100a007a40030301c00d160542001d4000c441c10302014440c6e981c00101c0b618142c0c0c0d00700013100c600859020003401480c801404206d508000c80c01080c1c6c54665106098581c216014003110409018013800c00c24009180c82c84040c0140c104c411501d4401c0020b4840e400413900f82071800ca0200030803c005244180d0403041310421172002d21250305200119841d0300740e1340304085690390f000000c20710940307450307044500300c1c48483d8844d03882d41450000c124280310188416000189100e0b1132290550b202c0142160f01014007246000364042d142069a0340200207080c2c2043c040c8510941094100ba00c3d203004e101040300c1d801c0e852800038441325100300d09032000f070240400840002070080c00c0e00a012108429011030314081541e031540b620081611907180c0003081d0520f401c1d070300100765881d90080c1d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 945940809 1250 945939559 945939571
    0x3d17100f06031505060d151b0503070e0a060e0402071b08160f180b120a0c09150308040b031008010e0303011809232d0c01021b060906070f030305 64
    0x81c3c20410031900300303c2d064030426a48281d00c080b4844811001582800f010900c21944640210700d640e503940e0301d0b0581034003002c403070300100d5000420046680d501c2204420012011212210701d40c0c1000e00090284c0300749019940216030000349035041c003912740f1b803251002049038064420b031500c40c102641c40d40c0d030306d240c070307000c80d416031200404c000c032003501d4250603078425050203039004140384080c03006807100820550708184201070991b09804144000e42803036019081074800c0a1401002004590a06d00c03031144111050310240001601da4085034105c80ea980240341d200d4581d603410344040e030b0140c0d021032120361034020f015206d2034010019504903502210740307072825094958020b00351101c0b400c000b4031614040c100c1d81300d81c1524540420307d44060004a842d8551250580d8211102c414090502090303d030804080070002000141651f66080c4081c0010807001c0e14284114144900300a11030744001c600e4004a803038010680e4081500505000301071081800c0280003007000b6159 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 945942059 1250 945940809 945940823
    0x915030303060614090f060f030a150503070b070807141006030501060e0103150c0302160f17070c090506011205010b1b030405011202090d05063d17100f0603 69
    0x40003a100780607070f40092003070003100710305071400d2100f00c20081041401c505055201c1d2040c03100310312030130304000a94440c003151130b40001e134be07445c1c031100342c03041c08180d405a03100ba0300c042001d1007501030540a80710aaa4099129900c40010b4a84a0324040710f0110b266014802c0511070100d84078180c1100c811640230340c00800c00c141e21103c40c009004024000030b0484002101055a9a4843d500441e004401450f005051884010182019a00110060fa81c1132070068180061180700320f03010f01b210710280851458031006944154285c02180300783d15a4981c0e40340002c0d8140d0154100c0035400c100082e0411056848100264058000c41d4042001e081c40414003410502700008480a03070300140c460110190007140603002a5215034800c54020080070324000020b03d0030040c450092800c0c1420420000c00c0081500140d88100c1200b04408101011a541c03810b104240405a40e11000e013901c4030034200d00300d540307006003000c1c9103400d0030301e000c4d10300a10721a29405041513030b01c0340035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 945943309 1250 945942059 945942071
    0x30c031f0f05010f020f010c03090c0e101203170c0304050615060319020405030304063203042d05060712060f050910030b091e0a1101030203100915030303 68
    0x10320001608a1402844480c0100d914140115800391000c4500030003244122a440c1d0561a411800c1d20040f0b600007000ca62100c2d4030301c080005e01e500e0724000e0010828449040c1c41d00b900c6130701d070803041072041d40450120a07003041d0038148584090343c4502d10100c01c507091801c040329103489903070007240e00b0340319409420040303404240500da510026100090006086031180c4200d05003070324481074042c0106074200000511510180060001841592102c0003600b0280c106000c0c00d44021a07242c2181814000302e01c2c00c41103800641c1d400c40c0c6c01c9204050300302107210f020802c1c1c01070240c1550840446207801004c0203000240d84d0f01c211041e030b0fa80c820701c2158006031410f94030203005a1500481c00c140c10f02003418080311481c2d000e01c9200720000c45136034070b441e52000040241d034222156001001e003000301c11f82107a81200d400c2c402900921501d0a180c4030322440031240d1031614100350b0004042001340107a400c0b5840508601101001103968001101c09610798a100450109003000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 945944559 1250 945943309 945943351
    0x1212160509180a0b13020c1c0906050307090e04110102011a03100b0d0c03050601050f0604060c030f2001021801080f150a0f1202032505010c02030109020402030c03 72
    0x140075101e88100c0a0001030240c01003004107a080e1400400c24030215944188081596079500c825140c4030900000060341d6415034a400f0341040300d40101050b40004040d5484042644066a0800c0b0384461908645a80f00e0000845044d85594044070902d5010000d12060207100200620340c46e600740c0003040000c1028032031200c10b14008050b1a8103402105002501510503001542d81c07180041c1400790781c2d446907031030b005243c216400540d459407080b00180581d0411100c00352030000111130290405150000043c8000c0303500000070200582041d010f0f1455000d0381084c07890b03804480841802804034089a4000e41041c44592a03c0c13041c1c1c12103010650146140790300660100361601c0050f90303128410460008030000c0e854209402c98800a19045903040d0750020303062816402c001543c2c140100b5150140706001c0d650743e070076440c18250301600201040c008441081c201580a058113000090052040400c0603400c103000100304200d020000d80114802c030000520814142c07500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 945945809 1250 945944559 945944567
    0x14070614040b07051009030801030b06032e090203071211121e03120a0504110108070e1201020c1204050112020301081504300212030606041205121216 66
    0x185aa6811440108010b10440140400038004070307001d0012205c079211202c0380941241d0790304109800040069006004102c806001c1c1c2d5040300085008101c0381030741c0104415405c241401d03038403421010103003040070f000c1d558205030b081c00e80040a440c0d49a40c0c1d51803880824005042c110781000c8501c0f5900100e00d884042550b290407080d005068403198140d0308450851003441000e100c2c4400e21850100e0100600c40c41d1045182c0c0d900404c403400d103481c0c000b20400041c80564140641e40f0308209002e503201403503184200045031301014845034141d041e4024441d15003405910301030002210b6407080c15200400c120780c8281d031650708046c86e20707001324128042801003606a0b0090504120f4040706008440d4200d4002c061915520503202002c0e82c407081c129174803c601106042501144907018881e00c5107000d0003842b01072541c90311600003082441940030741360240109181003024008204042507002000c000c1d0182d41e801ca8010003d04840b0803650580c8000403003144580c2c403886 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 945947059 1250 945945809 945945827
    0xc02130c110118020d020310240b190e120703080c1603050309010f051c0b100c030e19080609030d0f090f03120e030d09050106090507211107140706 65
    0x800103d41189a01c0e5080081038208941d0507030b03051180300102c014a1800c1e100d608001030620f060941e010016048036a000c103030540c044880d82c2428052400e204142220003e011601854106d60741c440601c001742c10001c00c03a403442c10610803c08048100101d500060401d0346282c804c42c0c220102d5450b100391130085030f0000500b42d0b0000e100a081d95400340c3c6046039280061705101d07081081c5a12540808038005801c00d181c00e80743c2da000017560502e080c040318048000d14005a109040d51009071461082e05081e6008800c80b00e9180d4008401c0c000200181640342d05849030303402c08941701c90303881d0041600c03c5a01ca14007003c056184102e8451460045e5008051072a0740c200354600381c82d480c12398101d8405150720740580301c1c1c05000910042c05100c1c01f9003400600d200e010705180c0d0841d501c9400a110891601c810b0040c41034110102c02d6079440d0b105e4860084141c0d0b00101400f03840b0b003040b01601c0312408544002004844401a4101400801103543c40c655802c070803100c1001c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 945948309 1250 945947059 945947081
    0x504051011040906051012320f06040b030a030503040206120112170403150e01060e0109150b0a14070303090b15011805010503010b0919090209030706170f070c02130c1101 75
    0x1030400e0034450b0080c0c0c120f40d1000b000e12210a015231400041802e210000061052001040f1000c12014011781643c0c41c2e04140d09460801c02a213800f40400e039104000c060140900c04044000390440d580c020031110340d070400101800d01965030f8054411450328011085408811805006d1484400075050310300f10ba800c0001d280702c078150106580000c0a4031182c80c10f10303540f2240d0221b180058815910300900d10001c2c00241d014410f0f021006417440d5810a0300d42c500d00b00b002c0d01301c2e240e04c240d00c02d02c442962003170150348100502d4107600811182c84000c110304801d200b00100e002003002200458402a01c1d14108810403125213400d4410354012140402d10030310041c4500000c0002410485a0143c003c1c00d001d030030000707032020658541d48040302d036075000640520a800d0500c400001000203062030350418000419501460784002c098010070000403000800c440d11659032011115000380810b03882d8100c007040040130741280100e920225602d102d600220074814410354140c3c0c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 945949559 1250 945948309 945948317
    0x40212061005030c0d0b0609040c0801050111010902090f180111190f200703060509010204090606050f0a0c02041103071205100b1603110f0c0306010603180605040510110409060510 79
    0x200d4010101e030000c06c03402e155650028130070f00004646450341d2156200c0e4a41c07a403181075203989450001407040d603100000ca210b50741890078200050311101d140b50340244100080703064550760080c02c041d00c00c4c082103611070a9130074075000f510004003040c010800e000084016604810382c1120036034444190001090002e00c5019002e0100021104c203a503520034000c090300e100c10b5480d1609429220300f83c400300d440d80d41c001803c103c3d00d0030728803c1500070f01e5982001820004240200159130003a10009824000030403c07010842d502c0d0361280c0e1846080c1c0150700d403203003000c050050140320a0005246064509000700c0c0800448911060440b20020720581c41c090700522104e603410790403c8101c0a02c901c00301d8001c40f001d8140180204200c0c0a0b00824000164204061034520180d01101c1030624040011400c852512a8480000c2e0050004202500c992403c985404940409007100c01e107840035003207581c0301440c0108100c682d510001d205403034440080041502816007044042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 945950809 1250 945949559 945949567
    0x31e0b01080a060b16140f071502060103200315190e010614061b07060c0302100b0a090b01090807180501090b030a030807020111040605040e0f07020d1d040212061005030c 75
    0x4280798004903000300740302c1ca20f42140702e181d4251141c600600a504047c03540c01402c07080c00107242e43c40c100382291200703200a00c215407540d1612007100c844070b01c010740d03a81d0001603100d10710b072001c01c01402180c14601c99450680b80bc10003140d0307044c1000f08a600d4060509100747d090110501610055403d0315000103004074440c001c00c031442d80301c1610b02d480e182d0f40d00305d141031115091080700024940d030f8890101d01c1000745002814203420412218001d840d0003039416568617403a00322000d840c441007000130140c204c0001a03401d50710f1903001c680e841c0300e0200081000b0402442a010485030300b076040c001ca98171044044103503421001c6454043e880650b0b5032010a208208154104403d40000119030a031450a06040c1d84190800000f08800080c104090540c50b501107610030315455851410341081071009460b00c62003400c801c00c000b205000418180c4062840c01015000200115516214480d211407215012104288a22540301c2d1203c11140204221703407007a60020402c61034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 945952059 1250 945950809 945950827
    0x2d0f03193015030204020406020d0210021303111816020d0e0d0206070218010b0a0f230a0228050c100801150e03150a11070b0a0507031e0b01080a060b 66
    0x2041e1006030b5900392080001d002000d61928402000074094070f5010340300c400310050002c0d00e841c1e840d500b071820040c410004503500351a6120107a054a51050200010090040000390780080f07500306204210112001e210b0f410541d014200d8002a01740c080da072505a01c0300c001e49980c05000800b83c9c00690804040d00103107172140003000740038402070040e500c0c2c0c1c900011600540c0c0003600400c1d47c201c00000d1403034030306400600f41055090149015400800c0115140300c2c9003140448034503c5141c0803030703114900e0b8000e202e55000050503211700a81080402c1d407580a000e00881c0569941c02401c0301d0842c10305058454090b82021074541c0003c03a46821174001014119000c540d082103064030441c0d82940c1d00b0700508480341000c40c254501820b106004a00b280d00341507410380c00440402c1800006000356011942c80094004009100d030349016083e4003405c0d0104032051a0a20b00c092140859041c2d80700030380c82c200c00c0ea03640f01300e507031051000c3d4110790f12030048080c020000c0c401034503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 945953309 1250 945952059 945952061
    0x6060304020d05190308060a060e0f130c0819060f0b13050904080304050c060306012001090b040b01030b0601030915020702031e010204090e2d0f031930 67
    0x1400520262000d0324502d01502c0d030608015001e450000d040c041414681c090640c0104d075140c020b04215008814613241940c05402861103103199401001d1058030a01c1c00e5542c11641035218072018000e11003580c074482d000b041510304544000b41d12200d258030920511080c0f0038401600d109212209216060034081003054011196441c2a03064109000c0381e141c036900005801181b260300c1e031a450341418600103003820109001680070f00d50030310070450340c3d07a07106503003240314504548100001ca4040308403070301614600a0182c600b02003030041c0020092000c0b803142c101c900922800d011078940c0c00c011000c4d601000009060050340c0303510f0300d00200041e80148800c6100608441903040c407400600c90444c0c8000c10b00f0720903503001c5004c02902016004486a10b9254009013a44001d40075805100364180c1000c2d60218101fa0742d8006050410005003d81c035041104594503483c00c070600c000301e070030064010380006581e80d5910380117014003006241041407880d14042002d80380301800d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 945954559 1250 945953309 945953311
    0xf06030c03150e01021603031404321b030d0903081c0b0a061124040b0c040909080304021f0207031e0c08010203040b010b180616150b09070215060603 66
    0x40ea0342e0b8082c20030180f50b0134070081005410801c00503034021540d04001e02103603804084c94901110781c408100c00203009007901c405020030a003a2890030710322880b10800b054408845c03c0d0843c03088956100c03034428903040d5502200b50860032143c500103200400c4681d034400740f00040c01002c0c18042002d40d0805000d88101c00181079000065400d009000900024040e82c00580420841c040a070014003046c0802508a039280c00031043c08250210110341c007400007007001e4100d44085002c2506401084110340060803248024048182141880c440c40e03482a10103d102c0c1c81680000002c90780941d0166480f9801600a805450325545603855403418960a510548690342c8043c000120403840080252800d43c00068981c6020303c0d00300310541c0185c01c451503185043c44641405250140721014070013055800944800b04207880a1141408520003010070101c480c0c5442c410b21540c1c8140c1050030200c901401d1601e4841040e41c40b40c0548040c600c0040340c031400201c071801e040c0011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 945955809 1250 945954559 945954593
    0x3040c1703030a2a090f0902160219030b0a02041e0806070f110f01140903190318020a03140106150e040911060a0906020606190909150c020c040f06030c03 68
    0x48203006a113003ea01c403484030003d4589000c00c03200401403201240b81122400030304070b810411444c0c0140301140509903100320740000d10540900592400c3c1d0f02104601c4001550b003d20f081c102030800803000c0b40a034015000705400402549102c090003c02044040c1c11a6901c030050641d9845807002200d25070002134005017849805101e054444004111089000000000004000450000b40581d10b10050134046a41e88103020052824002d1048108108030380d0078009800010302d00c485044501c4c400000e5401007a122001080c130051400c504440c01c00000200301c0c042e00d980c2c1c2450080000c145980029501c0c80e00e10005040586c05100505d000710f000c0c00e90040ca02000484030351041640e0000582c20400800120360100903564002c10100d4200c45061481000c542e4001c0d5544561a80329458003c2c40003880311030b04e420140107410304800d0080c0d0a998001a65a800203000903015500d44070041c4058011481240161390303126101c00055450350326203180c500114201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 945957059 1250 945955809 945955841
    0x80a03090615140307080606030319020c090a1a04141501030e0a0503090109080705090f07051b0714010801080a08090310060f060809030a09290f03040c1703030a 71
    0x2000460515040c1100010070700b483c1c4041030020828185070030410307258801c032250740c000002d10170242d0b00031003a20010384c07580300d204ad890580c40c0c008a10300700d038029002e82c010606006028410059400c08601c180440350001d02d4400c9800c1030000f21411540358580000605000c5807031b4406460501504071014036001c5401c03100b0b883e5035030621050410807142640005680e81035541c00c44005001465081c01030101c8629100100310303040ca00400820100f110310000402d96030080c41513600e03030308440304a0120400342e048101d03078400460003100f04c2c403c0c0c48150031050790721448556050b9055000a0800022140d5a0308800e40102c410581d0500422103858985101440b8080060550369640512140340000181404a02412a5903160020441c8030151500142c01c40219440710741c46080c48100c01d1040c03400039421040c417503c95036001603161a8001ea03140a10f0080c0d00501031003441d1565803280c100042c0d1034150b210350941042c0002803502c0c03e55030241c140c9103401e5034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 945958309 1250 945957059 945957071
    0x8130803120121080d02070b01050603010b09210d030906181e0203030715050a050c0c0a0b04080d0c09050f04150303052206082e03170f13091503080a030906 69
    0x601c02107640c010710b03171200146034003007005014009609001401001d0a444207407565040c40302c03180c0c00348200000c2d031380628101c106654111507203040c880340322090b10007680e22900d80040f004004e80780100007511039504103420301c000c642d54541d40d80038403a4800c0a44041100c0c030a590500140d6040b0182c1e03240c04107020520100d6216013040e803120f00008000200e614054001038100c4102030907207410501d0a00003c00140800204031860720741005480b4410740d52440d00f03c0302c911401da00900624100000e0a607039903002180c120540348221048c211800c582c005100c1124202030800101c00020b04080000c02e0142009022a48201100440100d0040080c1480614544c09400001d5244040010007074a840c0503c80c032200c0c40c41c1b5140c68010070038000800c40118000a0440007a56141903039042c01c42d0301722440800c0c01d22002e0740741c80210078090601c1c000c61058401ea0b5050288500e8004410040e070030680340d01071303c400e0030042d01c2d150440c020f20504104440c000e0341c0e40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 945959559 1250 945958309 945958313
    0x20a02130f02190801080607050904090f0816021e0a0b03090a050a030e0405150a0b090619080103021203070305040b030603010905070306060f14100f170408130803120121 75
    0x1c0014510310600803000c500c03010f2031400c01030485005030f00c8000f4030303000a07040c418010703400800c607161002c04070b6000c00d80350410705064408542e02c801c0204000710000e61909081c00043d259411036000319043d500303140002001c6041c412040c44100ea004110130b1003031040f244840d010790f800000340d0b4202c1c1c41b00d910380e5071002c0c03422451640036408100d0b1545903e0061429025140c2d000c2444401c00f0758180e5000c021403040b0560b4001c0200c8040040303191182503d07004203907442c030518124039011320b1000f40c5004d00401030038001a030084442c0c8034960408600002100c5042d649940d43d2480c091412400d00c1d0342d0707000a1720316a89552682c0003000410802c004842c040c50080d0000521149080044a810703000d42e07105030081e070038280d004407240d6038813217001048803c5800d213180002c00c0040c04441c004103080301c4034031200850b0140014004034002800702080d40030000880a0f0f15036440995074026802d850701c44950150044c01000c01840d20a0003403c604481600e00088076 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 945960809 1250 945959559 945959561
    0x1804030f0207120c0f0b1603030f0207080315040c0c030c1b0302041406010801060c1707020402040f0e0a0c0c051e030409060e041509050307030c021c05060f07020c01020a02130f 78
    0xf0b03a080e00c101c0641c450a024100114401030001e00015a10616041e20208900a81200c90001400341a91040e4444515801d43c0403182d415500c0840340b960fa18180b80c4101d043c45c223241c0c0e8117004500e17000040211a0040b114562003d8140e291500c1c4c01801c2d54a80f24450451603007031009801010000006881e18001c05110042d0800015014070f00351000401881d016442207040010200400e00440c040900c6860859444008903580f21441d0010a01070b00c99a4024105116808000070740c0b025100980c6010710341840b400e220158040c03204030343d59004543e010345643c11a0000c0300d86400003500700c00b482d0304030000352070800c0d90b51200308085900d60350148600356600d00401c130412032260109500c41e4803084007004441401e031105079582c0102040101445120000311080d551841c0c1802e074854031324412402c2e40c8803a80b40c4241c50710390a448160903070106102013060107001041204501d9010f1b0300401200d000c903000c0000c5000020600301c00a96505201f4001c0a42 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 945962059 1250 945960809 945960839
    0x9020f0a031505100e0d14070e0604050c120402030c040c020f250605030c0705012d11030c09131104030524010303211401080c1804030f0207 62
    0x5025205459000d2028040c050354468000041ea005494100744100d989a031100380c014102860090244000c00001c03c0c4150203401005c4d106072129400c108612a00007140c40030f41b000115488102d8a0726414002a620180c41c03803000d03072005114186071911010100e07680607000400b10381c8500805c43c0810b0844540805920043e04007565103070000302e04102c1650701c0303c20310000d00c8000260031080c0340110081d0082d0707400c2000002c003046000c00310806441409400400802000044d10f0704401c640b40c2c03071004101d001410268110002c4a24415001180c11a401041c9169a00c0f41e91854130340c4186029913208900703902043c80007180703201d2510900003c001403a5101c1c19030500078900403440310591100b032480c210000442c03981c082080d04490745030a0000b111034a00320741c00d06c02034940004400036884c0c1044884401c1b210101c041c100c44850042e030b980c4500900a02600e00c681054807d4542d00b090f0115000910402c0d42c2d100080c203520580c0d100c5030b122015403200c500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 945963309 1250 945962059 945962077
    0x506041524050c0606040e030d0e0d12140103121407050303010303082505162103060b0c0714030f0a060b01080a0506030a02011409030d0306030c090510090e070902 72
    0x55028010001c440c00c01e015000c501d001410034906200030400712a82d101c10040c03160340110b8464882440744d510030402c1c0c0d021030158080c00d2159440031f4041c9035407080c440c480c0030005000503001c125007800c1480f60b82030740b804810307a035070b0a03a00f1900c86840d01005c0d10304410400800d118a40a0104440080c003002ca208002039a900c1d49907040084c0740d0240038041041c1140713080004100c0d55400076816042030f500303040030798940d03281724010441450b20002c040c000c00000c801c065010445405007815420841c0c800b01700154551210a440740a04104000d0316400400140403041c10220000448034005040703d00d00300303c245000d42400c41a800440b0201d03280ea076525440e41c0c105001c40d078014800c003c1040701f85047d5000a44c0c0d264100000f80c144041c810407025000000b00c11240640005401c88180080c070102c0100200000d100550f0300640c21f14001c205001140507140c00b039500c0c0c100c060085030078003482c07200030302109035082020f01c00c0d84800541000c090025044082c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 945964559 1250 945963309 945963329
    0x3112401030b070801181a062110060f201c1d01091e150e01030e01060e01031211010c0c060b040b0303030a0911120a1407031505060415 60
    0x54503610b8140c2aa070409480b500520521500501c1113124401c82c039040e1120308080454855a40c081e841c16440c480948260850300005584020001d2000f250000418154083c03486a8a03c04441c1d495551809103d0020307581ca20712454451081420030744008201d100554020207001c2903514105042c43c6409900b401034a00ea0070550304081d01550710400039041c03800107118140002c02106050107143c2c61998400464400e03d103074800c030345021b40154120310b04d05e0091510064044000004460b00003820324258403065030301809007071f04582080c0503100c1242d00b5036903070a482006010252080187c500740700c20403180c0900a40007440c0098030f071903903184001d080074001e0b9500e0ba0b100901480c1808510f007602d85000045a40c0800c14030000510b2407801d1a140b01000074000d4000d501c80f0107103080049030400810f04400852040d4903026008510702e02807034440280d440050860f100150340c00003030302150b4001c1d55001034001c03c00112550307100504080010140c004003108 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 945965809 1250 945964559 945964561
    0x8091005090d24020a170a2903010c1e05160b0a05010303110a0309090509030c031210290315130c02160506072619020601060c0f031124 60
    0x891007000d59580c000442c00f005628101076034001030300b40c00e4100024190000c0c03180004024401380e6129003820071802c108046140c40c81c6020750404140001e0240c440c1d4071707180500360141e00881d40700444010600340e1140400c000302d001d44440d040341046200b0104d6070241c100024910303d4103248540c1c0307034000c0044d8650460500405409108c00101151380c0520240350110790406040400c490b800480450703a0303664240c0060450244e0024003800e880301041d000c0204003000d41080c070521609044558540e920720025001c0c4058241700030418a1440900343c51120520003160300074030f126007951000e00f800010074211810140321481150b91020030b41c034059410f2212880d48038404490214150a10001540510a840d00180580350018010b4007600b1020034001e080c5c09003c80303c41d26112588440800d40102c1500780d8018020300c1d0001c03e940c2e005031241d100050308008044e10003001c5680545030890881c10060140c41003034207518041c224211080d80004a0040c40929 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 945967059 1250 945965809 945965843
    0xc0427030513030308090c0d150507140708120a0902010c080c0309090702030d0e030a05040504202706191d06040603020414040501050d2006040e1e0408091005090d 72
    0x18070703206601d91f500c01c2c0d0040080c0300108644812443c010865444001212b846406041d03521114a000d00c0504440100e030010600040c200a00444c95515140701d403030ba6038a02c8010308903440741c0300c024085515100050085111400504500340c3c1c071f002101d00e0602951700017002e00000b185d10070016800000c407003120079514052030344030b44410300041d424a010400d01a04500690140c140190b6447c1c0003d8108108415440e00d400d00d6081d0340303035841c99980b40d0364030502d5030601c941030050400c804010807810014115521001103da81d00242c3d006100120345820a80007100240341c503421034007900f03581308401440100700b5601d00507075440ca4181a054541200c001240c0f14614150040110342c84003c0e40d0125541d000b0303542c01c0c420700c000d404410a024421440e50708507d0200e000305401c0b0352903148030300076158800601c00019600c0040d0100074011070b00101013201c01d0004e1040d5041ca100450894400c40c20541d04081481002c42c0000754603203010340b0b80c4644a001804 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 945968309 1250 945967059 945967063
    0xf060f0e0d0801050609031c0306231311070501050903030a0f060b0301050103020c0304090218090a090c141323130302060f0c04090e010605030c042703051303030809 73
    0x18000081010305007600d1181005007404605100d030324003410001440c4403003a502480340003502c16049034420582d07040340000800401180c011981808003020782d45462107460454803c0341e250041822020030789100a1401811914101d01c00e0303000280507140020702c0a010b21403252803172200460712454441191750964203001030705203003545080410700c051070050040b82d05443c001c0c00d003d41e0314078429103542d16602c41e40d88400700c01403001c41c4034004190501c11805030504100c90741c40c540e03107a00070a1310803110204001000800d00c8001003080d001516113020311111b008100c1c40e240f400881030141a26840c121024980101c03d408031310b101000c01c24260402c46c8000c04070708240f202e40e80030f07540301000f40440b031100c2c0e00c10001805140d440f008407400b4000441051000c00000c007500c83c003800e964000d16200b030003030b525013440c20b041910884c041c1c18221584a40580b0342a8030b0500c0040d0100b20503402c00204001c070540c021a4001588001d6101c2e41d10041c841ca0304120f6a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 945969559 1250 945968309 945968321
    0x9070c0c0b090f0906010e1906170603031c060515070c06090501080a0e01181b0918060b03101404030909150905090f06011514091513030f060f 63
    0x30081c03005000b080019103404080f500b08000c01d0341d00f5011070321600016910031307043c07441300c65200c2000b100c8504030b25110141241202c800d038492088072050fa05019003041401c4904175016842482114a80b40e00110100006140d07488001002e60315000414a040452145010a464000741d110108244000810000c092a14001950900700b0340005c009030740151803411034503154004000c40d10001c3d80501d05000c0024000c42c440c05861a105004e20000a403940301d40030704880005005250b8000e03034101c0b80364100000300400055903040020030036004515058407441d00d04003659540c51284803021700017180d00421301d140030318004107001c540350807680070507041140c45980c03d0343c0803040d4410350b1401d10f00807a90759a031044040c42c2c910750705003110140c81740c075000080b044c0e044000d50300c000209540e1019001d0240340a42d4107407103141c44194004020721203640207451a20701030300301c10440303140c2603161607a03076104c0385480780c2c031480140d801d1591610507201102c0310b03100341 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 945970809 1250 945969559 945969569
    0x1e051602060a032a12090b0f0a14150108070c030f0c05031303061b030b060316020a020306100602010b090606041a07060e060a0b0405150f19120308070503010b032409070c0c 76
    0xd0000e4582c6c0d80e201409810094042610811200040b4149000e03540100b040e100c42580e4030101c0d4a014200382c200c0780640e01049020543c02c102240d10144180344d8901041d0701501c0f062040325603094110752000380f600064074030340800e00c00110400c051003c07481c0250300414010804001d47c0c4443e500d400c1c0100544414140391290201680c2c807168140c0358000e285004440240000724401d0f4184088400002d43c103014000400002c003014150304810f40750181e000300150803840040c4030799180151402d5600c0b9800344010030995649207045800c0400c00d00d106804e04101d1380da00342c19520240940c0c0c2d40c5802060803c070011900d40f04801401404840c00d1140f400c00d66034144503816011440790141c1223034003562000d40c6950a1309030540b2030000034004140d66a4500d48585403241c1022000108130301c0116441e1881030080d01d050728403072080c440c59501c40e00d0100c2c2c2031040c1c4214103c0d00801c04610120503646080c040340c4100401e80350994044400d140c84502400e80d5002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 945972059 1250 945970809 945970811
    0x50301060207030f0206070605070818030414040c090803040e0919030e09040c0f0b27031005100f24050a0f0516050601061e051602060a032a12 63
    0x40004607800540d500c1200e13003208001d2007140d203c3c00896000d01c160100582554144024004d40907800081c80c3c1c03084e00c400c1500140141413101e100d45901c40d81c400c00220510382e01c24907644d842c10360b0102d1001e80da58105603403142c0e0b95960031400c42e0410f174402041091508100006050b0500103400010401e00c7c00c284090345d02c2d0341c080c0c0b100926900c0c2a0060b008107000030100051500d200014100040f000d806682e9a2403041a15a001001520003030f0342210300e082c0c079007203054000f005520000b0003170700d09601c00345200f800400000b03014140c9440d8210303000171081c040a00c00d4000e040081c1c0701c1d048900a0941350501499049502400c00c0130811208119075072003000d4010709509071500c1035480c010300c3d0014004001151001d00785000d18800059426004440100082031282c0301c0c1805002c0e10000b6a83c0303000d0a646680504144141c0000518101c0028010308415060000d0240480300448804180509089805c10700e0140d030898a10341005540c9840e40349800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 945973309 1250 945972059 945972061
    0xa1803111c080f04110616110904081207050d020a120c0e010f3c17060a0303050c1903021b030111090d031215060e03213103020102010c0503 62
    0x1000309800d42c020400c440ca842014003180801828803050701c0e041c1401002661035614030b10201400880044045602914884544030b59040880c001403280b42c0014010741494010340b0b20182c0000b00502c03200400030100000380d441c22540c405010700407041d03690045008a1061614111031054980009000101d4060b079980d030307440691000c494499207001c1a003006c00d08080a12150b00400700c558600010012803604c908c00308181411007207699070ba12241d000300303400c010010350507190399802c0400c0071400e0000c03078026030040031035040030300881e81210951300e02c506401c2e051480c100e0058111290b010300421509008408494085000700150314a40c0124012440740f05103890061320b20805030000d05000b03100303c00b00c07400c9007042032006122101070401d60400c68080c20340801c01142c0c0d01449130500158003002c03102103a0601c078040c44032142d0010950041d0012001c40c0410801030400000900783c0441803d03501001c006d03d190030b62001900b5603803041d164a0400c44140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 945974559 1250 945973309 945973363
    0x261e071829131d07030b0a0b0904031e090b160b091b0405040309030206030f06090a09030203030a151809060e060921071e02030c0f06040b030a180311 66
    0x150701060b0003010041c0002c0d000d03800400140754500000020001400740000c00810f100c8180c0c949840382100c8079040202d004c0040401005580c140c40c058001629410400c0c04514000c1d1801c010310240d080030303003071726640e421280680c0e803061900c0144d00d84084030003020007101c3d40009802c4401a005081828244240d03949202c901480c2c0034031482c2c072080450240360194000d500550b4025000c944d0701c0c82c0c41058400200000d440440c080c1d00d84074001b40c1a040c291050a0178241c1c1680914030f59242c1c40001c070060300130007401c11041c1c0d4081c0800529403000ca61b003d40e0800c200000030440f5902801c24500b158403820000d0300542042c0c0030403809010120354126160748071584540e40444113046180c8a0107003050080191101001e020700080000400c0c01165200303c0484400d01510307002e110103403040044154100f5000d000c140409501c9101965018010ba400014611120418020000c0101106401042c100600c80340c945c0030502c05201400031480200078610700e08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 945975809 1250 945974559 945974569
    0x109050603011a07021c0804060e0102030f04030615210501061410050a021203040b0108060610020705011103250b012c0705120907261e071829 63
    0x282c00f50f0350700c1520006420085541d08581185040c0e0b0b000c010140d46021460f0520781c50340540500004074981305443c040035840002218150454171000c0c84c1458510355898000d0040ca40e0702030031074070030304101080d040c4098003c08031000c0030009150400a61307003829421031340b442c1c2000c5002fa0001d0548065511104094405142c0600d84036a5518500710102e04010384127042d074603d50307000810704c0300744020400141d040c3d410f03000039034045480b102c042000d095406446000540c01640040000d0f600941280301c1542d928420b40e45400a050b03001040d040d4a0b40042e0360045000c81d400c405d200205803418054100c040d94421084000c9141c1c81d80c1d41d0701d154031210b8041110001510790703445003096418aa0345010414800e007405403415466105d5030140c503280c0312030040b5084160b132044401c40741d5507902c40c0160606591406800c1c0709a0f0654858900760b00c01c0d00e4000511120060603401c40f101100000154a02050b2000041000070511482d00c15001341000d43c0780d50b24 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 945977059 1250 945975809 945975839
    0x130f0b010c020d0b0c07060207060f1a0a0e130203030c0106090501050d0302030f07020402070b16021624050f0a030b0a14010e010e040b0a030b0906060306040c03030f020c0d030509010905060301 85
    0xa42460a40d0794a1094010348030b04d171b5004041318000f207090790800203030350003428920003c01001d00410111682c2d941da03416009240a5000c41e2240c01001315980701041c19030008601c0d1718803200c9002a8020a2850340081103d1035569503607001000110305a00c100f0703014010880740d5040502558400070360703070300450100170821100010f0700e40c210758407581128480da0f8030103070104080c9812003103000a40301d8014039402602172494007040300c0201c15109026036189020400320603018600320049408807002c01c1e0b003401400c1106122a01754040501001d80d1542c2e00417940403041c20511400d001140c0c000941c80b4a43c0522001581c0c00035a0340308030002c00e2030502c03000842e10001070094081a488540c218440131004000d0050200000d8454000d0078104c501d552510018182d80743e404a0340a81003a0616800f440068030070742c0c41450714160752045802200d8204c00040c3c810001a8040307011850014080c0ca0a5810180c1d0900800088584900755031402e0840301107100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 945978309 1250 945977059 945977063
    0x1005071106041b030f1a07080603032706041e0501030603080307080a09020919060e01080a03050c0c150d0f110d02090d060c0305180f0a11010e130f0b010c020d 70
    0x15810b0800003884148501c000080d0b810817260300941e007003414003001c45d01e45000c2c034100380c070220000540740c0c0d8059815a405084003030011450941070354403010240d400e2000c0404a0080c80401c8813450b51040f0141020b4560030b0401461204001100604004140e00c214140360074800c0c1040030410741010b0ba0b0340310743c0700e0800d80c83da07035510361007039004051701c020003580400890140502e0b207584110148119161241c1004100c1d111607190032180b0302440380c2d68030f0354032844950f40060300c00d00c05000401e41e01801c51782200301d5080024070041c1f15000342400d0340408501000403100b1401a944841c0c0c01360000c0102d400d0340d0301206c0c22485984000c003102c0c2d40008000f006a1074103060040c00395080141007080952403c00100944001ea450008440c1c0300c1e03000c4200d00e800030030350040380b24400c03005141c2c00070300b0f5542c4001011b20314001414080f00360041c65451f15055a5180d15001c1c40500085030420091084100c60b000c01810781000b15403100000181c6a400503515001d0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 945979559 1250 945978309 945978323
    0xc0201030504020d050f0c0310140705090604030f120e06130e06062b0e1b1c0807050616030608030d05040602090a081006060503070c0212100e100507110604 69
    0xb640707900120b4a01c0e000420010194800d2403020f9690a001080d2a050070b030044003a106400b141d800414281c0e902d41429003425246c481c04500d4490040c002425107440c080d11180c2450b0b40c030740321405000c0c030240b000d40b036103900e08034400c510652107070b000c000100080340c1903810604007060a05030341000e8060b228030500044003050565490000346e40d4400b0210700c1d81e488400011924118401c0c105407022401410040c0d10001c6074400b2805051034244200d00c042d20f041003004000003581d1804014607421300000c2c5040118501100030803800d40100014540c60400c1c01c1c43c40c51134401c40c0e02c1c03901054549502031102100c0841240d207410840d4001103110f44450525a000f4456a05030380d40c40385000e0000500303100c000c02e011a80c0f0035110b0f03040200550b40c4005031a03a2000b20b54a0000500c00940240103161912066100c0b0192004480b030001d0b50241000441e140541c00c0e819940c44490030241c000b090303000d0f0355485000e0b803030310b482e42c20b442d02822070707490102900c020040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 945980809 1250 945979559 945979561
    0x15020109232e0506032a090c04182708120f06010c11040b0307030b070207060503060a230303041e050607051e0c060a05040801150305072315040f090b010c02010305 72
    0x290303174104244032050314814160380d001c00c451002e40400c07907010090b00d0b02034004400040c1842c0350410541d421150007108044032105000c050308010407250f54201c5000d102c260703c03d03c2d1500d543c1c01700c2000c40e2003208959524084055020351050b002040e26003900710001c104130310fa9070310404218403a98440c0b008510201380c080010b0280501200064152081c84800400d20080e9043c06001c2c5143d5001e41e09410389600c2c04440e140300480e411030300507901d0300d000c01540d00b0300300744021144510300c40c038880120342300002421640140d01c00e044d0031190704a207a100c4505000200c009180407542c2e03a261811a6441035150301500008900b4003000098604a0180c1800301440b158801401d656407044803980c003410076001400344080540c03138243c03170030303122400c0300c40760070a803074101c40144589880e20070044e80201c40e10b064244d2036510800306d59001e8071002421a144180340e0b01694549040040302902c00842e580f0481d00f041c10100a0049640c0100c40441c40307980a02e004185 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 945982059 1250 945980809 945980821
    0xe060a0b0a150905030d09060f03060602060705030630070504020408070e1f03050a11040911060d02090306010314011104063203090a0b090d0915020109232e05 70
    0x4003d00c80d60100307406010b0307000d00f0890158021040420750f0615100c030031800c540ca0a00704e0442c0e006014030b1016074043d4011401681c00307403020310350000c0001c04400c410040400e42209241c040040e84940e0050444503540071141440804080c15080e03400f181440d18148615589000724420840030201e0311000c2242d00300402c001c140300700f04480180100c00e5480c40d10550307035a8032481c150381d41080800024140e181178081c207140301c0c3d00180c0e540940b03020b981c200521644185803400c010b0740d081048909a4400384103a90003540035061444511103121102c0f03003500c0c803018070351507001c4d41000140a0650400701e002190890015081841d84443d4800d40f1103008d00521804000404000c01000b1817000450140c403601c1050040001d44843c0185541c60b001c03002c180001c1040300c070b4217020b029401101740700280014400424416425103415420100c0b058500905880801807200d200004004402180b042089450500301600c690340003c41144103071103051a4a403804110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 945983309 1250 945982059 945982067
    0x905090c09010b0702091303210605030a03120e0105070804110109030f0f14011b08150a150e03030708040e09010f0f06180506011e140d0e060a0b0a15 66
    0x214502024014203107958444030702c20302903003120b4800c9118146880020b400328030b00e140003004007503058a50014074840204074012003403003600041c0c01c2a990342c00001e0b095600304110107142d8080d4903000c4c24440462072150a0780e08250210415038104418450f802d0b034081c0c09203a00680283c0413042841300300c0f00407180b07001140c2c000b03044055070b03076511000e020b200c1054082c464412641480800740a4800038240c034404510b40c23506c0d6104003e1002118020500f040c0d0203100400c04540032103a01001903070403005a00648201e00c044806038a845420080441600600b10000c600b0581c1030354411602c0d00c12409203030710241a0001281007080250030501c2c1500700038109024000501c403c0d08000d016901c175604003d0004071841841041c2481928000d00060399508030044425040150316800407164004000300350f8908804050260081d1028038280303000401d58498002059192020282c00b020141c1c2c50f0005214080e90b0b1480380c00c00b151043c80c00303502444e075a040151 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 945984559 1250 945983309 945983323
    0x10050f0409111909110a02011d0705130905010c0807080108150c0d0b0406090e011109090c07030507150f1a010f0f09050612041214040b1c020d0b0325090509 69
    0x1071481400c204880c1e090f02c8066014004d241e1b41c60f402081a41c46841e00b40b8090050941e5000164000c600706000c182041030402d1008007001c080481c0099203030742c455084400201c08140003d031804144458181d014a8041c01800f601c00280441040062034401070600505240c1c01030320002020760203010b49030032024407400000d004000055907107000101408000f80c002e0b80301c0d4644240301054003041c030250340c2ca401001d8481d45143eaa00f00c03101c01503901c504030079801c0c800d041c000780000920a1101801c86440c2a03004191888008400004e880a254405090303c940080f4a00c0703d0b41d00c01500c869207081131a02c2c1561030700084081e0346040281d0000c580000000880e618070b5100d07894114040c0740b050509907450140b054046440303048408580107280b100708410061000080060031006000c001d4807080104186618400c070391002460300b02e03041e00d607c1c0c0c2130100d00d414003000c5404ca042c8031071001c461056050a480700e02c01c81c001d0b001095078940100d145c00308104104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 945985809 1250 945984559 945984569
    0xb0409030207090507030608030403020d02010203040f06030f0507030c0f080714121803040308040e040804050603181c090e040507090e0f01061a07020d02040b040510050f04091119 79
    0x10802004503090081d01ca1072580118110542404003107a200d620910500d412103103480065814241135038208121801496003d0341103200030700c0b004c101d03251594580c0c001041c0c40d131800140e80004007038540a40c0d500400e00e0050620708014020303050703003195886082217014030b8200500d0381c980200795200301c0780d49403407000b546020030440d098840e03503003685004041c80c400303c2503288400c1d058641d0300c0c0b045000003400010305100c10003503a0301450340da80d00144564071080c1007540350804560b0b50b40089691000401010b8004032507040c0c21700c1440b14010b41005800340c0382d22070000141c0b0901c541e1040c6c1d1946000302e00000d0600c44184890005044601414424003642c501225a1501000c04400711546010b81c009030302c00c212202c0000d03400d4181d00f07843c100321054003084000120340c6000d82e049900d45000c40d4041d99a031240700d01c03900000a000042c1c604200078807400c9200f1203001c902031440c206c5c124000c40e60f940c481c1204554212151040c02d141401c13425007006031030b440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 945987059 1250 945985809 945985811
    0x213050409390f060c020d08120726010302061803032502091602060411010e12061609050d0803090a0b0f01320105090103090c0e010518041a06040b04 66
    0x10a81070300c84000c039190b2016881d03003000302119100e40e09141c80d40c007079110700c0d004030b00c101c0c001200604044d800d500800d4000c5507461300781464480c400c00d0b44101122940005207081101d44ca0034441c003403041c0d0010040c401c0e000060341c199800300b50140302c0d25a031020400401034101074155400c104542d14103810036105c000e01c0000d400001000721540c881244a0000b03100006c0c8282201003106810440e01d078000c100d1615191103070800495407691042c100044034081101d070f6111940440d6a0041100080030340c0e2030480604020b41d03e249019108021158100f00016590401003007103c54100c1034040c3e680e103c001e130062a000c0700301340090802030301408105050418820490480700a041b0501c0380e110003866591894003444410000180310a2240e002035104802400e0054010b0400003031607a03241c1c0300c09211403199846022806d400100500182c10440843d182905203200003184d00d041030343d10104840001c0f02031060b0140c00f070001170902e5480781c000c480041c0020780 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 945988309 1250 945987059 945987113
    0x239030109061a030613060b18070809251e051305040605060f060307030c0e0d240209010503070305060105070c080a0203150915040c09141005040213050409 69
    0x2414030040d04005121452250642c81d0384003103414007154091040d03c0700500c40c9421211665207c00504101c034800da000300404802035440001c1c50302c0e00b405025a0b440d03100f810701d40000c46902e81100000e5492400e0903046203004241480a02001078031503101199440d4108005181031801040e40300310b5010344400e404405200e160b07032041c0d0040d0300400b01801155510b100340310000161840c1aa04400d00b080050f02d9a8403a9110344949140c501e000720000c100f85c00041c0d48203010b8181501c1800c0070729042c0d0340461400c500042014680e040550914081030b00207411404020300350800d240d02e03000012083d038411001c035030800d0b50200c1d0304010907445070300c01e642c1c650202108a00030300c86c103161080d041810260f031920682a0000500c0c0403030911030004184580540704580e10b0700c004001090041045c02902c9210a2402d0301c0a00b61510810b0f10911000b1640014043d620421a460030700d0160301144003074400940b40403500d13054616195442da030000c45c00b08420382d000a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 945989559 1250 945988309 945988313
    0x1111b013801081b09010207031202070905251101020c030f0a031a060313061103090a0314130b1b0105040b01061701050f040c050714060103030f0239030109 69
    0x190409070000d480400e020765011a400669022006450314004581d00700710103000c0c0f04252000309511070040c415980b406c2d66035610b00c04800d0f565001400540c000745024041a6014890280e100b058003d1041924191074405030341c1404558031101080412200c851903102d09404a49102c2d0307015045a0307a40d42c4510100b0f107113401119a820009043c404004152090202c0c1c2000031400100707400e1550321240e03000f86c00c4064010040302c1003034646402d8400c824100000c0d61091403442d021706101000303450000c00402e0150310607003007058184a18102c40f00d10040783e00541e1054406144d1340d5a80c650409130340c180107180d5001a600700740402c41001240000607048a00a84822101210100707084d00a00b40c01d00400d600170440341010f150926150300203800200a8cc10914500100c3d03848403134104018991205499110000403c100340d8454103c4144491910240c0a844000441c500402c04110f00c1140030007144440c800010031840100b20590000800030004c070380040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 945990809 1250 945989559 945989621
    0x11030403060614010c020f13060512010b0a050303070b01350124030b0402040f0908040b070b130b070804020109150207140306040215030c07080301120203010c0201111b01 75
    0x70740290400002240710042555000d00c4035170201a60050406001444038001d20011f10700444818078101c0d111900090f258646401e0b100c128a6000c001241890603803082c0500c200030341d48158069801046400049114101c03000d05503000e40342e210117440500f020340100c005000103040744000085907003408050741540036803101c00c4000c0d078030074111080b01c0d0824695009840041e00e40400c3e040003d0051070154881181802000310028080341c80f81c5400701d90f9046a00004001c4071300050342418020320304400e950218500030b030150703a11031507502c0045000e0054248424050300c20702240c1168055904c0c0d01c00742034a03480c0d8501a0001140080d42c0c1c03a102e10443c00c40c46504039440d01141404940c4c184942c0c0c02500101c482114482d0300941a4401000003503180d0042c040c0500040c07139180110700810046842d0505040d042c010142140ca01c0724500d0150f80c0340c1800c4000303880101007582d145c0d55808003000b2801d9007940002c2d001d024660b404910348506400061454450 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 945992059 1250 945990809 945990821
    0x7060813030c230d020d020a03110f2401050604031110170a06060801080f060f07031404030818010e07090905010603050a0c08120f1c0b09190e011407030c1103040306 73
    0x442c20460b140110100b04c01e9895544000c41d02c8010307001200854003003805200c6034244e042c000411030701000c1da038140180c01d00d441d102141100c01400e001e8040240c0b0400d500d1409481c0c111030440c54103265030303101e11182d500c0380d21060007065280000c011640c010710010540c0280740d007490200740b4186070003e0081519002d07540206140e03a00108074080c00255802031070300e04000402c0c0039102d0387c00c000c141880c001c0c4128205500c1d5242030f802011a134038403500881c0300b078451340d400f030070030030514200368000043c20001c0368582440012401c1d00007501c0c0b0100c034400b5000050009840c10074a015008542001d842d6100d482e0f038107000c00c0360900c0c0400448146400741c41011241d6075145240e8400c02d05441e40d528810b0004200741e01140359142c00b041c1c001030b40010003002e108041074030a081181c21000301018070300c0d040c441c405503006606054900d40000c002c449032480400d11202c80c080d0186003003507510402c01031010700881c007407410300c517802085a441d9603480c0380c00009808 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 945993309 1250 945992059 945992123
    0x3030e032206110c0f04050c1605062215020901050c0a0c03170309280501140703060906030302070b0318070305060703060f03080d11091002011d07060813030c 70
    0xc102c07241d4003c144000300307600d12615401405601400402e804001c0134080161004200500400c0308200328460000d0029030284030384064903407454003c42c2118500b10003140f03017090000e01d220050001d80301e4903c00c200350a05030401612003502d400100e40300d00442804955920401d0070751414445d8080d120800c03a0303c941702495006e242d0014600320381c0001c0d6014155a8443d030020450302d031030140781740003003005841904110821a165030b825125044103c140e000d03052028400b2a03035050003206c001d05228201801030761b213141c1d4020f55501803403040300c0b614500800450345183c40c011410080410200c01c9403c5180c803801c05588404080d1014000300e460540000b40004096103020112a0040b0f02541408001107070440036029200e4005e075a079204121070a00c0b0781d6041541e42299000b903000140d50002c2c41d1100c1ca22510160b070b4050f80340c1c00000c040009a500c2806070354000300d00001c20024907220b2905a80350072550703000404e0702000c1d001c80000300c00d61600c40c8a13014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 945994559 1250 945993309 945993317
    0x2011401060e0904030f050706020a030b0906040c090506180d08132102010f02010b12030406030e06010b0a0f02240402100804030f0c111020010506030a03030e032206 73
    0x80d90300c01c42a110708580d8503069422a14410000300800e01a480c04142e0050b182041440c0401507a9902c00300d0713101d0381070340c00465510300e00d80150781801c0100f02d62014080d41c1c00c019401950320003400300f841d14415184200e00000b420420310b69842401d2124200c050220003102a0925000030960080e4000c1a81d00002000005020580c070003c001080c000380388607039090f113030341e00110b03500c4285200050540d03481c1c0d20a01e54075241c0c03006843d4144464005140c81e5424003500400340c032380b54007410500e40d0141d0014001d05144104a9401d40e40c20305000d158201c40d203038140d05211054038546140c025100210051240054115208610171101c40c0800c1d880c01c4410f5812483c240c2d0054000303102c00b40c54503442130042d40810035050207800c010340f40d50303282d00010324000c400c001040300040650341003d0310701e03007141d54900d40c900d900c000921407441c3c0320010076903441185402404042c4c4401203145481e0b13061088034900e00c2d040aa9040702440a40446803401c2c09104550010f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 945995809 1250 945994559 945994561
    0x6060509030f0106291e04050f040219051c0e030304140303090d0e040608010f0f05180d0309030504080613030909090b150a0806070c0c17030d0f110406020114 70
    0x114006103d0301050b1910641140066a1001515801410300d003401074070f000810030011b6004505d00e40304140032a86140510b603140e0400303082c0001c50958000c028051801400380300301c041d289603004d03030b284081e40c90b1840c0c81c1c1645400c590402c0800c03407c070a030080c4c41c0030000200a00044002c511075400b96100d0300701c1582c40000c05030b4034441114218020f8103c070b800361a0045c41110305528070003005002088090300d4aa06034210391504001610850b5901010382041c500e600805500007402c0e00c0e078040d05204030a2960302d40009200900800d680c0d1015441054025415a000307845a80101c1e80149400c513110164a203002c001039010500345200000c1000300340c000c000a40e5400072007254035450f80841c0201d003c100b85016940065548404500d02e0f0041000c14420f10695580110b4460f840c145820415503507000010383c080c05840310241da610000407940c80c4a40340c0000a02c41c560300c0d00178002840f0401048501010004000904540c15080140420391071144d017441 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 945997059 1250 945995809 945995833
    0x50a0c060f14040b0f1c051609230f0a093201030809041d060702150903071b0e0c070615030215030603070807150201050924191b020d02010c1e120606050903 69
    0x69900300d03118010402801400710041003a840120800f5a88050704a0915000d040005440a0a5608428041c03a42c3b113810b90000c40c05903584107041b00e0031106603400100702c0b840020041ea014080500850030002d200c108035190741d1300410110004070f24100581440c40710361a124030042c0c94241c014410966140801140c030001d550081501070009d52802c1d10550722600d80700b0a0325040c00c0c070405007020014248243c0c0c4690341c4100c880d43c07103042e6200d0725171a14004540d40d03844040c8502610090a00068640300890710344508401140c9489a40b00c40010b0f2802c185a08544950700616034002400f8417030004140c4611007640003800035035a901c907440d9a55515880b0000f003083c500d101c204c032110b0f20010031508001042540341c00407211052560544060500c0d20080c442140b181105080d8140165403220020703100a01410b21400d1000f02211035003600c040d461000503103601084c0303025517808411074007025005c2c005144d461001900036005001c106010f4000c21300a550 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 945998309 1250 945997059 945997067
    0x130b06010f02190f0c0e0105030d030509070302042f0c011d030702090702100504050313150e060a1205040506040506061f1209050a0c060f14040b0f1c0516 68
    0x901c01ca0310794002c180b482003044a140143e0051082591110080b0381d58001041400b44c002002e000c1c000302401043d41b400d001c1c1440d00180046502c10075240406216105101013124030460b0b03011180494a00d100c0082106203a00310350f482e00c81480d0118100798400c1080028003c00c804404c001c100d15514071000c8485810304000c400d02640040000301c00518080c68400d8208010744102c803442c01c015914030040300c1d410385051703444c0d40c800f1904242030f8201c1c03900034010f0700c00e840c42591190100da00150840c5a900405880f41c100070030114402841110720104460030312405000905090400b41d4440c80180d605451500a07000003a0b014284281d1000590304165940030064582289c102d514000d000d0740c0f00b50171030701e4204a00c0803510410000450601480d641d400d800c1c60020098440c01081030b6150611070b0042d00c0a401d04020030684048a000c00b0f5111b07543c41d50f04140c0801842110300c454012074200c0c1040000352340e240e000d50320900007042002e180c95440f180c151 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 945999559 1250 945998309 945998327
    0x9050a060b031203160504120b011a09130903030b031510090204060206070c1a0405100501090c0e150f040e01030b0703050402060912101a040b0a03110108070e0405130b0601 76
    0x209001c3c41000400d4451400380c1d0100c000e1407441c6020340c01c003600c0d00140818002602d0098802040000041c02078242c0764410340a548440c820350b51800e05594041088051004003a0510540d200301c0d24045c14000e400c4030500c1d45004098074050500506d01c03085403101074a4092250b8450400490350342c059108407402c2ea14540c0040255680d88002224210f0340d1075000c450640405250b100035008403413009018600c00c2020782506500c400c075000c1210f5050b4081d510340e604220002103950f8100600240301d8030b0940e01424003880c90b92042580d4400c50b40c0003e890a000600010f100182200082c1a28402d8a20b01c205072240d1104800390b0b2401d0b58081d511030300402200046261010426010201383c1c0180d90b40011007446a60403110300741c4124400070a0703100101074a103440d128281030342c0030894031910300714155210250000d40d014041030501075840c010407200d9020b40344130700c024100148180050702e806011401e205a81c1101210714011101c0418503640c0100112 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 946000809 1250 945999559 945999583
    0x602100e0303010b18030105040305190804080307180b0f0403051209130f180c1e030b010b0310030606030c14010c210507060204080601240f120b0409050a060b03 71
    0x314216400d20b0111001584401d007900160340405c1e5190f04161402e004403440380c5d000c1d4031015202c05855400200305001d5200316000c10041d5010800000c0d40c01090301e400c1401490140140403c1440001280e0020741108052100100f12245080c43c903034001c0054920600c10795140703400043c0390209500502142035407100240c0340e85601034126900103804242c05041c085030320044060040c403003403c42c4000740c84102d0f4840e000c0c05025000c41000e8803590442440802c0540384d81c4545090030810300400042c401e0010100726000707041800c5d80041d40d00407808111311680c0c2d01e4440d902d04004e00c6a0761806c01d240c00b0411a541c0036041c040203164008594a0300c5045da4510302080d02d120302d2200d4240142840380300007258842c8040d00203071141c0030003020154108920302045080101d908403100043c02540d09043d640581c1c201600c0f8000c4c2000364441c80e2040001000e0018002c00f1901301d0f04d0501c007207081c03100c000340401c3c206000f000200541d041c21424585c54504e101d000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 946002059 1250 946000809 946000813
    0x60f0807050607020105071b0e090c150d0603080d051501140a0e03073203030306030703170409020d0c111603020d0f050a030203040e0f04030903030c050a08040902040602100e 77
    0x410041c904041c0014503d031032051400d9403424000b0740d1086900240c41d5042d40d0820300b4907005000365003034040b8417134100d1200002000c81c070f113950703002540048403c10801c0c040040440c010078000d030f1540148020350392290342c01e502c1d40d2000046030024141100c640085000004403a40c540d4000e102c440c0c0001410003065241c4a980401514007042118504c1e030944106400040d440b8140105149401c0c110510040d00101a00e04960800350101040d44a500300304140600c50380c000071110100d0354400500e410030310740030001364228002da50051032958000508044a00c01c0e544c00320310480d10b01c1e181d600b4615258400c07156621098584000c0c1d0300c004400900241c54107040e43c00c440c40c070503408440510401e035101c500b0300060080450243e8000300342030211090f50b08415900040500c1146814642a140144404143d2101030309100000462034240442400342d40c05041c1c10081240d6201d0350341c1d40060007907000717129400050082400bd04003101c401c0c01010441915040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 946003309 1250 946002059 946002073
    0x10c1812050f100e013e0c1b04150b0322060c0f020d0c0b07050304061d0c010f0c0b16050c2d160303080903041706010504060f08 57
    0x2030440c00203080d040c05444030311408102c0d80400000300040700d4442c62880c07010400351121070f9114259401c40310390010203c1900b400a4050300d030400303452452844c0803107501e0515030f802c00412907842109251003081c040e140e100700051f0200c940c9503068400c180c0d0104618182c50440800f150382c2c601420340b590074100301080f00f0103064201320200c006040710f1444d0500762665a0800c8500c04004d410200308403420030311042d43c052000724402d07255414940b045c3c002c240d66046998000a244d00c09200f000700128091084070381c045400050b041c5555028075a440100c0c50f070703070142c13440311a0008030001c01d540c00c11849003030340d03001c0c55034010320307401054644489401001a46150380390410005020345617400d40c04000206604026450034400302750001c0a2610070120540403441941c130400c213070418a400e02c201b03182101c1d094900420113855810f8042e08620642c0d100a6824002c0c204c0306c01030540104115040302c078120b4081000d1a542d00761524815218441d00b5100d0700410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 946004559 1250 946003309 946003319
    0x1703070c060c0207080a0b16140909190e0715030b010905041107020d0309080d0507151104120c0e0f060a0b210106030b040b090622060503120c010c18 66
    0x80c1020002a42d680103842e48541c85141c01442c01280719415142c0ba45403c00f884800c035010303142c00c1d03619281480d1400000700c1444150085108403080780d401503a4403400181c5050031a07803210f2003030100d050203100c0b0ba41541c0361103175916040d008003440c00b0309030125404c20b18002c0c40750b0100e244040c1c450b20f106c40d1610701003200410b03800b068030310038031410400344006075103a031101d50402c0c4c0f113030319121039082c10100d0051030b00703200085a400b841010480702e80455485920994070b449004008600024860386449907401203034031055111020740d1760b01d400c000101d0164819220420b0401c1c50a0741c442c1e031140c2c403015042c0c40040d0000380d10700d028443c20380214018145801002460040300c8400c1c2d840071a070003402d9105400103680c4600c18405032505009094681204031501c85413410304e0000076079060072841c0b42c410724004880c3d1922010304e980c0c0003c401440000c003601c4410b4276208048041c2d501418150089503c4e0903038010300c00380111a08548480349032260400c05080c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 946005809 1250 946004559 946004561
    0x13050603010902060f03040c0815150301090203010c0306030218060a18020f12010e1b1b01110f120c0a0905100203090a0b1e09030a1e080d02071703070c06 68
    0x15210503015501da40101025840f604020700442d8000b079206580ca1400381032148000ba074a4020540c2a0003500200101e84003036440c0a07001290b0b40c400c10640c450070b0000a00620107000001c2d015424010800f10b01e80c0c05a0188003140d000351001c0f003421002c0ca458001d81401151007680c8040c545d001480000c050b80c05c8601c00c03d40c44180189045039081c42e4015a400606c42c0344000d01c48000184004110303844c0040d0085404039404030321407007141018034140030b1040d010042610810724025222001d4201907528180d00b00515550552550341451a034010b298a50481c0b83e07003008581c5240541c001c460050005545150085080031f040140101d000c508007011440140140c1070195103100c102001811040d04260740d40c48000d020a400f800118401985450203003c00041768401140045034160f0106120549480c408541803c1d038801038000362151001042d0484034440d540c0c010b01010b8003c240c0703030b1030000c09029624000d00c01162454001303070182041030002206 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 946007059 1250 946005809 946005811
    0x50402190e0a0e09030d14070905011b1728080a02070f02120706030f14012904230409021309050c15030f130f030f0e040204060c05010c020c1305 64
    0xc000c02c0c000c0030a41d00c1602c41e009070429030310200c994200050031520003585115080400c01d0b8511011300e14584060050003802d59481001d0510126a0100701002500c007500f403607660744015070b0580c1403130005161440d07402c8140602e01040350240d10010380c1041d46140c44c085480e994500840d03664118608019400184e400c0311a80604003070a40166a0b401e410381e0000d5000c8010600c26150481c01001d4411505400c407000c5c0c500180d60560548035074040f030548940240c0d24185981503210340e4190021b400c024561094003150109226184010a00340c0714803d901c0c208415000030100800c03503000102c001c0d4007210755403100854041907081914010700600a903001004600040703810280c010248070313011100001046004000034000c42e8002d8000c1203040803680c2c856031400b114611440700a028060072040c110303242d52182c00c0307030624510050b006540340e5a482c0c5000d0704119804d4011076440d42403801003540184001040040034200a1480c03918601c680443c1f401064 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 946008309 1250 946007059 946007087
    0x4515030601151404090b031501050f0d050a1a0702060108030a1d13050106020106030201080c0a02030f131a07150b0307060f050c0d0c0c1202010f0e0d0b0a021305040219 74
    0x150b412403d80306000250b0191004014071040442d0881300d40c8101410038a4043c10445550000001031010f070700c0300070b114542d42e4000d54003603094040c2404c1040c907103140040001d00320036a20031407003071305101c0000c102e018580301c0d001c850a0f030362515120b50f1030340680c01058000030707140881098070310003030300c554081d01002403c80f0324010130707240f02c9c82c0903501d00341c0146025039102d680410031540c0c004212640030703814100290a0900541d002510380c81092400c001c100c0c00402e42c01070b1000c14490b07482c024641606011860b42c015100d4261310b41094a05542d98440c0b8403c5584441540c00f5180344002c0050280c00700c1030421800391420b200c0361001c1c4041090510074120f031040c040150100c00045525101a2102a8a802c0f42108250b400c0380d500f038640000d030500142d0300b10740102c40341c001b541881074010240070007050344944031400252440190703d05200303405105500420420406405040b116600e420521003a17214a1800c000c14100e0a00107482c0c8612070010842403072 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 946009559 1250 946008309 946008317
    0x3030411060d06260307110f01170f0a23070503130516080d05040e041709100309050705010e0307050409051c05120a0515451503060115 60
    0x444000c2081c0b0480d003642c0c11441c43e0300310440c80c01144403152101000001d06650086260086503541d03007040c0d1406081080c0240d007a07802e49086030b0702603050460b942c00d1005200c01d181c50003800f454038000098032458280c514102c5071000e00c0310302c0190f040d41306103d25084400c5450705c0908689550000301042c500c501400300100001d03105024082c44114212600e030245401e101f0401d00741010840740c10140101000200940c1944020850b4400d4000c2d080b10103012840313210101a00c5245545070380f10414100b0fa00b03030160982d002558403130094089039038058071346006489910240c0d0240364180d001400c104540d103040d802883c00944501d059844104140b0b9040c80c2c07020810145402081c004104108003001d42da100e10f51217507107a44184260b0500d0350141c1d81e0298803800322070141034803404486000d007604416100500340c2802c032303030082d2000e42e880006d050902d06020b0b501c03809141c0031680d808184035511482030f4004000d031125900c2c100c07601d514080e80361a114140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 946010809 1250 946009559 946009567
    0x9040b060f030304090b2107090b03071203051e030903270405070c03030507020304050a360605040e0c09070c0f051e010509070b0d0207020f0901080115080a050303041106 75
    0x3510248060001401180e41c0424920300782010800c4071a42c0b034120701520301c02c0c20074034004000b0006000080780d01d0200c0000300d9041c0cac840443d00304074560300700fa0145207445001c8000c1551180c0140b0241085480d00c8103c40c100c41402103070f17880203940c1c05030694414010210b90000e0002145020b00c1400c00ca4980703d510300700402c040e21000c07102d190118030303a41d40400a00d50035024003a4001110302c05585014144030006100f00b0980c05202846000c2d0400040c90b985603191955a10303841282d540325821560040101030503d174041d0500450403c80c1000ca160310000b01c54240d946c000300204a11b50b10010100c40b10b170b44110b0252804003200601101040061050303540d00740d14005007100c4070150000c0cac00d0965001820703402c816800006d080002d1202c41080d211060070000000d070b40c84160303000051180e409403000316842004000001010300055000717031851111400b04488082e50f6003400ea464204010024125030001c000080000d10140c402c009146002045e1320700f8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 946012059 1250 946010809 946010839
    0x3100c030b03060a0b10080403021209270106030b09040f060b1f020105060f01080f061e03060a020408060c13030b061539120306010c05190308060f09040b06 69
    0x180c04002d0f11014071495417411075034003e0410000868030612103007855485428103a600035624000390183d0a0480c030f0108604400c2e558440c00e0030769030080d10300d129101c18041c403682c00c13003440c0a00c500d2002c24640401c8899038280209a1441660444030801501c0400d403203000c05044080e01300780e0b204002403074110f44007a00141c1564042c0050b070002815250200600c540483c1000c0111706010403041000000c0300e1140302540c4c098401d845000489207040d825603072070644400050b525006200c104a17003100a03601a200301d8000e0000c869480d11000d0b1a0b19079442160002021022681c03024408588814020f9810507805464039000390007100608202d500b10350f50b400343c0c0c1c0c8440903050b10f030990240d4504010300003110407810300c00d01c07a00c40540e80e0000c18084001c035131800300014a05070700170740c031941409410006558180c8185170140e42080f00392901140452440008190941007014041e1003003040501000d400343c840d03441d03900c0d21840c024441c0f64000e42c0080d1480c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 946013309 1250 946012059 946012063
    0x30304060506090a060e0601031a100c0b070908060a0b03030d0504060203160503060f21120403210c0308060d083705071403070507030b160c0203100c030b03 69
    0x48194000c40001440341400350801048080151242424500340441402100650701c00305800c07003000d0034000b43d2081011003c105040c41501c0c5940d0081540f000001c4450700003112141c29441349041c40c1041e40e82440c01e9030080303100d018060059101100003061407450358000003180c2402421241803044d500040425510100c408940254021050003065003038848164042e02d0b103400d00b64154600540420122141e09c02c2c00f52095900d10001d031441000204100c102d5901e40c0103403412009036a03541e146940c0030f4031084450b03008000040c91004101c1c400c844480c4805c0c1c1c0d803440210640e440442e03603000f000d00b01e554412501402900007521000041680c4070a10503403801c4418024111007403d4000d100e05140105080b40d40d08030b2035030280c2240c000c0f41c3d008070b400030844012503c50746180214071005000c1d100e413200200a002c0700148081c4911420001c0110068810000b00c0d103800030082c4c0250554007a00c041c01c0c40402e650006090754025180008807820218000783c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 946014559 1250 946013309 946013311
    0x1090f230616020d0906080624070f0b01060c0503090904052b0212040b03010b0a090b0c0105060a15080c0a0c060906020702032a0607060e010218030606040e100507050c0303 76
    0x10b101a03550702004081540c05110014405280307040c050403080c500b042c09420b46100074080b41c4542012008034140701d20410f0002d041644003d0482e450398050b01d043c002804440d07400b80c440d09800703000050390b648036007403540b10658040065418189880c1c14804816000b40040f1903900035540140c440380c100c2510b01c507107000f0182800820081a4501a00f0030002110310241c1003000c0100b403000c2240603007144c0c1106c651407007040d13403640300940c101d90005290708000c1380501d0020f408640c541c4150001809103504480200080d503075141250715040a03880154003069888000800c505011806000201441e0405038100101070b0303190011111144e074122046a0f0215900c03041d0700307040200d003071800d031200030818130350344002103814074000b4041c2464481c110001c3c9400802906070411282802c0c41002036443e0760f44000045c14030648845154001e2091200042892402d40100b954003034150f40581894150708000e080504001014a01484001c000f00410080208015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 946015809 1250 946014559 946014571
    0x50d0207110907080609010807542d0b120a03020307061a130c02101d10021809100e0403020f100605090f040f1e031101090f2306 57
    0x20944e480c10ba002c01c108245c5c10781050000d81c1c0f1001702406041040c2003101d1220200c0c460074085688010740700c1e0419100324910390b142cac4100500e0403c04000650f00e0b140b030717241011b200f405846030b58031101628031694054001c01c0c9a00d19108008400f5651020040b22000340c840701083c58041c0b2100e00d40014a00118010f87c0000740303043c01d2084601c1001e4601596010b603443d00c000075000074501c02c00c00c0200041e0340e40e07608000301155000300810001120321840034400710600d0010703006004401c440220b100c1c000e215114103420302c14802c44000c1e001d503000c000c09000203041071001255004040210608441602090352842c41d00120312980c0b10380e00400c194421a0314403403d040b00100c400f0382490828030180b2003a070701c60400e40c1d48000d015207600107568540c28046030f841c0c13a241c005000c4410b041c501d202400b00d40785c3c500348800e00a4a03825800c407040b8042c00c1c200d50b040380019100c800304d11540c40000d1003514000c2c952140540d0020300c01d540741030300300341003040941e20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 946017059 1250 946015809 946015817
    0x1090519051b030606060a170a0605180c03010b090a0305100e12040e01030311031e03090d0c0512090303070503041e08300c1609051303050d0207110907 67
    0x20400c542040040c61002c14010b0356100b9007403007804a5996140504428800c8802007801090710b84541c245850281b0441c203110700909100a00c00002c0c00c1b580200303801081e418070400d01a14000d01c41500400301500042d00d160f207014030f6951540c10100c0c40300d50218040c0710010200c0c1040102401800c00607200040202c031405c581440c1210300c2c45000e43d000d00900003080110ac0240c015411640c060030010200740400d444503055104008510f00601c92810b14440f103406007002444c812291001101c0803400900020344907048480c0d4001c005502221510300b141c4180b9019040c002400b9040b030342041e040e41d0300c040c11a041174205205140d00c2144581400c1107030315005000b4084800030f80f20700622408080c500401c188400032150302e164200408640500c1c1c200c80302900c510041c2e41105029034140b8210641074815000c0d158217000c0070030200b4450348819040c4551540300c1c10320780101c020440d0084c0d041103500703681070841c100c4502070603140c40161038828551551 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 946018309 1250 946017059 946017103
    0x90f1309080f18240d090515070f0318020d0609080f19030c0e010e0a0b040902120108031335011b020f1b2106090d0c120c05010905 58
    0x56401c0c0d031507804007400784103400482040c00c2d4055640f03900c03065030603a030380c113159902401c4003848003400854200601620544030806004044200e80c54020100c0d42d030341c05807142c4002c0c0218180c90300400704074807a00d44a031001c0014608140d0071134069101b1309000c2240181134803800d0040d0031902c01542d0344000060440400d2400540404000f01c01d4101002a00314401c0000d11442c426144036050004031304502406a40320f000c50002020104090355850b40c0f55698803001c0d40144815001c034074030030000440c81d48070100c00d4480110301d04011031265442d080c04031200f44540d1034000c4005d05026114030441032002d034040100c040c0b140011072a9011120000b0492254001300c1045401040010b08206c00202e80c42074041e91442c5041403030303400d08001078001d464441d031140d00c1080c94680784514000104000f8400c00c0781c14165003008030b14841c10795026099090003000741c1c011101c1c01c40b0aa014074241440d85016500020b86019565071741c42c0740851094041c084198810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 946019559 1250 946018309 946018327
    0x80f0d0e0415090b01171905011410051c02270d020a060f0509210709050f0c0a051903051503010e0607030b0303130f03060c05090f1309080f 62
    0x42411505040d0580c1d0400c01d240d501c04000201040728000c0d9901140c1340e15400040b688145030102c5001c0b40c42c2400c28103801c052132070040c00c10f03030980c034240481c0c245000010403200c2e08026400001c0302500d6141820130f000b00494030303a40601c90400c00b140c0e4807880703103445e032401d48090721140184e00390340b601c0007140600b010400701c80591024841c4039200d40500068440c80c02e0013084550742e0914200d002e5500009550501034030001d41c0c2c0100c0400c0500c20360100184a2030160311100b41920781d040d440c2c80c645000c6e594200d0f11481c2c290901d101143c0c1c05148000200300c00311161500e54103242d00d540d40c10302da09070441c5444c0c00080c0c0725410312002c80b0b100c0c0580040d5040c218020404a069520200c1d210301d0001d00300e0080c956030300b49004e13250b1814070880d036101126411440010f52101e4103101d601ca02404207a134483d2804885045540c0550200d0310003140c01440184031381424010031058580380c4680000e0103895851090010b840c0300040c0a44070044998580c0741c0081c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 946020809 1250 946019559 946019567
    0x108011a03030a090509090c090f07030617030915070b0f01060e010e030606040c1e050a140703020c122503021002030906030a05041e0f0b0a0b100513080f0d 69
    0x1040c88074820742040101241a81d04002400e048941c1505e503401280c0d1100300307180c00d1480018071035030048a100d081100302031010421501c9840d29803001c01002d925400d0b000c405110654480e03100340d004000f054640d1801e42c4920000c032025111443c601a000c0d42c1c4c03c607640c84140c6440c0c1c2d1508229005119007a002031100701d07030003c203180844402200d03c1c0042e80d240000350005029540c2c0704003401080d84664028500e410b990700e490f5124003150700008002d0390012001c8800103440840c6104030807100011a050550141c0c02800d00b80c20050400641104501c2480114801d2981c54944500c240c81e03010510b00c604a4000c83c62442c50050000e0400840c844034115081005a0701c0e1301c0c0e44500a403a0400310041c0000f0300c42c0e60b20b00d0310080f80c4460f03141540c030003143c10211000300102c1002c60104181301e04040e840a0300c860f00990b007902d00213040c0681c880ca04801c0c442120740f040c40a800e036030b00c080e20450080d581e19900682400901030404601e5088220742c03040715504 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 946022059 1250 946020809 946020851
    0x30c1b0f0d020303091f0605040e0d180b070b06210c010e0d03050f1e0f030105190305100c0c0c0e1e0603120a0c060c0315060503040203030702061b06010801 69
    0xc0b80090b510f54504200000d845001d00301400c45120503020160211310030540c07084000d0007003d0030410601481d40846550b0704030401e00c0a0014118080000001c01060a140100e90403018a01e06019145e0781d040c00030740f8000c0490740c2200442d8811030402c001109000740788421840584203c4151030001032801c203441d0f6005020780c104407066000a46c0c01401c98200d40103035503107240c441003841545e003214144400a40340f240004140c00c1440e031b0745000114102c440c00c55168401801c03881e10240c0414007448041d01903007000b1469915901540c0107401600d2040c030f494556001d903540d861041d08040d403c08070780e1000150801840140c003050001101000c00d2540d2102e140c1000025a119114140c1446000d0f02042d4a21054003804201003181d511480c00d02c0000b0100360024003d010308281e1a041c400006c000055850061007203a00540e0040c019500d4072029809100702c640c41001c0c0c02c00d00030141c07d0b9051000000b800504d010344003140c008220032803054826010500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 946023309 1250 946022059 946022083
    0x320d0f20030907060309030c2009010909150f0605030a060203060102010b1c15110c0604020f012109050a080a050a030f0b06030406200d090204240308030c1b0f 70
    0xc04000b0310805501c00140c00c0110745040c135001c580d01603507141c100e81c218011940103140004280d003010000d89903408220f074050090303407592190380e03a8007192015503110702c4003c1c0015400305035410030343c1c8468001c0044019000340101d03070349540b1301c04a40f4019001105030b4549601100340615507a081c0104100c0030001c4440903100104455007100da2040800014009101004003402c041c1d86604401542002105020b4446800303a109945810080360100c0c89004001180744096008120015aa216001e02500d1541450141500401c206039058a991082c040501e00094101c40102000003982d40c4007601d40c01d5110f0050180c818a1044001345801c01d12400c0854865030145d03980580c004d600071403c0c001410002300d0a0a07401004600302400080500754000b007074006011031803007a10101b20781004c404001400400d41c07810040001241c00c41000401d0340c80008e181c000020000c460319000c2000075444071644049403405441c0c010640c80c5400c3c0744180a0030003040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 946024559 1250 946023309 946023371
    0x121801050405090a090609060513170309030f0c030403050a080a141e03060a050a0f0f17031e0904140921031f050306040819320d0f 58
    0x2d0410000600840c00100081a003035a1000341c07205001c240d0f0080081d00c0c0d00800f00b040982072816031155074031035010701501d9607100b0f150340b82c0394000101c00312840362480f40003071820554100c40d00781c01a48100000040b5110034000400811414018800d0841c030640e00c0c00d655a80703a10f00a0401e82c1d0032030b018250000f0034011400c4501000d041100c44030710101130036949a8600c00028a071940c2c0f9048690032007500c40c80421a0280c14960405480907000d040b00e03107554451322181c0182d50400300c3e10103500103000c1d1100c0400c038a85101000504140c00714100f00301600444c04580c41041c222403000800d80c00c1c401604002c2c8803404034401c103800441d510111800c1041f4251001810000c030000030b030040048a61101142000a40002030940d01f16080c1820420955049008dc20f0110201c903503501003800d00138010301c00f00d0f4282010f420340951142800d010b000d803040d079001120201c1000103840691851044000d11010303024005450400d40c9400d0318a4130800c5060301000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 946025809 1250 946024559 946024567
    0x18011806050a180623070c06030e0f060103050c0603250504030215160215040e040b060f120607050318030c0f06130b13060b0d03092c04030810050312180105 69
    0x240c0c1d03001e015250400c4d01420310006402c1520503190541c0b040c01000b501d648107d510110782d0341c0c0c0c190003605d4680d1900007141e09070401e0580c1980c445100384402880d0360b00021100c00181407040c06140e220030f06804500025580b05542002401110340003030000d4030001d000d004516000c400d000542001e0050f403030400c035a00d0758203d0700c3e14480780041d1003154420900c0641001d10320485018101102e129241414146031009d9814001e991451082c2d0341c041c1c020b0aa401c5c0015207040303440c078100041c6542c0c2c42d840d40584403070b4005048400c280c03110080030f05076400c080004242c1150f00200030140c2070041180c0c0c03030a184000d060352039a00f030054122404280020b4450350450b01c4604030000c100c02a10703061000307163304400250462020b64a020504d5006039000c41104c550b03621044408104107084006400d40585003045071000e8000724011a01c00e20900382d002a251142840b2291580d000a150106030b40c1d0121074081c0c00540031052442032188aa1800400c2c01d0550134 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 946027059 1250 946025809 946025819
    0x906090b0a081f120215250503070b130b0702010c020a11040209040c0c0515192004091a030601050109120f0812010503010506030c0618011806050a18 66
    0x30600c201c191080070052000042507000c4000e1061116000b0038601c810b045981e910304007070000c0b4504205034818900c418512400c0e14502085a90f402031211010342150b200d4413140c603403540f03c00815111844203005540c0010b02084089000d08a00c5039028090b2403d482e002128050061001045905101c1070107440754001800d00b40866209442c4c6682449210110340207014030180c8a91141c1022030207406135400c060f802d8501800b880641d02103c865004032414040195140b040074800400c280c00210300d00d500000312421038032011712008080c807203182d0b05504143c0040031030503036034440010010b03807000d40740228084c02e501400f40c0b50316283c00a08041c0e0588942c1c00c0c1c42c02c4200620b0204890089444101c89c0d00c4403009803225180030401381c05001c00d024150082d8a40404070746c4e1481d000580d941c04410007041e00e850840800302d080c1440d180d02b00701c1d6062000701010390001c4050190210042c03c2940d4451382c80701320500004040f10f985611010b0107207161b41080c85 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 946028309 1250 946027059 946027079
    0x90c090608060f0420090117060d02090c070f03050a02070806011805042102212a010f1a0406051f050a091707030b010f0807052419090609 61
    0x10780b221007201c108411184880c08107010342a00110100c144140307117180c280d120048000761150500c280d8030b080040c41c000b8103030030b80c511042d526240d0108815503043d00500d89040d200d075004e86112607030340c10065a507558580301513100300c08401240d404288000456810400c0e000240a107000034900c5514240c2c070303100900345049000c100345031201f0019050049c0300403019800002201a40e0715090a104025111743c0c044000c01e84040504080e008900c2180b000d13030b1245801d80088845003c00d140030002c0700c00905682c2c00c165526501c800b42a4041403040312900d100c900c1c1c080400c54650030030001213407500c0d0440317413144805088100040d16012500d40f1034542504000d580d0382208030040d104034150398410040044200351105107180d010402c03200700c038451140c43c030069803a0384140c1c884001074051034499500401c8208040d2402c84444444c0800080c582034100901d141c403050a03510804a00800f001c10a00b4150b140354400800001440c062038241507043c00c02031160 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 946029559 1250 946028309 946028311
    0x1e020f0301031403041203021c030507020c120c040c0c140a080304060213150507050c0319021504352a0f031608010b04110304031b06050c04090c090608 67
    0x541a002d0b0320010800305030013003044038041d00203a5980d01500300c0310f1600941e60303501021110024030b54601d02c9100c443c06809803c1c0190000c1e0060500440400280608403440040c03036a1548104070803062540c54610503640e080380b82d03558003110003200d03041c00c42c0c1c1c80c103c5500c040c05170351183d100f90303020030114010f0740e8000313900001c0540c0d103403899071442c01a02c4035070308040080c5400f01070091510b90080000c01d40b4520a030306a03186030000302c0c1016120b035043c0e100c03d6450140745403154010300d000b0741d8428255080321a40b40c2800d132289007541e484049190402c0040d106050b01d0340402014080d80070110701c07031800800f2180d00030b520f04445544440c02450102040c910301d43c035255a804020301c015200517046550b200808900c54001205922070195207518000881c00f035030501e801000c01e0954100c0300c980c51500c1c0c55404030b0b02c0901d00c11440d84100401a04400051054051130b03000307490403c940ca4a0b1800c11fa04c0700103c46101c900c08050100c4070900f00b104582183c205 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 946030809 1250 946029559 946029563
    0x106050f0d0b092107050613050706030f060803030c0417070b07150902030f060a1a060316020a050a0b0a06090b0a15020309090112140601060806040903211e020f030103 74
    0x10070a91078a144041ca4400c104e60324580d0140f00d01c40400425407650b0150500c03500480450302c0c0c5440b0f401501c0a8828035103005049030300804001d00081d8003903000f4404560305040c0016006968659190940d002901c0b40703000d039030780000e08220b9080c00b400b01c02610a4440c000d00032083c600220501d0603c1200d0005040c880541c582402c4034210754040728445030050b003902c03540d8201c52040d82e1220000c44220301103030320b031404110b82c28608060900ca00304000c0c00301031441d02c808100694001b18001030004510950030200000340e000c0c40500811403040ca20450b1604006051350305035103a54019021443c9020750801e01c50303550310501350444415200c510400004210100c1c1140300d020034580d0031082840c000aa0749100711844001c05003c1c1c007480c0c201e6880d442c00c02c8e813030741005c1c0700c1c2d600000c003080d0103d00030340342c603078064040765100341010b40031401201c02101c10580d11003440c52903990781d0f843e121449685500e01030481c00c1458011864000c0046400c0c120780018000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 946032059 1250 946030809 946030823
    0x1a010b18130e010923010b01051213050708150a0b01210b0a03050a02040c0509060d11161101110c030d03050a090b04050601210c271803020106050f0d 66
    0x103010079610709640070810080488000340320900c9141411440c200d003040144214075098030380d0102480d010311400b00140030584d1010700d404040d0b5040b80200001421680314002d10318010f04c00224104401e00080030208003801001c510080100782941d802070007000300c9070a00d1861760041c2e85c000c1c101d4200d0b48038080003168181408030400d00034800d200d803841e0030010840012051020004001c280c082c401c940900500300d20183c211580d01903000416001502445003100e20941d603080740303007080340c100c0c0c40c20705101480340f0f102521343e840c00c42503071200902902e80d00c1c956400038080c202400c4200082ca506c0d100c02011a81d2400c0d8221110704140d82d035000314841c404250401c04605401000c82c01c0941050b0030103903103804080c81081d0402035030800201c6400624445040120b4002c0c074050a00c5207800105441500d5508010f00d48600000e1038480000b46ca225609140c40b5078000d2030210001803801a00315031094105070f229034074008841e41540c1c0d840318000400c50740024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 946033309 1250 946032059 946032079
    0x1b050a0506030a1401090605030f0c0d02130902030a0309030605070801030503030703020c0a0507080f2b030b0d060510081908091210020301061d0d05070504180606031a010b18 77
    0x10414004110302501d440040000134000038904025812020a80c5c20450a0380c80008009800d103075601b007011003158020381844e405a0162404184005d024030610002142e07002c1c455002900340008140e0480114038055424030030300116204595000c04c06d802d0040c015411903c80560741d00000b07150b181010380015005002070428400d91080302d902000b152511500d402c84143c64050700300440c2d41c01d10520300b00115440a5845131240751065202d0944110514001180a041c0c103a4215400420410450001031400c0c45030b80e10072000200c00c035003014140f84180b402c0406a1007140e082100304104100400c02031000c5400320303035045a044031484d500a030607504000891081040040c4003000000781d43d50444440c0340310600d280da850700079201c054100414140440400b4020364800b003800c0c041414558440554005000061914902d40741d0f00c807415561a034108841e2444405146011a80c03404030041c09081c0f89441c1c40d040001140b034840301c5c000300d100c1c2c40784a950444 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 946034559 1250 946033309 946033321
    0xb030601020a14281109040f0f061d061614091e060a0e030709140a091b170616020a0b100e0f040201020709051b07020301020909131b050a050603 64
    0x10702034000140b444407036420101503000a158481c0000903500d07005104043d40312890013010240c459070744154400c04c4c3c25912785501102c0c6004140480313540da40c503400c0b0350324900003802412500842800404951400b089411012941580b004050107c142000f00d040384c0000c05492010030240d4500d5281d00707208080c042034001d050304150b00420001003048400d580306030400000c250650032a20703440e03036544140044510301c0d040f0907002c0300b0340d0001c9a60a26190170000b0300324001c03160001083d80c4203040b45c100640590014610f244010803020040c54107001c21a4000e51140a10518143c0e144001c3d46941500000900b043c0a0000148070180b41034000006401c040480003400c3c0352081c0c200703100d403500780c50a0340548104440042e02302e16a0103504d12800a100010041c00256030305066035801c6840c0490785550280192041a00c1b800511381c40749000481a484840031400c08c0c44603208401140040d4002c1d004041c0000c0d02d0381a42d00e4200c400c03d03205030360b407a40c0d51 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 946035809 1250 946034559 946034563
    0x120d0c0f2604020a27060b0906041512060b04091107080a0f0c151d07030c1401122f0f09010f0507060e0c03070b041809030203131d010b030601020a14 66
    0x203401402108105c000109010a40404001902191030804000e0580c0f5800412a9402200e201e254800f03010001800b04000000c0c00340740120003400d0180f0f00700320400306a001d44e03c4079004a0240c00c1d0102d000c00001d1104d01840d5265428403442c50320b032600b0f5494040700ca1080320445400c1c410000c2494004d180302c1da03e00c0c1c0c0306a412030003502105140d415000060002682103010300303014416074850300f110100d1038204681d409009544414684400c1d00b070099100e00169044c010707400c80001c0c602506010301d2515a0059261001c0d0f4a88592102e00780301c0241100c01c1c07901014400c2580001c1004101c0310421024240403090300e55082003101e0901c6240001040e640c03e05204800c40030700010780104680c1d00b00c081e28a00c40d203038904003825004910a000c81c490307004115014480d0071b5400b0414860003031058a160140c0003001184114840d8400c9070034581692800c8102c42814281502410040c5140ea00c0e600381030000030f5403401d805101804100c3d10041034400c01c042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 946037059 1250 946035809 946035829
    0x923040c03080f04330509030a030f0c0222240506090d02040c02010c0f0c05070b090a030b010e0601031a0f040509070504110306121903080702120d0c0f260402 70
    0xc20f12800700450000d203050004900c4440d2110202146030100d485d400e0040007030311500500540180032540352914201d82200b071f02d2241c041071011861607c0050b03103c41d0b80c117000c0c1140c0c0c00c0c00c0502c1001502c00340d100f204ca1049404903401c50880d46440d82c40840f021781421a1000c807203041d15403503c0c00003e28a001b080c0e100035802841e1091400d0030755019048280b001401e0344400000e000c2c201c505541600d0003000062580e000150240802880c10303000c1c21400d0340241c2074140454490340e400010401c01c1e000340119052501c00c11017150b0f494012096400c0d00e0924201c00c1032000000702e13025408000c01240300341c0c7c03150000350107600104281740003024020000d01103942d4503d6907418552040e90b8860040170b025214503c2c0340c1c00025004180c1e400c001c82051500347e46d4a08440c00c03800644400e045004070b0303004200d60314248001e003024041100e800111301003030b690b024008402520145041c00030315250080d660303411040c2080000e84000c0c1c50481c507507861002070003600c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 946038309 1250 946037059 946037069
    0x90317070317092b030b0f0d0204021e0a2102270d06020d060504050f0603030f070309050901150314011a071a011409010b030405030a050a020a05070923040c03080f04 73
    0x4403a00c0030031328440d14001c9000b01290151420406000404140200d060b050018180c00450340c0800e10018102640284039010500410038407000b07084440d810300b80d000c801418002405800c00825206841c0d1a11030b000100c00000c5161074948680701c0c000001da20001000b030000000b0b104588d46030062146503440d03001008650b10700d500300d20500204481d0003032a0140f854000001c500c825005081030180d2001001142007148407009420554888802141005140030000500d62214500c180c083c1511070041c442a40400c0002400c40308020000180f4111002c010440d018450a4034581d40b6150500c0350381d210818100901d6540d001ca6081585044c240c000158510940000c460148001c454042a0b82d84e910004007150005179000b07007076504104040981540642c004007604551070040e40c41e01016521200d04102e440c0c0d010381c07003680d201c0c100c042ca0310721545540c0f04440b038551644101c5040039240c1d1b600d0b01034240002440604009909800030311030005450041c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 946039559 1250 946038309 946038343
    0xb0a1a0c0a0c080705030109020a0b090a09020a0203040513090f0215040803120709061806121e0e010c03060f0306020703050c0f0a0219141509040c09031707031709 72
    0xca52032600d00314002c42c5202e094458090240c010070a45418010000d180f034000b030502101ca8200f1704402e00d154441207000364059199000000d80051500280085620680280d40c603640b07030406000c0015005c0c100700c00f81d07a1274001190300140500aa11405a40503076071400c10200c16424030140340b080740c0083c1c80798440072500c640500345070f182d06807003092581d0340c0e41203403580d800e0b00381ea40f44680102410001903044003070040c28480c180c0300780103250615012031400e45041d104c1d8123005442204024440d1200d4030b40c1c800f804240154403142c4401c1c6010405a450206104c021030103c1c000100381540000352a000e144c0b02d00d0a80c0c0b040b04a50301524050001410003d5403450403140407402407641c100c20b110711f40002c01d400001c0300e00c00194860541c030300104100c01005130007440e0094a5050001200a813554171400300c0e140d00644035209404c1c02e60070144801440b031403002210f44e008001880000c1d5100a09200c0130b00c0001d502d1045459030300410303003441c4000f29015040303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 946040809 1250 946039559 946039573
    0x1204110a091e0c0f050d0f0515011409031e01140f010608090d050904090606080304060e03120403050d08090f060403030516020a080f071e050307050f010b0a1a0c 71
    0x15403591220401519040301d400103620241c2c082c0d02690405034100c1c001c80e02505600300c242d8004c1004201190030304070002203080d00c001c0c010702224000e446d0b01d034000e03103e0640b021171541c10200144501c4041c3c0740326403c04100c1e900103680c2d0880200080b00401545100940701442508080d40454010040350b02e53325081d1005241d2540901c111000289101d011994002d800b050703c002022243d81d6851070080c00741c1c20700014007a4031400b10381583c0e031210001440c3e4030920203817000e40f001d6a0380f03103402c54400c41003615203502410140c1e1040f10030403040000400004d06034001009a040854281c1d8902540c242040d08020000c5011301a240800040562503400f0501c680d0542d400ca140c0d14010341001c81e41d41090010003014014104a0010480e085401030900380c2e1042c0003401d00c0007a100c4400226000c85001110280d101050000030010b00f1301ca01a4000c205000030031045286d6000030314120118450201200e40c4a180007aa9031509000c450045003120111600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 946042059 1250 946040809 946040819
    0xb01121103070305150a0b09160507140c1002010b0904020111030417030a090e131506050616060e2b03110304030903060516210207120206040b0612031204110a 70
    0x480c1039065100ca01c040703074200090b1446040c3e2084001c001f9000d0480c0c8080d559041444030007608100810090003814402140090500101180100f034444042d24511003503005102542070b142041c0000e690501610098545031000016030080e024a420707100749140048690851017550400000c04054003610500e4401c008001c0c00b002c196543c0704002d056885448076a6110300340c840303102c007200c0441600302040c0d286c04080c1107103686880000d105030755080012030980c400d10001c201c40c100740804106205491080b070100d403e024001d010210360071802000d1000302d00b00c070b000384000d82070581e41c00c00d80310f64000200314009001043d501e06007802d020304a81403500c0b003255018146000103105541210b8009038500c01c1d9118016000c43c1a00230525000f580e92560181035400c0c40b02c3c801280b142054441ca82003590080c2095050504001c0301c40340e80181814081e8035910154005010000200ca00360359102da0581c800c0d4440d4075090419074000c3c0310700e65000c42100d0005c12 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 946043165 1106 946042059 946042063
    0x12110d0e01061706010f0f0e0106112d070609060c020103051e0c19030203010f06050d09021315080c030a120c0c09020a1107030b01121103070305 64
    0x3041603d41c8115481802ca004018096500802c01004901c02c0d0300c460130058000ca101e04202103013400c14106103900180b1078001084000302100307070701000038064001c190113090001c100c400300e0400000c1c0050b1040240c02135500416900041160242c240f041c200c1da9181c40300f02c5a0a00c40e00154000c100080480302c203c0e850307a0b16410b00d0522914120301c152555400039885107080f500f0040c07080460000b0a080c144100014400c550640d20f00e02c0c2145c0161509030303a20503244090101819030310b5802900034402c04401500760100d50450380250381e107540c1107004240e45040a0b5500c4424030b5070307160140c000549410204000130301c662000a081c0c2000c0083d42034541c1d0f00c00c8102266423290300b2040d804038403000180e41c04041e61040038403100090011f50300355162040004010b2090a041c0d81060040004001149100008518006040d1030406989080280d = true := by decide +kernel

theorem cover : BRFrame.Cov 945863309 946043165 := by
  have h0 := BRFrame.cov_init 945863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 945863309 ≤ n) (h2 : n < 946043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
