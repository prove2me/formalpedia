-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2728
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:34:20.506413+00:00
-- url     : https://prove2.me/submissions/9a21aed8-80e8-4b79-b510-c2a234613ddb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 490467625 ≤ n < 490647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 490468875 1250 490467625 490467631
    0x70803120901110316020705180a180b060607020a031b060801090903021023090714041107020d02011806051c020c060109111b010506030115030506131a0a05 69
    0x10200310800050390100040c0304104407800248106410b5803545007618022840361907824040d44100c14010032550742c1c00e0104c444003800000d05010034501140443e0a8442c008103e401c81c90320010b020001524850481d91b10807400d60310180c41d00f03080d0000407541c500503803000d0285444107480b25942a01020081c01b511000d071211900785e40e07258a20ba0403141c100c0d00c013400581100b05510780141b8950070444640060b082700c61480c1d0042c0017034030103180d01a6251075056201404c10044100c00c814403020306441150104917030100200910f200e4881c1c40402031155a02c120a0801c580c05418105100e00d0700305a01700d0025100c0d2005801b6a014100c0b650045401c2d203100708007404180216542e0307a603c4400f8101f81e900c0d1000344800f91801d005010541030302070180f6220001e03a4842d01001c901c07032800116850030180306141c00c44980c0c501d95503941544d04401e00219100050340d0f50031041740c428404124001d030a010380307a828889040b015a019000c01e11800c5040c540200780 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 490470125 1250 490468875 490468897
    0x506070308041113050f1602120702100509030336010c0605090106030f030801050f09072f011107060b040204050619051b1c0807021f0b0d03020d110d090504091103070803 75
    0x100d0044440001d03a610b185d09c511101c81408104103910042c1455104940c4c0e034000f9003801800c0c0340d803e00000b401c41d0031003080c07000760102c4260183c0b0301480450b45507200c945c005500300406108140002d0214441c408003402041e280c0d800f041b06070130254000c0d4000c541024055604d48518a801442e4850a02c1800c0c42021a82d090310000d02d400e8882c1401001152507000355154a000d052036200d003200303801c2e0181500740d01d194035440002e000d000381040020b050036584000c0e5142c00c4080303071448140d0501a500c140028003464590b40100e629109484909400703c49110300221414400e020030351000286480d1901031094000410300d086034420040c01c00409a5134100700c3d111442221204011f9010034455108000320880310842c0b0440070b100891100d04e58004254100c040240450050344910464001c0ca51b00c4544d06c50f80d48c6200c13010f44207002d44084010280c0840e8060b45108560350f4401004101c02c8020504000700d0140c00d0303031405503541c1e001c4c507160781002d44484 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 490471375 1250 490470125 490470151
    0x513090f0b07050319020f090d020d12050c160302030c06030a0f0617010f0507052215050a020f032107210614030f120c0f01050a150506070308041113050f 68
    0x12170103a95074000d650100700c840f24206d092000307000c1006210032242e9410707a00300c9480f039079141c082001c9080d20003c16080da00c51983d80d00041d00101c1c47c0c00720382d0403c1d2403030303d01580050005980101d21080ca00104032805501ca4880c644034500415100d0030441426280400014021030100c070f0b0602d14140400003003000da001c0650850070b82d081102c04d18001303601040003a602c540c0258080c00755804c1c002c00cd081b900d844031441040b1105030449040030a8003c02c1a07098941c3c10000002c20a103480060340c00c20501012007010b10b5991070303d18041ca06054001000c141c820805400c808014100391030540d414081d50303d008003d140901c041c0b150202c500300526080008042c0304502218000346440380540042d942c03503400013180f07102103010381c5807254036584090040c1801071685540026094032540c10b451034000702c0c1e0f40400e00586090000001113500150a56801070b0044e055021a01c054030001e407800c1c0745009400b2080b45082d0900408000b1006540d201d041002006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 490472625 1250 490471375 490471411
    0x5150a080d090302040507090504140906060a03030206070503060d060c09090c0311270613050108060a033c0b0123030316210203090301060f0513090f0b070503 70
    0x60340c58030010002a00842c80500c0d08100506060344055403000302841c000700d88503182e0f8001000e0b9000705040c80c000056a100340304c01c1035020f218254108404840c0301c011310340b031560065160f010042101090210102c0094410f1300d8a00e86000034941c041c10801c0940e6002001400c402c0081c0229081f070307031a041040d0095400780c42443c84940071004114103040740c2e2001c2d08100d0701c01c0030890001d407100728441c1556031224400744c924184080c0038070307010604100004005010090035544160b51908080021230501c0d242041045001c000c03860b000340e104c00701c010480e400850201c2c509e100ca0a840c0c01880360408085040e5240c040c510b901d40305840c2d00800b61030550f40c6415500d50002c02c02d1146074030340e40110302400f0740304040800c0028049032080010080c3c04243c00003580001502881900d800c0c0b00b89400b800400310031020403030070040854070024015100b00d0140f070740e41d0031000500020404401d001076110320b50b40d55030b00c2c0c9a00010a20f07003099885400601c0d000c600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 490473875 1250 490472625 490472639
    0x140a050a090503010b030a24020f030108060703090b010608100803030115020601081203130309081f0f050f06010c0303060e0709170c010f030f0b0d0605060307050f031207031205150a 80
    0x1845c880c3c91401001485120019228994440f060072294540c000e03074600a0071083c2c40500182c03040d01c4502c0c036072544075894064880d0070510010200010140380211780c3c4001250112401d06446540c0b8210400756681c2144901241e01d0b500b0038a11848084000154a00402449402710340f141d8281c40d100c2e41e95550550340c5103155012009000000d000003286002410380d41404540685845401c0075a030350026420040240401146040c0000844080e0342c4507000d0706045201c2120100002e06c1c0200040c529440c010f4a000d041040845141d03092600c00e4112001400a41d8501c400a05044102420320145032140c800c610103924440124098045034003210860b0607110b4604101031058210b0040516806034014550780302c082c24025102d00b100036400c58401c9070000b0301424003c0400d46000c1e82980101d01c10003050140401a45011503c650300420070180f8540714800d502d01901d0031341c0024110341c061890081006403000b4001e203040320512054903062442074035006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 490475125 1250 490473875 490473881
    0xc03370503040311060d020403110907081b0c0a020a080105090f030307020c1003061502010c140a140d09020d05030901080a0501080d1103040f03210e1f140a050a09050301 75
    0x9009086504180020400302c0d826113010780b0804c1008008910f000d0015030a072040380c110b80c1003540d640c02c4c814001d296905040d82065000082414240d5241c42e10b59031800e110544121112585000840d0490301c1400802100b00d43c941d0042c0000303400c584418485000b000200c88104a900c594003040f50602c030088120381c068240b690151200114a1040c44040b12480d84d000d000c25654038070000e081da0541c11149092041c65002044032020b509008000c1c480d028255204143c003040320025040c2c211080341360354580f03000382030384a000e001c47c000000e1001c03c10294010305e0f040c06007010840048010b000884003601c8400e031b5502d0740c5000900b120403d00800c070711640650b0400d5803a5001d40e074168400c54620048901d807903251280e0031000103c1e9401210301081c1e40c810703a01a1440c1b00c4c0e042c85036096a140568400c100000060b00d070040d1740345100c0580700e10301800308650744036091907020716000d04042550754010f144010030640c4038000b03c40000e511542d0100702868180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 490476375 1250 490475125 490475233
    0x31115070309030605040510020d0b030f070b0406080c070c0303050d140106141b07121403030609041401021e030a0b010c03051e28020d0f080c0306030c03 68
    0x2a80b080728007800c42e83c621004180180017900e8900c00e00082c004140c0c00e600082405070108a000b1540140c000e040c1460101c22122541007500106007d001103004042614111212841c1c000c110f48c03185c90456445200b0a1400707449114445804800d054010008242d00041d02d4001c116a1011007020b200e50002801204000345504062030043c2c03440c1c201809074101d119030b44106088008040da4507120803640308811606800402c5000e100307103440c8100c0700707603000c4024601e1450001c00046134402c0042c8024214071205009d4840f0311000d605403803c8901c1501c000c55603200040c60702102d500102d4258507a642491a022159480760b806910001d82c191903075420800c80b240040c05a0040c3c03050103095103000d110b2203400341d140001e01180704900d0007004d90b51826508000b414038902031a25002d0200351401c042d0001d92002c102988a0b011000e00d580365250300c00041d0400d03800d041c0003a4180308170015000210500d07501c6d81910700150906c591041d00c00d10070900103280364 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 490477625 1250 490476375 490476377
    0xa0513030812133216140603040804060f050d0203041b09140106120e0105130302010e120319090b0f191a06070311060103030c0c0b0304110f01030609060311150703 72
    0x11040e40d14480d03102c02c07001c080c805013030881813459280c00b000c45864069810300b082021100a41c04001c4400b122124811064090301c0c0f080c46e42c036240e203035144d081c81548210010850707207042c0801018442c500351511030088500955032400d10307082181c1c00b82c0b20800d801000d1440004001001c442910655048480092161b84160b282c180300ba01d416800f2044900c0458982602c070200020030b224080c0724586000a112005115060082c2101c2c03c0850002c959403020382800000800013060300c1d88250400c0b0507103295100108020090540f54030f000344041c041105000342010700303208251041d0458007603460101d1603012071105550071400d501c942c03035040041c08169810050300400000b4041d06011089092440310180303007403000d03403003980011000e200f8001004007203d2410000c210320484d450071403d10303854001c010205500c2c041d00c00d10724503036000c3c140d034000d0f0410002019646810803080342d9900781034114803c0080750600c170312540c0700085a082404015140b50030b0701 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 490478875 1250 490477625 490477643
    0x4060e0a0903030b060c0303010311010c0b0112080d110309161211030a0212060411010f0e04090311060106050c07231002071e090b0901051003020a051303081213 71
    0x205040c1100400d4125019002c040e11184810000c0e2120701c0201542010040210364035851400d2003840203c40d000943e04200d5080045804180230101141c1960040900d04001040701d107042000f030303c5050392040009080805007418a6400409103110381000e60030b03038408148560141c0154a0540500c46a05500710450b001207402115440910034000e802c030385450603150002020041a48548030981c1c0c000400c01040000030350a80700581c0003820140e03c0d2030303500d070f1014140075250320a0900581d9a07018000a0501c29203021529199200580f80503503156507006001c0e50104034841400c1c0300b946e2000404039401c4103c0e1000039454026015420b0030720381040307a07694140300800d0851180e0701010581d004400d800c0003055450701e5600d04030b40d02c0c0620302d505507021904a0340c4280c12160042000c2c1c2c4aa5004000c1408103282c016030394004418150340703038083c00001e1400006690b1000c8200480c00c001050320700c5c00d1100f5286241e445211900c0e10300e29072038009142c0d0389 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 490480125 1250 490478875 490478881
    0x10e0d0e0102010b040203010e0421080a0203090c090903030a14010b03130f05100510080d0c020103022505030301170f030f0d020904090515010602010c0e190b0c061504060e 76
    0x21040200302490340051002094201c0311310000b9050360000e8001c0c440020b0204180070803c560746c04079140e640c0b540110041c1c1c401098034003401c0c0d0f000003003d032000365400000240c10a1070030721446e01e5005001704280c4650400745115030340d03a0412145051000e18011202c5410b102c8000214121881c0c031100c6450756a40c85940380b80c200242d0b904480c0c0c440080b501c900003034018001c86500364078080d00022140350a003050342c00110345034421074407500406000760500703501c1108505050340a0034050394034041200340315500103d00690900950302d000456007084808001141218050281d4034050201200c41a849025074094406240d00420106c0b114202d00c0026000c030310f84a010041c140b1031000046000d807655088101d4580d000000101c035400c0d00f60433170303a002d000c43d88001c0103101062100035066541c0c103610980300d500310145500d000500002c650014107000c0c131045440720051054556078007030503540300f5a1070701c40c60045112420f1500c01d2200701e9027800f0f42626140c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 490481375 1250 490480125 490480127
    0x3010e0a170f03091f0b0102031e1c1409060106092903040809010906210f0e1e010b01081b0313050d0c0203060c09033d0c0809010e0d 59
    0x42800100000e8001c42400900a040c000c80081c1d0310490b11640946a601d18944070344a0241c1040c2e01c4072011480c3c180c01803000c0e680001600c0300704060856100d5110b03058080e0080c20301a119115064010a03003c080c040a615006010b200881e50512030460b202e0f10080f0340c680109001e95400100c0d4103a080000e038207038841041e41c4c005c0e811103c01650380002054407060740300700d0b8150b0724614000b034003e89559200481c072008103068a01f01e0a03050700356100c500e01000c40f0a00c040c5403504c445007c40490701c150700c0a102d01085608540715900c0c4100b41c05049001000f21103c15442c0920300d0400303501510360248205014005450010442554018aa08043e04030075915217a10119800144100b0002c1f1049500b83c881003085d00e500d2040610f0884010803184140c00c050011006035100002e030b145c042c240d0541078554002a8016400c4d4130036001051882c0355540c1c5440c1c400d002e01035800081d1340000c9554070740240c0d4500e62603c1c01c0c3c0740da00340c0610346640401c041c00a41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 490482625 1250 490481375 490481393
    0x3081003080f16320c031c09081e1b0f010c210801170304030519290601030e030a0804170702030a0b010503011d071e090e060703050603010e0a 63
    0x30301c082680841d0f11111034440019040940490501c4100580d0951400b80e10607140e9102a581c030700c0c020312290002c03402003a105e010303055080e0340c20382a000300005c10b140509284030240c5031b544115034102c07541914081c10780b141d144854007030303014002e2015002c0c00c64a541c0d40c25090007038060140d41641d103004403021103800f5010b40d41c4c000a80200b00741a03050707115500340c280080c1d030341d10207030f504004030342030800341c0780c0343d060145d50040008000103640442c001009800300c500900702e185850805410104810210b1004c0a62000001c1c8004e4130310b14140b0700030308017a0b80c104000b171140501142da80c8100c44459001c10803180006000842c2034005000109601c200380c0d0821046a012038503108125100322056805000140443d0a00740f20380400d0640d01190300c40d40704201d03444e00341c03200741d46d00a1446c8021562602d034564020b075402c1c0300090498440400c04803440071760054030b6640c280c0c0c44100290801d404598540350500910120384940806080128596a00c4e4800303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 490483875 1250 490482625 490482637
    0x20040b070f0f0f0b09070f1701020c0610060810031a220308010311100c08030903070f06090204050f010803040b0306130e15060306040c050d060603021c03081003080f 73
    0x404082500c14a0005803034a00950b207243c400e8403050102c50241c07518800d1031500901880d1150301c50030040040d44211121501100c5c00c89200c0c0300130b552207040f007601a12501003d400c15100d02018800e400030000d640b042120a59640c51b0a1902d508004505090562001800180001040320004e40604490b160030a9529401e941c0c61604a111340c409a080e001042d00865544401002032100655030421604012a4020a00820300902412800c04c040f0301601e68403010002961804041085611144d0031260b0300b100110103103008000f134241044200d011f50300b0000840c10845460140c036050b583d03084055818a418103040f0a0350340c10041140f917000e460910810369188130b034403d4505403007098028080a4240e003041c02c803e5100a40601c2c007960180d0204404140348056205c103980084482d404147c002d42412070260205400c06036000e130307440142c1c00a0449040001e8000e178400d44070105242d5461030241440c0195110207411101d08104c0004120304890081031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 490485125 1250 490483875 490483883
    0xf02032509050a120b130b0c070501060807092a0f03090204060f0909050d0215070c080705010c0203030709051f05031b160b0c090a170a0519020420040b07 68
    0x14080e5652000a03c2042e0150300880070b070700b051040d50041c8480e14441c983d111400041941c040d0050340e030b4499051310010505202c1d00d0001c41c4080c1001001e410030801022490100d850460300d803100f000003480c0b50307649000c404540c1c0312001c2d400c02e8400a0031162084945594040a8613a079060703000c0c2030a81000c0346e000d661140003080170100c9405c40c101520760140e00042c0d210180c81c1c035a20b01007001500c41c0940d804500c0c1c0c401c5c0418081481c0381d0003c01c900c0e2550b54904103141c000094004d0403002090f65013001645002568008050741c890b4141c0d58a2081c607d030358005000c8901c1c0c0c03000501034081245c221000b12940140300541e00031940c0c0001f5010048800c801d130171f494002e002040081c088940440091104550401d600007015228051805a880001403481c0e025441011664841d94111000c0c4032400d01490034815002016a40405c8401150724030740b10805404920451400600b03c0b0070056030b500f0825914400420b15141609040000000350041c2104035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 490486375 1250 490485125 490485137
    0x50901030c0e0f2419030c14040b1b010903080609070c02030319200c0a061b0f02011107030303150b03041205030910060b07020405090606030a06020d0608070303120f020325 76
    0x150800f550070000300b82c4101c0c1c1700351020410b540c8400082c01d413580101050300700030b00e400c0c116422000c0030049900b102d80c3c1034629540d039480c40c1204403520714044034801195280010b184c0070b041d003010903603124030400c4800c04032554502405460344030810001a4240c0d1084c400107804401844a40c0b00d001410b090802c000e44c41703108039000c5444001d02010058001d07020201203402c0207961742000d0921400d200b0b0500615140b04031b2005085000640003c0c5840300c14419a400343c4035500582c010f480aa03030301c9607180e0401a001d00350a0368500e40816103000c0010744801c400040e2809141e202c5c0d40410703a501034200482d451782010740b1500050050291184d503c184c148111001008000000c40c1c43e054580100b1044400060240e103082d04580c0800100d56001b240101c03000307512400058a80f01191403240007405183c00001d0305108017a0040241078200d1b90b0101d00b198000e10610005005410000a074001680d0501c2e0f0f00b8409090407800005140440402c1001c910f440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 490487625 1250 490486375 490486429
    0x180509070f08071403012a0c020a090c0809010207050a14030c0106090b0306090d020d0516050a06061802282601060f051801030504080712050901030c0e0f 68
    0x140c4404400c0b948400810341c425001013241c1c584012034501d284004074020080350246081141c02c003e5000085030b452482c0c0803040e245107014450405000d600588484c04481d156252400100f10800c00e42d00840d101d2000500300c9a014000c5a17850703507024003e0074020303200380e0341c0081184180c41e02c0421070205121100b0002c000744985001441d5200300460101c007070b0400d150401c0d8020307041d100715400403100c202d01c0d50380000c1d4481640c1c182d0b152003551098080f001e00c02c06100311100610b280038000c2e1145c14408260440d42c1a5621742d030b40722200312410b4044100300c4c801c4000030751035028092040c0c00c4520f10301e00d5a0720305000c14104171042180d400000001b1291030300030424001ca6150042c881a64400e110840d1010b886c14201d140503480c41010b020351210840040c100741d1940002020010102c0568840d5680a80c2c400030070b480c0c2900180c20754002d0b40500303000078030301600500964821824401d10040152101c54841000c50611050340c4820007007011218400c100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 490488875 1250 490487625 490487639
    0x4090f080f04030210020f0d0f0210110d06050d11040b0d0b040c060e10020606041a0a060306030314030106080a09061d0703060e0606030706030c09050904140c03060118050907 77
    0x1e00462500c520352079540c80c11031040001440d040200002198412061080710520014420026900b80d041c5a501c6040300c08080340341405c82d0541c915032138148181861032464000c05007030101410071040c007030180c0b0384c2c00744408044d848401820b004040c160b406c0040c145580b00b400c001e90040c10148d41b1446030340301c2d0002d186003078608031240506000100a090350100e42808154030407246401403140c0343c07000070750300c0802403c0a4415035980c0408440540d5810a1400090001d08103500e540d6231050701400400c5c480c4400d901003240d00d03805c04003046203101101c2c160345c102d4076080e41c40d407144500c0d80001d1824400031111617a4528840100554a901003010000900700900c4042e040d8a003203021755407405602ca619610800500c10141d40200391402642d0b114940090003c2c0c883d002140e0700d10b0300d503000c01d405c10141010301c0140314400100606030000c0b8002c598800540e0701c24169501000d11800c2d0145015195401051240b60802c0d070700b0051001c22500e44d40c1c0c9400d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 490490125 1250 490488875 490488877
    0x70902030712050408090906061804180f0b010e0a1503030e01030603170405010e1903080f04090c0306081504050309061308240711060f0703150305250506070204090f08 74
    0x41c20f40d0175400205040d60b19251040c1c0c1e103903215206881e907908080f80f00c41d616450045100d40300d8412074076170704032200030010003120b2070318180c01c160b10108180d003604081010400038050680700c02c11a8000403e030880c14014172800c40244007482d4007961864800301c1c0d4402c00c0c154014101034444c50000041400b04082440e04210049256a240e151100151446070f040081c01e0081c1c6c954100c0c403070381e42e078007030035a01c22039800c17005a03640c80c1e00c0c04003d00c00521981d00640c040f5480c140408120076415400300381524184002c41e15000c4450303c050140010442e40100340f5402003100c500581000b8004e044048507148000c11060b44481e0824105410600c2c1540b11640182007146160b03075107200b46400518074141050a444107514154550200502c1c0000429442c8040303500c071842a40304100d80d01e036000c101104940c503480d00c1d548132026040e5586c02c81d52185180100c0103840700f0038200311070004200c0c43c500080d030790900c00944281241a5a09105000e001c2d010409d000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 490491375 1250 490490125 490490131
    0x50f16030e03160806160219110a090510050f010306050303030103061a060721120c17010b04080606100c050304090504021302191d030d031401150207090203071205 72
    0x74440580d14090141454034004441060341005203082600300b19a05000c202113401815209600c3c240304801d803001c0e45440d01d048184001d01c1590b020000c1441480c03e055249504211110126103a031801c68105840c3c040e5030705900402c4440e0100301c0741c50030000500e003444040c100407503880e0759000001d0464000340d2041d2120b030b464880c02c801103071018041220400040384c120f8104400e60702c6141640b0f440385400840400440d10804206004a20003d40384041460620180c51a10340c02810034007043c00000c07400f2483d0002003001011001903400380c2d1003580c000e040b035039292030400c0203002d80c600c10f080900c0007000364100070520600081004d402042e0307001c602d41c282803050001040001d0034001c510b5106000281207560b003255000350740203103450084c00c15211148080c0c0c92503990700e00d0550500c551035a114144e074241d0403008041003d01c54040703060381d0321010b040051804401d0040103070440001030011500c07550145400c1089490806940e11071900c61800722101a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 490492625 1250 490491375 490491377
    0x613020a091d0d1403040803151519030606021221010602210403020108071110020d0c1704050d0c0302010b03070609031511090f0f041b1716050f1603 66
    0x2c1c1c0d80b650902c000708200c08400006280030f524403014081100407600000d00004c0c0220341c0040440c850600a02c3c0418460784020090314010038080700410b0345a2107140c15800b01e201c80c1400b01e5401d0302034880d1504440c000d8016081d2214035503041d0070035038803001c903107024500702554521a03600c0e10204503000e0012a0001c5c000d20400600041120031204030207161107004220500060b64020b0390315402001a08288021503d9154001d0400e8400088404151320101e0300113103010254008014280c40707600c0b52849149944008010640100e801900591160b03504c18642d500c10140032814a00a100006060003040c00090409038140d00c80e00005000c980140207028050310500000c005a1308100310b609181854404a805251386d002d10510103c13612402c1c0703440c0c0d85003005080308010070030001e68241c841141c00442c10401c812001610000e0303850411a50000c001c1d0050b03070f84c0020070810500040c0b0883c0d90f03074400c03240110f11300f2051109807408000001e0000400b032007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 490493875 1250 490492625 490492661
    0x306120111131a0712030513050a06020406030e0a0b130f0f03050301030201030e010c0819060807031b080f100b0f0603070c061b0504051504030807050d02060c0702030613020a09 78
    0xa80082c03c0000d80c440442c40503418820080d03d800a400380c040000500b80c14100403032143d03204442a0002d149072000030f0a94002d100c42003040041542c003c0c07080d207032140c07400c01c14845100025540d4107051800100301907034480c0414121895003a02c620b505100720140754170f5164640d85c0320394810040174120b010500210043c41150303018000c81d074410f040729000b0820103014480003007561102520002c0d58103140704a20b441d100d06604550042e00c4503100300c9480e5940c0b0302d81008100d210380d2910300c421103060004510140c0100c1c00c25510b0040100401240d42503a80560007003458000c09035015072610620612030322280c018500c1640f440d00c440d2086520f9003044419102004542103031110741c0d604040302d054111040e01c1c00d56034141c8020303803403910203140b85641e841039400181110700d020070381e1020001c00288600c81142103038207484044d1504080d014850007565070081d40341d0049000035261440720003105c00d55034002442c10009035a21103030682142c04103603507440c91580c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 490495125 1250 490493875 490493879
    0x801050c0708181c051b010305091e030c010c021b01020c010804030509030118050a030906020f07030b0a020409110403030e03010203010f051027050406050a031a19020f0705150606030612011113 85
    0x30a08901b250125007801c0c1800a860010b203642d4640d60845003240d000c48001002c1082010200240e0365601103000003000190042c100c040d540d116500c2003000f04a80fa0301f01c0304015480880c1e4001041070607180d40c01a03888a44e42aa1960402e0343c005d60159616600c05004461801194540a005a0203459100c1c1c2f41d0400815603d05034018a05644c0550340e440c103980c0000030760703070103c9422a100380e82c9500c0308003081c0045d10544d0302c0000514140709046004104003001841207030702c2500d5154142c0c008805143c240d000911482c01c0c40c80300032078104010b0506021a002000d40740c42c1002c1500c2036005017140c01d080d1510311031000000c842062103542068450b82d00548411a900010340c0e145598014440340c15035113801c00410240046a07003600c0d240d86010b9440c4d00c001c0c055450701a60107a41e100e54000601c02d030b580d881003284000070481400800c50041201030101840d513a1004248020034014203d5a080340d035031240c0c05034407111810042c1080380e502c1c4c201011070b18 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 490496375 1250 490495125 490495153
    0x50603180601090c18032a09051f0602070b0d1107050109080d061202100f020f0609281203020f0d0e0303040c0501021c030902010c0b0906010801050c0708181c05 71
    0x309a540410a42070248410710100e41201458010b450440400a07e00c0d8003030310002d09035200940c0007480b0a41010140162403100812101c03a9060f141c043c02e1b540d0740d031260700702d80d10b014038403612010206c2080394401600f080d402041d011030305a14410301d00025640d902e8212000014180c072411000704050b800384002d40207510003402024002440c3d04060380000e01c401b0701010302c11090002c04800e002446c0c2c024800311110800c5138003030701d90034544801d040b0b80f074048800d9044e5030740500d84e03c10b641074804000b07940a910b812203208516000008015802980b05507030f030010f0403805101c0c0e44000301c00307401080c41e602815006140c490030301e842c1111300104103070072482c1076420072400e00d098031998080c0521400c40c80e24020a010303a05000613076007035040e000c0c040c3c907252659042140384c81340014600d0481d071694000b0005941c8104000000b0301800710000d006039010000b402e032040e065120490000401000039030317000004080d8206540109200305c40c0e03500019103020000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 490497625 1250 490496375 490496387
    0xa0501060908070b0d0504170c06041112060610020c12010204050915011b0f021c0c080d090315020c0a0c083c010b0901060c02090c040e01050603180601090c 69
    0x106074901c01401c5040c101103030081c0c4e500804040540f010382e1040000e0034406107030380b01e403c50b40d010b000c850340d942e4188181e80c1d1034503000c80d002d80d07900c1014a4441d4a50506100707108500095401500064880c0303c1000b002d01d5001e0003002c118418020000096980c0c105250901d29110000503603440c9000c05005c101a402000411802110300c03990340642d81207001c400c481e000b0051070181c417250500d82850200807940019401440c0c007003442d184208800d5900b504c1c81d004d0305c0f003240700c40e6403407031895941d0001d401c2c1100080c02c0b154081000464880700b5110315444420094142680c490b0010301c1e14000c0d15090300d2009442008004a00040c410740c46007405660000d07403134800046c0103e5031108004004894802504010002c082c82035104101000c001484cac8402c1d56561403000b05104580d0074160700c90002003002c2995200408200e500301d40e6018800c840680c83e000810555800c01090190056800040110342c0e10003400524003802c840e4800040400c8090401491 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 490498875 1250 490497625 490497629
    0x110f100f1406010c0303021e0d18050c10020106170d120510031101020a0209090c01030b0402090d290408040609060c1505150303040f050f01020703170717030a05010609 74
    0x34585050760000c1c000d28241c1c50710354800000e00348038000c4511450110004c1c0310f0341d01107003c2c0d040e4007520311240c51031060040a0840142409024900048052078262211500c0c010a45e03404080801107a04080001d40519040f03030000040d0141e4403070b1070604240b2140d0040307030f02d42c11414400d403410b40c002d55440c071144074003401080146441c03865510940346c40e000181015580d0b4900141c160f10800030514241d1740a0320f8070301c140c00c0c100c00341c3e5540d501d82c041c4203010a0034600148407608040c42500e4000100400503a028400c1c1e882c1c800c401100805596a81d08000c0091084520060030071401584510000c96841c1d262040c010b19241720394000400b08181020303d88046258154925842c0c0001070f0005560348442107200b01000c0007410144d014000030500080c0c040c1280144802c4800507111002855000001242c490702103000c001c0c240035400400d50030f075009540c00f0381002445400e922000c001b124442e1031480e0011034803240460303110301c018481942e0012103200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 490500125 1250 490498875 490498901
    0x130605010f1404050414030a0e0103051303140c07030b0c090913240213090501030c1406271804030f02210f09060f130b070201090302060901110f10 65
    0x1c1c000b81401604001500e4400d01c140c03185032208045010300c208000030303030103598400044071380e9442810784c0900346803a0703003d409000c41c0c41e080002d44603499040c41c41011a926a80d0b0a450310240030b8003245540100000e0500b5104d06c8801100250500083d00e008a604420598644000000b005411080140100c648148502da00d8000684503014540c08181c01b1103042d00e58801c40003071034028081c542641092400000300003a2a8825a102a05990003910804034050700c2d4001101034900c2160b00c560002da081084419030521030901c041e242c7c3d41c44080d110403c02d180b00117154500c00958060503008007006000070540c00c0859010140f00340e002a003c1c00d9040c3c03140c1440132880c00c509a107000000220040707520300e00d00c01c490340142c00600780c07600d48594806840207a04500c032124442c1c2c1c03104202060341c501510030b81d825990305950381a01c003401d503400d20900350003880701c0d40e05206082d100003c040c00c05104040c010016100104610f1088100150039a032800c100d1b11 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 490501375 1250 490500125 490500149
    0x140d0203040317342a0314090a0308030a06180b27010909030c020301060306140a110f09060d0f020a030c03020405090103030e030a050304150e180103170408010513060501 75
    0x1101e5504d90104007518540d40c500c0060318203904da4043c1c1e170780b240d41458508908100408071070500d0b4800300c40283c143c001c3c1da680e45112030490382003109100b0011001d0f400b2040200400004800100440d4050241580801c8041d543c0780c03940327212000d0301b0f003003205580c40d07100896040c1010301f01004d8902141440032000d141c10025240c0004040c00703000025a225a50f040c21305014503802c909940e030150080064540e642072000040112400d0071f08518402c50105114071002d00884a01c80304076419103240518601c5031071111362018400a4010b8000c3c40082d42001541c0715031000307400111000f50350703440c000310000d007120101b0400009041c070500c014003042d00e604d0302480c1541c1c0c1c142002d000c00307065000007904c1c000358100018058840040c0228400503141e03000a25007070240c4508182169200030081222110003000303580200940c01080820381ca1102e00c4120f07264175a0481c903060703c8105107030030341c4c104903003001d0b0780e168000c04002084139601c40c040c01481d40a43d10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 490502625 1250 490501375 490501411
    0x100e010906060324140f03060c0a030b061c0c09080d030605030607090e0408070807050a050a0c1710150b04290a0801030f0305120f2401050a140d0203040317 69
    0x40254078919000d88410030846170480030f103545500700701c50004d0710020201c07005403600300d009007850703401440305100207814030706128902e040202c1a00c5a80c22116200d61109840080c00d0b002031a4544d201d408102c204140081c0e45842800800b8800f20342d954041421414801070514061002e0060810003070500c07030800c8014840c0000b0f603001940041c030310f940d680b03031030a14182d14054044054510302a080a03201000000654038101511501c08080c0c003640da040300b0b13030b021940c004010042d60842060300c480c3d00c0440d0700904a84803903c004084990b21342c100003006400c1500000c03c43d425842c801025070340111400300081003500d10561519100000082248c0b10620004050788000d40c1200e080601070f50a6401d0100307244c004bd007181ca483c0c054044082c009558000c11081ca8103c0c0901400003020082da88560603100e45143c00d440d940c00311036905a001546c0c3c0c0d0f02c10103001d581001031f15030009500650281d5500c01c4082003820181440c0640035104400a110b04040d03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 490503875 1250 490502625 490502681
    0x90e060f06161a01030b07030515040b13020406020102120117030a050d110a030b01181a090117070e1002031e030c07050a03021c080c12100e0109060603 67
    0x224015400065503055203901c2d81400704000500e8080e00240156807040081c0e12030314000d29090f040300d00030001440c2c20b4031110b8054040b290b06441d03002c004400352042071002c0c103150304000301da000c025100e02d41c4040031040d20022078000e60403540040c0d40000e4451070780440045d03150f0140603000c00070f400703000c5120103a40da80c0c859a00c559080c40404500780c0e0580065602c2019140c4034010411383d12262008010020f080c0074403220b0118401da1142c00d02d03207002440b86810350b0030020070066140b00d4600a030311a60816541ea5040181c00b0f2044107e4401840714180075800035112075000040c0641045844280715400034115801032001440d0b030524805110100040415017035075a07152140c504625115105015046108020711041056800111913602d101c803040e06c40440520302c1d400310b44180054450300e00036034090101042c9142c00c0201e80703420050300c03484d94000c940d4500c0e400c151356009078445a03101d545c0340c0c41004402d801d40034188002010050350b10b4150a0104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 490505125 1250 490503875 490503889
    0x3903030f0b0937020406081b070b070e032803090b07030503010501081909051f060b0301090510030c15020d03060b07060e030f0d0603020f0a081506180412090e06 71
    0x1c40c140310401d03800300810884a40c09060f0101c1e54030302c0001d5640700d0b1203140184c146103003076410740429030f2a079440030f07110540d00007505c603000c0e80440c1018483d04c0c3ca01040714902d00300900e29a06000c1c125520000e8409558280190700d0721380102d00e0407605a040150602079254851a0241820000303400040d030300608990545409007044002603d0b421040c4255000300900d00c0105031604150313805200c000904001400c100780103201d5014070704100c9509482a034400c0134032504043c00140300e40b07040381c2c000b5540045000d808842496486c3c80d0210300700800e81c0326481070400c0d9000e06501980c18428038109040905060000034a007040246281c841c1100103401d099035020305101005045c0211440110545500f0340c955103c0e2442100509103880201e100d0b4054025020b024102500031808840340e40c000f914080030ba99881081003900140019441105500007035460b030b5500c003c145c040c030301441d0807841d03100400038041c10300c106903009200b140100c20100072080d945d0700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 490506375 1250 490505125 490505161
    0x60c0a060c0215040b060a052202091201060e07030b010e1c03090305010c051803061005060d06080706031b090509180c120a1709013903030f0b09 64
    0x14500081071a4014422410080c0340d0040320401c00b494000d210610141d29200390240b00700712903071750700c0c15501c900b000450054044944248140f1602c1c0d00d5054040da03000d03190610014109240210115103151301b1104941c0000b0001e6441c442440320b45945803145481e20002801c0801484609200042c245001415982030410302d0140752001c162041008000555004009010b00e5601c4c840260150701702092a076110301d10028421007610b000100940900920031802e158542020144070380780d80700010102c0d5682c1c940c60b0000d0003240c10481000107048642d40020700d81140d0fa64142e141c1041d82c0d03050308100405500b40700da5030398011001e03000400070b04d24001e14130030000301c0360501d002403c0d1954000c895101c249400d900c04580c8405052140c50140c02c00d074603481e961082809200c00741c5000440c1b003513a40c107103001d0040000c9108904e500c88110207102c00780000b8903a0185400850000f600c40701c0e4412401c240d405541c1c05600d086070311038841c0c40c02400c80b07504070240ba = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 490507625 1250 490506375 490506383
    0x906220f05060712030207050f0d0e18070804020102120a020115050d0c17070504141b040b07330f0f0e100903090806040b010312090803220b040e0114060c0a 69
    0xca0703103013841c034001c0d030480341d034194814240c95011045001c5292221144440366021410080a00c0d0f0b0034030300002001d510381c02c000400445512074841c221403940c0010012415881804d4000c001118820054032000c0d406900106210440b81030b0009151529800b85010f00c580f010184001408200280251242c4072013180100c14010901440e0038125071201b50003500e8443c803080c40340c100180709449441c1c200000351024580742008289407040b841759000c140030600401c00028005401c210640203444428204482100c1030280000c025540c5402800d90310300306d201c112049806030325616804400c0030001c02d000b1310000754841d9a03c4080c50700c2c03155900f05000c2058003a00541000e0000441150381503c0c0a00e1710040502c0d080c002034402d5140b03258075140941c401c00c220815601c54001450030103002c1c0380406e09100c50414041800641048085110304550020700010500c0d169900d649501d4101e090b4440c000042d2a140150b84c1000000302c0e0f5500040c10075441580 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 490508875 1250 490507625 490507643
    0x180f02160b0a2c06060a0f0b0919061206270f0f1b080912040e0a0f0c02030d06050d0c12080712030c0305130203070603110906220f050607 61
    0xd8070b111030000345107801d40c0005801440c10364140071009501582c08040c0f80c202194115113034001004189082403044c1e80610f080540309000408012000d014440340c007600e010240b4084883c1c02c1c0308541950072960000b00402c0010340ca00e42c2602a14008150300e4185400c07000880b649511000640d00030b01c4807080d07c440e0000301036112035020f043c0d09804080f04010816a100a08030742d4034502c0e480400180055011030f14402012600c0702511007200722443c980b520b00243c04c0a0110002e001401c0c46a58410491011031140100515148554007540e500e2528034180401c4890303e402c11801540e11219030f0b000103509607015802da41c01c5050390f00c0f90b03414a140680003441013020013409020707a00400f084654140c1c00804030400162400d008554804080c4603290120107406035156016100c20440c4a020f40c0c8010985400c80200500e081b400101041c075960118502031207115590000b207002040c50b041000103080001c260707240c524545000030b141802200400b6001c810 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 490510125 1250 490508875 490508881
    0x1030c06111203090303071107050d12030b0d0c061202030105091317040909060605220e2509050f0112290406060306050612060a090c03020901180f02160b 68
    0x3904010702110b03600541e100c43c2e560f00d8881c3d01a9103079001076805402150010a104403203150200d4030314141c2c5c401418170310149860340c842c1031030040c0709543e2000b4107641e000f51310360720380340d039a0300c1e800d00e40c002c00b003402c60145010b1005040c20000d41c03003804403510520040c001c942e91010703000d07000350300002d48180c0b0310301c03c4c1040e0524104072210341006007000180043c03468565045400f0060150340104034540d51041030140300e10300303540b40b00b45400d14080d03420a441d4440d4800940c10903040b045a00b18205450158418445481a080200e45400f0104080141400796079400030400e07000105651500031100c0008008000060921842c000540b540704604a10f2210010240850300b0003800c080c01c0410007044180000d4615074242400a2187d08121090707000c0340d0013410042c07909940b0700701c8170401070114450481d14602414400070150341c0e40249140a8682d00c080000c060300c0500d1f43c102220758280458440307500501ca000310410030340c41a600c3c010b400000380e101946d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 490511375 1250 490510125 490510157
    0xc14090307150c030210090f02240a020a1202011e1a04020730050f0306060706050903040e01060905010c0b062407020423041e0206030708060f010801030c06 69
    0x1401d078102c0a401040a80b0403119190b100852196590198003540c91000004500d5402e48500c180058071280c0c40c420b80c2401800d0550b00c20303815200112009020000c00c039005400d903413118a8020040e409080090284401584c1407400700c88540001c20850703406c868031820300d080210070b8020302e0703903940c0b034804061400886092120764000c1c011960b41581c0e1a00c0110001807601c41822041e1111050342c3d49101c1c0c010250071142c01d44c88a6083c40d40c19010411103074402005590000e20078018030340000d041d07001d1076000b4844100555151070600e0b260021398001607000c80d04000c0c4010003000b03543d03004820410141d41103a00c0c924941c2c3c802001c603ca195282030100325400280300e0345401c2c030f0107031805000c03150b208840a1100c1d401c044600c492251a00346541051003041c004500020401e04071021643c601d400707050f91411180d00041d8180e00200c1e026804a100c0204005031032600002185100c2002d003814506541142c4034040c94032924020401802000301c6142110 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 490512625 1250 490511375 490511383
    0x16091a0c0d080403030c030b3105010324020f090405150904030504080c010519081f080303040201091d270a08180303041a13080609060402010f030c140903 68
    0x29460801c40710701546072900107203801002c50f410b42c0081d00d0070014050300c0b0310a00a00c004a0340080640d43c041a2a00207581b0010a0031840b064404020040780d0f440001800380d43c2c0214043c3c40707880340424440450350644440b0f1070541d401c6910401c1b0700e0700181c0801e000e0b1030308284141d800240c942c2d62500841402340009000701d0703000200344108030415600600920990788128180d801c0c0c120300d6001076600b405903400d000081c40c09144180d03c0c40744030b13165007944010104190213514410101040c00c0c204e09811101d081c1e00000f08100965030030400d010020042407020401c512041c64901f040b81d0310244c5402590510203007904900c011064001c0c450b02c0400c0b00f42d03102c5c19480d1174440002c0d0301080200c2c0d00e440c0090400c940c00e103004010703a8210b9002085400314121144400780031903118800c2c505000c0322620010401c9402040b855110321210002483e007820305000252203080e8030200c5104260420b01d03d804105c0e03201c0040258524000611500d0b01c440c43c0c00a418 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 490513875 1250 490512625 490512637
    0x50d110403081207020c030706080109020304170a0905030105060a321302040f080a05030a050d060f0e0f1b040504090f0f03081b130e06010306082416091a 68
    0x320900108804031080c4011807004d001d107426400320340e100404c0c20f050507100d00c0140300c0c28003c1000000100028206034000310b03441803003445155100d010146d000035081e041a800c1b04002201c1c0c2500780203c2c28244242604400b085034005500c500e071000c2c0101202a1000652000a065108039070310003031078085141101c001002641c0d142c0410503c02c00070340092182c0c559a05d000c81000841c50b60101e0100c8080c0d81181c06180b030004840410340d510351081140710a402da8a1400150b0710140700c1000d0302800c0d50307120311021800c0a814281c200c003400f41404207a001e0032503103080d1104812040f5001c4030b600703440c04240203901e402c1070542c0c6041003a001e081041c14031404410150712003200341c4101c100c900c0341100c1072107885040c4c196014080214260000c44071051106101c2959281d5108005150210304151035403012800c001c9100408400003207171509070310441204032641940004000c110703034014108444001c5c07414401c0e100e90304002e500d402103603c3e004804801c4505c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 490515125 1250 490513875 490513883
    0x1f05010c051501090b21030a1d0603010e04060c090b0901230c070608090c0102072d08010b04241e08060403091d06011e021e16050a06050d110403 64
    0x58107607034a49049002e041500c0c003040c456a180c03800140d040283d4400240d0f031b015038a009504200740d288080e80c404031480e0014515142d0300720350b00402d80c2d4200045010b410040080c109a040074540309003a01e00c260004014070072283c40501c0514030000075600d14070400d1820003010303003600000244103109804000b00c4d03690f000410400908000030040201d41e0340d40d41b10311050b69103418960329151261b84607070042c3c00c442010801418ad03240342c413044015081c0c40b52008190440c043d1040440c550001115944464803580c032840c003071144141281440142d407100c010f00c080a0308090109004031708002030300070040c1900364807031890f800240540500311a20750401342000751100360b003445480d02200c0e000320f085110402d182c05080c002c1c0c0043e15101801d441030356072594141031002180c021072054240200d50f43d50161300c9404010f1411010300b44039045a001c1d41010006500503a015a00380d1000300040c6a00004031802c0e07460341440020080003c140288080c40340b0380c4050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 490516375 1250 490515125 490515163
    0x120b04050406020405011e0c0b04080c06070315120803010e090a020d0b19020705030a0804030302160b011a041a0304241505090705090f0d060617061f05010c05 70
    0x401c0b099074020001d13600c0981303a50380c130061445103502504001403650400078451845231b40014410450040d01720348240707489414213640800c420f19250007283c0f1500000d40340c12642c4034108501401c00d02600000b40c08541060490301c2c0c00609100611038060b202050380c0c0080d580410900908021780e40c01001100183c2550911f510b03924410f90790087e0340900451002d015020031310803120381035400f41c0610f080500810081c3d5419000070001e40906408114003403011005015008281d071081e4121800c550520302036680482c4406c900d400984020031041c428600148800f1403d440c0b01d2030003030b80d04d995a1501c260b40d9408850389541050982d070316003881c0c1c0702c25042520070590b412800c20125a0b03d808200500c402581c0407404988204441f440c9800c065950007008400500142c41029942d503401048408030b91118110004a4000c07550f0b9940912010ba00001c0c400106190303000a98000c5205500d00c0c81003505018500c0c1050082000c00c0c0003000358107080c03404803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 490517625 1250 490516375 490516381
    0x90d1413051c05191707030e0604090207140105150d080408010903090e2809080c03191b0c05100c210e04020705070608060d060903020c0406060e10120b0405 69
    0x103191a40e046901111a80a41541340900c0421180e034101160340003c00e189284104400c0803219a20175142a000c00074001556007280e12003400a00c02002c1181c0016030711100f5082ca20500c00950240c1882171f41004180004c040b0584040d1000d0401125510000c10503490001e21522666111303841a50130400f5100515800450074411a40a40341220403070b62260103000c2e0030f911044441e0035070b03a140c0000c210403340f9030344011041803080c94003501d891080300c0c0c25071640d004041d1160020116640c82c40180350300070070748244c0348131064000811032001e54691074010501d0044ca400380312002494440c05105030f180c0315115030442282045894842c1559820b4200c4103204404148200f400f520141841d00c04c0354501c5070002c005e80081070410f4401c8854184c06407120341c1c810100030044010414034420340c0381c100d203e5002452512090418003013a500b41d039000000740b2803090000d202d1626401002d6034069101d14080400403c00400c14006025407113409410a10300410 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 490518875 1250 490517625 490517659
    0x40909030c11010c0b0a020a020307050a080301080c01050304470103030905030f07050405180d0302120a09020d1101180f0305010515060403201314090d141305 70
    0x1038011002e002e180d01003920311550780150340c0010314102c0100781560040c0080c011010f03a6010705400d90151040e03034a41070664581d1864aa04e508003030315120030000042010f00700c01c0241e1450000f0a080207030a500d001c1d103e00c21040480301d0b64280c407c0382010030ba0340031030b005c16203080601e41420202005109403c200600840240412000300714003c901184034503000410030741d8031800c04010202c3c18142818800a8075001c1d0812914a403401850720301c20400b80401c0918a4841c1ea005846074100c4448100c2008080e041080445c07426141401507100d005000d50071075084050510b40740401c0b401283d055280707444a015005031104081250f07842c51007600e0459000e40028420780e00c450701c0e43c0d2001d400b928204c81d44001e04000400006003c0c2107005a6011840610707940f4032002c00c0410a014800c0c41008042c2c0d5542421910799445d004155411013440e00040146120321035020302640780c50700303205d4528003010849107845c58a21558901400000d0f00c0140c0039200140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 490520125 1250 490518875 490518887
    0x30f0c0501020403061a03010c03021303060b18160905060f0412240903030b04020306090612011b090302100c15020c031c020703021c1407030e0306090c131e0209010504090903 77
    0x39487d21950030001034160403440ba0003524403081e20529156003a525603603a0f0002003001d1544260091305010141c49041241c030040c2c2d05c40d00540d5416001130303001000c01011010039070041881500e0a0041c440e90a044009460903a400c50703006a0010b241030400d40459002d08006d50800b030029007642c1d1a0f412903800400780c7c1c40c800d450521042c7c941c0c500308002c2e8041240d04640060380180081c440703140500605c00611480c500000704982c0359910607503c0d801034020400420705021040045003031001c004469850300f842c24000032541e0343e84000282040c0c60f00758900c2034000c680e10100200a004660075680e00c0100c1b04044003084045c00302039004a0800e0f0301600450209020141603039035500102c4030325035501308450103401c1301e41c20950040300003a030410140c10047c840e41c0d101004000d0107115210f004102d030085050030858601165202504220b003401c4440c000c010481c2cac0c02e03820b41385c640503015850300e044a0040760f1500441c1d2105d243c06060202003001c0c07540041c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 490521375 1250 490520125 490520171
    0x13020a14010215040b04030c0317010608060a05030303150603071709010c0908160e070c02211b0f0f0d0203070b030f0f0103030c020d0c1e0e0112030f0c050102040306 73
    0x1e000c0e01c481140b0f0b1103030312a0740081103c014000982d0000001e0009114030b0342401c240f4840e0a004081000d894180314414400360041400310303c586044c007029141c001e400703c008040c224010b6203036140c03a80012144244180d0740300d00070000440031580c0c0500070700e505403141c00c002418218920341081c0c0e8a020705450702010002ca20b85038030204c1c00b580c0c0800c3d510700c0c03080b0281040400901c1d00081c0201d812006021404001e20a410744e40183c0d03400311081c491001c2c0101e000c02c500700c842c81e40c1d41802800d071f007220745440020b03480c03a100c5d855100902c08050011560140700400034030110305041c3c18500001d505024045011800c0c00101d4041c601580c1d146c1003440e92669105031040710302e0000c2c00040d010170040b1500a0051030030582c0c00045503c9200d0014019680703000150844640c001a42d0f4444c40010301032140d00c00c01d0840301d0040000c0403002c0713240c02182d1006013011550304240c0081084020048061000c00d4044400469009034100710600714040c6c05a0814485c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 490522625 1250 490521375 490521377
    0xd200a03030f1506050a050f131203030c030614010e121e0d0503070e04020d1103130233030c0c0307080c060901090201090b0a030e0307060506091b07080313020a1401 73
    0x40200c090000d503c050300a8261a201e841e803e00c0c2030741ca008251020740000c00f10340100b4100300000318003200c4888001c3d000b04010708110465803141d1070003805583c0c100807074030101450700c0c03410040303000424039001c1c4801080c00c0080b40e0030032039000719821440d8000030800c24840c0c40010b26004025038404c0d01800150026101c0c0e141c01140708444501c002e03955000024000380c901c04440ca0154010440f1341c03034000b0005030700400c503c4d50844c1c58004541c00040e0018441300c03c0c055040401d00454a420381c01241c26210b01c100769610485290401c1c400309145010000400d0b010f50303c01100d01c2e2003e074000b12901d0303541070314001c19958001c0761950003034010580030034140300050141090711641616881441810104102160b070000c030400700c101038503100000f000380701c140010301060340181d60104c1d0310b140182c00e00481ea60064a0100625500c208901e641c4e0090800d581c100e5603c00c10850356130b124941d05114504603901d000c0d40c0581d0311380d4001104101c52941003c050780c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 490523875 1250 490522625 490522631
    0x1b091806031208090c030a08030717060306070f02031209032a100c03090b0a0e0601061706010c0c05032a010906020304170102040e100303031a030d200a03030f 70
    0x100a6904055400c14400140b900030b084500e0007181c2e010f01030050744107154008460303180481100213071921189402c2900c200e0800010312805961240c00722140310090a02e40526041030b41c08a80d59442c0104030604000601070035501c2c0b0341c400e000b200c080008500c0c09010b0740c21f001030f60315129031042401c401100c065154403440c1015400841501407650380c0a4512010b203c60740c00c0c09004044403010800d80d45400745000504460344843c0501422900012061104c120462800130103801900c14000d454000c4415040c0c080030741ca5028400303280510640a1a00d4100c2c07000c055a0010341c2e040c05070300c0b01d0044400f84045c145c0380d00d00420020100780c4150a0064071032100c00e00030000180c104100510100c0410741c085428a403140c8001480c0076540d4581c100c60102c151604682c900d00c078501001071607454010400c4d40a1580119401030300400002591004c2d0400681c080c0f110300380c1c81c1569038891a201191441102c0b054491150492030b00a0051249428001019103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 490525125 1250 490523875 490523909
    0x90c05280e090d11060402010806040204090614041401080304120c0306020f0901020c0109050a050603040c090e1b01030b220b04020a200303060d03050f0403051b27070c02041b09 78
    0x48110740c81c11302090044044e01007a2666001180c130b41030010804c50b003040d020040001c60000510404009001c160359540802220b0001c00054401e558610003852150a0042c0003419000c0f0440e4200d4181c1404c8030384103160f914281aa13032440d64070107040340b403002c00c401c04040c00c1c01c001090a25826401d59054404440042d03401c40d01d103014072500240101001c0c8018107024004581090003803440040d406d540e1128001520170340c14400740780c0c0c0c0012058104461590440e40c0c04600309007418403925210002064100b0b01c100d00010400c2d0841c0518042152242e1050141c80c0b005042590b403820390300d10141540d00c14600500141015001c41d41c034000b0080160b80c010403000303100228504441d20201c60b242c002c5051902e00100420000000070801c20082c1c41000d81480b40100008680b4208216001e910440d12046003040c020900601285420160f02c14020700f800201520940041001003003103101c072903415610a040d00b04010b80040f120400c464505408102c104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 490526375 1250 490525125 490525127
    0xf070c1806090e281a100518152b030503060a060503130609020a0f0608071d0a03031101090b0f0a0b030a080d1d0a0c0612090c05280e090d 61
    0x1c8a00c00d141019005000704004883c01c03006412148a40140141c00090110174040041d464064031800d0306000014000c01c403d082003ca20402d500034908000201e00d86040340310721650760101031620408108030403086140051454080a0003290060203a0b03081c985000fa22a50007901c01504c00c41ca07a8030300007401d500c01c1c0102d911520010080351801c1d6445d82c1d4010250020400403680f080255001040740c1c0c3c96242403200600640c0d0301c001490614041c040d05049660740e03448a6801c1507503814140d61101d120100459a040c40d000f859a1040440315004240400d0010700800200b000c1c0544015a040c0040c02108195810031040300900201030b40d40318500c41c010400101400404c1206551340d01c039425149160031020f02e04401d4410950805100f108100c40c50020440c040c45072550001c00c681602031491410880c40f185501c0c1c0c002112a2403262034461601049411800c13490300e0340318440325548899000085444401106500c00c00311101d02240c0300d1005449401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 490527625 1250 490526375 490526383
    0x31505060a092702211c080606090108070504050402070809030d180e0901060e0c1315021011070516093c0905070623030403050f070c1806090e 63
    0x500d40f070041c0c1c264031881542d81c110b16490000c4007642c0c81024a0300d4003d2240d90034000a4030310941c03030b02074603031510200b03008642c20612054040400440307504001054039020b044503c24902402c03c0c10342c50343c8081c0d00301c0d030f1881160880c80d0028008143c1004110070b44001e0844550210103480c01c60110703040440315107140d0360340709200c4a0101c5040110280030188950000c02e1500041a02600e590b0b5403079502606071050518044002024500e03840c19007070032005171180c0c064240814a001c50025581c51329240d038800c1003542d62200d0a00358940b181240c607540d41c008160b44540b00d031040060f084002380c1c030450202a041035080c0700003200550040f01c00003c4400d12801c1c003559201001c102244d000c01e0360800945c1c0f844c0041c08148100700c800c0040030b40390389442c1e104003603041f8281900c2a8510340c4100030400c7c0107020001e60400192141d524150440d992605c82600b0300715841c5403a40d02c2840305c2245106e8007203842240307810420a03a00d50000c00e108100499169070340e6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 490528875 1250 490527625 490527641
    0x5030a091205040f1a04030210050c01060e0405160503031c0b0901091e0c411c1e05040213020409150b18090c09040608070302010818150a06031505060a09 68
    0x80b05c0010070040c801460680c3c5190400c1c480d5251090800003440d82e00c1f82140d400e604141405403002042004204081002032486840e4450585145143c000030950340d01501c03401342d000c4500020a4440644154040018000300901d0030046594420b0040000c20950011200b55a00c001980c180b250103070144115a4105039101d250308115100c2c105100ba43c1c083d5030818040c400600061031320304078415601e18403403070024103030368000d0400b2a0015106040118a1403800c0512070741d140c415010f034200a08800e4600440c195a443c0300050170011203010048002e4404240400e441c1c42c81e5114110b840110700070804a1070300c4d0741840d2560300400c420074204102c04441b9018a050180b903407504140941c050b6421300386020300040070742d00aa081b0000c15840100d0402c1950303484460180c015003d902a544c6000480700301e603844022100d5140c2e1109013034404180c2c0e000b509d83c000c40055400c18a601030424a00c00b0364009010305440b00c0748a50000c810214810300b5612038404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 490530125 1250 490528875 490528919
    0x60a08070603150e090d0912030e042f0307020625111c03020717070506181009050c090c0a020727020f030709120c03020105030a091205040f 62
    0x621850701a0440281c0b102400d000300022481c1800a80c52050707040c0140600007000c06410586690706008002c0a0340354400010076940c0000c0c4030210350003c5072854039460a880c00704898203201004802264410081d9580c00c00040540e8540c681e1040a18040e1025609891044c0c80b829041019901c1d1001002d9140035000c2c1d0540320325002c0c85030b0321014011030042c1c81c031144002c495480c88202c2c00f8090b4000c40d0b00094201d04005241c0c04d003400300e8032101e20300303414080c00b070b21880d640300001408001d501d0b04625070051584000c01c81c01d070100f0070990080c080b044042c40c0c01919000003c1d0b11030b001e00511008200c08461780c0d4140c0310030584a038014403206151540ca81d4001601000350320440ca0a041c04180d440c0395400100310a850310715920b90750b03040c1124014006007165214060902d1810b4038240090030407481b010459809290103a12512549821801450000340c01071018440180c00514560048050130845c1e4052012180450b41d41d4030003041804007a074890 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 490531375 1250 490530125 490530133
    0xc03070c0f150f0512040f080c0a0311010213060f02120d060e0a0e2a0405040303060602060c07080702040522141b030706081b030127020c0a0b1803030c12060a08 71
    0xc0c8203c8034640451b90150150110340013404a0b6203a140d0300381d0108a01c003030b054100e0220b00b8149030700a21808142c0e041c02c0001c501d0008654010a03454000340543c4c0b00b04003550041c08902d500c20088000c1c1c1a00c80c00c01143e4850f0790072640310041c20743e44510721105106070008ac40003043d43c40b69074910886c0c0c602808640d0071010070112183c14602c140c05010034081c1a445640d21117100da03d10403407094a002a01d181003907006458040024000710440b40d0800c5101d00240320342c0d040c4d41e01c8a6059501207103540300e4001045920701072444400e1100c1d070311082402400b0105041071160f161500542c0d40c40c0c10b0700c860b04c1c0890541403160300d0f0035501c520b030208003141c461307a80103174880a00132800a000104260801c1103510a900800303484040c415030300300b03100c1c540107070940c0c801c1e19410840c40e00c00d251001c2c54032210340420140c90004017000041c0781342440c0c81c000c414481410281c941c0d034a0b044509805c0c6422248080007055602800103103a4209002c143c010b4070041c80c014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 490532625 1250 490531375 490531387
    0xc0e090a0b130b0c090a1701050609160f030c09080115050f0a0b0301170a02091f12050616020f0114040b09390a060c02151804020c03070c0f150f05 65
    0x908150310810301a038100c00c0da202d00007040812401c029101c40103a500110f00d50814ac001c000c01c1800144c20f4a100d00080b41c046044641c00032403007179409200e814041101d807190903080d0748061580d030200856509020803a24039490013181c00c800c1d0707a021954040b641c2090001e00000c031407140240c460211040005100140c40d00e481c00da081c404141c121600410107902240a0010a56841071b101c0c122030102c5441c41e0320198030030050030b8072400402e14011310b9218070755910400741814810b20f041100100c500c81c801d02003040316052210007030084c4a05c50200030900c103004c85d01a0791aa006030301080314800081880b09030112064140084420241804e52013841001c800b20903001c5c0181c12604a13440e0141524010485034860484d03100c07880c0103101c22411070b8035400405030410801c2e00e8014841b00304a041c044001e031001a15141d004081e1032441c0315143c0044d0607482d0100001403240c103029808000d4804808200841007010041560042107034000b00d00410030a05c14 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 490533875 1250 490532625 490532641
    0xa020a050711040603020409080301080709020a0c0f050f2406030309090f070c121d04140c070203031b030301170d0e0f0d0c06260103020603010902070c0e090a0b130b 73
    0x1848000c02d400030300005120381c0e242c2c0000e081b29101e00c070071900d9030008401000340c3d44090040100400c110102540380042d11200201584500c501c000c04011400920030b082c06000c00819038402181d008450b8180e40170350121540110341012140c124446600291703440c02e021041c5ca900c1031000e00315807440d441d140b01c0c1c0510078034020902c1c2c040041885035400410005421006004501c1d150f1004c00c490020342500d0318094448040e010b503090040c1c007180c07000d8451071a64000c81e215051034807480c03540b0019040d40301b52045104841c10713031023842203c3d0401000a40c104d40d03035401d01440c1000850580351311074003500c4035400410309e0340d0b98500f45428404094100b000c4003c0008292040399942c0481000b00e81e080400004c000340a401d000c0e40c01541030911012855501e03a080c2e614550000741d0034801401410f0289070007046410400032000721040180c9140ca1001c2c11500e011a02c080d0781d62035804099403580d1002c0013042404110020032601c45400103c0980295a4100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 490535125 1250 490533875 490533893
    0x60403050303180a0602040605130504020c0a060f0905030403210c030f03090303110307030f0e0f0c041a030d020f070902030609040f050c13020403050601060905181e01030308040302060a020a0507 86
    0x43c1c015041e000d58403c41c0f00150b40c502c001c01c0546866102ca0342c841000c4030030f4004a04480e04450b00480c0b04200040d100ca200040384403004e0340c004004507141c1c1c41c02450710060300359145e00030301030711002c2404030402c4440c010043c07048452829100202d100300d0740844014500c2c540c0600840c3e485904075081500c01d4101035031a50203420301180440c440385d04c01200e41d104880d00c80000740e03a000d01c1403104015004400303400e0003140080029190a08950f611041c046907154400c030390f9401206600003071811a8400c6007002410b80701110040c240103511610840a551000d0144030408213100045109a03401400040d03c00304030f66540e50b9440110080c26542a07a0f50b00c1080c031504911b94070700c40b014040200341c4401507181c0d81b5519145144c000e040c1c1200c010700040d82d03001c3c829074442d107418480901d102c4050920b55200c0640a0703100458400c0040e000c0c8000c0000801416000488617004921035421600195a1a441d890807402540f5a540000b4010044000030a400e12 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 490536375 1250 490535125 490535161
    0x3030601050a031a060d020c0610050f040b19030f210c020d060905030310140a060f14041d091005101710050109090209070c020d1502070b0c04090b060403050303 71
    0x1813030070a2544200c500203101138004103083e2200f2600000e071060899024001990000002041849100d081a00090312400200500742c00740b80d0340c901d40341280e560091040b001801d05071882c41c003107481b4102007400a0044100b0303940c00070707410001c0303040040f00e15070b18100a82e969940c01580e010703a4200180c4182e0145c0a9981c0768070f44010304d02181d000e00085000d01c400c144c0004031185801e91041c407500100f02061b100e400c6440040251a41040c01c0c107241c05941e1900c0008000e4400014410303005a4024000528012544c01c1260780030010b844d000f0038880003100c80014070500000c5c25604222880c0c0754140b9120010880446202c1c206030135021507d0680d41c8840144d809601260002d90003021200c1e161071380c860941c02c0164049412a26501c0c00c140d150200781c0119013091b428030781c011320700502151460491482541512406a4040a04400b44c106000c40d1100c541090181003100340c83d2840040c41e9241400032102160f500c0307009542507686154084c08009111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 490537625 1250 490536375 490536401
    0x51e0901090617070516021e010e0102010e06070305070c06050c120114010906200609070302040c020d020705011b050a03120e011e05040516030b01090510080c0d1e060b03060903030601050a03 84
    0x20398141e00603a03505e200314040b00c07a0799081c9480e50007000001041307100c1d0040c42b903055914000742d004141002248040e44803126040c0421148c85402c01101c05044940026100c05d14103014480d058140500404440c41a031144d100f003640c8071140328103005074143c40c0e01c0c04030301e4003001003290f03c0c0a5103003400c140354148210080c1419180d503183c1003284c102c030040c01a801805043c02189401d100c1c2211058180c401001003e0810001070341e5080c0034050b20741400b241d0406040c00140d00000490038070350100aaa1203100340d03150140140c11404010160a41404148039a40ca014400ca0007403000c100d540c450301d48003200383c0d540108406001541e0600501c40030050380d080b00c01c081e038002c0d403050503d000a50316002141003141c8018002c621000c2e003048003044040b40003e0300c2501000700329010340150420307103005c401e58982c0301005041c02000ca201d440034413040350702c40c8031910415001d84105a54130002d03140c9920003141d815020030001e0140440c500d1003036000507108214 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 490538875 1250 490537625 490537657
    0x10c03020a2f0d020604021509010819090602040602030a090e0c0a08180102030c1b1903050c01060515041d07080f07020703240e0f061501051e09010906170705 70
    0x40000302c2070030030301200c2142d00503030301402c00c1c082181010002da4044640350042c00e814034402c000020016403015090003405140c008002c1b41038000d6500403045551700203000c554030703541e920000e51240c00901511001c26180c600002d4840360300205188a07040407081d0301c0c58000760903001c0e1089080070740125003145104e9407615541c402440198001d600005c6d407640c0f12803082c045692441c0281039690615080810409208040e15105180c0706606040007901c850f10305035480c1c010038490303204030303400000d100c0c1c080100c40c0d07018000c000740c41070000000d0740c410040b20124002c0302d05070b5000c00001c544000203410164444265a00080b20b8416560b40d45c1c1c0c1c83d1180002100d10001d1480c2c9102908158031705a803180c0726648a81c00c103040501060745d500c0029a0311003d005160000d000300701c0d50030a03956841002100c001d200800c0c0b26143e280e15205a91005400a161250104200c45008205207005d001d00d4490b401090741c50490b107941d030520449290704802c0000c580403071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 490540125 1250 490538875 490538957
    0x80c0d02120613201c09230705010503071215060e040c05042d030c1d070804051506040b09100f05010801361d1e0703020f1801080c03010c03020a 64
    0x1803c3c081c0c20605400b640c5400c1c1362840c40c0104244501d07031f0741e44000003580040c004010b036076040300a03254050301d00d08044c00e43c00003200300000074010034100e44c90042150300b07012954940045482c2e201ea24265420031030b28230b01072001d403154465402401045d01c821942c1180b0301d48072100b60810070b049c002003050090364070f50b18000c280460fa0801400058010748141300c8130700104040307031b0200c00b61502d111340d4189178407617940310b9210780c8052220b003a07d10001029521941c02c040344c1804d01130502c0400d45840c0464030f44020a038040c01e054110482000503181d841001d00a050720001d00b0f12840012180410070514801c005a0015200030300c44044011006407203200d1010145507290050100495030040c24150f240d4500c1071440008094401b0241c400182d003400d4940c1941c05000c4031140c00006156010100e041d610091b18410000c20500700104128003c0c1200394000c3c40f146810020a50680c0038018940000401306c7d24003400c050382d007090b241c94040b1840750924501c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 490541375 1250 490540125 490540177
    0xf03020f070803040503120a0c1407180905010506040e06070503070327050d09060c02130b090c0a110d1d010c150e070b120403080c0d0212061320 64
    0x4190b9440100c1c0c2d0780001c6010032003400c0610903003010450494485140140c485009080405110009400340390021006d0310540e03410810f040180200007446511030390385254000103400c2003401101c0035402d02010030f21a04180c042d4a0200c0c3c031003c050200ca0755101e00881d02c2d50001440c8004164590030750302034000800c0b40c0c043c1d41515603001220409038074103000d49405d0400d02e0308001c01c86162800c10800354080620f41c5c81a50443d00c0e05004020380d40258081d2075080c1a65a115048800780440c81240e440100013442180d10b62301c00da1081c5c86242a1541407203210140850824604149c4540d6400c500c403511860505200c42c00e083c00d61200c03805200315910344010300399103800201d03801c2c500f04001c0c401410782d000090326206140c4020355056102030070082c14000b420010548042c041c00648280030a220011900e0f1118034607819040c1304181c8006d0700030084010032800310007160150b568911130b0011200320b20611040320a0070b541c0807102400c2200c41c1d51402032100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 490542625 1250 490541375 490541383
    0x120c0d0305070308100605040b1b030f04031b0b0307030c02011b020601061206031104021303080304050622020a17030d15090c1b11040e19050606060c07030f03020f 72
    0x40c000d80e52252070303144614002c1c080e154060020401d4501041041260326402400c45054070494001c254407010f4052140b540c103981a0600100c601012501801c0720343d000c2e002c0c10499005030200c520391300d139030800f0a08003281401140021802080010700880c025044104c450b42d09100000f101c20148100408004880c1c000c0c0d40180c2003c40104185a444900d0300c8041020032030411400740ba40d074810102d5080c000c081070003160045a000b40300c2c2000c042041c0110f411481c41603507441c0505c0c201e511280225a04148455030000780005a1500007007240003070782c0609011a903a060100c1c000e01e48150701c85c2003440b440104070780c500300106401003170090891145911601414129504143c03021900c8610400402918556200c512041110300594000c0c03032520a9107040c00106028110042100010313108040c02c0e21001400300c1c0001d00c071030380110199503c5807209800c001c102e21035000d4500e040d50048400f0301c0400c640e44541ca002511900460721561a004820350070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 490543875 1250 490542625 490542649
    0x70c110d06020c160812030406050c0c060108030a020105240f0301060510110c100f080703021b0606010f08131e0c030b01030c0b2803060b0c070501140c0606120c 71
    0x126803c550114032130f50980007807240140041a0180403040103401c810145400f0042c4058070254440020603812494842140d0491103404240c1342d5075038444551075070b01c0d4060780e0011f00540c03910000851001811800180f40503042001400b00b00d010002c00200c00030a1032203543c13556842c80005015510001594a000b2240d1a0201400180054a41403003482c00d0594050011140032040c5a079008200c0c0e007040d6841e041803402500c400500310001e00070708060448803403058400422140e00001c206104800981c0c941000000490084a002105550a0b142c0000201040300001c244040c40e00104941d03000341c20f04a01d1944034404206400d60081c1e84101c03034080140188000c3c140c525000d42100c02c109440c0554085555030a8124131400b40c9503c4658420314031036521070b81024000f0030301f4800203a250a4082011600d40c82c140c89003034041586e00b10090000009541590341d1070b0b844501515081d62002c09000349035800e010701602500640315840341c50b07550441445a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 490545125 1250 490543875 490543897
    0x715031d060a0617030309120a0c05060c041509080d03020708070f0f050609030702130c0e1008060f0a05060415110f0102070201111506060903011d010e1203070c110d0602 75
    0x8a1900d84100c0040c02244404007104c81d42080042000102001802c1301044080c0554240e80707062541b012240c120307062400801a0060b9030610040c24210b0000c0c00940712030b49003410f1125a025800c2d03030240000d2003000f1440c0c1008804401c207601030f074090901c1030f001d2841c01c0d1030314440d80e990340640c040d02402124941140b40e00d06040c00f10401036542c1c061180e20045140265503000100705014860b100e00d9a161101001c500e194809d00c03d2030780003900580740e034201200c80c1101802225044a0345405050586c4010302c01d8605543d41c0b00858502500c92840e10b4244030100400300703241d104940c20310101e40d56000b10b00d0300c1000f03101d2100400390001600c1740400e10004088050300700c901c031000d60118900680c12400741c5207040c1c12880880d6000e980b11a501c0200340508149001020400241c01c489885044103400040d00703041e040c002d0780e1003003001c4880841c65000941c3d0900010701c5034404a000603600007441030300313000020008613400c94507a031401c0c1661321403809a8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 490546375 1250 490545125 490545131
    0x111100501080d0f1b0b0601030605040e0a030206060109030803041104020714060a06060512062202130807080a1a0403090b04260303090d0507080408070e01030506090715031d060a 79
    0x442a5684005130f00d8003460030b4500b101c08215001070703e401d07000e000030700a8006100f43d40030424503030117940001c00410000d0000e20105204001031911082000c2083e03000d40070702c20000d01c0d598455030341d050650303030320080007802d40d1a1619a1500941c0750044281c120781c0c01c000c64000f0462803040c6404c9010050001c1c44585400e03090a420384035a60300c210184001480380c070410803084260541e1007001600c07001c1d41c0308522101d107503074000c000020040c2c1318030001e0141c0c4054109a920016a41c0441c1100d030b00541d01c19139540d85011144000d8001580140409064161031008a130454000c3c6890306a042e203409800c80710780c1c01a8044d80e42e032000c8941c080c9165500e01070024240e1090350242d400c0d454503501a0740c440c9801e43e65003003040b00004202e410000100706450103040a0421200002e03261510100000d02c280819142842039000244100000154003000d456620b20b92100f8416080c0b8181c0103442d0540e840e003030340740680f500600c0c001d604014092044041c8c10000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 490547625 1250 490546375 490546393
    0xc050a08031914041113150f0f120b1b1207030f05060a231302030709030b1005150307050c0d082208031503070305060a140105010806090105011110050108 68
    0x16030304445100030880c403040f400808110120710203000c5d040c5a50380550360b29940c0d4482c3c01c0200e000309208040d5802c0b040504602054000220015406552281c4098120307240c071000312885211007408020a80f903480e1001541d05680c1c5091807035032190701c9102c5420100d0360750440c514040201d0b80000001c0e56400305d9403121070f6a020781c0e42c10a9003a902240d4a504041d8a100c0b041421400e1003180001d50b031a0981d5034132802d044548080340c000045441b8100800c004000e005144404d550704a0244003003005868001c14910031244020211038201c03110050b4251103803c01030007201070001c148400700148100744007515100d50756558080e56480c01c0c0f0030300c000c40060404a403030f8a0301009141030024080f88112030b004081e203101e2250a202100000303240480c03c1d0001041805440107110030752416400503003400540e100c0858250380c8420046641d8503080798103a0744200004c0c0100045d500508a02c1140c581d02825265a0095481c948094a40a0780324461a90045c104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 490548875 1250 490547625 490547671
    0xf020d0512030a0c1806031a030a0c080115080d0804060b030a110901151d04061829030309010806030316030903050f16090e0c04050103060209041406030a030c050a0803 74
    0x2c001e22031130542440c4a09210454586054078014081d84013495a1a000300c80c800d03806a010070540c450060459051150302c1c64801400320480c804c0c5501c40d0300740030191418103210f0641206803021000100441d501c0e19070704950250000d0410341d07020b640ca0102082e551000e0000030415801114124541d40c544002d00c80c3d04071050707102d144a4001c0c07240d40d0b004541e000200c00c1003034403000c0e08849000c50010004006051a500880c101c106131016001c0c141e4a03908900c24550000c05407400151072243c0700c005005000100ea075142e0010000c1560f2036010710b5030305410200240440303060528404050040313078803981081d004185010001c00812404102d07100440c110000940000600e40c9400002403100740100290181c442d2120031f042d030400c1100c10200b1344002c10600007940e481c24400020f5100307204007400366040818203206029141e200d280a2030000d401018810441d0f00d00f10303200703059040d0445041c09104444c034081840303503001c0c50207503216a01301900c0c0700300112 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 490550125 1250 490548875 490548881
    0x3090a2109060e060f13150311220f090209030606060a090312030905030f0703031a011209050c090106051c14070c05100f0f0c02010b0d0f020d0512030a 67
    0xa00100d1000414180341011a40402000102d8409081403c404214000042c4043c05200c241c050629004504204428100314060084900002c140313034800011003000c9080c7c5032075241c0030315043c2c07081100b001070091080d0102c8141626240003000b07152504902030086201e644880410f94002c02d0301c144e145000d000880e00140c003207a0b900e1078024811030242c2003258610003e882114411705100c00f5a0003900120107250340401179981c4c44028196034625500140803c0d00000d207080c60304203180c0d20003080b0501301c64050712000d128a00d00c400076800b50002c524202e44501540d144250b070b13038461001c9540038011980700c0c45d84030213003042d0f00c404281d8004615180380d824040d50b400c00410910b61250050f009251403842c0c40c0c1c150074000d2502212100c1d1002e0240382c10415a4888148d40c401c000441c19403109121030800444100d00341d0303141080c0254005052002c0c00005070600c0100b0040034409000300a4403007454440c54206044548601c044640000c1045031b01e0340f90744 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 490551375 1250 490550125 490550153
    0x30d1d2a03480f0904020d0629091e07020102090307080c040e0d0f05090a12030e0405090f060c07020301060302101d0111031206030118030504080714010f050901120203090a 76
    0x2010242c101000c00c00040100d00c1010034680144801e00215096445500c208841142c00000601c681c2c8070120b00c1040644070000350507000d08910103440d2840c9080e00c2c47d5405400c819403031014600c85001402c40c10329005d4041c000b1743d0740c02c1110700040d0700c09118060007000d440003d060114500014003082c0d0340d1141048420303801807003181010580024408002003110f103803aa8a07800d01101251540b5915002441c000c04262883c20070154040440644903405440034801602c4042d600c5948481805aa0700349800200000e00d00c4000fa1016141050008002045a44ea04e8020071030607a070912071390000402c13900f41300d00c480c05c4da00c0072141850401c0c40d00c43e290910044483c0d4407400351810013100c1e1600e09021036416030302500b19000050720b00017500341481d10f918000c1c11ba40d01c07620421081d400361040005090482620743e044d00c00060311060318002d2032000c11600c6070b01c018031141c10f100d0300c003211684181e5184041c6101d10308400040001951608006044010361 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 490552625 1250 490551375 490551493
    0x50f04060f0b130f0b0c15070917120c1c09030b0703090c05130c020c09090601030b09012711031605060c0a05030d1d2a03 54
    0x45020004403001c0358504007101c0e00b4a80d00e6890310400700c8081c0c004003082c0d0042003641c01000b400300e40401100000e007030070700d041004c4980c00e001c000080c54048604482400115064100c04c0010003c03c008506500000e00d058403c1e165140d000040c464001d0010351050354443c0381022075441c00c61078045503040d000e04105059602d5540c030080c05d6140103142908064441c020001009150200100a000c1c01480d04568080c071012a00050980307070800801031040e02c0c9075403010f042010b1454000c0e015000134240d00da08613185d2046048014203c0500c2d0b41d0f072410910182213040c8684c241c41030000003c140c1d001e8041c00c004004151409809220360090704881c900702c6e58078400c0c43c0854405a403000d84910010380c03010304240f159400034005020025000c10b1160190340079000b02d802d00c0007030b51904007000c0d4540d44d0303d078880740c0040c0b2a10b47e0207068000c0c01221195411181000600329199421500404080c140c65841140755003110300c0b2880e00c2e0007811201c440400f581c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 490553875 1250 490552625 490552631
    0x2a031713081b0316060b36060d05061510030203061e0102150103060905191106090f100c12050a0e100c02060c0604020103050c0a05030411031006090501050f04 70
    0x80e44400c940c510524014040011414025000742c030800e00581e541e184814100003003086441c100320001e00300801c0c6003031003a914180c6107042d4683d40d910501909408905510b202c0c008400040c2e0007480c0681100d900005841d0200001141009098070510815207801d00c0b4044200a000300d025105083c44280760043c410080706e5140c0d41c954140d940c2c501c9601010002c20000180d0030150040c0c2403a485a840100100601549800c450b004074462812115000d03101c0d44000c204030341e1a10010003075180d50071080348074507101f009040684c03002404000c1e01382c000c000140c2c44c1e551b624035500125000c2c449030b805002c01200303072140445003420050301e04035070048000c28240c075188640f0b20420465440c0a61148981403130410241d000e05203036a0303030800c5000655920380c01c44003240000c1c2454000b170f00c0146504241e841c0010691a401c2c2151241e5560701c3d0a0030004035a142c01d0700c85c01c0c0c1c00440c604054020322004202d954000100b65041600f4018400300c0c44d1245806282 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 490555125 1250 490553875 490553911
    0x30b0103020c0a23010f0204050a0b0306101103090907080702061f050d0501110714010c2606032803030e37150203090c01090b04062a0317 61
    0x80086040724981d6408040c8407050b83d00c45003014014113a403c2041269840c0000c0210910034650040c01981c00841d403201071940d1310a10002248011560260807000014a003891755016080ba0b00242004900342c0f4244114640400e01800040ba4044005201a014024403580500260307030041c1400c0e03c0042e1a00724000003590529281c412640140980c0c1060405c0c0a400e5204001d82140b10018035603408482c00c1c004003003244000541c20035482d2000071101240a07105994000005800c1c0d103604000c80400c850304030340000d10840e05070161040385030481800210088091041280490710b401c481c1c03d0050032500c40e81e064441c141d000c04128000310301e01002c14154038198110001810b0f42c035500300024504c0b0804010a40c4080600c0d14420b110710360060741c420302215080704c00c098629401119002024442d18000d0b507010031003030005910075511854412095840f12030007113420500c0d5007404003403142c15000164610328106843e403912003000d40100c3c0c10350189010741 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 490556375 1250 490555125 490555147
    0x11030414010b010e19030b091606090503120903031903060f05030f0307060509120f0a080603010b0d0209070306030c12060605031f090f02130c02012f181003020406030b010302 77
    0x1d50030f20130181c410404243d1324080c0b10494180100510b6102070707181e803542000300345980d0701c00300c40c8031071003200000c0d400102d01c41d4403038645001140c40040081041800c1107803400c040c3e0740100400303500b5020811a9040816039003003c500054615500000e08529008502c94003031007507001f4920a41002417200c0074520f0000503183c05030307004a40021940c03035820400b4034000304005244451007000c20003110040400c070141084843c51340b50200c4a980307450800d0308940007d6140e50340704400b0180000942070990f011035102e41541400100c1c0c58403604c0d088a001040e42c4242c0045100680c071204200701c6005502c01410103400820452182140510028440c0005d25264a5a51740303040c052043c6400303801207958000d0900a45d0b014005182d0001e40000c40042c009582440c0100345154900070700640c1003040040e030903000303100f00404c0b11070076440080d110940d1a100d61001104e5030303440e9442038500c02036032001030b5140d10f03040016040c0c1e111241c010b4181441405190a14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 490557625 1250 490556375 490556387
    0x1a06101107090509070305120304050606040c12360606050d0804150504090c0e01030507020f0706050310030204110a091d1302120304080106060216150c08090411030414010b01 77
    0x2d1030703200c1ca0208407035803695000b510780171480c0e101031300764070541c160407150741d62100085000368002c0060390f043c0e5845006000a540141c0c21010000710381626410508290342d0194a641542c50050100840355071081c50780e0b40d0f203000149081c0c055070208101000b11030b110301303401004141c07440c010012075504c4001036402280b0584ea48100307007042c0c40c0066403203078045901400d4404401c102c0c1948128004010400943d0b2080c003003480c080203d00c0917400004c022015541c01c100a00105003090302c00c179204d0b003001d88456810001d901d0003200590702c50064042c04a440000d4585894a0600042a110095110311101c0d07440429864030902402c10040d4865800c400062940403d8808a050b0308440700da000401c1c080403501142201064020742c0c125681d580c22200c1868180911660455007882004411101d00d1168800a40101031100e4214000c2241c3ca00707003111030380850251080802246d501e007000004020800406105443d0036249a00003000031408090002c1d083c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 490558875 1250 490557625 490557629
    0x90f090c0e10020a050a0b040b060306150d02041e050403090e0106140903160902030702120f03040b0714120106090b070c050f190e01092301030209060a031a06101107 73
    0x2d200100c000d00480e43c000c21442000c5a07200342203030b00309030240c01c024120708170a036070494071404604049030715440d00190b0f1030b01881c40d20340c0f429100240e00003000341101c100c8008a81046c1c48040071042c07400303031407145c40c111500c81c03102180a00d040d01c0e0042400f00700f5005000724103e0080140090750b07120300010700140380d200c0820303030b03030345101e0006807621811075941d83e5110074405000c6031541c2c45801550141e501602210b107000400090000e060090722a210040c0d40180000f90114130210320300c0d904000507003800381c244090344010a2030b65012403d070038040d010340c0c00100045c07648854204000d00750340070800d0400d465a500c119402d921031203010711841031544140759954503101d6103131840d21000b500309680740c0d940c000030722200707001d100700504a80f070201601440b000504800b070000c951000005496821030b802c2040b043d00241409410100700040440024201d9900500a0f0400e03a0401c402c5d1510404114241200403a02000c01003485040e04003104d0010321401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 490560125 1250 490558875 490558879
    0xe09010b0405130f0c0906110312150105090613050a060528050405100c12080c0703080910290a0b12090c040c0c1401050106140307110d090f090c0e 65
    0x2c40e500e00710301c0030f4015000400484e50344a00d01880d074400c0c00d0308201c10200f1100c05888100c203000441c011241c40380511082c850811020100091540c3d1441901d030b245d416050402c9030500c0340c8540440c01c0d60308140716050448020060500440c036040c003c85000300316a18149203400c4184155052500b280728402c200f0a0442000a08850182c42a60013816010700100d20040c2141801080d0611a88043e6817942040502c019008e10551a4500c5079080740341079807400310315650807a4840c000908140c070303038050001e50b000140c1c481e01490004540c000c2d19414007840c0c0c454160002c802c1220b4162046a007144204140c1e240641a602c2d0700300c20502000455498158490508220304006944145000484542c2d107400600d903080782401508440010580201a9401c1703402c00c7c01100f01103040035019002c0e1051a1000350b42c40001840d1100c0c82ca0006408240b5010804d115003011038400070040c00428101000c0768014490408244403c0c2001c0401402d207076540d101c00c40c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 490561375 1250 490560125 490560139
    0xc1e33040c05060a09090623130f020301030609030e01021506010c0809090702030309101503020d060f090c0503160536090a110301050f01180b040f05070e09010b0405 73
    0x40900c07100019201c02000301070800c90351124020340041c69500c403805800c0d445464021702044034903440c45004014103001d866141d84552440400803c4807900f031480c0e501c10340f034200743d00402c0d5444c00a58001e510030223000c00c0c90b0140746000b5000c002941c803402c0c11580310f400202c1c0c0002124200d282c1008083c00d00c0d0582c1c90150400e03508501c80c00340ca46412031500001c1c00b80c0150300200135071080d0144003c0c3e54014001e100f10100350741c6103e1100c00c042c040113006001520300f00c2c80c20f2082c148100c000190090400030210141c0d54880b1050301d180d40400c1c0c0c20000c0d41810301c800003030300c0f065404406401d1304060004080300007540807441d81d41c003494403030031034010180c03041c0804192408a000c01844c016210031354a00d01c40a044030f4544503003440174424141406440e001d9a222600d5018a80c20800340034408480c001044075210b40790001810241c0b600d104c1e81c401207003240b0f0040b4003450801c902800c500b017003125980c02808850010010300caa1a02500c040c1c6508480074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 490562625 1250 490561375 490561381
    0x1e020c1e030102070f150e0307030203040b13120624050a17010b181e090d11010f02070b010518040b011206020415120e0d09030f080c1e33 61
    0x320340240660513000f085403813000d242c10240000800581c3da14050140d052103204a80e095103030301c0740900540100941d00501043c0a011180c8001e051010302d581139202056685003c3e01c0b21460281109039281540c40c2d400c10340128903034444412540c400492006594074000206104075441e00c12184030803110000981b00110a4201070721620f001064460024060f14008100700800c1c5d0381c0031318892802100310000141c03150582d1259200c003014004042c541b80d0151140e014020702c45016541e25101c8202100292003e001403c5c02054107405560500e000d00c04c404054102d02c00d501d01d106d04c20480080c100f003250307905442e90403100000320340c024036207503010740180d802003480010304c05110005658880205a407800881c1810f006001040280759242d98410482c07400042c0030045c288049821420718100c1c040c03040e5449860b12401c80102403c22801c807000302000200e516440c2c8041c03d081002e04a010899140445030110f940480030188210f000102041103c071000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 490563875 1250 490562625 490562629
    0x203091806042d0f111b150705040f090b0d030c0f05190b06041407050703020304030c0603050108150c03071b020411130918061d010207031e020c1e 65
    0x4000304a41410a084034038a020160760701d03010302d42c203640304001e11303102d900820461319000b00e880d521800c0445030f10f41910b119114606065058014a491043e0071f02d00c0601d04540300c200348640ca2030317070318682c4071030914003000381503145980004c202c1802e04090030203a03900d440341e1395502c07689400c1c8020000e040e4a09440720592400018180d40140600020492401d0307a408008900c6004402101c1d034960b0304101c01c4500e030b090204201020b84000400b940c0c0038600030150035000e801101c1c14580d482d0b83e0366005032440d410400010392540010445c81e98104202e40d07040d58009503008052a154450301c0a9000082c207803010015a10313051800000c01180c009c0c00e080d00074005010300240455500d0301680000d0702c03440c5001000c4c070b00040200789031145191500f003418031070042e40c1042c0c0780c0c4000340100d019070b021040702000070074032000001d1005000e0f051182d2160741941d0f0f003440ca2103549420054000741550004004504107a4844041070411648914400300d00c1c210000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 490565125 1250 490563875 490563881
    0x13b031c0302030a0b0603041101080a0207021309020901082b0302070b1003020a15120b01021c080405060f2e0803040e0105120c06030705030402040912050d060501020309180604 78
    0x90102000000354040c0340269034503800440c443c40d803400082c0b058501c54420b1107514070080b540a4812003c103900d2074110340c402c1c4055604502e0700c45015082072401c0d00000c004485050002d0245580c03002d406007141858000d041c01000e010002e805246021040e1460b00480085131031244000092510442400381e4180c07100305400c5a0b40350346074a00100c0603010140b036808160b00c07414003c04005901d05000c5c41c66030f200c180e03564400740100001c0044130043c00600342c01e5070540c000d080a502d4100000011585050402d5807011200e0415040103030600c0c0c009015416039045e2603081200940c2d403a4075005e42015885800d4003142d904444400c241c0c1c9040d000744e00c880c0400980010541164540320707040e00c0007101d04e4503851103002003950f681c540031030b4841e400907400c2c00080c08590040c0c01561b2320600140010400180d50760b40c0d51007040740414885c01080c3c020032070515000b003612030705000d0402800118a0304600070006074624030b5500380e0000c62154003000031070310340312a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 490566375 1250 490565125 490565143
    0x20915130606051b070803181c0506160315030f0609060219031d191506030b070201050f01080709020d020f0301030c17070b040b1b0a0b06013b03 64
    0x2550801115450b01d07001041e1354010b8000c1d0254100480666100b01e030081203000c1110220401945018041c15807100440c3c10f0380f4109900c108403007040c400c2003944400903480e0078412000303071031103140070005184004010881001050302d02500810144040382a803800e40344c00c0010b60b41840401e1503e10060840c99070000c08190011400c090725081980e00c14041c0d40d190340b4140585400c3c511054241000c1e4500d800c1d140c1d000e0f411110448480c60782d05842107000303465201c80c090b203202c000015111035600407607400c85c03e4010050b030707180c3c203110700754200d08003148450241d450021403950300c1700e25000b1075480d1580040e40380c190580c540d040341c1c1c0280000c800c058580d81d482c1041c420b242e09520035220100d41003002c96580c0d100c04112482910703144080d0030f08203030030701d82c0c0e207111500400d14003920b5504d0b004142c540d20600b0000c09600c04d200b0a42650300d46440c400040c81141c000c041010080e80103d82c500d4000083d9030303000e02000da1511020300c1d1802141c0000d1800c0090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 490567625 1250 490566375 490566409
    0x5010503090c0a080d0905010203030c0d0b01050d060b0405040f050f0f191404061103091906020c06040f021507022107030c060f0810081903051c02030a06050904020915 74
    0x1803080003d243c0d04c0465240c000c000d894445620160743c3d40d0043e600c900c41100c0003c1030b01402c020420038906a503100403080b81040c0b40c1135081800b1004000c00b00d2b8800c0d081100c9406010a0400040c0740c82e00400c1801c0c158001e0502c080d0806000440710660080c0803034110308403540000d0280ca08406a1081081400c40148003074103070020400c1d0118025a0165582c50900413207a01c0d03400c42c3e40841e4095020f200007043c2c0180400e40d00a115079203c281114066000c12003840303520782c200076042c000e502410f44520400d203e481000980310390440803128640040c81814050f17641c4011071341c2c0c401100300c001c00340c0034000d842040c105103068000a00103080f1080c040346081d0301c45100a0000c09688854686407580405000500001c2c81030425076030048071104401450300029076503240c881c0c1051800c040214a215403a0038914002c0864240d000c0f0030849201e4842c0242d20003050103445003116410941c0100d00a4100103000460500144603202080c1c1c6824421030982141 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 490568875 1250 490567625 490567639
    0x20d0f08090a0308030105150304030c030c0302070e0a020d0b0a0513090218040b0f0105010c0b07050d060902031303081b1e04050d030c0605070e06180312180907030b090105010503090c 81
    0x70f900d00b09403507410070b02515001d81c1501440c01084194201100d004603050346501c0c0300d136465550b040381e020103a0b50701141140924100001c0c40424030641d1401881480c2d800b44e01c27080b0082d448003c5840d161304aa01c25005000304028640701c00080c1083d01c40c9501010640d010b0311300110300c0d80d00403003295a911007910000c02080c418a43c481da40507140d049012a806d0340c2e1030004486000c0e0f40a0007500c228001c40204402d103000e8030045c510b58102c1e5401090b915515042d0301c080741c00071540012007003020340800041541c03140303100e98080300310744401c050780508030b09500e290300500500d800d0500d51310200403240c4403200c090783c00501004140c100514801c1c5401007e60032030b00b0b0202c88050a10b0003040c034050088208580260000e8078403030400340c0751b8522041e20f181d00308440ba0180910040c1300e16103102e58009044882a200f124200c600c4c1c201d09110070040c0003400b1900305490818658041e40ea00da040c103046600904e0481d40702c0d2583c945190601d90b441614943c0319107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 490570125 1250 490568875 490568879
    0x11b0506090601030c0b030f0106120e060705040810050c030c2b060e01050d050a020402090f060d0c18320405090109210801052403010602011413020d0f08090a 70
    0x207000a10141640d100707468210f030250307582e004040140800d40e441c0329a001e0000050040388d2040280030b0182d1000710b030104034003030a2071005081910560b269400143c0010301031102c00803c0054241c0d00501190801203440c1c41004960a40409404601ca00341e001851010f26240042403015600501c010a0340c0914544000300051681d4810f1144015089000007401d01d85000e4400a0a030000081c00300000e2036800c200003940114803c0364030160703e010160a64883e540a4807070000300b04070005070300310642009031542c88482d41c40318200c0082c440c1445494001510b100328071071300750420880c17040f600751402040f14002c0e0029800900e8107081020310f010540000031241c0c080e04400c225074501c0d400410202401041e41d501103000d40d001000380b0f040111400304912641c041c14506240f501c0d04205103513100384c1c400f17001070703460b5060b90380408480b105c1c140e0001d64849841240011aa02061302c00084030706c080d20000f20003c080d824454100200c0340070f10070042102c04203503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 490571375 1250 490570125 490570141
    0x11011d13110f1c090b070c062706060f0605040e04110d0f110109141201060803130314150c18031f0b0d02061e0705010f09050d09060905011b0506 64
    0x1410000f5203100e10b0111140926056403240b0646460b16009141e14025075a201000c4d0f0f0410410301e4101c4009503580007000c010004242c0310005040410340720403103040503080c01015544190860028a40c0390041085419007200807207045541500707030358480e5581c80c104080c1c10b001000070940c0080301c440450702004840340072051020f1051f031840481041c60401154906d2041c00340c0751200c401d0140c1c2601c249444500f03200895043d9001280040d1503080a6081d078020f813030110400301041c1018010400f0030122851400d8440c802040b2031003000303000b0b52005802801501c0c080c20000703114102c585003c0003a1141d05006400c4520703c0c42d141c6840340c0650104581c40084038a0130814010620740007501c95101600100303442d082459130255010f03401100030b201c2000d46c1c020048580040d0007030150102c03028184c03200050f0440e01e1b013005810030324401d440d82c0070070011241c02d00c90b454003c8810005d5400a00e00704843c440c0031103031640204000d00b8003503d03500c04c1e0001c01c44c0b05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 490572625 1250 490571375 490571377
    0x13030b06190501050a030f0207021e1201020a0e0108061906021b030604020a050103020c0a0f050d03060501020d0f080711070b092b0201120b090a0911011d13110f 71
    0x140c8030076507030041d26003000c0301c0d80c05071805140100c0340020820003010718698803d800c03218103130002c0040180307880050f0f40002e44507880700340411440388419209500310b1600091000403100f0b607400940c030b4401040e000800340c420100c00c49040c40800c60214100392901d40401480a002d04096a00d45885000295032203c00f009800c1c0071010340031a0004504011600501440d406003003a224a4206001034001e900940c1c8030003003912a104818000c68030000001e4180e501810191114420441006041d184190041030566102000d1007034020703407001d10b4150000701442c10411607140d0500c01c0340c08100760713050100c651003108400724040310854020302c402102124034084264103c00d070b04880d902c40190000740c0100004000c0095400b030304550304e0340d081800c000201c081001d000104030b00002c1d07500c0720800f80e440c1440700c20001d040015000702c1409003407800d00c0d001c0810701003201407070400c01c1d54080c011450744090445901c0c2c1100d1965081030f40e0319074554440c840c5030209 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 490573875 1250 490572625 490572631
    0x7120c170c06190b010e04050406020c0d050c15010e0a0b010e04021315020c0307031202070f0603090c0504020c19110402031312030c05122a07061406030a020904030513030b 76
    0x100040920800b50b2141ca1007202c2c4c031140181c4543e40e03111175074030400000380300051003595215001c0102150881e0280401844009a07840d078548484000b600c151030040b140c0c4d5040b00400302c540041c0b003507012030300310319501400028010074240d000c000104d030000008050180c10600201d94441440d03094072070a03090307480c4250500800c8060150072692000c1c0c0414403901900081c40a201080103642c510604030294012501d600369141c41e46544d4940650080000903a10f180c1c2c0c00400c406110050018201203030258240702950b03c4c40360711802d100b807164080302c0c4013121440402c2049149a6060716004004644038980000000750200d40c54104590317240f04101c0540d5081e0292260844c00e0503140d56032070400f2244803010000040c05400002529601c580c4007207920400ba4040940174025000d464551074a85401030603103510007895800c8100e4501001020b41b4000f5040710341d2601160000d0042c2c4481c10281c03000cac410000c0084100481e007102000340495828a580 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 490575125 1250 490573875 490573891
    0x180b01090e1c08070c03030b032d0c01020c060a0e090a1e0203100504051509010603150f08060c07081201030302030315010206093d06091107120c170c06 67
    0x22100804010014a0003241e203403140c04943c090011803c0c06200f00c8010701214441e0a00040c07100031900028034003c00701c001c0c0c9103003541c4107480400f01e40480f40c0781a04010b1110081c6170066007100081e49a5040c190721500841d0041a015407180c8101e152000b03a01001d0a82c24242c100180300d04040c014080520070400345104a500300e56099108692040e5802c10302005a0703818001080082c11000d0106a0301c08424841c8006681d54071715094002c0c08180c800060400d5081a22000100590301c03440001451800c1002884408075072261300142c0c52001940c1c4810500d428405400b40000001448192000100c20107400000450156250f01e00400009840000480ea00c840854811680390810103041001d0103c200100442c01c000d15548180140300c00b554545a00101c883e000c01292280310801c4403811910030981c0c0c03040c0d00c0344028904040780d200c113802448001480004c100d12081c40340240011002030840d00d0b0311441d21603540c1c0d0008030599a64401c20b8600c46 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 490576375 1250 490575125 490575133
    0x101517010b030c2202161208060a050319080c030403050709020904151805190c0c110a0b0a0503041707050d0e030102090f0411120f040507140f04180b01090e 69
    0x40c640f000c01c40840f02484941c140540142d1688140603420141b41860890b448050346000540078010b03120002c03880381d4440c030306490443c00b0400f102d400d96102c58002e401000719000d01d03c081c2c25880d10f0703203a00030309400c0c2e0702c030301c16a1110b01d0f51049034809403c50250303d0b004145000c040c1c0040189050444003071103507091031850742180d0242c912030f58550000c81d000c000000d400f542c1006134010104030440f52201c0c28012200251500c0e0001e80c0c00140346103954000704540a000700030408030540d9100905c50814044901c2c0d07202e800b4040040c42000720008007000701c0d620780303c03030840008003129403145c82928040e9614801da5110801248810882c000141414402e4880305440100009810840c80b803c0c0320003803c4460440402c0a802c104007000031070510307807142c011304032400700920601d01414641d0800c0c4e110741010000140d00c80d000003043e030365100d48a80c0d6400845000640ca0340703406240c00c0644407400010710840d210800007603c1d41d010b03404089403150410642d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 490577625 1250 490576375 490576393
    0xf0d150c0201050105220f060f03051e030313150906020c0f0c030706030b0f090106050417012901030e07170d030b100305090708100506120c03101517010b03 69
    0xa0b030980e0b000340241500f041001c04580040c0000d0300c0c40e1109a4020303000005c20350035403000b10003070317418a80040078000300182003081042000c110800402d00440c500795070002d40d4a10907500c91101503d003941c007481030349a0100303100034819004045910a801040042143e24051020f074004007803000950140f83e000625800001c5100c49001d00c005000e0b06400d420400c05030028003070305064a4014400503640071540d1107003452070340a082151100790311586401d00004941800c901201e1032a41004810f0a40e20140e200104c40a420400700a110030710f0800100c0c0181214100f01b9054403408500080300861250500302c4030140700241d0300180e500040c29419140f2000056402150020204601d90311a40c070040d0044984400c1d12291a5200d2061303260103204c804940c0916990400d1142070324040d80d40701045510100980158406a8002030300c0e034402401c1040c40725182c170582d8185110300e50111000e000d640b001e440401002c501010b000b04443e1070090701038031925500c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 490578875 1250 490577625 490577627
    0x9191a090a0507210f0c0e0c0f030a0203041109041202070602030f03012124061a0306040b0f030a050601030507090204181104030f03050705060a0b0f0402090f0d150c 73
    0x40207503556041401003510703c1c035040719054800303542d0790110720503603070003029400081000440030145805541c2c00c5081c0b60a002840500d120094204000d01320204090a0b0051010003943e900005000c40180c880d0781e60f081c00070b01a8480d481c59644030604104000811140d07060000c1c0c0310241d035003240c400d10b840b04030603a62881840c481c0001404184010048620f840f800d1741a4001840034009035144c0381e988028106001c0307107400c80e050303148200d4082c0d111214400c40008211043c51201c0b050115404c1401a1001900a5004980320015078000b525110710600a01d40f01030200d8900070840c0c2822501c8007401c0c0800c4500d40291540020b485916000755002e6588407003004a910411150100040c0217096072845503010600c4000b0100c3d10b00b038111090320307000f41c980307035945d01962802c2410448000d2520824616001c400041502d94808000c0d15410070348006a64040f54400688202190503000341d20007002d000d00c17001c104407203140703426021086000344100100080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 490580125 1250 490578875 490578883
    0x1080105090304030f140304061205060f0906241809090703030f05070f0804090c0f090803090423010803211b0d02130303050405011413030b09191a09 66
    0x51a95075591041c0003c2c80861101e020302c62a561042d1458020705030019207003030460700507030f00600214031185400103400e011030052640c0050f0803550700e804400003270009209080f010745501c3c010052001403100c807040d51b01400c041001d2501c641d0b61100b083e18090701c030a42c0e0040400d4082d1260718046a0042c0c0d0005504050307a60548a181c2c0070703200c070001110140c00c296024dd500e030189000c5100856a004000c001600501c000032170f1030200c000703010300b258808801c80c504000c0400020407050601205031216401c00300c074003142d0700141842c50140c081c81000c82c050104506800012410400030081500c00e01e40300400820404030244100c0201080b1805070101d0f504650300c04284038000000c150001740404010700700144000c0705190512260011000b141d00000c05000c2580c001c02c459544090f401003140c6480c2d11481e5001034424a48002420025a800403900801041c4641c130503204107043d46500c84425070074040108414010391032900c400d00c00216408580100d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 490581375 1250 490580125 490580131
    0x20c15010f062c01051215011106040b07032c1617061b160308042d0210020f03130905010b0f1801020c0a170c040b0a0303030504030318061401080105 66
    0x161004803660940e0f80510789003003031000c00ca410040c00b0003030034261101c018510360243c8001c00b4201c0c1c110340407100240190818004804d0240c0c071803c200400188024129035000c41c1519010403d400f00042d09442145046546000659140710b540d4043e0000180b2001261003517031600207150b07640c1100d419203440d400286009400240000710702c2c81000007070710101660840c8a40c40c011010401803a00342c1100411400216281c003444180038050300441c1d000980d0001101c043c20021407020708184a140009004a420000d0901d5040c028402c01c8075100c601c030140c9684900003810807e52512900501c1c1085207008004a0032140341000e03681002c1c0c80c081c242c0d14242a20b5869602c921000300c4803811881507130034403495070721140b100b10b004100c404500f0f41c446c0c0192035002d00301440316400c140500e2400d80049647c7c0d0b01c580d0154222601420001420384485c24214054400481c440c41030070305250806d01000743c0c030743c0b0001a103115400390500e2a41c99111203802d0701c0d415 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 490582625 1250 490581375 490581407
    0x105092401030b07090b16051b01020a0312110310030606060906080a05090c03010f020c0721020628171308180112090507061103030403120f020c15010f06 68
    0x1001880042d040142490300042135041075070281d541d40026882c0740d4000c86c40280c00300c5443d011001003101c10402c0c030881e441d882c00d0300c5d2041022200001d50301c044418000c0c0c2040840a4040021200e6074020340d106031404425035524a0280340035103a8010314402201d007180b030102d0008a5602c1100b606065642c1c03a9035074040c0340c0b900244580a0880900190014080d8841a0304180d509224045052400210158840080d500301a00780a055400303825044654011903510500f440c3c90384240c5a41120015118205039141e040e860348103804240444402c2c2c1012805150044080c0300c1010740b5180d06061075640340d2414144003403c18004004135804e01060702440403034404109000f130185000d03841e40032190111000d41704d107400d0039078194014020034045680d018400700030305035451000710718508083d0750007403010103100300324005140c0c1e44840c0d224040e12074040f103c0c0c0c4c240840860320807081600349800c10030001e10410040300d0340301800080050184062040c541c1f82 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 490583875 1250 490582625 490582693
    0xa0f0f1103090f010509030a061d030403170310080d120c020309030604021c02041a0f03060403050d0b01030912020f070807061403040305040e0f16050f091207090c02010509 76
    0x541c2c040c400003200051103607061141c14825100152020400f14140c7e81c001e50010030000d500000010748000003500644054004000c140041250740c500b290710700c00324405266527075032040d2441403088217941210045000700c2916440d802d0384070000030081d0010101c10014124400c0c0140d80d240f06000d41180c05810030000200940b07066030034035a4180c14650480c0c0c0103406c950000f170464801d0741480d00079007980850400305040003c51683c1c01182034009200605280c0c80141884c0140c8480d01c5c03049454400294007a40310740c02400400e50f02441c010380b850800d1102a45405140f070240d04148a100c000080009002800d071040300c00c0d640301d80701a402e0030b6a101e507403548028801d41c20301c00c0802000400d0550074500501c070b14420750a0200904198021007106103e90940504004050000030740f0080321908070f030015101200c14000408500704058146125548a00010351520b90480c03055038043d00002d12a800d0441a03035144564486d0352074100d44081098150891 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 490585125 1250 490583875 490583887
    0x603140106210e01111308010905210f0301030b06010f0311040317042114030a0e040c030f11070c120b1f08030f07120809060a09170a0f0f1103 63
    0x2a401e02c802020041420002c5010b40300e8504683c2036a0154181100a401c0002c04568003c2a444e00c80003610018009000b05400c54850350b544140e032060701280305000850302c0800d40115421103c2000e030540c038140d20b139a52803c000b01c03884401c4800c02e000c00e0b005c400c414059413092080c0100100ca08640b03600381421a294007035a0000031800001c0c504d410440400e01070019520158031004801d9010704c00c4a4524080c00e510b1418048400701b507200344406035000c0c1c0c110000350410310742610700090341040104c0480280042170a605200791900a14014801f0b40900401d40580030f007101510140e40e50b005111b516401035400313001e00d580c140101d07588840380d0004040c046008408403442d1900c40c8842c5041d5030040703c000c280c0800004100c400c1196034881000050098241044a890450103441d2190401000b0350f42040d61400440c0c05c208181c034003c107664088400590715142e1043c00034014544481516001c1200d00c01112000da10811181e10303071805080c0a542031013 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 490586375 1250 490585125 490585157
    0xf071a0103031d030d26010e0403020d02030903120a12050a0b03070f1a0a02121606050121080c12040b030708240d020112050a0c0305070224040c0b0a0206010603140106 74
    0x70310211200e100748414640d600506d00f942181c0b03280038020440c4034203060b08041c40c010340340034855020a0700390340040c06003034895a004980c01c01007003400c505040d0780e2020505c2c110344501d80b00c6846000546807a084c06020003c5500040700004194103ca11a84c0c071920301a4590320f4074428904208055904100c80e00e0f010005070915480500417203008030601140b0f0140b0f0341140044188040e60000e00b00103215044c081c0500511007042d0f2801804002d070885445404541c10241116a0015190042840c2008000c1100b41c410104a8440da10303003030390170156401500c010b03000800600c04100351507101d070154840310414018400300e444022040c051050342405041e4144503130070941000b4010360303020f05480340c80d0b80c2d18006019104900f001c0c00710b031001b5140c041103500070220803007504074404038282003402441c003458580da9145800c48040e0030f190099403c0e22008500c4410080c1c0018600d4144e520310b03201405115a0000081300c094024400c41d00000c201c410f40445c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 490587625 1250 490586375 490586387
    0x90f0306020706020c060103140c09090a02310902120c010516060b040c0e0a08061308030c070501111c05060d02040c0c0606080f10020c070b0f071a0103031d030d 71
    0x820310810f80541080080702c1542d06201c0c00340d00c1034401c4d407800c10582c04807030000e10001815101c00c940034404e6052172221165120864030009004485c4050342d4117000d81c0f0340342e128540305400b03000031003000c0044401c900900141a000c030301940d0070006900940300003058a058070841a503509007408201e440d03201204081001c250b410700d03070303c00c030b84442900c9138020100c004445445c0d0b84c101c00f00110034004405a554400f152641003070040c0021445210451510036070002040b40c4c8039200d003c210300d20f902c61032a0003411036180808010000032030f84041d04018440462007a91940280480404d4920071240c00381c0c441c00c4010b1520044c0361030390260031b44000d9807420381c110b0a803a644160407280c0c25080500329500c40500600110030400181a075140c00900030750a00c0940c82d4110390703401690103000c06654003c508400f800f5074100684456a4128011848016804210401802c1c5c2804150b000421040d0f890820982080c00c4e0541903070b01400030078490b4285c0c04104c1e40c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 490588875 1250 490587625 490587637
    0x306140f22050a050612010515010f09172107110d05010f090501021e090604170f0105270a03091406120a020d0c0219020108180d020d0f090f030602 65
    0x3502010385000741c4200d01c10700c82e8a100f031034940000180c600744081000000c54400c4400d0354a40c0c142810002140110483c081e034450003070030031242803100302d141654002420307009000f10382e009070f082841e0800001442046102040b2107010071005100005000f44240c0001510501b000b070f002c210b8508010ba0781c0002d040c01880000382c0000c8070f00800040e22400142690300c0d80d00411003501103140c260303041500455014169140819100208507d402140702d40b00c07120344000003c202e2010184884c5101500c008000c02c4107284c0500c0e84191034101d8103a01d185202c0c014061000200b00040c130940b0241c0540ba40050703a80780c410a902e000c1e041d1050260090024443d110f44440c0c40881c03070b4014410808096222801d80c8098021507808024480441d80f0a030103002003801e445450014043e020310700310045903540c500071207400e02c2d0242c07010381a01c01e2101210404c1d601007000c0075a08115551505541e40e00c41d81201c0c404204d0054050340e18a5602c10000500c50f9801405 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 490590125 1250 490588875 490588909
    0xf080403051b0a030906020d03021806030402030712050607032d05060a08012909061507020402120a15090c0518030c0303030f07110106030c03020f042a0306140f 71
    0x94407030300c40720307080c140710143c902140894040c1c2d03030a000158061100a041020340d2400b1810720070140e43c080340401c01140128003c0d00c000002c00d040d51818072600c00585807048031288a03040501e8140d98a0034111003800000c0d151103d660b0700d000d0050f40032a040591300401410b9059507040800c0200400303400c2030340c8441c1e00e000006080c8402c0c0502c020740004000b11803980000f0705090b050301c0410102551080e00484100703e02d80e038030841c1d021603c0c0314514849880d0b0f201880824000e21a00b12002131148202d0300308590309040b600710800300c013000d4080a10b2595200c5100c4d003500c1c6018410004100c040c030520380081d403e80d00309041114001c0072030303417003007031000200341554402c1d00c102009614100c1007180c055008079911004c4015400200401441c540b22441414198000280704190215920740d49951f96004108a01c0703199000c0e81c009541e0401c1381c0c024a03925500c130b2011904001000400198840b481502c004001d08027100100e100e80401038001c0ca8000825 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 490591375 1250 490590125 490590157
    0x13080307021608100b04180f060b090a05090c011706010e010216090b15071505060609090109052202090f07050c0d0216050303090d1103240402010f0f08040305 70
    0x341c1002c0a40d070440c000c080d0b000140042401940c8844151403030350303c55500450801140d01010010203400141280d00504c00701c40c4401285805005494020314003680207401e0b80a102d1141050b5010a008001c04070888126542e050019a1580c08500c090501403600034005051540184001808840140705680c850302c003081c0400d1010625401104109550324440c060300c0c148148200f820030b0441313107114140f42c0c860f9141d07110321034001d00303030440d20b40c8680104146440303040c1525201c0030014242c00556071144400001401e04440b4802441401e2940e0000c00c0d2128106415181d0090103010b0240d540a1003400d00c02c0c800b400e49002c000082140051440d02800b1101c500c815a50141190810f09100c00840000a0700094465001000a50758582d16081d08584181c1c0c00354654084100c0742d00047d003003204400100801c0346038041c4034101304040c0585684500e101341c8480260b840c1c0908111039000d503100c01a800303d095071000c14080b03401040a0b00301c3d0403c58240c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 490592625 1250 490591375 490591393
    0x9040b040207060b010f1107091802040c080402011803110409050309061204170c03120c1c090209011202010c380403080702060928080304150e03031308030702 70
    0x82412a0b100700070a60300c0c2c0e50794070318403010f940c0e000041045d600f1281c54001c0815034800c00050f1143c0c1948100c000c0140c1c0d40707454020070248408880c40c4290000c0041081c50380c007080282004004440c2240003441c02040321648000a0043c40c080c0c0e41c000150903c84440d20007404011301c9055001e45181c802804404015a2920001c25041800c01240d00740d43c1418640072a80805981583c1c804010074800e04403000f50000654860b000c0d003001d800e0f200e440c2d9020003402445200fa820f01c0c0d660008000c02600c201703e4014144551095501305030907039072003459991b446071030003000380044e0b030010f04031012400c182d6003103403181a51203d01e1480f80b00510113005d82a18044c851940d40c002004000505803c51600c55004840b400500341e51b1a080c0e001039101c8030020002e00300060b09620f0704442500d552540c01c9202e6116458a83d242440c4c140709812802603012614100c1c100920124100d501009403801101c42e415903015103680c1c0d0b41d801c050385d000105404114410340d088 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 490593875 1250 490592625 490592629
    0x30a110c0313060203070f11010c021201020406110d080601050724050603010509010e0d0f0203040911091c0b010612020c0114090c010309020904020d0309080d030f18110609040b 78
    0x100a1824440300440d503503401407500180b014129032100040d9082400200c0101c0e4020314040c200c203901c402d80a454001d5a401a1240c00c802e10001e50010703200745850301040742c154018000c0c3c07000d54442c00211141440c50369a18100c491aa0b00010800004604254000c0d000fa0070101e00c55190250721400b03031540041480d000c00a0507044540751b100340150b43c1801e01c03a41d608051100024408010008245030340c60005035000b50412079880940200c091081c0160303400781c00c80705400c1c4000940071a80102903000307003030340358031074003103c150a14203c05452071103081952204800300305030701c0c040094030b041c10b6204104000b6a02081b207410024800c0c400c481c40d4280d48807001e00507003081c00d012443c000d05105018149031078400c8c090b0141c0d56038480954010b50450303035441c1c140351600d42181e41c1140c0b07500c9074032036101e902e4201c1c1c601c9403d60045c0084403483d000400000b8a07606150b03080290b04d500c0274140d102c4011254840b42401e00041050a4010b8004203160f805040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 490595125 1250 490593875 490593877
    0xb0d0b01050d02161e0c06080910050103140c09011d0a0e0319081503030d0209030c100c03080f1302040e011811030d05040e24090a150902130605030a11 67
    0x14851344529515094400f00f00044a0802583c03624080b00e00030031603c0d0f510300500c1082da004241c10710040100046000d402080740003d500700580c000e00c501e5a50b440c010295280b05261011113019aa22050490074015080d904850080c200012a42c45000e07030506d03045000f40c80920b40316110030b812222460100000c1200307401d80c420b618010300900780c1c014415040505180f4001c1c41c146007401d002c1c2d900105681d0103200c401401655941807a0000707140100b18910301e600302555902c0c007e127003900210140709290280e101c1d41500d65072500f0f0030300390980c200d1f400e20555800545407009420585e02c9008a05401c03c0001004480d2112620000d194008200c0e0019440c80c030b500014101842030000c09145418050305044c2018501411010010034095140100c01700c886080762a10b0b0708070701404c4020344054820709100314400007404c1500c84038602e44281c20030004160350a0303c207d4454002d04144003410324107020084031554009401da20116888e44a0622621402c070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 490596375 1250 490595125 490595137
    0xc0c03020d030e1504120326091f020322020a0305060a020a02010b03070501080727030803040b15010516110a1214060f06040b01051210140a0b0d0b01050d02 69
    0x140f6030300d942020310000c00c800540c01034800003084101340010040319010810740742d4510307894107004a103495103030001107050f002e02d01c903060014803602c244012540040782d15a140c0740e048107914800d07001c1380200720a80c4010744d2070003034207108001180c844007441c0000d4460240300400c01511507549032203e40c5010f0041d950600ca40b6400144212a160240f00e0802210300c00d5016210080ca007100103048000d00420369000e000440b5500c101d031642d0440081d861009000304031100507200e007071888582d0800c460450788007810202040000c94882601c00c6042c1050350382a10341030309035054482d00015004126601448a02d411201355107101c04207000d450590714400160a00e41052242034010442620700d54011005200102d103540d50a140d01c5034054801240e480c41c80f1004941c04d1040c01e000318003a590000034041c28020b0303030042c0412554030031061500d001e010010010410040d1052000e82c0c44104240070300400c1b00d0b04440b48042050502508090075a500719041e07034025 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 490597625 1250 490596375 490596377
    0x709051f090e0f06010e06040207080c070b0d050c1c0b030708010504120314071407170d090c0614071b03080d020a0807080c0a112a03060a020c07060c0c03020d03 71
    0x41d80500b024408200040309600381000010322107545441e022482044014100a01464001558109100744c2c2811150130981c000d00722101c89646a51003001504101c1e40f041c81d850619021440c2040d81a041d580f41d540600c8400780c0b031a083c1920000202004c001054240c001c8c11400510040f081c801e80384590301410806c4010131000d04010100c0e030183d0480300c042e01c0081c0510842d039501503004415010f01c012181d541d810a801c0c201c1e208007010f4407514101800048085810009403c549403640c030840030200600d46940b002e840150004038850792107401230000801041051241c24a4140c0c20031b046165251a034403105481e520a0013100c050540004250394003032380c41240d156103d011071030850b0050504000c541d80920603603151004110006102d08807046040c09030019902c3d2400200200722801d600c4141240481c4048612038068035000a054020328000c956403a078042e0041c2402d40e00300385064824101d0307883c0c280d410314511240840103850b01c2d010014a6070003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 490598875 1250 490597625 490597631
    0x161101020a0818060933090c1e0d0602031003060501060f0e03060106050a05180604090902040e0d090510020106090903050c010518030406030e032a0607050301080709051f09 76
    0x2142002504415240300d1900e440d500c05810406031150100700500c00303503e0a42070985e40c40444c514041c055100b031800c000c1d8401031b0004d2242c1c111000524100b0200260342a22040a01540c451070240707564100d96001a0000b200c0800142a907000715805010031508403996602c0303403120811214240c10007000b0a00200c90304600c540c003c00000c3d024503084000b03119640c101000203140d800752801c02c005004020030079205840044401e070502d21000b42c841b94403107981d54420800303004c00b51001d90050f071a101c18070031034880100b03000b020901c2544034026024a0203041c0b107500e83c03e680c514002c41d5654580801c000c8410300400c0d110b80e00a544558582500d40042e80c01c4078806485103601040600003d59220400f0060382c0450741c2d00d090000304040d81c81c950904522403e212a280d5540c007155070010140d480c083c000d1200c44140032900540e5803a90103a54a20080c01407061740e501021080005a0700340c0c210a80c40851000f0304401003480300d4400d0001c8040780c102e0111151 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 490600125 1250 490598875 490598881
    0x207030501020c0a1505060109050409061b0f030c0206011202120f070608150607020d1511070506010f050306010807180204170c100f2012130f0506070506161101020a08 74
    0x5d81d00e94144550056041c08006a00708840042c0081310036200d00c0b0700550311102d42006100c002e074040c1d202c84015840009041e800e4640c024410f8030101c0074900420315002c0340448040c40000d805068a48000c1c180c050048242c082024400701300911422034030446100c4800c0c40d005000c000700400e00741d00d94103400d090659140c510f1040081c0303070700c0c060117052001e00090382d5110150b14209404c4075a0400400c8411481c0c0c01400000201980001000034004d080000004065040700c0107640307c203080d10b40350700070036445240a10407103a90b948440c0c0140100b8402030444204200044401482c080e91780b12030a03000c40100c130300311200d5000107001d07503010b041030190781c124058186003c806a0f001e0903405404480300e05404070808004030958503c4a00810000000c201000030742c82e12005641c410003014202da0103102d01c0d403100e034a0005101d041440c03d59000b9540140600919910070100b4101018109101d00030801001d440c54101035082c801080000c01c980e031590320f07a03d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 490601375 1250 490600125 490600133
    0x733050406020c090402090406050417120604050a0603150c02030d110a0e060a0c0b0402060c011407030c0932040608010b031e031209010212070c0219030809100207030501020c0a 78
    0x1a06241107011310558420000140c0e100310040c0d40c003d0348140c0000e1103465074103081101c40041594110080400128403500203141000f862040030201c2d07050105035203003001c10741900c0092100130944820040d103000303101c116421495040c156881100d0a1107400d080c043c094a040b0503525540c61400120301240301d130703c20200200c2c080c0c1940c2803464032030003801c02400040360b150042e000305005400714003113507601d50440c0c0300d00d0720f16002031000482d41d9201038141c0d01e054078032101091404070900c11307140c0150306140407900861008180d10024031941541400c443c00d00003c4624500081040d44e9180d105e070304042c003540800052a02414000d040c984004c40f004e1500c5000c40710000e82805000200300c1701d003400070802c018019100c51490b240a03000e20b90b00c4002d11540c520402c00b005600c14000314959000311008c1c602c90302603558034a244030503030002400c201c0d41000158140d003002d030050a54044140b0468251680d641c4805003260490500440c1541001071010240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 490602625 1250 490601375 490601383
    0xa1205030a090b01260606090c070206040b030c0310060f0c0b0402030c0d050709060e0907090c0207030609120306050f031b010203040803070b090606030d05071101140703030c021b03073305040602 86
    0x824401858181000d0000903042234000300705401000700003031030204640320001941c0003400a00401526401c0c44200c82c81c00da0030481c0e20408540c0803280c002004c034443d030300d81000d018240d2503250041a6075140c500c141c460080050f40c051148402c0402c8a86880803c185494040c0380a0040d01c7c0c105415035080d680075030311141c14226044140803d580001c6030380003c440e440000000c046003500300030782c18a108c691014002d0341c5841c4c048018042d22079112031380c0d00201e59080000980f036408100f94503184481d22a00740e03204420022106c1d52245401100c030f801401203908040c1d0b5100700301c0c69640800b001321410030815003444231101c0d04100094005104601824200320314000043c882d0158030009007803040a603840149a03401a4001d010090030804010303603506841c1030190241528184800041c403681c00c0342a918041c903045406540c0c4000c002d482c40b136103410500c545400c07088011400610340c0c40c01900706500408156403296100d6103842e521079180410103414 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 490603875 1250 490602625 490602689
    0x6090c050a03020604050d051203040606051302040b0d0e030405060c0f1b0d150b130c021605061e090a12030f0504030c0e100302060c1501080a1205030a090b01 70
    0x4688240c002d01c0181d44a000f80e5044d5002500e2403074120740b150514034545010061000030381c100000a1009004443d000141a00c90a4511149802781d60075503100300e100d1071080070000402440300c03c007100e0ba00d410105200c241d0780c045034105601c2d000080c505030b204021048683c3d0102400382d1201000340000d0502c4803600000794000c10038040407400b156880c080003440f20300500b039001221002f59129140c00d01000d0030305412691034030000d0005000e10841000544a81440d80e1540000c800720302040e0341002d00807074286005084074004180020601c04640101409610603907100c0503030754401046d800d445e80b054100181009003001c0000c819550070044108001d1011031a507807441422a0043c5405490a5680e80c20501840000343c00007580716000180c20568071100040340440e4840c030484054150341d131040101c2d60f4401d45440240142074013110214041e000300055503218062810103c1c140b49c50b0398955418000036002054810100d04010245080604941c08 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 490605125 1250 490603875 490603879
    0xf03020c220629070c0816060e030c0a12030507082109010207021804030e130506010f02070e01060513090e06250e090c070b010b073302090d0f06090c05 67
    0x32000358400400303420f803040c44600c46954807002809004214521000720010b1a000c015a24601e942a00442d8080404d106080002d400164900e640c2d203408160740018440080c007408081b03203070204003010320590030b0050341072280901c14600030a4a10008141c165109401280b004201c90007207050640c0c06030201c04980e106100040041e10752559800c181c0070504001c0403595641c0c502207501076250648950030440d54180c41140c2e4010760002c600412098a607d5600408220b00321780e034810620074100038103010750040296602030401440300c182c080c044468940e0311819180151003100002d00c00b641d010804201d0480601c00c502c403400318100300d89a0051085010003044104001c00c41c500c90000030340499a9411302908540030340347d001c1d01c024020340c1c0d20000300240b5080311a080c1c1d0004100c02110b140c0d598a80602c3e440004050410f0001315240e0a8080094105480003a0806002d9105401040c02800440c215a101c0d0b1000300d1540002d2421100c003000d1540854 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 490606375 1250 490605125 490605149
    0x1031112044202070606180b0f030c090109181403070b0105040506030604060b120a0507031406190c0507021e12010615080a0209180907080c09040f03020c2206 70
    0x2c1803190341d500782e0280c0c01a4941d0050703201c01c050f041c8a0000c09441d88002401e0004000d50740b03201c01d542c0c200d100102021034188041388400780906840d05040101e0720b50102421005014904040d03000382080c4030b83c0c9a85958484e1a5500d15805210306440b030740107070380003007000c0c000c00c402d4890182c090325080d10284601d0a1140110380d4541019200038405a190b000c0740400c0d0702c8802180e03040c0400d140407210080c00c0c2d070903c640c450185004c01d0b101034070100c2010f244803500140c000d00038001c0d40702c001505c40c01124201d0042046142c000104041003201c0030150b500d1410302055101846c030092048500142048281c0254017400400c40e414010200984d196200e0021404082c40c1031809059541021560081c41801c04495001046c26400640310205194840c459900442220002d503140c600050350341c6060104194000c00000006000a591404842c555031203401181c105e801d00e48001031000700e000c820107211a4a0a00e10082e1400702d0041030004c00309030b401c42c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 490607625 1250 490606375 490606463
    0x30c1e1e010c022b0c0e15012001110d02180319030f050d11030f1015030b06090d050d02060a14070f120f0e0d03050c040e13050d0e1f0801050103111204 67
    0x600702c02c80013404400c0d009c144248d202d00410083d0003110380c1f01500c030380c4540e482502601e000029004003000102007074403500d106002e070138002010400c102400103c402001c40641e82240e502d402c2c16912030402900344180bca00ba1f055000d00e99802c0480040e19480b850300084400015100a015588200e000d81f410404051030300d20021241c200341c1340208005804201250303151080560721600310300d070500064148803001c81c280e41c0561407075090f19030548511200009441d40c041101c2c641c0074440303004c00e4205000700303949019842d190402c0086090004c20401c201ca45c419a15080d2940303569418025503c00d0222427070030b80403414200007038184000040c0840c010380c01071407021008040403480c20f0151408065455600c501298804445440d004003007001007400207016611842041056441e401034803012005160341f221000d82c070300001100607140706540d500c48400d00304581c1c907581d07217940c251520590090740100c0e581008040700c4059100c2240c2184c0c20a0410b001e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 490608875 1250 490607625 490607627
    0x60f07030c08040b0f10051e01020106060c1e02011704050703020f06040305120c031201060e040b040b01050d0f15081f020f0406030b030c1e1e010c022b0c0e1501 71
    0x403298205c82034003c0307051030b903071000031513001c095450300507076800307044c16140303001d0028009811821074000b03038000d114195440c003050325030f4407181d0801010041d420540348851020203080d40301d840d005240140780b1240054001100070030503501541c5c5900301c000c4c10700c00c0d42440d0446a0152505584003032405240d81c44981e100e002080c8205048800010901e003242010030a4417200d080002d0000b00d5035a4813200603002c02a00c014880c01282800c030807681c1840c082c400ca00c4003d0068407040d19081c400350001c801031108030505c1b03c00c0caa50b8448008421b003803030001d2014000d600000c0424060302d111100d545203100500d4035406004000001d000915001034bc1c08031166414041005244400080c0c10f00c2c7c0030b4140c090b040841c0d50100c9052504040703d40b14600415150400094031880300d9002e03000920f0416030228015030403000c01420009604081488413603804481c0f000102c10480b45840035800c141ca1004003445d003800101201c0c080310382c00c8220f14840c46010815680 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 490610125 1250 490608875 490608893
    0x50609120306060a110a120801090f06030807060c0c0503031003140705030705121014180d0f12020705030f0705070602010603050a030305070513060203040f0e0c030a1508060f07030c0804 82
    0x500e0004200c0a03800507094040104003115407103910070205407c520350028000d0064109100700c84115091101d92141410311b8881c202c1a00d404c00300f40c520386941030311108060801c00543d00100401c00c8088000305501b80051402018000c98480c505c1d45103060061004132041c56101c0705030000c0c0002c110308d5400040d108115a41501e15200044080c0b81031802c0c94401c210b001056801c00c070309940c1c040300f003003035440c4a88485410300b440c0080100310716540303589091002d0081080103184c1a2018011785081c0c004401040015107005183e590703160454000152600035020081100e004104080c0b0200010303000d0b80c8000c01240303141d40c440e00d6076900c40c8440502855940c0300825481c51050040340c85840440f81040030741995620300a642e6441441000c2c0404000100410004202a1420700501c2c280c603003a405d580b602030b5907400034140d90941c806011030b85040090312440c1880124400c0c08180690319007494901005402d5611442c423a00411142c00300300400203110301 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 490611375 1250 490610125 490610137
    0x1008010e01211e02270609101d01061106040b01030f0c050415180608030702131407080a050705280e03120c1209370305060912030606 59
    0x421068040e24450902c00151003040501400b0b02a5030000f64140c1440d0f1031a40c1d041510941c1c907091425019820b00344030002c1040c040401c003816602180c00e6161500b40ca1383c0101c1d0840c0403401407a510100440321484118108071108a00401080000c2c0c225100d002d420301c00348041d08440ca000e41d02c0a40d40d4005001c000c01e408038101d0b0070828440e0407407150010f814068020000c0c41068284544001600c4c40344511541200544201c1023045000d00c0003180d60b0354009500300300c2950f08019004080f25040024196500c3c101c0c0300c24140c019295004040c0b94031403402c80e08101c0100420394400400e40701c1407081c200004540c0c907603c4008100140d0210900400341e01c405a8121054242700d652a6031620a00d01d518801d00d02410090241c440c00300e049a032a5040c0c01c04141c0e05000f8000c00c1603211420f503189040b1091b020f8240c0f8824080d006c868036050240d98108040c41403a0380050710301d03a020600b00582100b0401545004168802c0c2450a42c80c0020015000c0e00c915 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 490612625 1250 490611375 490611389
    0x203070b070c08121b0c0d0c02120706080403030c030501050d02120c0a090c021509071a1611011209200112090822030c330e1008010e01 60
    0x10000940e440c1c4620031007014241d0140c0402c0d91103522004c44d02213084117031901e090040c0d06840364000844100d045642e41d900b0b41014258004a400c015035140d00e80382c405a070002c0581031031070380f8110f0a0004038081c02d4181c0ba002c515081c907040080c111030510300404185450200180007070b0b5101c1c3c0e00000315a0341129502500070160041904068407900c41c0e80c2c1014900c0000700750700380c280d00006001003081d401c03900c4505117825001020601514012010f4004031810f100700e001e0740110400f4684004001468144c428010307080c1008814401d5600041c001c4600140d507921200b03185a07281121000e1004034000e885056010b00c0c169250f01210240c0c01d181e5015900540b080701ca000081642000809082d0411a66940c010403481070160a806aa455a844010341c0a000e0f030350440048826103041c02c41242928010390b00d180c08840c44040620050742c481d4841b00c460301c68071350350301034a00720354424003020044007004502841100c50041c0603040c00d5410240c111020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 490613875 1250 490612625 490612643
    0x4050703020c0d051b0a0b060d23030406080f07140903010b06041d07080c0a0e0a080d0207030b010b09061905040b0705010207020f06090303090d020a08010e0705040c020d020307 78
    0x2104419030091242c1006004540151030358603040710341000180c10644000d10b42800070102c3c401c0c00b07645450000304000c2042d80316201045c1e15091144101c44494464503682c040da4040320200700319080018a90a000c1e80001002e000781607003c2d9105801c80b28a940801250419110241840f0707040b42070021130f2a4040f44030b11140d0303025041450b040b036002c0c00560ba901d4a80220000c0d00104203c1307516034140450110340303a03910403803c4e40c0c46420005860f070f05000c80b46408403048070840c1455540b00b1800714012640b084180110a044401a0000d1118514500e001d403108001640100c510400a2001c014241c86030070445e03003101c03074000c0000d141d04403200e019079280c001c80d0080505940c002c600302040080541c02414498000c40700750351a1001070b410040780f84542d07099150540c10501412100d418945041c606e03141c4000c02502c14035440380401c43c03c456044003526595801182e0820040c00d0a116a902c1c0038841d00c0070f0041e110040c900a540d0748504403009000541e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 490615125 1250 490613875 490613881
    0x3140609191104080d0503010303050313060b04050c090a0602010b0f01030e0102044214030702013809010614030a0b1003020301060210050f0601050c0111161208070e0405 75
    0x41500d05071400300a40d50041084450440d08210300d078000e0f001c2c9507218810700d41c58480d0036020b80c6c140d0b41200c3d40b56807120702c0c560320b00340f130781100000d0783c00c0403507055499550165140d0365a00815100c0e01c680f13051141c4582107101000301e0003005d54410310640e4034028000e20b141d00c50391580048010282008140b070000f0070503882c021b00c219480340c1030441d0301410350501c030940701c066441c0140710108a207840100c040300c04600c0e1980c803000d44021a88204411002002140103540e002d142400000390f2a42d0654441d40c15044820b42d00403040c880a0758204003481041c0d0746c1800010a4919034195814103c000d0200d580c80c00b0a113020500c0440011404c02903034100303550040d03010700705040501212002501170740082c050b40d4058040e881184131020041d20426204400c007441082c5035445010042d1440c5c1c2c40301903e40015500c52002062040c00c10b0014500f2450103100b0f10075051050801034000d180750080c180401c05524144484183d004403e48082d0000b10740c001480e072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 490616375 1250 490615125 490615141
    0x203060601050a02031314011404050607060b27010f06140f032203050a030b101715090c040302010e030a0c03030815030607030e010f06211b14010e0103140609 70
    0x802074041b40d08061610700780214049400c07011065418100781c0b0b41403480615400049200c0c007950103a01d400071414001e1501285564100810880c4042c10200c02c0c050b41c4c00e003403052004540c080903d03070b411030001000308031128600000204005c0c9440f8078214412078008203280f03d4a030080020000110108000400c40c074504420503c08070700c02c81004100b40b03406051500f055404a01107490b101102500d0b003401c0b080124500869500c0c0301d0a048070002d00381d4405809072000f40d004841c0030302550962151514140101d0852030600d48a600d10f10004100000101120307000c1d41100c0c8144000600c0806800141d95250800d0303246a07440380844022080003608940c1d0501c280b1060000b03407901540025400000c1c28000e012071801810b4039029202c003480f030711030105440a50300e03d4100d500c0c1d80180501d80b050004000c140441711804886440c1c1e500145000f1026581d050b0721580c0100b07200c6407448080c20705220a81d0134036814004000c0040280d8082d01c00040010441 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 490617625 1250 490616375 490616377
    0xf07030f0f060605030f010c020105060d030804021302040b0d091203110409020a020c21062211041805060a0c0c02090106050a110f071805010803030105120708060c180d0203060601050a0203 83
    0x940750103011100c0b813115994056008c1c1007507802c64005940380c20301046141c100074400b500c4e026015260340b181c603210ba60070700040780c0340c0d03071030074404998248130205d55048403034004d001404000b540801d40b00c0242c00d080b902042800540800d2510340100320484110907819201201c0d10340714016114095910142d00f0052140001c40c1d10810098082c030194812500d0800a001800111641c0760303600c56918202c207500f030303050003070b4040d500303c4c440b0005d10345617413143d400740e400381c00444d18003060542070340350000f03c4808407416000802000b828201d00d12540f1441000707403501400b8090141c011407440e030418003038801044800104180070340d01901c8480c1c50380704800201c40003c03c12501550320346025004043c00c034444009075501c03001c0d50703000e06810795000b5070195207036928100030084007500044240c0700c54000c0d80c10000d01400140617503440390f0004550710343d6174441c10040c01850400d24800a114a030f41c90300b420003503200020b9466001e0720a0812546d01c00001c80c0c10307491 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 490618875 1250 490617625 490617629
    0x130605060f0409140103030e060901020a0506010305060912040f030303020306040b0a170106080309090114010c0803040602040f090c020a031206090f06090c1704080901091d06030f07030f0f0606 85
    0x300100080072000040c14000038021200c11600070800c0c42602c0701d104140e0b503020b2202400240082c0c4001a1516181005000f5891b05004032520b0b4025a5950781c00c0010907401501c60350414400c03c1080c40c814488007012081c08500c1c54076260800d142c010300102c0c540005400c240d804000246240c94651043e100c1c00f038000c10140c01d00b0740c1d89211640380c25980d4800c145a508050001038801c50000507900441c1c0020200e01c8a80c2c240b9903042007003011015014104940007c0c4440840d0362a40110300660141c1000359a9504024000c2c4800780e00358441c034005860941244801e40d03020a00c03540890741858810400070000040f1000b030031098110403030883c074200540d01000441d03400001118002034080c001c0c100c0c1480c2c2074070310400c3d0358506a111851500018001100c10300140100e440504060050303e44500d00c641041c9250305030b1700104070fa10014404980303030802031020031603800c00041140d0b0382155603400e5035410700d0320014110700303020a224042050640003500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 490620125 1250 490618875 490618879
    0x50a06050904051c03090812060303091c0501050610021b0609030f1605061207030e150a05060901090e030f030402040f0c0203040905130f110103200702090115080402130605 76
    0x81d8500703007810483c0c0c0315803501401c10808a002c0034108809406800382280071900600f060341005058020030008110013807105505020800400400340c0d02c001940c0c1c02c00c003001440355110045460b00608560000d051544600ca010b001f1035420340d030001c0c000c02815402100c0c0d546110304040030903294014003030126818056000504003600001a0300c030b103910450480c85146598500078016140304071f1214141544442e0001000d04e8025002422a92001c104540340d103890f0440040c1a80e10a80d1005145926581445044d1074241100c501500305403008100c440101e02c0b441c1c0e924841c1921a45102d070f0044001015580d0302e0b44801202e031800701e0140110090aa4002c0d105e80c00f44c0500c044c00c924040200d8411103080380f103420034542c07000004c0c3d400c20701c0c0c1c1c888128a84080c034490b41010b454212006118010400ca1305017451004201c1e03417581007038810804204c405800c030a004400c480c81030808a0f40c024141e81e001501940c0741c860b00c503840180a800303004c068003c25 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 490621375 1250 490620125 490620139
    0x50411100207050622150207170705040204030b0906090f100b0105040e10050102071502031c15060f0f020109020306040206210f160c050705060c030c0f030a03050108060408030406050a0605 83
    0x5040c1e0000d4041140610707510fa4604005c903525402403199215101c460080182d1002c0001e0000714000d80068104140a0007107c680950301c1c03001030f007a83d210b504215000c021310401d000d1603001c10048240c001c80142d0280c05a425544005a9100048140c8141e00c0343c032030762041543c2c3d0003282210040c0c44503140e10f64207854900528030400c0014410035005115540c000104000803505c40f2040e0030903039014501d806008400101e0b8103a0100c0302500c1d159541117880c10708001f860041c03004100329100c5202c044140f00c1d02800d41c2c0c440c211800700b5641017000c81401a54007207201540540d04940c19911049400750300b40f4103100c0c8040d0b2010100d00355003806441c02c0f1108915114030100030703e50210341d22511040303030103200c81200103107290701c841c409100070304c0c10102800100b921542141e052048042c5540d240c0401401306460f15040005d40786100c6505000d60340c05091240010b04490500c1d9403150000c1c80000c4c0044c03c000e6942c0046201a440d6401610050000601d00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 490622625 1250 490621375 490621387
    0xc110d020d0b06030f150406020d110a02151f050603090a05060f16090b0d0f0f09030306050915060703030b01020a060603081902010b01020c042a050301080c040504111002070506 78
    0xb503044040035a1001c1c03092003500d000003118140001d000749404004c0c41d419502d07407134035911103019400201c0f106030100e49915501c5031111031100a800504450b5008110605080e07128106040001d00302d2513800d80495401c1c4500c1a241500d03c1c1100d005a03900c40e85ca90b22101c442d4144001c0000007461401214148406c089101040d41c1c081c2000b5000781c011002419401d980c041e41500c0b030060440300c280302050311003240d5440102642520400840d131806481d543d0780c100c0d07580100403400300359200020300c40e6040c058521680180408400300c032400c5041c0000d00e060042d803000608043d00d881312504582d1003805029036566022a09110994680c41e1104440c3c1152024203180820500c0905100e031050260070407010068000e4568651b0a40030712001d400c03102110503c00c60303120a0000c00f40c500419180100007503566494680d4100b00c0b0107424940a568880e202d14149000e01020400085203603000c144112818a040f4030403c006030304090069000550041000c03c0f4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 490623875 1250 490622625 490622633
    0xc0304060801090c090e1b0310091529070506040303020408160e010611030c0d02060105010f020c091302031603060f0c0c080909180d05090f030307030c110d020d 71
    0xa0400d80d00a61100360442c0e890380040003c403460414140001038000d602005120042d580306a04088a40c40030280c009443c0d5420517550701c20381c1c0b0507580c45039105003005403c141d032045017003100401480700241c0f13181450014002980c0d031120034699103840080500c0300218130031205502d902c0001e0b00c01c10318017130030058000c0d0810b1090390018000d1407141184000300903c0d80c0b003075900502060b1050390804034126180d41100702c4c00940c501c01001048403900302000110315a503c0d56005182941c1130200041441c2d4030030203010295403000040816544e035050a859200503e014441043c11a40c000030f45003680003600d40341a41c10a94012050103101e80040300e440d6050f920074840c134100c888044420641050300a0196003040c043d00500f0300d000200d250704505000c04075003441c0740d452880c3d42040094126031000c1200000d04208605001c942c0d03c0c03414a08401440c00d1078a191800b82ca0723907002640040201000306012080c96807660071050001c3c1e009412084015003900d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 490625125 1250 490623875 490623877
    0xe010504050124120f060f080d02031e09040b0d2307060504031e0506090c041b0206070c15230903030103122604050327010c02011d04020c03 62
    0x1924000e03401c00001083ca484018810340702e01c1c69849203140b1030403410100702c840d003404003004400300f904c07544403c50800e180e000301c80c09803005500420015142c840c0441c40c103444440d0030400d54000344071074819904403086040080c0e895500580d03940405100180003400c0003034016a0000c8444030342c80a00c41284040701e03a64210885924440890700c5680d0f41d5000603106040001e0300400040c40002c1e2040800c49002d00712455102211085655490404034201c91200303066105681804c8603240074040c0c01c1c07006400a90300360305003840c01300c02034407080018405811b0225200440381001001c4400384c6800039209001c00ca0342a107801c0800400310200203d01040000201086880401000716412282e01800c0c4840b03420fa840b00541300340300820030b0810312802311243c02c40d202c81d0341e808042c030951040014540d1001c0c1e044044130706040704102086826041d09a8030503076600f2001d56024540c0900b0061810782c42c10114204025003003002e250032a001290503014400000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 490626375 1250 490625125 490625129
    0x1b1103120f0a110c0a0305180d14010b09060f01050304050a050115030215030f1315060308121608010b25110907020d0806090702010e0a08181906031e060e01 69
    0x7080074031a00d491444071000c2801036000d150300e030350042c0032001c0006e03024000401400840c19200041140034100160303014139071183c16074400c00029034111150b0001e104486070150200c2c1c00b0308013400e05201080e589404035152034180680000428140901001200710880e844002030040c06641c00b81a03240442d207100c202d008009031002d5800c070240761310585e0720640081140c80305a07a600b0b1252419840ca440055400042d04103203d0b0008039680a140b01541c00398402c04d40d14184412940761225000700107424074200d0341801c82020f54000c141340d044940d18030003941c465601000113040250508049480c406140700c9800400580141c0c8400080040f85d00440c80c0e61002400c2ea00e550182910034001403038040021398503d03152200641140440c800001d0f0703241c40c80606494288030a070309450042010412007040000035400000e80345059032800100c440c5d0501440710f0660b0f50192609060700c4400f42d03449070156500000304484000000e008640c4d80d2500d52600760b100f8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 490627625 1250 490626375 490626391
    0x203100c0e030105010e070f050403121808030306221d1608120a0f0909150302040e01020c1b011115190903020c01030e10021209101b1103120f 63
    0x61240405a240600c1954102c41c003122001b181c5a81301641100d00500038907200c0c0c24803605000200c00306081c03c41c200350011003619409052600f034002e541000805034084442c076072013041000143d40310010305d88102076030203900303002c49054900e61801030001282e907212a94941004250440301c001130003003080846092a103521034440c00099140e03040c801c0c0700d00c0c50700e404101a96000e8170401d500b410450440c030306084040e450b00010415a040e103a08881c40000510b42802545802d208045008107080c0085151580c0f61444607144c0058002c1030200500c1d00501ea40c1c3c990180c00c1c07101c512030fa954180c6803060464510003141c0c80064641201d00d010740514002c000d01a8070850282940580041242680e181e004501900710720303401400038010081403000788500e0740003409080c0550f00d15407407070340f0301242c0c4145000e0f611500e5885150800740040c680700120312190300300c20294a04825004039142c20b02d4514030a80e021141e04e20010b00400c00c15517440c040c214090300c11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 490628875 1250 490627625 490627637
    0x19020a020906031501120312050f1009060602120904020403020d05030a0f020a03200c130207030e03060c07021c05030703050325080c0d090c080706180b07020405070c0203100c 77
    0x6210615948848401486003044e04003001486054000c022140d082032003460991050080d05031b643c4280e60041e47c80125140d80c07401400b170300d0700c24090514040d0043d0310341080fa0030b280201c020341e9a5070201c00c1c142c1d9010005140413072519550115006145c020b0000c0040c40035624007181d4030f9200c021124002390340035241341c95440c0f02003a0301400a030150303a54000450800002e200207000408a50301c18802c0703200340c81e16511901042201d640e02c4020050320b60a0718100031340306c001d488906c1d61194100d581017066612001055514154050300c04a1098070900000c0700450012a001361207880089446000c050f030000085210f80c4182101142c2c2208000600c10b403c620645810b0106070280d000802c3c5108100280200c03090b49007020ad8400700c0c0317448184101c000c40d000150301e5000100107021103a0400c1125841c0d1301c540c20280c000c80e00d001c49000e0070b40540301009100e15201c9003c64a0300c2d02c04c03016050b00f541c0007001da420309c80e8101500307001442c2d910200d0020901c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 490630125 1250 490628875 490628881
    0x30e01090b09130519051602011a0a0b07050a0624050402120f100b0708031608090d03110d0f05090606101b0f2f0a08031e19020a0209 59
    0x4028002d542c00401c02803c0d014480e880c000030032015082c002e0600500b08034503000040408654004c1d1401060104801c0000700000d2000909403100c1a4502c104146103e0a010716a01d0302c03404070045031089506241c80d10490303c0e02c0f5040459020015244504003c5c0d2001c01d10588495001301e82800441116020351ba03d042c072040e40214140c8160600005000910000c03100345072a6101c0c84022100300b0084d103030131000c02147c00414cc00c0d0384520001c4200403107180c3c1b40c0c2c40c1514000b110300708010589404c80066a0760309810868400301038075000c0c110182450352080e10700c9004110410b210301110846808000c010441c0e19040a20034140401c00318182245c0c02e5400f03034580c1e030f607000041c0c61029112000e080e00d401e0482c0d003040600404d41c00b1400303c2c0145481d400d42480b0140748540c0c210296500c0c20380c083d501510440e0b02070313030030401907400004a9407030350307903000d01c0352021040001d00c07581138001d64003120485030f200300c82c2d28072884c1c0c041080d840072032080f112416561 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 490631375 1250 490630125 490630139
    0x10f060b0306091503030c01050402040515130906110a02010e15010b04030b090a02150c0606010801230f031c0201050c030c1608090319050c1e100201021303030e0109 73
    0x454034861011140020004070b005400c211a245a012030b00000200c2c00c04000300100e4038690029107a41d11a075542d400303120862500c0d016060304102c1c5400e0f44644e070308044c40040c0b0280260003090a1056071030412908000307586d040b00100d81c200d0010107459482400b4041c0c0270307003521a1015107e0103024401c4041c4224109030714141d94a9904207070410342141c0d00d131a104c41014000c4a01f0303200740880400182d0745d400c0e51454090003500780d16200c135149140700785014000340030349040c08010001031000d41103516203c0c801e480b0f80303951459101103140110705c03880d8040c0c0d0940d0b05030203943d120b0745042402c00b40f1042001d45660007005690ba81074561010f0380029201041c200c00304100200324109410040803410380030f249003c1c9020300080c0020710b0030800c120390080c20301d82503403d00705205061050240400042e95680642040802c503281205000c81c402840b419014548080951003581034920707950340b04d0304460146490342000f61501c000e40b10218001660080d01280d80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 490632625 1250 490631375 490631381
    0x1612050702131401140406080604210201060522090b0405161a341208130c0608180304030809030d0c030c02040b0f0d11040e03040303140c01060f0f08010f 68
    0x611501c03080381190b9081c04444a0b4080d00b845d04554060349031600414040c0c0c0a000c0746015034800d64100f0040160400e001003029440c91003031040d6498048200407984601c600c01c248854000c2e072072000240e04c40d510318003c154215026055685c10700810040040005880c0c401d003521201080c11180c1d1030030741d40d181c04601182c0b900601c90030301c064030b01034000c0423241c24081000d03286901e42000301003040d4141100e981060781c0c0040e0150301c81710050341241e03e040d04003540d001910b00484d00b0340c458140b405058803810301000603440014941c0740e0285982007040f08094140c03542c5a650b030800c0085500480e0a130740c417a0040d100c030001c0460186c4e00d0480f200341d054555640404494007040001c2c00d030085e1240e005841c4201c4610150344488115a1451180a14503811f803145414003040358010340c404c061a5004100c14800710307402030100b078421000b070609141e4036104500c8260241c0708a07405080a14a2610040303a1200001480e005603100f5500030040401560724110a07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 490633875 1250 490632625 490632641
    0x50d021c020c060c01180809090a0501210203030408030a020610050616030806040209040f1e0618050606070203030c0601140d0b06060a0207051302091c0b0c161205070213 75
    0x350b802001e0034440c505056000d450742c02c0d070303107000010034aa00c0a034aa0101d030300d042c4121021a00040d9003641072801a100302e4004a5002c1c0810156040081044203505041c50442591202c07c0e140c100315581081190050400501900d884482100b4042d560b61015900c03d0011200e464010407a414080300340c4034500c0644c0d0305020340040b2038030165018000139005130341140d000c1243d4901a210340c0140c1c41c0344d9455486c0020101000030480b12040420004e075174600703040480030400000c481e09200440b00c2100c1002801c0e4a6140001ea000d1140070340003501804085240c0440744e001280c4141241c219207041501c0400b10b4041007103407962a900205a004039201280150514002408406400340112159507803034000040c0040091070580b03903040e80002c1c2c44841420910a00054822600c02880c0b5400e00ca58500124001c024000b000320701c4007003184008034002c0440c048a064016900c5901c44d6030700c2200510523400348006a005080590080100c8003080c854401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 490635125 1250 490633875 490633877
    0x40c030e0c1516030e0a030807050c010c120509030a06060803070b011202011e1106010e090c06070203063d0e06030c180604060e01121406091207060612050d021c 71
    0x3c41c0c0719001c0c0700700c08802d502e0b4400750208810600b80c1241c41e00e4010900002d58081c0d91060740354112480e100713150201030b500f0710341041032540b42d610000783c03981150741140006017400d1f503c0d4400900464a490640c4002070b00c901c0c2040320009102501000500c0729500403800e03040b40e6030700d441032035100710f518044c02070000d6130781980d00d20166484000b484040c0224505440301904000c802c9180080a80206021a41890070b004106004020003280325109491490421216400194031540014106401d00c0310f0303400400c8401046817110040d400001824011b07420310041c9a400c07440c090702448488510000c040381481c50006588583c0e504020210501d240d00c0080300340d03c0b4000a0400d036080f0ba01c66102281000e508200c49000e0300841e4101c4460002c50f00740405000790f01708181d07000341c00c08400d11802c2c0c0030208140c48840c2c0f000c90075654445151500100800455029803039415205101604000011a40444020b1194210781081408a1800445030354507090f0314 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 490636375 1250 490635125 490635127
    0x6032904050606070212161203080a0b0d0503040e0108070f030f11030f030a030b031e100504020d0b04030f0315050d032601030311010c05130b18040c030e0c15 70
    0x8806840e168214980c041c20107805142840303203560200d010303511842115101ba0f000032421a6410944001d84401000d00a000c6100305050380c6015000b0b54002d0403a0300d50b55214600420145c0310740310b1f4280b1f002d80c00011070750b13229603500060089120038041c90f01075005031000090044141206401aa84c0007c0740c1a900f580c665540625105009411500342c0200808141029170034006085002e94a44000c112400e6900816082c544010010121300782c244010341d5110200007918400c4225621002556803900d000241c2a081501d0009182d6480341d41000105a84081e140c1c240d1851a202484a4074083e008500c0900450107419006090081d9000c0840d00c10a800c1d03031203464460303610f0264222500140c0c640a0300340c1054010a514807542e26900009202d865403c1c0d5082c40c2a0b42007210190500d1b885088512072400748000104070741d44c1401c43d904030708140c0c0b00c00800c02c02c9441c00609002d405450303148440e081c1030041784040d01d0182400410b000306440003518035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 490637625 1250 490636375 490636451
    0x708161a1309020a14040f060206010803031003030807090302060a0f0206090f03180a0f09020c06090c0108040f05030d0501182403080f1b010b090a18120203130f0603 73
    0x100300250070201040d020000c409981780e60500051000704040c0c0f2003890001209410500040c0c03901e001070b0703c0a03c01c0d500070004c100b0309c00410560b600950350b151600310b0300340d2241c0f0411940d0742d42070381020b984080300252038600240c02080c6041750800136002c0c0c812943c0e40041e126120000941d190549030001c026034011891280c40c01c4005ea00d0041c441d03802281c0701c640c6280f0301213440d0002407001d40d00181f085218402041626403045090b00100b040b800c032000020114800500b000b400001203554000400006009a80300c40180d90380030001503030744907244082428240440443d041c50142d03942d0f6118055082a00c0c007001c0c1d52602d0484524541d208061170740f18600302645403138140103801c00b070300c4541001d0700c210100c0800892890b8090041201e1000040c6c801e060f00c914101440b280302c4800c3d01240103a90300005400000f00503440107a044d4850380590000342d16400c40c0115641d51082045001e54440ea40c0c20404210000381021003004800001c0381e0080e0302c07500b2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 490638875 1250 490637625 490637639
    0x607140306061303051b15042c0f01031403071a1305030304060603031704050c0d020f0301060b19030209030601032013020316050313080c0708161a13 66
    0x29600071101509140c5070100b0741a441c40ba4086070780048845030070004006001119242411803002802c681036413603200505400341c0140702c1c0d0303c43c0501075920411000781d034824004034040c2c107101c4021540c44902d4005281c58184200340000c17107102450310b0304185024000070030b440420703504c0081c4004044814880090a0800500c00180c5600c100340701c100041c400e0000c0d5000324402d501c00f107480d07400c503d006001a04070396203008802c0c0c9140f00b04000b140d000564034440b03150a5400c0541039542d400816203885060300450741560070920300080e2466500014041a07001300480b0500c0c0da8859412410b91044001042c0d15a00900041c40401c142c104104024066509000184001c140111320050700c160304009589501200b044441c5403043e000480d03840c158502203242d841c22250741c1554598242000e00359080104109254240810601e0040d0440c031080f0f81d000c0c1130341290488040c90750300510145800140d0300d90402a5003005030ba001c40a1030b400c1c81d49160a02030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 490640125 1250 490638875 490638877
    0x10816050f03030412260708220b13060206090a0b22050d031e050702070b0717030406151a030a09060b04050108010c1b08090f0a09050703150503060714 67
    0x190700c5034035000c00c200001d030440075288500903007881180b4481c1e6021988003040d0211143ca4000c01c0d200d44100100c9000529440c00c581c005100c9030b0a8296480d00d070070342d0680d41500b54001c40c003246400100706214114a40050f01151599400c64140e65600044180c8841d18207800a00d642d41d100d0204032148408020008462100702c030584122809455052800b404241d066001c07a5980811104041d071482002c24401c0d110101131000c0e0a24600c000c1d5282e02621900e16401c1c0085048010012070300f48a02e03c0004070314400c2d840341843d080c0800108124607080e284038407160400100d0b000c070241400c0c1074929a4802d103045603600c3c4030710009000b03c076500b1201c0541e5000c0c40301c0c1a90740e62103000d000e071030444c0002440c040b810001600c1c6040805010b55150105100c072400180c8540c00c50f80503220682e0740c0d440030324040c400b041c10303c2826000041118280030400403002e605070301074445500d41036080011280e460041c144c8441d0151648000189070740b201d2540d02a500e8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 490641375 1250 490640125 490640149
    0x9091a06010c080403030e0a06080f010b0a0c0209101d04030c020d060219080601030c1803060209010516031101051501020c0405150d081206030102130e060103060f170601081605 78
    0x2041602d140c100310380e40e812042d0f2140c0c000f2070104a001d0b4100c440e07070900702d203950040d10aa0600b1252410400e0f200c5001d000c0c14883d060f1070321000900c41e0f50a40c45007030101080d9601511a90783c03410b01c0c801c2484a02050b0155030201440700c1d503950301c2000602e05a600880e01501c90791850246034003071041034064a442910071070b8003009180b10a070328466003504108115544c48a00341020780005069502d81000d0f207040081101000c1d82880600c4008412682d00c050b0060b9075500303143c01a42c29020300c90461301401c1401e8026418141c21118080310691010300030046a555041e02d5800a0b2080ca28a40146c0c003511040717801e814503502131074201c04000b4010914801030380005007050004034003100e9101d004105c50880c00910380c2c6054008000318003d40c00c0000c804603140c0044401d1140f100440c0300d03080400d009034026407001010b8110110450f2030181c50f0002d07041840101e007a040c1180c803650000245002010510507100507251601c1030303c95280030100405040300e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 490642625 1250 490641375 490641377
    0x20906040b0a1b2103020408071404090c0b0c01060b0a0525050d0e010207050a0b0a180e04111306051f0311030f0403090e06030307141e070f09091a0601 67
    0x110040c02818400b10543e0203500c1d110310100c07a4032440003114003081940e138400550a042c0180414401e1900109109080c4d80c2c0760180e859490702c0700300004000d802900700103004205068004100140c40c10002d000e0602070030001c0c000d03a542e940d9501554881c1c2d0003040d00281d0305000106c02c0302a40f69034600810600900d446000c2c030603031175103801c0002c004503000114610842e58002940c041c489403005000855418000c146040140343c018410b19003080704006c491580d22720700c15500c14120014010410070495189410310b0b000851001d11144107204071100c10040c8102c0f90740380100c0050340d801401540020300c0b0800380360030905100103c64140f42c0c50742d55208190455002035841545e41e403d008099081c1410060245541c9070417041c9a0202c0302d04204031524000122010107500909200e4254140700603c0d040102502c1c828070405c84082e00d082d080000012010b050301e12030b44601041c01d9642d9910011039541e44001001c0203e00c0c415070a0708166100415804041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 490643875 1250 490642625 490642637
    0x3050a090204060f052d0f0118080606091602070603020f070f06060311120a0312110310030309140d0209040f0812041203020708031303020f011d010c03020906040b0a 73
    0x303900090aa074840e0b040483c15507103a1004100c5c5103842920f00e070b0f184454888072850541502ca034070a00303400ca9000c050146050744c50403d02c0703911031807441c034043c0000c99410300034503112440a41c0350300c6d068450b80e00c2040058082990a40e03034404481d01a4002d07002006030700d10349a41940607400031082041011301c18416100411850450112014420040003a00342d045150403011913605200c3c242c0a00c621400e4240e80c1d00c3d00088010b01283c0604144000741d2450740d0100281486505018440034003000f0b0003d60081e1070340100c01d692003911441d499075120b0f6003516003c0a4850b2041e80b0210400049026040040c10fa9400c0b0b4017404140c030b004c080944030310070781307a000102809180d42002d0410050042c0c000d05041c45543c2da1034113620f0b0004031b4840118501014002e80800c40282c0c0d0b0176010517000300a240c020101072002800400ca400c000354a1010200440d40d03451350821101e088045d12070710071910039a00041c503044c01c1a0918441c0807007600a80c410741306101c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 490645125 1250 490643875 490643891
    0xa0e0a0603110111251d0a11043f03050705100b1c060209060c0703060507081005060903010e06130215040515030702070909080a0f1e0f0201090812060108012403050a 73
    0x10070406d00c4100f00019036410340303060010f000c07811600d908591189a05050100344002c40721007400703108600b04214131003100c03245400c513001e001c02a4141840024000c0b00c0344420190400041c1c03040600420940d50300c485042088015109826042c40d8003001c41c00e41201b91300e15400030303a0400c6026220060138201c05101245659001d8020b00005a12070402042000a00d00070558404482d141601040c100703840003600021141c000d16100b4400410f1a08281d00c4c250300560385541210100c80e13030344c2020040201e8140c2c0d2910168010520b82e200300d808903140900f02d500b00d40c0050a02140003d00342034504144d00090000c60450003035010004200070079000b0302c2c6482d8001c00c0c03500c0d80c071440d003180980101c00301c00e140402e002052041d40030b55080e8641c09886d8030410300f88141130782483d0000303c0c0100b050b07000042c0011000318803600ba1000c0d40a80620522003a20b421941d40d880e1003e00d441100000700c15041c40c060620007000c3c00348650000e03500800c0440c000b0407614 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 490646375 1250 490645125 490645139
    0x70c021807080c0a03021b0303091c05030402120c03010c031b030203240d141606030b0120030f03010b070b07020f06040f020a180f0b010504080601050f0a0e0a060311011125 76
    0xc141c07c00110001d603c04400d01041d01e5041c40150680884a40f00d00d090f20604003014000e0302004101a1181080011304411004103002091a216000340204119004200e010b8014034001d80c41001d810f0b001020308c08600e00074401c07a03000c0e28800d20b906031006440c120b0121000c0107030080f5038110445010030070008124060040034510548042c12083d00040c0125810210681c8010201400c0c0407001940da40c0107071545d0040401030300c0510300a0358030741d08203143d0f2040580604034004000300002d28003240d48042c000d014480ca41e8460562074040040b40c0d034406442c4110541d8103c440440e00041c480c42619030002d00c0a40305100700f6035251021503500250a0f44c0c8200d8503110800c0414189280c0301c0c804590703000b4204282498106802282c0e100d2050040c10b0080d460080c40451959a4241400060048592841107850082c4000015200e81c1c40200c03404030b403021019401c1c0d8013580c0da1415518401c0c4c010540c0785242207016542004440d1000c110300498500880c101e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 490647482 1107 490646375 490646407
    0x9020a270b060a0f02070b0408070e01050108190c020a02040c030207060525180906170601050a03080304150e16031a10051512070c021807080c0a0302 66
    0x4102c042c4d281a4038003a0300360890040e004c804500041c076004001101d8060707804c0e00800c041d40d40d80e100e0065408910648000d1180b800a890800301d0385044d500c080010ba0b85841142c000b140650049022503402c1000c20001030740000d581e009026540c001d564000351205200680c8028000341011242040a8070030100807840d40100c03650560a0f52030b2014105520041120f2550780c118030820348804204200e4500402c3c00009103440e1900b0032008980c0c0016600e031850f075a640d1107050301294110781ca680e0940d11103c82c408a507041204150019220744901691415801c225241040c03210f4024104160201046a0102c1510301d076001c90720256800d00b1202010172014a460042081d882000442c0c1c9040041c900c0c0c0c403040c4c0103001c1c1d009640307586000711044c0d50700c80312540071990007000c50300c5000800c1c10050180b0040408103142d180041c1051030021a510071 = true := by decide +kernel

theorem cover : BRFrame.Cov 490467625 490647482 := by
  have h0 := BRFrame.cov_init 490467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 490467625 ≤ n) (h2 : n < 490647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
