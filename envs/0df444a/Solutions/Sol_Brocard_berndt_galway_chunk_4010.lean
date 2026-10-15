-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4010
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:19:16.715981+00:00
-- url     : https://prove2.me/submissions/88dd2d82-8d8f-4a21-ab32-f29228f5c40e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 721043165 ≤ n < 721223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 721044415 1250 721043165 721043171
    0x92e0c11060c03120601090e0412080906060a030215070611043308180706050c06010512060f0403090b0a0c05150906011205070e0c091f08010509041b0b090310 70
    0x141c840000401110301c0041c0c0e405603104c40b034a4040040324a0f10b66540450310141e100d40038041049050007000d1706e1206103030380324542915a01c001070b4448409940c220303032100d0104410001402d05c056080700c8541c4800b8864184440354580c10103481000c0c0c040c0c0c03051940000c0c00d200140c9500b0b20200110b2007800d1100214440002c29104100007440001c02e03c441e050001e01c000c40080100f8074a9204d500c01c2d60401940c036580505644c124070b088103070130300640d400403500b800c1c020643c0b0308802002d001044c81c0d45884d03002c44000d96004c2c000741e0802c010b1090110345112031000800307007800b03141e441000499644c1400d9040c5078050b076882c04030302c00076004e00c848000300080490641c0ca01140020884074545485498840715500c0088001c21010800c81440380720f2002c2c20494200340c840030711a801040069040340c02800621020501c0080103111605200707a102d540b09210782000403c0c0034203030100016004c1107600201c59030b94000b41344441d6003014040e020580765106800c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 721045665 1250 721044415 721044427
    0xf01021b16050607110d240e1903053f0105090405100c0512010f050108090303010602150a14040c06180e010504020d0b1002030d14060105092e0c1106 66
    0x1101c9101e0244e018042000c0346407040034940c0c3e040341680007264420028200940800700c4124001541d240d00e0810b83c0c90106403030740315480030410200c1d00c424802c01c103c05191b0b030b660070340711600000d80c800c00102400c9000362075008e000945060343d806c004496200078008541815000750140c1002c0d000380700880c01c0c003002640008103545c400c0c000850204502140c0306017140e15016078407000065030503e00c000987c0114014a04040ea50282d803400e400d50758000000390303a0700c400e2040000680c84400c076903010181344880e40d900111030400200700000c1011220303107040303005c0d03500303580e9140000810006141c000c880700c800c10b030030446010310300f80c504a0389050500052042c0ca021707070b4000501c290724580903400540c01800040841d2046c010700350000b907a0781c0020000e00b007a2413410f404240c1c5440c504080701c5c8100d9050f901c562600c040030f824440d43c9030300304c2c0074181c01c040b001207124010b40115010408000c019513440307076048403d05054240c4a003006003140034510410074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 721046915 1250 721045665 721045669
    0x8150f13020619021f020705010f02030403050d2007060203060a0501030c2c06041d130f0f02030f030c030a0e0d0302060106110307082106090f180f01021b1605 70
    0x291640050485030300c0f0b03010542c91800b80d0410744100242450072658983d0010401c40d00c2d800f030304d01c0c1c60059008214010241510b5401c900c0300340c502402040d020b10034102c00c00c800da001200d0286014450b404140022040e220f255001108100c89541c1c01004010250528a640d40e00402003403030103010810000001070a00d000c000001a88002000e9500e80f20244082488280701000340600b0364641c0d48240120800990005a1540030746001c08203d040d0071760150480030903084200d036865501140c1d920480280f8548040342c02d801007190903000014103101070042c81070703654042c554983c0c3c034050042c03819015502c1280310b50100d03c501070110b9400148135040d03610500380744104010045050b460360103213000060600e00000380c200800e04a100100c586800f98005082068a50404110450a080f04c003c0e80d00214000000e180c0081d10340510b2044140c10b040d64480002920202d09a0f4008954000c900c0a90104110304040c104500c0245814100304992082c0c10580 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 721048165 1250 721046915 721046917
    0x29090619140a150e03070902032401020c0d0b071709030a0c08070803041b090e061b0d05090a0308092803030f0c030f0f090302032208150f130206 64
    0x280410000030481101d401d41c480d400c1d00c0003d4514000800c80021607208002c00c00040360040314040e00608500107122843e40c002d03640100d014801ca1451191000490420304400d01c1105046115101307540409031600303545108054007a4104006134609624050210b0404c3d8450030860801e000401080c6040401510407200b841d04e012a404a02d60411980c075000d0388001030290540001032008106044e807004a0400042c0f58901c0f10a0b607484542d01150389044c1e594546030003044c006141d80c122038403116005c1c0150070301c550030466a000e2500803500304070f402c04d200703900c100d01001c14103400034603603948901c0b600000c3c080e20707907a00c0910b00c809a90711700141480d1501e20318002014041d800c0525103e405180411400da00c1b01c17070043c0074085a5802a5080b07140c150380c02c0001c841070181045094240d0011480c02182030050000d01007454046640b20255070004620f5520601c0f03070750116105175000c02c28601b44508503445800000d0002c03045505000244801a02c03104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 721049415 1250 721048165 721048169
    0xc02030708071e1506091a06071104020c0106031a06040c17070309150c0e010f0c020d050a0f1506090513080c0c130917130509090129090619 62
    0x1a15450f0920418640724110501c0c1d03440206420318041c04040c2880c099400f0904881303142e41d051088003c6181c510041d0102419410742207176040042d600400c500041d40400300e5005000145000d42d2070180b54212200f0b50000c440304104003001c1490030b07001c10351183e0040011038040048103000c8001600b82046039104410003501e06000680c058000c1e4010030030190404c1c80310f0180b104040c03400c030040000030071017800300d0040c0e6024a0a54072845020850000382e40340c04030302c001d13a902004000002d901e0100d032a4403032010603800042c0c800c0007140300315100b088401003075440d60320300300240c5044c1d40103011a0340c501070401441c86900000e0a2106030091040d41d9190310410301c01d8182126186204c0d0484500386608044118a0744a41d1100d405038140c102c404094820101451103130301804c00380d10042540620583c40c0142d01e0b07641040309403000181d405c01c450814514180f078500c0603403402c0030310258000181049414598405000c403043c5d060fa89002401c084101071034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 721050665 1250 721049415 721049423
    0x20a0b03010e0f15090a06060816020c011d0607030f0909020708030f0411030d0e040e0312160203041505030f06031f1d03040e0a061211040207111807030c0203070807 73
    0xd03c02003107800007802001d40c40c020024003810080d1a1034600d04014003410303c51100007480d01e10000d1103004500c4124000c800c001d9010300324040d10305004460340b00042100c00c804040c032020541ca41d5580c8001411202d21035240d107914200324604c0501603071a0f41c2e01550f1058010010500042d24003411a58800313041d044000843d166410002062007031815001d416200b9032004040f190341058190701c013207204407070500c0061103207041540c81c1d028104801540d00d20410103e0942c084c03101c03181d1168105441200e0801d0750b240a0b00362000c084282e80f0011410000c14030103912100420280c0c0076109030001c001003510360201001d16102d800c16800b1040c0d86010f80101d030300420b421030340240503e00480e529a500c030300c00c15000c4a01030301c2840c4c59501e00000020b5010f4103e1003002c5c070076000540944c110000300e06010195200000c111344851124001c00381a07900c081a0341c00004030794149000324600f000b8050115510800c52400b5940184103140000d20f40404a4151aa08c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 721051915 1250 721050665 721050691
    0x518073507030305160b100806090a02091302030a050d030c0905101215090f140a1104030b0a020f0403030f03060902130b0903100504080c0c010e060d18051009020a0b03010e 76
    0xa184010f8200e5003c41700608816000d0184000c1340b02c0c1550401c02c0e80c2d03901c400d443c455214900000e81e141c207544c0009400411600018603903048401c1800d5849002405035000010a56113070744c06c2241040415001c40d5440364114140d03540300b41100041c110968900e0661342da140405407808180c02c0428403510f40b504801e9882e072250038a480d00503d41d5010038041d51140701c40d4080034002c07060700d840078145c01e2000540b0ba504076011701d08140b400e03c5001403a080c00c58886203541f0b480180001c4200380c080085952240d0008020700007140281e07a8070041031401038008044d00c8607a03105004460042c0000c1800003690140802103582e16084640e036100a0b83c04030741000c20420b012901d280c608802c00c03051200c50801450905208403c2e64010304d800c00064620001940c14260010411302a00710034264030f600c50b0007500300c05180c3ca0b609640c1036484d10b14150200b070607118400d8464400d030085080c19422740c40501905100541190b042c0019640700b4076000f0912000825 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 721053165 1250 721051915 721051927
    0x50a05160506390106060221040308040312020f06041a31050106050a03080403210c0b040201110a050d020c0609030c04021303080f0a1b11040518073507030305 70
    0x11100d610b1918400d4100a00c4000c2d038441001c0e40b11a55a003c4409400c0307248484608d00000e01c04980c2601d500000c2e44d42000c1c10340c0c0b101340c02c95600c0f14010b8290b01c01d80c20f5450a0800400100b841a80b01f251051000d20b504840b0b419242406811112502c0d00700705410011a4140c5894401d030301860790000300c60383c440c20030f18050070045c1e01454105560340d10200031b11096000410035030707002e481d048041ca4419101c0d00c80040000042800190b500c0c4180300c00191400704058000340149032400010054500080c00c10100080480d180d502a4407491452601408403060042d0115070817420001e0344400729885140a102581c401c660002c0c180f00f84003058494400076541185806481d5948480700d0215a4440e600302408100e0064034407441c400c1c0d10989071403095001c098084405610380038000600380207080600c0c40201e0071119074034004100010001010b0b40361001c51030300b1200382d265511b20200c0d0092a41c1c0301030040d01c50140340c00011005c00300d0764107140841e83d541e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 721054415 1250 721053165 721053247
    0x6090c070b01140a1a04061407020402030a0b040f2a11030403080a0215060f220f05160c03020d05030a1b020d03050708090a020108040609050a05160506 67
    0x4400d000d00108215140c20010076402d0700200a4103000c0415140882034903150800f0750400645100444140c810410083c1702181c8900c11994070340b91803a034090300380350f84c6a00113010398104540382c00102e5580d50fa000d10a14140c0101155000a00e4003000910307503080801c801c0b01a071405406194001d21400c042d00c0c1c0c45011241c650510000030f50740c44646914050469a0000c03002000502c5034042e804140040c1c06030f00c9016043c010300e0f1504944041e014050240c2003448480e500b00044c04007608403c80a0003410002d601c046030010301481d040901100408aa071003400c00c00c0b03080004440020780009000300c0100039801d1242c1c40b90307075200d1100040d1520f0f0100d410011b0312482101c00240e00052140d00c2036050b900d007400f41c0c1d46c4200c01203030714400c11680038940703600c801d101c4400755002d035613a560007a0080e4004542c0c842291606450400c2c02d1004a840d54804000c00f10072482e0610480c1c013420007201c080d450070548c400c100451400d14480b4400151058142803c09 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 721055665 1250 721054415 721054417
    0x304090203150901030f170901080612121812120708180a030606030b36070905092b02150c52110604090212071b0b06090c 54
    0x210300c0043c0302420075038481c5084580302c0c00040381200d00050510f840188812a181691084c0d44182d660110a030f4482d130801900c5003581c03482010501500f00c2500f15051000000c01302c2d50a90700c0d00c0c09080c20103000740541800c41044040454002d00e4142c1800d003d040d04848840ea044034001e0303203c840e0710b58a400f0b403200400c0d01d19441040c1364000000c000c416000300c400c40340030343c44000056030b0b00401104203401054444015000c02c110f008481c1741014002811648030f142201d60a5440b050304508885040e5072598642d40074014100e9502c80150350130301c0148040040000c940c0344540040e41d500c84801c0241e00108007900058030480d9a107090b03038400c0d100103894159410110000d81c241051a00e2841c0c004a8041069000d40141924482100c8200140c0040c0c0d03501c0c45d220343c11040110260141d110804200024099079a400a0701d003440940b2900c1700d80307082c4040007601c6d074200401c1c1500202c003c070004001003a40740d40b0056001005a45485103079031226000c3c821 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 721056915 1250 721055665 721055701
    0x4020105030402030f1c1106070806060a120f09051c17040201030b04020d0c0305101a030c0c1204050102010605121e16092c0d0302070602040e07050d0605090601020304090203 77
    0x5281b0400014800080c0c182101c00710310f42a94444607902e440300134500340c03218400c9400201040c150004503000d400c01000a040d0b4000e6890240b00d00355a404c0740c1c4055615181003020a2500c9030710030320621105002d421080081c401340590580d03203486014240080c0c85821095200c040d800080030b40e4041c0c0c00ca110036100003842150ba490281c1c41c0b983c01400c0b40820079001a280030000340c0b003083c08044101c1070755081043c908001140c0c805104450348024005288041d003449450b443ca02d0411030400705c861440e41303654460307003003200090071908a580303c180304001102d0710240409020070109043d06402864580302e032844501a468824046041c880034421140009442040c40d4404100e003400c42e0f52550103a2800c2ca0b41701e6107030140c00c280c9242030700082e50b00050180264000c00707149206078405410036541d841d440318056811622080411360010707a05807802c50505c6200042d000c1190541c20ba814240e00007980d074010303406007140040d400004921001d11181000742 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 721058165 1250 721056915 721056943
    0x30311030f040905042d0219050604080f01050a0b0604030303090f08030903040f08060f06011b060516030e010603050c220903051e040302031f140f0910140402010503040203 76
    0x20b9a1076035080d943c0b000744001c56003500c0300142c802194800700500c400c101e400d034102520303208681c5019003c008604220300d201210005c00110009540d1715998082e00040068401801048042c2c1c84103900b0344200400d020311861402e0031220f450340d1082c081d103040d00d030076240010308080c2d14500ba00041d50780c20f4000d08000d0b004020007400302e00010040c002d1b42c20800c00e0500031692100c04642c3d030541518642000114000007408030b51180080b0905d058040c951402968803586a16085550a4500a0054600504121016801d40983d8030f5031030340308008001442c50b42d219992507041700755541d0721031005500d09002d00c290f0541060f00d0800b2058041111510b1850b001c0d2190303200c40402c141011842c550461030403441019581103c1d005005400d2500510720b0011140c18600780040b9502c2e40e03881070b540408548a12584144010101c1c1c0e403450030494011441c0c1469180b04550042c00c1c8140e0f680081c91181c00650040c0d42800c0003a203940700d600c0003074105034928803814 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 721059415 1250 721058165 721058167
    0x10e0604061e09020a09050606120f180d0c1203090c09060602071d0703090204020c0f0c1315050904140a0501020424080718050d080702030d18030311030f 68
    0x8244030742039101414401c620011403006036805400d960030781d010140c0283d8044a01c010030003841505800c056440040140134601e0b01040e03c80c0c00c4800c41d82a99a00b00c0703200000100000140034002d07440909000c0ca0050061041c403000003491008440e41c010724104900c0d0b0454100c50003600102d008603172100345902065207030100040189000d01c42c110040c842d82d0070010b07402c4442c0d100060200c0050001c7e1501d0703a98034800380d010b0f10396013200705d0300300d5400c01801202000c00d011404160610340003511132078441008208035107040441d1981d0395484c0441582c02102e01d40c2c1c164080704c40c2a1040841d966503403d214441c036071000030b0300048c0d000788401a402c2100650081090303032001072a0303200441d4a020102000074110103148086000000807e01c151b00445a8424084c6031080815000303483d480801c9030000d610700110313402c4402048181c114a001c0c01600341060075854200c0c0301d041c0d904054500041d040c8006403c0c810307844004800c1e03001c10300898000c0480781c1c002d9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 721060665 1250 721059415 721059421
    0x50309031b1e03070c060543050606090c09060403230609030d0c090f030f0c090c2f0c0910030b0c0a0324090209031617070801090305030c0c010e06 65
    0x11075182c0d80000c0046585c50588800071904601a10030b0300d100c240311101424800344510f4419000084a001e0140070b842d07a440c45101c4800551080c03500c0c10f00c28006019a0b003884014000c00fa000135006110000c424400303042c25850b0700040c0c034203ca40201200740801c134a019056010400c000f03268040303006100c20070503580e4000004000445100034104204141440e045413100c0d1240962003850000c1c560400c0803404601c560ba42d520302800c540c0340025502d0340c48070100c1d0710403a991004501e00c05882d410710003022155094020742010000341203000a0140d03501d0b8601d00e07100c68031400420300883d90940c402c84410001d5940644c00510b5814086400ca03800e82012034007800003400e00c418507200c914188802a030b107101ca00e684c20700302d41c1071080d00d41c0030f5001502595007500c280381d407800203007003039940400c014102d83d402d0003800c02c0c001707180c14140f04654006d170302e46a041c00c9101c0002a403001c21a80c0c006140b24010f91201031398032055015008081c1d00945500c00e8000b8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 721061915 1250 721060665 721060723
    0x5100b250f08130b04030f11120d1d011103030402040e03120901151d0606030606120c120903030709180e010509060708070306050f0d2901030c06050309031b 69
    0x901061200402e01c2c000340d0381d00c00321182c0d141700b10300000701280b010f02c48000025440e900b0104100d60001c02480100400006080c903041c2010744410000d2007400e810a00c850100303c461841031002c1c030342480d1801e80059429907170b2002a1009000369507a0700c002d1000041402960124220188901d181d414224021070280c80c4403510507070b5043c0c030381000140e1035080350000000300781c01090000c0795640d124204455900000c2c0744907040f2004016450700d203249000001c1c460042d408402e6190100300c0011a5034400060130000503502c204244075496400000f00021940c5010481c1c2e414000510f064010f000489020481c0392700b000c00707111f10000c010601c0c0748594ad003681c9404959807017100442c02d54180c0d20445170030072030100210f0309500b81210140056400f950080c100e5010760040c00c4040740d0148843c0b04080940801403007088500c1c0c41d800010308080c03070040d00b10700b4080e145607224466504080c9100e280140e0350099001c090101c242a0504110901c03003050302850 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 721063165 1250 721061915 721061917
    0xf2205130b0301110304030c0f0302120d05101413050c04091a0f09070e0913140d020c03010203010308030a1515030b040b090709030209071b030c0605100b250f08 71
    0x181c40340300b942030030000960045a102942d1040f501a561880458103a03151076010900d042c1c01a411401002c00c4540040460401041d500c1c000c00000201c0d4540200c0e0f028030900103801c500d410344110b60340ba440359681c00161030b031206101c0d1400115034a83e48041140d920507903000d140207905004241031880b00249103c200c4150503680110303d00d100c0e2013040942401150684003068821140c8541d60400c0ac00c202e40c450f00410086802400907100c25524541d0301103403030041c2d070002e03283ea43c03180d50500415005240c150300035800c6505644c3c0e064160702000b03050500302c903900c444e24078400034041c00c0c0000400e8103c0016515146140004000d480304070000e030300032400d0400141e06070400d11052885201d055540310100c5045600700320311101d000d0701290402190700c0c80c5c12403211544e1804030350075100703445030300c407003111032401e0320580d0300013800c40d0b2a400000104000000e219011160200d0201014109801a103035011141c5548268040d01c48910400340104000041c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 721064415 1250 721063165 721063181
    0x16030618050420150714030c0703020a0b04030b0c18040e0631020411130609060801080303060907110703060f141b180f0d05100608030f220513 63
    0x3d99110580401d000d0080c84555070300c00c1c03d80c00c405450395000001c08044080e000c0340b4880c107030305030302c00200400140c5542c0201c4050a1070740c200307020070411860142d82600c01064505405030070b00d482c0d92909071400c0e0000703156000705840081d12516400c1d940119994201004000700400d9040300003c6039102e2084075015294075001c0b91601d00710554488105202c1442819080944215401d11000d01440b1b00003c0c3c002c03100b800205040405881c0d81c4d070113000c0702c1e554056003e251000c0144030a00690094146410810074802141c480a50080e0300040034105101c00701001d1308060728155a42d8009400c061510b8442040840681c005804116600c80c04131020340b914801e28401d041303040315052908408100104e107100d922000428000d20040035140e00d100e502000c41c20240b810386040b643c54100d000c07600b611520601c00c0c000504a800d004500300b140821010301544151264401c210b04e0302d90645c84c040280c500c062000d801c2c040c0c80381e9520400b80480320081d006007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 721065665 1250 721064415 721064423
    0xc0f120e03101a041404080f070b04030f0e04090b0402010f050f0f071202011803030f06050618030d11030d091104060b040812090f061602060a18050303040806160306180504 76
    0x3d003103001d02c0b458207015594103a00b034003481a41c1a04d0340d039200032143d8082402c4c21b580c80c106014550108214104582c4194080d40300c4141c00b02414074024048040421180e22031840e00c0306100102d4400007503254403035420300b032185403e112070030281d80038040d00403444011003001400000000400740900348040c8a04c0c400300840441d00001d030b0903611b1407403400305400d07101d40300c100100e032080e0041e030880f40d00346600060198031000070410715440500d510040850f0080c03800d01c80d060401c08110003100518001207144044182e146e00e91080c851104a002d48516815092002c200600c600781d05000f0410040b1603074800308840290030501c07889034070340684006282d60400b400212084504002d0012111044400c00c10040f030700035200c4501c0152150b0a4000161203030001091429960303151031044010681d4504c030b2100e0650031541c002d401c2440208245100001c046400000201400341c03001001c1c44100c00620580d4032130440c0b1912035489081c0f003025944070070f00507805 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 721066915 1250 721065665 721065701
    0x8040f030b010b040e1b0403050a06050609160806060904062d090b0f0d08090301090303021306051903090215031009060909020f0402130f08010e010c0c0f120e0310 72
    0x1c2d030080401c1900130751040031403003220300f000680d20a12a0b800030880d00c0b206000b4a0606490340c5505262021040044550030b9a500070300406140c038030034599012500d1080140c0101e081300c4014821071002e081c0502490020441caa40c903585d0f9044030025010f0f6075111010304a4040c60140e00c080c04202c2014200708501000c108502d01e8080c0001000c005400d10145c9058002802303680412003206842c3c40e0420f20a2600b0356800f801154103103030007940c0260300d03500645e08402c01004590f0100c400c2c0241081700c1d0100d03c0b100c840103d00a235841c20300150220740d5002040e8100002c03400c08000207400010460b5075880c0060010a9591040081001c41d41320070b884801c64100d104042d610000c2a0400f140074a0190001c201c005e076030000c0d40803510f0b42e600004000b012181c101e8240c03651103039a1885400000d202710512000c052070b099200c00e1094a410070304500091015201c14039a03a046600e160207205180d04800c2302800316960030303403450400d000610039a410a900591 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 721068165 1250 721066915 721066919
    0x30703030b030f0a080d0905010e1b06070201080105060309070e160306060c0302031b1002070f021327050106240815031b120109080d050703090804180908040f030b01 73
    0x24001043c0f034000140700300800d88184540c94a00c400d8004043d4030844548846843c80011000e0003602108503060004016001e600008081400030495145014150911548000d0303030b403100c0d1550443d0800d9038000d41d00e4590821050400031076403c100700006050f4248907069641c0707816900e441006daa002c0040e183c86400441d000c641002028005a000b40002c2e041b100101036400f40206010302169084510b00d02200d041e0782103804144c482d1070740741030038805500340980f940107030141808040060f0b02e00c0c4411907151032621034080000140c0008180100701095002c4409001000344407441400c0640800044a9828444000081c0e0701804a06003154040210107000401006014050b017458502240e0300c1c40218582c1d48000c042c41c03260041003003807054000c99405000082d5a4030640e40c521030554002800d91000c1600e86601d400c003103500c0d44195410b46455019031945030b41003080b00c2c03010f00f08010000e08560000600010481d21804104040380e204108400d466a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 721069415 1250 721068165 721068169
    0x32405010b030f06030a020301050721050c0403031812210e060f0a03090b040302010509060f061005030405031e030a0b090903030601031e0c2309010e0108070903050f030703030b 78
    0x940a01c00c40c0081c2006201081010700708a80f1242d2010020381143c01d200d440d070b0006030039100d05440c00c0e4007143c8a011003035101314100003040842c1584070001e0000c0c2c00c00907800006172190b03100290400c0801c40740c0c82060010010910001d0000210703030710f56641c181c00d01c4c500090071000079440781120a0041030340d081c054400c41d800114010162400c024100001150fa0760151120300c04040d40c801a107130003d000480740c1406030b1302035800000d07985081c1d01c80340d144c840e02810003500d46229a013000074541e42c070b070902d8094640ca032070141c3d22901c841c6003851950140869594440b400030f40443e0b4002800da02461164030003034400d001414014080c03080345130098580c1c0d02a0713041000061f505500035001200820030002a6940c02d015494190045a0210110500258406005c003500281184030f00d05002240f0421501d0003400100113010304603008625810302034450000780d1071501841c03848004603004000ea500407001c5100c0c0301d07203076130200360101c000c60316100c5182468 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 721070665 1250 721069415 721069421
    0x9081c121109040c0e090c130b0d090302060105030f03030718050d11031c080a05094206060a030f020f070f050714130902040902120a0201080603010c171308040324 72
    0x201750151820700941ca4412920201d580310110207000101c8150000404600c0040181548010b044002a1900312803400a00b0a40107910040c071a81c0258940040b1190200031039401c10350b0b03420000c6441128240054803c640c070b50250380d1046c480e040607024000d1960051101c0340b021000d0784c2d6240603e1440f01200c291603c1484c1c0010342e02c0000414110455100d1504000b924089449031a14903444070340c0c8442200c03113805400000b20102c034680892040c40312940c3c00d03848881c00185411008a1a107009000310360b0300700340e150003142c2800070b2990704481400ca046000c8640c0c4183c00cac20018540001c5850480340d5101c5c0d07a40004602c40c5481640740d12420040c1424442040581504090b000004c010380c0c0c400e5a41034000d00580e80c15803120b07401c8042101810040e09140005006071000503c210b0290741400d40300c4503403a40c13020304860601039076510310301c464a41c20821030400312803140041c0b5881c40042c1c08000d0064488550307540110800000c400b02035003034101d4050b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 721071915 1250 721070665 721070687
    0x212030112150917190503060d0f0201110d030c0e03010203101502030d14010e060103090b061507020618211f0e0618010b0109081c121109040c 63
    0x51440740c40100e01c001603500e041c540080940321804200d650a5454074082281034090380400c40d400041c650034440e0b41c0803010b0890038510b0810303a00390300e0a48003180c0c40d044100001402c0112443c2d00008581c0a0203920030504010360884880a84850001d401081202140c50208031045030224881c6414000c4034400d8070071481202185103000341055210586030300900139804207000f1002100b04038031805114506031060000c103945807001d402440c2c4009406070741058284000c200200701d03030121203900b01c0f0050381e01d507020b40e444a200900c5800f44840007540705500084000400303001011f200d02c403401c11502c90441c03a07a4208a0080c258010360000c00d59041540358855a052150511101d070070300540c049046980c0110701401d00b03c0459031010b450161142181201500740706007641000282000e02c0300d0350505080940d120252500300c405040305078000c00541d80718013001411200f095106200d046012400c81105402c0881018007075807500380a035010511034004001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 721073165 1250 721071915 721071929
    0x70b0a15050d020d230316120c0309050910030203010e0d020607050c0d03050a0902040f05010f0b1201150c0803070c1b060e0d0204022209050a0501060915021e0d02120301 75
    0x1413400b00d541d0301c03684c88070741c4038200c90b034200d01e22150150100244010030164607215190390100d0341d5442c21325a0380b00580301007002c00420f41403000000340c01c04840b03002da030f400700c034290660b40d240703c584000003080b130300f00079015400e100600c0c1c0e600c04009410b50b490215074090740c07016070ba0600c04440718007461054000301e03448440039906640c001d6018982106510001242204054000c02d013034800800304c1416a503038a10040060700d000c5044000600101e0301644d00d04039600c40d40f040c0d000d4060040425010007200000b10150050441d00c070101e80c031004540d03e038685183c02401d886010303c0700380d13070b480c4000e03181e03041500c064135511056902f541c030b032107107150991418401144044042280c010fa0700b0000200300320b40300f1403030461410440d5802e020290600d0000b1090700c0b00900903680c0142420300601006030009017000503100e06c021554164100100100d260130b4020580542c500640710481d03018010100b510042804d041e002c9403540070b141083d41c9010310003407160304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 721074415 1250 721073165 721073179
    0xb0c030d0b030114040510050c040f06030f0b09010b130509070c1b0b0d1d030c06040f03050d0203010902090906030f0c06070614010b0901020d020a110f06070b0a15050d02 75
    0x1102810260703004204081014000040c8440c80000004002030192420351309a444005100d1144000c0d01540c1d034010240141c0b941424502004040b0008240c0601018903850301c1c5c02411036007666210007080030000306001039550b035075841d08649901018092103548142c11000c562414407a0030700d03000315040e81e6108804802e944546082e10100d11650303c481e918a000007d803045010040c107000d06c403000340001c201d4111020350040340c6507604050040d8105001c0805003000c0400d17202e41c000e4100d000000620120716003154107104e64050841000d10103c0003040382c2e50b143c0c0c046c115071a4151204540394030707600c08040d82c0d500c50031200005c0c2d03071124001d4240d50810030003508407a4031503400891742404a501000005000343c0040441c00004600c00000b5a410810b075010b09a10780080e01000c90142c40c5c0000b1038140e0584903004440c0b01c42c0c900c80071b0320b440c07040380e240640091600e0328074100441940017900400d6500c40b540c1880901c0031070140340c41e10119808560081000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 721075665 1250 721074415 721074427
    0x30b070e090103201504050307080c060726180108010501051e0d020d02070b1f0311010f050f070c0509090d0203031303090e0405061906052d04020a1106010b0c03 71
    0x14074000e4015155004d0103049040e515854840c0001072402607078100341c468440e81000145440c10425a001803229403001c3c0308200d19072603c104850035103802801204010002c11090002c0003051580c085401000046011611400c40741d0a00704050076668100166652300045070395004a2030204075404442d00c07440340004104c8010076000003060405410406029a02c1003280c1040e4400e0311061900c2d4204403c00d13b04608040f0448608038034401c1890454850140404505024605001c0d5003242e81c0709141c012000d40c6d0002030300003a076540e0350740640743c072548000451048600030349104012410280340401c0380c03502e103030190f8029821071341d130400c0344800380b08182c00c107506010b00410041052010b800a451250b07014400401d228142680c00c0070005580d80c0b072420340e0074603202d000e12590740e458850039003c500420036961104a0618440d0fa8160124041540284006083c0303403915000400a00c1e1400d5000696210380c4e0795005036040e030b110390390036484541c00800c42 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 721076915 1250 721075665 721075673
    0x30315080c0d02010311040e040606050607080430120e120d0e0a0302031504120c030f050304150203070e040f02090901170f070314160e0a110903010510030b070e090103 74
    0x42e581581d005140c08a509440e1810b00d240310b501c80e401c00c1e81090402010001031040364010940140400d0b41c400745404070307a88600e8144d0281d40030321042c100c032204480c0f180c1113540a09441c0000c68884c03e114808281c07030315080041003030f941c81d404103c91240c94029032411030510981c0803910f001820704c0a40d6144103d90303149100e1140f55000501c1e040220158608004038201041d0084c0300d0807903820b007070810105000d44250300703004000c4007012507000281c0c05032080c01801c0c001d0a001c1e803240c840f40b806108c514450401c03a030246201000304010a640300c40094541502a60100440240103504134241d100750f41c40c2076000348000c00100f14852030214081c100c80f0b44601600d0210a118146500349071480d441a078403820185510114160140b00105240368200c403040c00d0945050182d0f01c030040010311000203603a844074107651321100e0000303c0300c3d0500014005c0109152613032042800721168082955042042000107045c4ea00030014802e221100506004450303103580e80d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 721078165 1250 721076915 721076929
    0x10806012001020c0d0810140d031103070515010f05040614060304020111060901060302041b0f0810030f2102281109040f120f0e0907020f0f0703030315080c 69
    0x2840640540d420054005240c0045c049520544aa5510f0b040c0d03604040914920042e40c80c0c02011220004070090b00144c2d031010000b0f0500c80d41420324482c1c0c00310442c0c800c0e045000b1000082c0c054000c01d4074500f0706801c0b800c0114103039094000e01c2106141c403601070108507861409048004800000da50f80c444c6450b102443c1d010388145010401040c800383c195080c010280c44002c0d1aa4480f4024021841c0034045e40c04c1d5000c8041281c00d848c07500c008020029188500f1072818000c1d92070200da050300000c02404080c40e0403c041d851241d1a03482c1ca200e11755940040344a84c41c2204d031444071000e1000c101984165054040b411014500c20411541c51040d4102201e8a140040c4030070b010362a11002c00b4405c6001e1000040c07401c41c10304000107581c4100001000f00082c504a1610194000c007050403600c1081d80c08000d15600e6900c20303454546c180c40c203c816440744240d49842c0c880c000411a05480c8280d0382440500c18080c40f01a10146500540783c0c580c00181e5400600d0500d24 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 721079415 1250 721078165 721078217
    0xf031e05091908030a09080106090c0c150e070605041e0f03030e031e0a021306081f02160803040c0503010b01300218010219020108060d060605030118060b01080601 72
    0x4102a4400b540d07030482c903499036000c5600640418280602003103814000c1c4100720080460b40400d011444403154010000401000020000340c400240d03e900e5803071941c00086400074040443d0402616a103000d45290030a1240a40b2031200b2455a8841102c0102c031104852030100006070f0a41582e50648001d0311141050781c062041c2c50300c550755640003583c1305006003040c401a0000c5000f0b80144500710013410b0f8842e4805081420412403054005044035541032040c05c885502c01c1d184c03002c0c001900c1654240f05124001ca403c55040c00042c00c000d40c090f91142e44440c0c0f00b9981c070000c3c9826600c020030391901091100c80340031245160711500c8180c2840c0c6800901801c60141c110000300e030040040340c408891700000b600b8080d601040200310094580010240d4001c1c6580001c2c04d0004c0204058000c02c2605580410400290450320142500a000b840724108000548054500080069800c2410040c03001255401440701c6401014182d58000311400c40c0308402d802c4000c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 721080665 1250 721079415 721079449
    0x10b0a1505030405030c0a0b06190f0b1e1219150312021006081606050c030304060b03031606050f0c07020d0b0615040e040b010f08031e04120f031e0509 67
    0xc00c05d00320784480611201340c01c542309010070f00041c102001440321a6104002055410801141c140815085a0902000c03203448014160303a40e10f801518203d500c1300f44410483c03880e0086181030600e2000402144200004182c043ea161070103c0c1e4001070ba101e421106c555424010404c1c004148500c1c0060035036030990048440300c503042d280407800c403081940960f4a070740040036110b100c2000f000502e0001c1201d481c11070700340003400d114140c9a2002400051013544d4030001e51903c4d440500a5404e0843d01c0e80c1c0c041c2c40764899080c1040a0b10781123908524205154000541d02c6500c4070039a03028640183c00402d02407001d071388100c61007502502e035903030108114505a10620340c00c0014400340c0b0300c4030b1078031819081c00d14080b1100c00c0182c0003211000383e102414000c0000000075aa02451012505502c6104945040000d80720383d801c943c0c1408964888030080c00f00118003c1c642a110359200c842140034040d0341c0342031303003e45000c80307002940c200103030040da1400c0d8091207134000903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 721081915 1250 721080665 721080667
    0x4060510031505010303080a06080705060d060806181905060f04152a080c0a05071a04061506030501050d060b03120705210313140705130608010b0a150503040503 71
    0x60b500d07040a20b4031040a5100d885071104014010181d00110040d0000c140c00018400c1310b0410441c00d84032409801510702952000c91005c2240b055a00302c44010460742c400e5a41c1800c020600504100e0001c003001c0c0141f0036822140c04001149052035030007500708021382030940307512003a55001e560103001552516090075405240a17110700c10f09003503400c4001c2000d90891a903120700f051a94100030841880012410040500c800c00300716000281c1d00e04e46184e80d01440d15003002c1800c08607403980300c0b00414a04020411074154410700d4022401400c004600740d40340790031400d40320309005642e0000c50140405002400580021040c3d2000500b69203002e1450005c04445800c580c00a540340d6102503000c50300420900103410b1040c1144012610394540840c10030150600390070001c0c445511841408400714040c01408007031701c0024402401506c2943d1407402511040c001d41009510b00886140141b508000c18401c441c60b40e0305200e40d50380882c60640c0e580c1c00040050b20035000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 721083165 1250 721081915 721081919
    0x41e05100608011e05040b121006061803050a02010c030201150e091b1003020702030c1e0907020601051005030402031603140708070f05190e0a0204031a04022b0501020f0a0e060f0304060510 83
    0x8d4107000711140100b8081001500d1807a10301d000700190001303240408a412118014004684045102c1038410740a007018465002a803808900415000d08480000b01c800764011070b400782c42d8480607000d804e40c2c02c1151b11401d0500300304070309240b41d00401517100007407046800c0300c24043c0e006043c43c0340c001015101710b03243d01000702d1649040d00c8a0302d0306550203e902d0201500d84000d081303401900520050455604084c0071610001034a0300010901a000c40000d0441d5010885070035088555030710703a51100c0d924a0201011034049590004a0044190114020758001a0075044421001a2101c1c0c0ea28141c20300410783e0310152010300d400e40c060400b1641e02200f038170140c000d545028006030381d1072540c1040540441c0c03a00b041d880e40a41c3d0018007015a0701c1c100c801000b508004e10030035540c6c0c0c03490440c100202d040c4000625075400402d010f042009403001a251454a603180d0809410880c0200003280c4103c2400c0704c00d9540610204020800035400f00b80d2084003418030000c000c1d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 721084415 1250 721083165 721083199
    0x907061b06051303030c05030c0f0f04120302060907170c060307031803050c0705040b091b09040906140108060103030f1107050a080d2c041e05100608011e05040b 71
    0x140b0b0032146402189007807890703041056070500c00c0800d8661986050303811400c04641d03500c0c503489908408952024040382402900340b0417011135000341955a05407050002624000c2e456200440d0b01000500034000000f4440c8020514a0310340d152042c098039560605600b0081c060700301400c9601016a81c03410482c801d116007000c0c014280c0070303071101526201202022454021305801090045003001282003907500c0c0c6a00c219001440400c00e541c8400121a42c1c24950003400d0403c3e0307009040ca50f0400c00e0004542c0860351100c0e1209000803582e898022240e62024207110003400285510b00c0e01900303e1040450342d80c01007504081da141d02c0d0750b03140043c40c0d18400760040a401d4002d50a481c6d460f94003c11009405d21051041401313110301000c0000000044074075490065484407119400c80c841045940d45001e0484801c0029043c8000c101d2200c1c0428002d681c04101c8803000440c140c070040c0d456244102d07005404020a604120502001d007a00009103900951240307040da541c6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 721085665 1250 721084415 721084421
    0xc090315040b22060b0103090204230108010e0309100c0203060703050f0619090b0d06090f120c020a05010c051f020d1d0304060f0504170c011101050907061b06 70
    0x30440c940d0340d840a90a050920a49859000c0d0095007000c02462000000301c95904202c090340b0307007000c00040d401240200507006411494070096000d0b1a00701c44e000e00301c608850300c0c181d83ca80703088144004c1c0e80303030440e882c200e55070515142e042c0d5000340241a41c52411303c0068003d050586400120384040340d0220b40340c4442900c02c580420b4550301041441c04060121a40c041e000710384d01c459119000c1885900080180641450340d510741c3e40904036901d9442284094907030009081103501d000307082100030b0708482001282e44591810600b002d480c1702c0c08840301c40c290000c10503c4481d2030300c0015a141d03c00403004841e070303028543c0700301840d00d10b042c0e8542201c100c2101c05a41c459205220108a403440585413425a9105050b030307950110000a0302e0941700365042c2210b10001044050f2103078041d0f43d0203810400443c48011113517144c0841c15040781c0501707032160b103403165110381158280e030b004807058400c83c0d05c400b130100105407088011288007180c040d400428084152214019 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 721086915 1250 721085665 721085683
    0x709050a020a030507021606031d07080c10170a0b0a0302060705010b031207080319020c0a1a0112020f0904021504060c12020a030909150e0403020c131109090c0903 72
    0xc4280e01045280180780c05000c4c5641c0540c052000d040c3d040e0069201c51040d040c2070090307004060761080030302d2301d200c6507280007480076194804450a20740c0c0c4007143d6688002144040b0301134440c00c4000079007517000745c501510030304003200341c28880c1d641c0b854090010141480c9242c0d0041e0386403400009030311980014800319000b54000305000c40f0103020f140c900780c1255920a4425410001100842c0c800c1054907003005984040c2d440840000d8014000381c01034100c444002d01500c0174a03800c200705c61401c940d9964610f10040c0301070ba030f00c0104a03038003190b410010390031038504040742c03a45203070542185a00030720040852403908152210844d154110b508100c0100d650304940a040c003d880300d40c41c4204805200030718a136251560018007042d01c0d84688840561500601c0b0b186400300320081c00584a2504200b480b40b915003002952004400c0b80c150090380d000d91906804203a500480d4014840207501c03914046a10040c05802803004000c1e03841c0040a00032951155004d00c10504 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 721088165 1250 721086915 721086931
    0x40807021c111509060d18230d020106030f03120f021303020306090c010c030f020c0d03170a0621060f09080418020a1704021215010602010c05031b030603070905 71
    0x40300103540310900a40d08a683c5000403141003d018104c030655038030040307805000f40c0d1b100c0400c400c280401c500754511211900186808050b009050002c421007803901400341c0038a003201c0d01004072880a070700f21440c600010302007118070401c58010902981c2001d81d404500140018412009005001260003030080d80b10a114012010000d40c6410040785801491800191004d200d20b600080c100d500184801010f100100c617028031400c0c02804000c0e45404058402d46242c1800d240050400d808215000740302030301c890200c1d481d001a445117206461094000200851181210003581c0d8024101100c41ca6255100e54110320301501335002c64601c100203181e01d0328101026405c00b140b10680ca4a0000d00c1448244540c40c1e0255426501040344006203031980c40314000720b815000c07140707082da085114030503200d03031001c114040c62070407154298000c00c00c0a03200c0604581500c82603504000c014603500c50452091950b100954011100800300c6425699500860040e0b0304125003c0f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 721089415 1250 721088165 721088183
    0x40305090406140a0f0e01050d0c0801020f0304060606080601120e0a050a1101030c0804120f1202130608090d020304090b03211c020313120e21010c050301060206040807021c 76
    0x25103d070070001c1e0b184003d05481d01410541d2801c1902c002c02c4040140701d000d204500c94004c90b4248101144039030040c00500d40259914120110060200e030b000303940448000e4030705540004c040744134020325400f41205943d100003491100380c0d100054000a9800030003402091003020020341e003044040c000b40d20401080700c0030f428000000d000c071440ea030421004c0c80800c00c03c000c006007802003da01500500d00344605043d040410031101c0400c40c016548103103200041001d81822101512411111306546c0c0e0700c600da0302d0307148040e252101d4000716405a0b00621040c01202842e402a0101107006403c688060756000142c000480240310120505007000540c280b4501e910074031411182c181150951450070207440081e100401035001a1000e0440383d4200f103014070440d1010741520b4010040c060441e108104d02110689001e60b602c0650710305030703151041d00d0180c4156412a04140c028280c0780d9034580740d00350298007200c02241e000f0702102e000d5082182d10700d114142d40d401107200c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 721090665 1250 721089415 721089449
    0xd021909050a050c16080d0902040501240e030c01210203100f0f06090e1305030d02180d0b07080c0f0d0203090d0e1e0d02040c050702030d1b0803040305090406 70
    0x107000b200d801400204c0d40810400401c0c50f011500d00b65050a56484000540d43d440e10b00070341401080a07580080d071250410000085805203003c1042d014949007030380c8140c11180c40c00542d4081690f140094240c0c00490101015601a00b6131018100c0e08040440030b10380118540c40481c2d100701d404061034901c4c00d0080c00380801284900004e404210003251241d0309109021349601c4aa00c505c078441091a40080d070506104d00003014255800422640c40e07401c00301c00e5074065000f41210040b01000070394088814a0826403100d9056009503420348035442c0c41e001101d5450340200382c035003e0002001240b81c011500710080c01000b030001c900503160b05100100b107042514141d02c120801c0402e0110407002d68031040e0200d900c4007800d0440702c010031160302158004003c0c56010b5845480c103525501100d401600074030b4910306c21415640c06458180080d18148a40705944000100e05100200003814035001142c205000742029810001c41e54001810f072074080c0c200c0712140855101c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 721091915 1250 721090665 721090681
    0x1b0515010e010e0a02030a1e0c142106010c050a030c0b090609100b030c0a08210a020a08030c22050108010b09060306131806092603060d02190905 64
    0x289000d4070710108110615498124000d6820101818010f142079001000c07030044003c076400050000030a240e050141181400701400404441882801184040805c0d083c290000c1089840001900310b0320340304401081c205010440000b00706605001d50223070480003003001000a100a01e20035a1000d4510700749141c00140e9501c050720303124155102000f4880c10354004102d20a8980040d140043e442c22001d0000b4a810444d26141c0d8002007141000300d5104004205550071900c0511311918414806074041540d1064958600060300311800700c00004013842c006640040c40342c1c6106051841c64000c00c0d280001c0202c52440b0b00044031805c2102d960007298050052102c074041c1810b055042000c502c442c48010300300d5104041041707591070900f006a00082c0c074418401002c01054615240400042c000707141c0135a174102c82e4180ca203800982c0301038144400c402000a41d81140c070795006001c07134440c507040202e0b4415084401c026004203c072040000500c001007000c01e07582402e03c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 721093165 1250 721091915 721091953
    0x91809100b04020c150c0904020703020c040c051207050a0311041d07020309030a0312090c0e0703060b04140f030705031906050f102601020a0c030e0306061509011b05 73
    0x2280c280260b0044c06090150344020900e10749160701004820340c04d035904080c0f00800d100b05801c4603401480840ca500905074001660841501c1c196002c02100c44944070588107805001e0000040d03400810005419034421009052611214100410340390000c41a00c092038105030040e41400c000e108003035221401c07218456030042c416002442c0741c0350641000c00c2d00c4e0116601e0140920408909100242800e6448800303020382040030008020740710040710305100015240d000010382042000b041038042d080031141220508480032007500030320014091382504030400d10394140580c0d000082c454400303104520010030031f185e0800003901d20340340440840b000546800b07400d5aa84080003143c42c0e8901d01001500e22108011000b450030070920501054a80090b404650001c00c1c00703400729030495400f0074010703c01e886101e81c3d00e0300f1a050640d00e0030100c40d15640f0106261071404076a6007880280744124041c5840411070003c09500002d20840d510200d40c184d021500c08800c0041c550 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 721094415 1250 721093165 721093181
    0x1c170904060e1518220209090a02130218040f09020409110a0b162a03030f080916031113022809080a030503220c081002040f0b09180910 60
    0x26100341d101a0416407003009400d0040844012445500d5010500061701c03032001c8895900506411040c078124141c5038a801c8100c3e0100e010304282884a0281c50444c000e5500c00ca015a82d0359108030b0355441008003034400103814086a0366500c643d4405030302c0d43e0080c41081401800f014005030303031040900140594a0744119000a0184081e000081111400d075030760fa42c0010219000c00388075148002807450000ba118a007a042038800401c060300802030713034040c2441e0740f40c502c69607440d8140540c0b2441d040c0c0591804801c003520a20004070500c0c40e03425106009891003c13031003442c8640800302c1e80034000b1040c502161000501e16500d2502d13904203c0c400710710b400055280b80c80c021554030000c00400500344200840002c099500040b4410f152014880704440300458500384450303000c01c14040c91400c0e00540340e40181e00c1c0c640d07000311821100010800e000726450150a0450707900048031003175004a4004480d0010120700710980d0042c1c0c8100c1c054060082d0b000c10040c1114122 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 721095665 1250 721094415 721094419
    0x50606040b030a290604090b0109050604090c030f0b012f0709050405071e0e06041b030c0f0906020c0405041a010305070f06170c03040201030b130e0c1c170904060e15 73
    0x140d00300c484d2901c4513801e5900712107a0040100d100800304005840e080321941006800c401c02050009000d0010340250002c600e00762010000d00700c0c56800c00c015902820043d03404580c640506503841e941280c080c492400040307892081c0c000d14894260f0034150664403c030b00c0161200240720503c2022b1100100522150492400040c51103c4640c1130320f2861041420071007000340050890385a903000000b0f40342e2081e0303c9429503540400302400404640c0d0380c4100081e40e00384040d2180707016049650a03100583c00401c4900c44640401024020060007201c032000e0308098107194642088181e8041c510030700c05801d017141054072a14030440144e000344100403400c1d04480c0100200c04105810504880405680c2e5842d0700043e80a8081c03030354041d8100c2481d140d10303103910206521900f0085580401d0701d40c015040c00070400441e00c408400046280030300d084030300084055094448031650001050300b4420000009000ca0b0051b61051800c26400000c1041000380c0307002d2113440a1003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 721096915 1250 721095665 721095731
    0x604092012181903030203040b09060108060c09040b030f0307032309100c051f060605030f0a0e073b091c03150b0d050702060f0a050606040b030a 64
    0x1001c04041e2000507008a920a1601d00d080305400410b00801001402d10a041d6030f1051140c40c0082c02984221000e440e0f501c051070215400c064003084540c121345c01b140080c01d86485410b911002c9178804e02aa541c01540c0359400f085a450a011101d201c50020001e99201d034510b04000e41a90b035100415094046000d001140c00d055043c10b842d031080d415501e502e0341c40407148041c0c03504040300002500600ca00d800c50044050034840400510b4103d0300e0502c01c0d99a100c005958600060b100d00345140902e030002089030142ea8003108818003030600301c2c0d07402c07503507105500c102c00c65980f800310280301c512b4000b0525100001c2c0c403c0e0b4601104280c070200785800a042922542c082001100e250388039142849011f2290b013001d04903c0d44111207103400d0b40d40b0449503020342d002d9204150700d90300f0400082c0da45070001c107182e0712070800c03a5505590780e40d0b9401c010300100001400207034000c0090001050726000d1710050340c0b0408140400088181685195145009401c0c009940c1206 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 721098165 1250 721096915 721096927
    0x250804110f3706170a0e010e0601140301020f2215050705010b01320d060801140115080a0e01021c090c0f0b0a08090106031a010e0a020310051e06040920 67
    0x5031040410f00d98141138602e500c4583c441101d00c9015115046100051750b00701304903503010707500124125040320701e80c02c2c0031441c5240560078503090740541c51508010715020b20068201c12290549c40e58400e11007815103084036191030304842c180092251003400200049a4001005001d2040c8101c401382401c100c0b49110404905002c1240310048036000b200c0c0c20780340080c202c189032060710900351800400b440304940340c0040754028078826482481ca101a4000001e601c4100c1d10011454892a6107520991740c48030002d1001d050301c0070342c03088659420400c0b101c14004080b000c5500c81144100440c819100d4101b100708038030107400074803003407a084400f00049900001250081d80031030900090aa80311040d10b0300415180c5d00103040c103c0711100c081601184d542109050381c03504800c480c0ca40c1c40b5003800208074041250261041035101909204600d005840c00c2ca002440803121041404007a01040440d00660300c4881042d482c0c0016549007500005440101c0c420a0f901c00e0600c0b07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 721099415 1250 721098165 721098167
    0xa120b060f04141f020a020a140312070305070209070c02040e1f0903020f0709050906070e1c060915020c01180f060c05040e040b250804110f3706 64
    0x202c940d01c9100d10302d114000544401d5100d80310342c840c0a00458a141d1201c06825401039222090160100e2040710f24400c007040d02041015400300282010380100026400349030222075036809501c058062084c14081c400050343c500c852948202079540d00d016400200b84103010659070b00030140740690f0812924044981d0780c032026044030b444504d0000c00c011031035080a03810b14074185042d902a02a5080101c1c0d0050250400c602a00700101260110355448504441ca10750a4800c2640305a81c0700ca10003d0b90100b02019030340c036000b5440083c041810350340c2d500c0d0440d490840450400c1c3c02180701f46052100f841002d155101d0504051118a880d5581c0300b108100c0132002072555603600f02a0ba00c0074801c4066034040c20b4003010080d442d08060a1160071140b00b00e4962103244250321280130b002c000340710742034410030392070700d1f002c002ea01c4540d100350b001040700090940012100b116003409640b1000c030500b0400a041d018002180140c8040200c848103202d03641400c49000c108005031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 721100665 1250 721099415 721099417
    0x307230304030c031202040503251505090d030e030d1215060c080310080f0a050c100215180d08060f09041e03031503110a0e240d05030a120b060f 64
    0x3166251070301c0400c01c560040c040c0004e001f140c00094044c80365100780042c50300e131403614800c500301c002028004969160001c00c0b00c407015404040001c1c40602030103100303007801e40c400720b5041d110341400601c2860001c007003450421f401800c00000741c1000000c02107007410780700d9415400e4480744102011070070201c01408180c074242c401007601030000300041c40441103141c604050082c040958200361300c55807a13950b840004520980d114011100750304850315040242000c071400c0c81d009000400044180e050386210020400788095441d00440303c03052009000700c050401031a212141e5506095081c000c00043c40012180510030200034000810b040b00c030006032070a81c1c03892043d4a10200c0c40d040f000381005003a001d82e080107984001c01000452190010902c0d81a0b952405107070359010b43c021104004d0350310180c1d100c156010501c2c07111042c105585980c00c040c1c495032826505940e1145503600c28061000001e0aa10198a20f0503182c0030701200c0d0070701140d0b46030a24461030180c0d801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 721101915 1250 721100665 721100687
    0xd050c07060614300a0f0506010e060f010f09030212010c02010f0903020c22090b01031416050f06070812010f080a0321090f05061f0f0509060a0803030723030403 71
    0x1409040400701003a11659802001c030020304c206865483c8902d00d00b08400d0f900d00e500498290003044000700c0c0500032076030114031820f030003400425004110310040d544007650003005010012010404405620780c0710070170340800742060002480a4407020b00900f1181160364070a5183c1c00c0441c44804a0750014001020403c101c941ea000c0c00c244080400c01d040e04481c01d041881d05041c5c00105100c050740d0128100c80c0500b199044001d5210041912000080820103214801440521180c10075190000a0180141c94186005450740300d10900703800c10561601c0e03000703a0b14018000755022001120042101304014804990242d0b0081d2050017841e44113034660003a04055004031043d50006011103402c004945a4000207040081d25450101e8440701e13181000f4111034001c07020301141e802201c2d100c0c52000c0c10a428a41000070404001c0c02250340440c0c2d00c0804121203205200650084910380c4070a034000b001012410440000e003e1081001d42c0c090007004007280d00328104001c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 721103165 1250 721101915 721101949
    0x1e0a110c060a051b191403030f1f0801090602030601030608160905060d020d03020d02010506062a01020f160309060c0809041e020d021c020a0c060507050d050c07060614 74
    0x180f280208003110102407082c054a1440c1d02c6003080c00c40320820748400004420b0300810821b041c1150503800a0360f00d102c01d5826000820b260000648a080c082d882200d03602007003000140090340d907880e07160a4404000090302d18541c0001400700a68141c41800024511440500700c1040c6c1c100481d40e5840040c495802429150720009403550795000540c101194000c0444022811a00b0020b58070340030344081202541c41e0201080261600405440150301046000300780d548000215280d1075012020a02c107664003880100c6440303900c6006044040d5020b2080a590300490078002c24119413540440144840c0b240e2000c00b180031001212940c90041c1c40c049580c5100280d40e01c034a064045102c0003152022640e403a00240c1e0341c0081103850824464515030750b60701d1080c1001c9100300808440030407200900c0100091160f04a241e200006007819070620403101c0d42102a1031003103a2110503804005800d0082008500c41c00000d004200c82c60a08002c400e0003140c01e82d201409000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 721104415 1250 721103165 721103167
    0x6120c03030a05161a16050309070b070218160206011508011215021c050c0c25050a0e0105120703050d1808070e01032607080705031e0a110c060a05 65
    0x214072031300d1400300c03007001c2980800c807aa0307a00c05600380c03c2c2500348156104680c40360002c1c80c20311341520920030303603000c0e1082e40058801c142c075240062911764400001240c0210421041e100c088019007181d03840360700c4d12643d001c000e40300c00e8402410b0040507048510782c000103c0948850381c5e4800030b4607043d1108080b813000014018180405115070351500240500d00000341d0418142100700848004040980140b02c90b460702d801c034400900070058901015800ba40e03d915240e0b12403404c10b4a40300d0584528a03269840c3d0010609a00103a0086092003100000401082c10000100c5c02c10341d043d44040c041e42c0d800d55842949a02181ca20714040000c00041c45084500030307a80c03a801080008101d8032410b5803140007100050003440181c4101003a022201010702e45040c00a210b101008040f0b0300d84040c950b6040e805030060325050340e00b44828050080300104c04820750010110301c528280d2103803003180780284501e08408403400036403c103954202e00b60322034000791128588181070803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 721105665 1250 721104415 721104427
    0x90607060e0f03090f090105130c051603020a2f1201021b251818050d080a050a06120b061804032f2d0a03030506120c03030a05 56
    0x410141024280c051468010030a1a14a00301c00000504d00c01d1001ea440160300740310340d0204184a03100340704454204055501400e50801542e02c0703841080120704056080201a824a0051030115101100583d12140740c402c2440301154120402c400300d905410b140458002d0080540d111414801c0e01030300c903561012103680000e4060320020081d902106080001900000780e440400c0c16600d074520150345402d01a0b00442811a401c0e900d09400230b451320498055400000e1400c0810b48805013514017081000070402d2003244000e900517601c0305098240601c5050890b44040c100c400c10a26010f030820140003104580000a0b400c028440f034659101c0001c02d24804000f51444800c000c2d6800300000c0640100780310303003008000c20622000e55a1502503c450b003a2940c000f080d42c0e0700150442600303031a1201c9064084141c0c40c20f400001381c1c2c3c0012f103807a2214401d000c9000c80e882c3c80803c2200e00707003002000c500581010052100b800c05801107900c038840c410100c0d017000000034035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 721106915 1250 721105665 721105673
    0xc030e010e04020f07170a0219020a0f0603140106031802010c140d23030103110906030106030501110406170601080106140c03181309030801090c030e060703020405030709020708090607 81
    0xc40100002d8820742d0381d818552002c181990041400300c8007070550b2200040000807000698425076610380003068041102d68000e0f02500056004990000d03580401065070048441480000c02d0203481c0410018092a0504882d16050300044101850004210a10700c00c00025580003602820814491249070070054817540707400091550300c2c418034040d00c2e25584d01c07400c040208940c905180349007600c2c80030b06030b2042c4030a11000e4440c848800b006820303840d00003560368005100400020f1919517956a060a6920700d00e98070301d2091000c2000c2040c0c40e0410305295905881c4501d081007854000b00181c45040c040c0100e41c01c000105642c419078025900440b80d139251014101d07502e50740c8203c80066800c20300100a0300075110305401503d85206030107548031131681a15022807917030a0840790300c02069100206802c164542d1076a2207100c100307020303003130246007a41d13005a62181060103062800030b160b03004507203c078030402c15840810140826a00090000c603412540e034861420 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 721108165 1250 721106915 721106927
    0x6010e01120e011b050903070e0105031e030d1a0f04060e0109020703090801060b03070306080a05060f07020c0a1412070e04020609120d11120903100c0c0f0506091204060c030e01 78
    0x1041c01404d8a515a01e20003540060240540e050f08074100c3e28440c7e07d607040311105500a104458040d0300c60303042d8866144414421387c04507900c0310210707400e141441208109490f820414a9804654003d004901e410300721180c1c0801d90f4103070f13000e10205180941007007250605100d6284450707030104584080612840081c0700600c05040203101d055143c00000e9402e52040d218000401c1c82c2c9100001e6030000070510301700c0240c02c80e01400c1c540d034480f900c0d00018003004000d0411405201617510803995030360078023406842d003c2c0c903c651078401f007001d1010364444855404403a0380714100400240020f5205154081da055990949514010300410070755900428a1142401030304840094030b80d2090020b20a414240211002d072044114040e02d14402d8220894040d00700560348042d8040641100440fa101c520381064444a5a121181d40106400c2c0881d400d400481c140702d402841040444060842264050328291902d2000703070411640603401424070070452021911607010f00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 721109415 1250 721108165 721108181
    0x4050c09090c030f0105152205041104230307060e030a0b090606030124030609050c0402041706061c0f030e040e0304031b0608043507030806010e01120e01 68
    0x1814030300072820240312089aa8204550307041c1d84485080000403240b03081003881d4001c40521010520b028060b01101e501c40d4075201c140b0010303210201000441d41c9680c0f140c3c044c09807080c050355485504141000f00d9174280d582c0040024210300c10b03180d140350380101d032030340441e02107080c400c82010030180030034103002135900082c01006640c0200103521801040443c42040110000c002440071030700c1e008103040340317201c07410030002d0404400d0000039125440060581e00030000c0b0340401866000207001d0380e1042d00402444221102d110402400800071650032035001c41c2c1c1c0b00c269103182200b4007060480c04002510018a21444030185400b803031502c110007001074400c0c8401212034036100d42c1e030f40c0701344002c58002d80070354100c40e20703109954904000d581780ca40c3d407070042e915607844000d0903001210062000884050586001c5004818101402d620503e50103032101d0050502804943c0000c1115040c00b5a0a0400d50a81e03408010b038a01240c244d0b40000b40c40004486007401040f80ca = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 721110665 1250 721109415 721109419
    0x5060f07051006030b0f060a0308030a0c0e041a12060123060c0708031902010212010312120207111507020d081b06041b05010908031204060209061219090803040204050c09 75
    0x41004424404500c0102d4806c035503a44801049443d02010700c441e041a82c400507003140814004203501c84225041248054141e18056414150140004045400000b11a000caa004000c0d00715541070a5034080781c00107141c8003400c001e62500103414100128003600c0c445040040440b040e4a039509415140300310700e0031003141c9000d0b0716042100c3d52a88601402040c54900010070606036105008581c4140c8100e8003100c1a42d1840d40c801001344003620483c001c0c0007640e03825909600c02440a012000e000300103155440300301c1024410388900c04000030350300c900104100005a100c0100d16074140381d00451842e520740342d0700005000e0032400002c0c9100c6025203000c1c04203105005440b241e0791050300c0642605155a9801902d1422440c480d1465540003400f01134944000411200d5001d8050707040945080c2e0a4000500c0c0c0b90701c200d603011032142c210170500c813850b40c859001c1614420100002c01c0401d403984c452995134040100024416a00c3d4030015000711070300030075110b0074040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 721111915 1250 721110665 721110671
    0xb100314101113032d0c17190b072105040210030b062208070e0f1608041b0b03092a0a0b07060603020402032508040c15090f09020703120605060f070510 67
    0x30506c0c080c4c91014051140058620410b070207070300001c5011802c480c6003082c51014911a2006903141c0300d41507002842d10302801101002144140a01c045a60003075510740000a15440d041c810815031204400500040501d0308034200190b490324003c86800641b540d0112540c46410b24209280c001c40e6008600c950051620009818001c50403540c013524952006250940d680014100311105100d5000300091501011402007000b05183d807030510b4584480c0003640d52541554026540f090752111995404541405e060711216581030180e11400e071203c01040718000d00050703028409010346d480313402c0d0001d03881080003140e0f4404d0000b5940540195240e00d026000d052000304944402400b1000c403144c0403044520070601d0504c10341c2d010b50000051030602e407200328030302c0d400c64620040c0100144c020842c0340c00041c4020040c00030b9100941c0c4c45a051a00500b0740b4000001c016410781040e20901442d5503110540d604518071240081c0c40b415141065860002d11201c49580945 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 721113165 1250 721111915 721112003
    0x80f100803160605130201021e0304081504150e0309010f02010b03010c030e0601080303040302120304060b030a060e011109060d022508030417070b040b10031410111303 74
    0x260b52200c00c12102d02881d4200b0807551160807038181840c2012000b40103070060822019000c1031860b01c00c1c1031f4500101140e061540300e1900c64644441004035641c410540801c000420480e850030065078254070700b040c4200c0b15184e450031f65a009400b21541070000c40109006a50704c02d5200200b40c0030300034024864211000e8025008201e00c814040d528061400003080b50346001049a00460340340e03000342100841e14030300c29101c5e0000781017160303c582c840001d031403a42d80c00c003d803080040c0501030018903054128060390071144849605091030405110070070b22983c2d4032090300c6201c0d0070b00d000542d07160015030503001250400056a10714511241000041c0070a0001541c851845406c6442c202c000b100c051070128003c502c40141070013460b60010700050307a03c0f4807140d0015415030342c203007031a0b4580d80c81003490301c0000b090f030110b43e10464540080b2940b038054003890089400250f0710f080400b00c07606003d086240006400050b549545404000c12004500300030040d40805c800c80d40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 721114415 1250 721113165 721113187
    0xf0d050109020901090b0a080601031a09090c0a0801060b1204030318051c031e0c0e150706060f05090a0b010207051003020a12060b181f02070609060906080f100803 72
    0x341008500e1400991740944c086401c04001c8210307000c0c9605501d50300255617030040114058002c4140444007440080a01d8602d900d4000b40300e406000c95401503c0102940c90a00524604a500c110b4081e1305101040000c0031300034080b1819590b0684d101030f00c0d59141c1c14160060511514000d403941200b6006a05200380818202040003610300c10142421080714118207941da0100744110441c0780f000810303070340409503121181d00e006c80d042c65046600e10400040e002c14489021a120318000a14a404c03c83c10b4492040a005440441100c050800c4042016042d0080c9440182035649540031110b078000c002d0701c4001d0000a04410030000e0304d0f031004002c0d401c552084004160540030701c0400f00880e006800c00c1e20301c0340e544c05041031030300e82c150501c28500c941c5903a00401c100f64000c10f440007007280204107083c560000c0101c54030303100000f81420f566a00000c20071550050510a09602600594000c0740001480c1c0c042d0320303142c00f1343c02c1081d40e542c041c2300303907200005031880c0744 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 721115665 1250 721114415 721114417
    0x30213030b070c03030c0504060f0309020d0b070c06050612030f1308070609080c0d154b150e060f041401050307061701210b070309120e090c0f0d05010902 68
    0x104d209507414030455032540410f481c00e002e01d01408011500582606600a00c240d201c50207082c00201179240440090b00d03000091141961000c0024100403450401d00200d4000d0541140c2c00f03072402d140000d48001595100c1c080c225401c001d540c0d00141d80d08686004c0400c2c5006002c40788207503008165180c1c8050a840c0030780c410600d0b01d02030442800c520b441e05c484561038854200714503503001e0340304244ea03000a00807008071540403900410b20b000030070075601c802c5080345c164654110a402d8030274210760503808241c0445910b1070800127244400480c58804104071341924002800c182c4441000a4002d54220300303080d0028a070851039200241200b90741412500c060302a21491900d8040495107254913045074001041d1550040054480307484486e83c031041e1340c4007803503055449683da012210000751030702000291101d01d200184014110300d6100030045051210302420950042903001074000d017103000344c1c60081030380e1030040545000c031900a010450108041d41c5c5402c2c0100c02 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 721116915 1250 721115665 721115687
    0x6030d0809031b0d110114011a0f0706060e13030c06050606090303190e0a1a0903011d010b03060c0423060c011401031104020f0d090204151517070906030213030b07 72
    0x403c200042c5d5848081032290f44602080542001d40c40c1c1e08202854007814041d203000507000790200241002c001e1040301030070103944500c0011840c18a01080c02c2c42c07c8602031b05401c076001384824440000f0740c204900340c404c0f0741e000b4800302e0140d80307400000340b0500035040c0c120b41501000400c160419420801c42c0035404940e11500b40a424000904c045d50140b409100b1040d43d0345103110891107040005400c07145001000030814002c40b2004540d25512010302e84680e85d110484800c2501d0180421a488100b020300c060810f450035444001101c005000c0f01c4c001484a010541c0d203480b80801c03100480200c400910403c07a102c07458002e0488244415102424805950421031505000703c4440016404030b0604000d59140c0c100003c2191040407640309680300304c0c46100085200c1d210004080e0300342420010200c00d007003e01400c07a1080980402d080784020041000d400081c51410380c1c0251900584a40281c8032000c0000c0c110340000d04800d032a18104400b03180e04c0014100c0d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 721118165 1250 721116915 721116917
    0x108341202040e07060507150b0d0b01062304050d0f08030c04030204061a0901080711010501090501090c0306032004060915031e0c0e04081c0b031506030d0809031b0d 73
    0x110001103500300300d840340341600030600010000c00c81500888c1031040001d030a40304000d000120307210108d000482110f00800210350b00b1311140010820540c200b000076001c0c104034855201c12916903240043c1c83d128a01074030b44030303580300b4901d101803000480114800981c0405121740d01c2c1040300c280c10190708544000c034861401c001c404595200400b0b5048142d203100d091032824117140c14010345540100805420400007808140080e4503024020180202a20040024a541080410382c1602d043c0d8104800341401c00c0d00810002d000c004d2000c3c81c0c0c03605540d040402034890310006001e804560b2014031120705154000c558480006c0a803c1203134070510386480841010340100f0310f4149805005801107990f12410880d440302c03120803d034404d200340421b0f0714000703040c64500046a041a166000541d44921060700c2c5c0c201001508a02040401100000e2410000190791503e60341c00f003004104400010070300d010340400548030070b20b4000200180c5c0e075401c2001c0f1544c44140c046600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 721119415 1250 721118165 721118171
    0x1a130303021605030a320604110108070c020901140a030c03060b03160806040201031e0e071511030f0d09020a0617010e011508060f042c06010834120204 67
    0x60504d0001555201a9482101891100d22070703151001103500c41107140031510000f40c840002060244111403080740301e8030659201d654044001130015000038040400d114820140c0000b503510521000d0442d010b41034894071100900021a2180c0e03020b03403004124007411000401004220381000705e400b0029011207000c16003c01c807851840d0b9080c404c00e003842c2c000d880480c1c0075502c207400c00122040d00b1011030410041811004007101e2100e0440d40d52070704024001c3c4040c11500c103084c140d01c441468141c0f164807420180704e4803032140d4034001c402c814000450704a1090150841080160014814001640e8400d405440552000d200b242e10380b5a000010031108440d082c0c5905946910000c0d0320500061503007036030500c80c0904216400302d201d03103822902d40d883d4010a0402c1d103983c0043c9010400151a00211308400011840250482d00041c0b00c151000a010030114107410b89024001c43c98024660b0b85000700704510402504012000c00d05843c01040c0f0a0a03a20a803810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 721120665 1250 721119415 721119419
    0x2010e0f06013002130c12020a17040c05030f070905071805040903090305060c07050c06160813180501051009030302070b0c0c0405011413060b03011a1303030216 71
    0xd19203400e02402401c6040c8084400c01802403c20030701c516501810411621480580340c00056000110001d044482a02c500e100307240340d41d01c411b03482c000c41c04805c1c05500340154a20054050303051349001d0041585800006414050720160560052030050107881681c000792a172070341c40b0011030080c591540d003420003041c01e80b4402c0b156110500f03148080300129a007044200b2014001510003901044010080840070900c02d005c8980152150f2507042d035111020301e0004d00f4504100e411903c2a1401e1012444007240034411150856000240c0c0f82e80780c00c4003181d001090381c0360308103d0f0840c0d1541074440101042d60700880c165401255001d05000451404403000500c6000050050700140b00800000c0a00130280180754040001c0e03c5401d140280802d081310003da005a098600a41c002042d40c140300d2401a804880c10700244209401e141c620140c922040c403811a980c0346d5800800f4059901000b0307108035810070b03034044c88400e90702c0c100259141700001680c52803072800c00300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 721121915 1250 721120665 721120693
    0x30a09080a0c0e090f10050709090902030304030803061216050112050717070c0b04050d08061008060d0c09090f020a140f0f0301060519180e0307230a0302010e 70
    0x160404040d8040c1c21640d406042c41e24044000da80503003c01a51701c100d40814280d50380500101c41320340111100002c00d440c101c1d20040c8403219079800064000d2600d102c440c0561004401c8800380c0b500701b11610758944460f004181000e041070003014090055694042d43c9200300d00e0000c045903c2641c1e01c2960007803050031101151815158040400c418400030f498103c440b0041580c81113040c00c00e903c080440d44c40758501004121012185a0403030035433100203507040100c82e50011400c0c3c0b40350003035020010b8040d261080207071040c0d200300c000c0d080c400c00700104006003c0103019061014040c483d880e103080210b00741c0030396040348500d03200b1a01040002c150300c010000709000030101c2101220b2075043c040401d814603940340d0103549412000c04c8030340704c9840314620b980500703400b00c409902d001c2c1c40e42c109201701b007040002c1c241002910307070960b9400070944a0154001103140071880058050080007505110485541d006110301801807613019840026101442c3e800d07100c600603842c04c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 721123165 1250 721121915 721121923
    0x717040b0a0215250908030f1207020703080a0c081c020304020306160e010c080409050106120b0a1202060309010e060a0c09140a0b0310120c03061a01211805030a0908 73
    0x1800d20001c25001028a4000042c0300400080f50b802d41050714034146c5588605045a10040e28411b444000050580300113140c0403015500c465184081d001050a6544a0400d440384842050800c1100800a814040b11004440100b02181171078000345c110791038154040e402c00c4034241c0c42030082c20300284a034481426010444041c551322006079041c485d005485180b1005010342da038580900022400022900c00c090281420b502e134108005900e02c1031900303507002030000c01e0140080d510104607401c070400f65140d030680d045902a1312079403400e0345a8010001c00c00c034103943c0d10581c030910108551590041c8550100d40d0399104000780c4445c000500009d02000554200c0d807204002c112401c01030000d035411081070800c40130095613907102d00c404208101d0041d81da403850300000308100700c00c5220703c02d0404e000c45034203581c415102001a0119905022440390852011400042e140859000b00c4034403068154904400e05ca43c101140d80c1d4014803039400100c0e00220000c500074000007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 721124415 1250 721123165 721123171
    0x819060c140d09031103030f06090c0415050d090605011401030b060405061e04031202100e0610060f020c1305010f0e010b070f11060c0d03150f0306020717040b0a0215 73
    0x2a4001d45480c50180080d0018185038009508100e1241000c510200003440214040c1114415038425410800d0810000100140620f00044410041000603040d40105d1b1541a01350342407070b44d1a03244156050340504140030004148a24020021500400340c0754003030a0003d0070383c1d04000f55504502444064401c070b005e10740d88604107105200d501d600340f00c001c07010081e080700c005090540d80e90346e902082250280200c003680141d00031a107110b14030b1186a0000f81c1400c01450141050159a42103510b603000e14002c1095a0686002460007000285d20004019060307001e400300350b8010700c0003400203000710085024182d04c002a102090020700d816a5040700031540b901c0f03095940e4180500340c016080300d011244551200d01036492501030401e0300c00b110301501030103109000003001c5a10303886081c1714182064400b445980921420390040d01e40c010001650b0340182c0c14414042e6088d4480014140c000181c0410100202c0000d004480d00d41e03000c0704c0c1d0003c21441d01c864809411 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 721125665 1250 721124415 721124447
    0x50103090512090d08040902030f0a0501120f030201290406050a08070b031302100503160306060905040e030405060310090507020a0807020418060f14060603060102061b040819060c 79
    0x991102c03019011032000404500c440241250966241680c0ea00c24a420940c01440c4e859408810406c2414984a00070b90200c080c07034041250b9818921217034400740d190301e0042c02c84d07860859500300f014000d41c072030030b1707640c0050b50b008080c00010f14038000c003100001c03203050240b410950b00203602d00301200000143d0700d044015012580c2030260000c5241c00c02040c00c10b0782041d07020440d016846510b04c3e0806c00c2480c0d59001d80d41d2800d140055241d03500d000c0603030704062600e581007200d20f0317014600c03c091f91070484004c20f842e188003641910790b000f0741e046941d21400010501c4045400ca15080b0100c170415002484180e98170760090fa01c0b01101640500710400030441c102c0149019440040001c0b5101c05d0714042070a01d4450204a0318030540e203820040c3c0d61a450203c405a01c0c03003503607012070101c600c103103036281401c0000d46030308014040040240c81d203201c0d0458007030000c0076240900f1001d0120340f1441c5894400c1c810344c800c0c0703200a031071061a00c00207030062031113001005580d14074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 721126915 1250 721125665 721125673
    0xc070807120b0c03070201090b0c1819090e1e03071704060f0507022d1c1515031b1406070f1e14070e1e060d030509280501030905 57
    0x84003042c10f000c2c1d1000740f00008556981d04a1000506111419402180c0084902d51540340c660700c8002c1d44135000ba0103030710800c000961081e4100343c124110094400c0020040740324600c030b81c0d4a0703147c100074616074919008078a4420b2861131002010300240c0340a101c00924032240924141e030130388214010140015503100d0700c981064000c1000b400c440c0e05c06403000d40e0b1010031541524400000f5640c5415155003035180d04054500944209411a1030481c4181004143d81d500929129000b008240f1244c0b958060400c103222076140600454102c1240c0c0e079a00062401c04908044a00a80e01141c5001000d036145040003015910380580c89a6498881d403440d885c1c00700444c4030a10007101c40b0a06029803000658140219155000c0b2040102045401d2040d1001703440f000400000c8030103052002d054034429003091807900a04156001018041e440c181200d243c4121056580c0112545003051445452080c1040c0c09045258418210a8581d8011801e403882c0d520090400e0340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 721128165 1250 721126915 721126921
    0xa0f050c07030c38040311010b0f04090f0503071b0609030506040201032703051c1e0207050a0b041a0603030a05040902181809010b09040215030406110c070807120b 72
    0x1003034a420501a0b0180180c00d1a413800900515401150340a0000f000d0081d0b82448209500300c030b104040100c05c00b000303010300c00002e00464200450182614440da480c0c0458909002c5a010035584250f08142529585c05460500c86601d20701042d64040b00c0884020006030b8a205030030041c01d40b40d001014201d20b440d0b680045010b080d0140b86000f40510740502c4945511001e00c05156191081e10340c2c1e9141d00d4603041ca500716016522083c4100350401c02c80c2d60f0110300c4d82440b4100802c1c3e8502c0161136602500340725203094201c00c00141510350003002d000134003a400920340d03407801c9203a618400540e01c040030306d500c1e40900c400c64408204107010911100c1d4071900501102002c1402c0c17030903001d5152000440203003094041c964444441c1d07050100000d02030082c444258020f4a56458504081e40421141d40319070042c03c00002c000f04c0070408102d040d422122440040305900d1b525031105248490302c030030191051f14424814400b000903400c80c0303810403074a19600040d13444503070b507 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 721129415 1250 721128165 721128173
    0x5011511071203120b120c03060a0e0d14040b030f180109110f0f060d050906151e180109020406030e12030112050708070b1317061501030906050a0f050c07030c 70
    0x128181301d5403007003d0303c981d14000c0f00e84494036a042140c00080080103000d035140145410250082c000f00300071400c0020041441100007062285c02096150011310100d6002103600f0a0156812070007403000000248100c403c602502c40d800703075000849547d840304d40c3c013840c2401c0302e0001c2c400038005500031202c40500e2074001f0801d002c0101c090940c2581d12090381c0000d01c0e55001107280c1415656820600403604c10801c0480e5001c08505000c8110101080c00218091207a512001045840d45546a46501d40030048041104a0007544046503180d0024002a400900a650000303180c841100714480d0000380c269150b0710f114481c03a1075a401c0c02d040007850070800c04181d42c00d102d000c40029010b5070400c0751000400d42d2034401501c800c042ca1524854143d0780d407201ca2a90140c444418079014046105600030252340010341c0a00d400c60f00590103001c0c001d50250240707140c071041040140c0c403900070b41d050070200f400c00c120542d540041c1240a0060041c0500000c071400b41081c001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 721130665 1250 721129415 721129427
    0xc0706081e010321020604030819021b011e0b0117060409080711180c0a1d0301140115030e0312220f05161a090d0605011511071203 58
    0x402200e00352245004400041004107200381d008580803071030620071200009032441070651083d80b61015004a041c5500c0007010a0400b9108451046030a001c00300e084849034103c90500507003118444c0008030110060703008101c10149400b54149401411000c0c6003103201c1c10880100c161a03c511080945a4034600740300300801c40e60300117540e8100200414100c601901c000351044690818031710103501030007180c0d0543d550300c0c0b04808607442070040070b1b4142400c0d90614485441c02d031860700c124001c2c4500ea400c0f811003071901546441503d07000c403021000b45605894020070b0180301082c00090880803186a20010f22064000703101240302001e02ca03045035044041d42803000810000c24a0300d052100c9074050884043d8492000c47c02040790510401000a1001034410001441c101003101085c641d0030401100240001d0b01c03020541d902044c400e07a294219008201940e1104464405010801b0754000829042021070481e80c2c4002070f40015107030302c062400e011501d50380d404e81e41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 721131915 1250 721130665 721130671
    0xc0f0705010f060320010f120921050c01110705070e070905040f0608061305032a0706020f0609010c0f0e06070209091c0203130311010c06050a060f0602030c070608 72
    0x800e549456950b01c42c68040d000b1003000d1805443c0041a512030901000010600c601200d4107000c2001035408905404c1022001491400c140221740e00c00240b0348062466540d94540701c10061b03050b10140e551368032001400f81e5060920007040b60141e100700001d6203008460009105900800080c418206c0003040540c10a6950030701c411135a4441c00010280c820004800500070380e26241045441e80801469401c090701c03515032180b4a826403039450301e903c82c1c0700ca50700e035000214800c1d103503625842d20090044041c6805440728a0380340e0340000c0d1500844658940b05110b14000300e001d00c80184656a9071492a03101c0702189441c0150645040d12104035203a44110107002820141c0c986070465442200044094051007c5103a40300c0e54075440302e030129007154410700605004440c1e4011110560f0b0f0400ca1040d200301401c0012280e81d08060700c000c10141c104010301410800c15000700050387c2e031027a2034021558841408a9490180d042e144601d40c1c030501c1d080020354041e01d0f1135a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 721133165 1250 721131915 721131923
    0x61818102414120c090a0501081e100801020d1b05030c0d0b130c02012c1f09020604091b14030f040c050607050703020a120309170a060501150f03050c0f07 68
    0x4103004400c1c80088540c030b804c0318614410300300024429200d260883c8144054032007428002e000342040b00b8641c9403035440d014108124100080468107240700c080303c1800414400009555405420011314041c0050469042102c00c1810022503454041c2c0c042d01d1044e01e1000307519051002e000d0a8602500311018540c3c3c1107209800c04001d010114059401c0c0c01300300360008210054441414544000c02c0345280d080b000c205041080341c21000325401150b5a204001c42e55a08c1900c400342004018101e002503214a001a000410700d6540d040120f18800c1401c007040c96a6108000360b400841c5050310035024041000050092003c2c0400715070841d005000654005848601046140d03100c08070542d00e40d4481c05081003145000105040901030000005104014595001e01408000c0c0070b0380000310791840c1989021081003000009282d000344041c000c0c3d5945400302c105107007242c0308020002c0c95001c00e2000140c000c1c06182d0040506005007031030007800480d908001e070403403e0111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 721134415 1250 721133165 721133167
    0x61206010c0f06050403110c01020309090c391c08090a02060301140405090705090f130c030c1409090616050403060c0f0f0c050309061818102414 64
    0x100894051100001d005120f1100029503081600300a0281c06008a8500c0356500011803840740340d9001c0281d510441c800d95520703501d6241ca002465480c0181030100d0070310b072202224008841e4240a444009100c0004040b02e600a0508096190344915411403403034183c00c0ca801205c2482a1a00c0d580152080162090301021b80c1c00140994420781c441d541c0c0740b000481034151440c29101d0300e0b4100703024000405201d80f40c84040388002100408585501500700c00195280b10003618040c2074941c00442c0d10421512460071b450100c1560090424002c1e60600c0e03003a081c141002c029000c2c5440f04028003140e07407002c114060690050056400300601030000100041d4240036601000b40d150b00d40c8403013644880c07030051174a13924000042c20410351902c42004140c0100859111400c103641c455611488010218a83c0408070802508080700021501424540004644c092055100403010603661100c1d0103d080320110031002d04164a01c2c049440b80b0301644408200301a5400d801e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 721135665 1250 721134415 721134437
    0x19110303280801140d061b120b06190f1218030e061c02180306090d0e01021c080403050f0a12050a090507150221040504060611031602030304080a0f110f06120601 71
    0x2d40c7e9408038204000840e144e032542c84503018207801845002c01c0300381c80844c00c2c01c02c0c880042000710b218100401c1808404402c111100f0700c00c2070010021139940e8010300810200140041004001d9141500010121910b0b2840f034500f0074111500d06c0e50f000ca442c480300c0317003801000000794040030440c0e0001303034190b504c4440c0382c80900403c2d108030f40c3c3c2d5000d88460480d40002405403d40109100d0441d08141c5e607008140c181071255400c05042490700e9181582c5d545001d03190381c031403500041100340000c01e2582c490756100308414100c440d101418003154584080307a2080d24400d00001f003554200900910000c00c00c480303580e2001c2c995104030391009881c3c0400701e240220396030346035190038000102444941400e018880082906240564410a40541007a22800340c800c0075043c0410482d1007500359a020803c2c0e40140c07400c0003d5500c0302c1e600389810f80c01451022412200120421466101890007812140d004800034145c03a10f0000301006c0707118889030050105051149049603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 721136915 1250 721135665 721135691
    0x307261203011d1f080f1903020d0e03070306110a1e09030321050f01230904030c4403010e0708040501090b070807030b0d020319110303280801140d06 66
    0x902c00081219101400240403141546c500b010042030b0700c0c080c1100310030112000260b000602001c102c0303032440c3c05141e06641500184c00c1140d60313803001e00050b0400704444551030102000b03140c440c1450700c0d03030219071703414030400c503210b000f40194038001c204200020800b280c0070f0350035064409004480c040c82c2010780a9a5003c0711401d9030701c800c01003c2e490040c0880d03030340030021041c8243c5400640205401d0800041e03420b041c006c00060070000c646651001b0840ca0820103507074050400c2e05141210210035401c00003071000c040740d4000790007840308040d40e5031107c0212070503555041d0710200c0e9940e8101041c0ca80c145c0c05441120150340e00c070070320004a5462810707035000d02e24a5440c1c6226040a0800405403000100668803600752650401d0059400048a004940341d00038039040100042c14052210511404816050b000000e010801320803a071500510140c500700c0c02e91078030001724908885601c02400b9458039054031714032003c50342c43c202c02500c09407031103441d020454135000c800d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 721138165 1250 721136915 721136971
    0x21b1501060536011b0b0109090201030e0a0605063a140709051e150111100e0f0609190f021302160b0106050a0206060607020307261203011d 62
    0x10b420501683d244281c1442581d11a90000441401d090139455013115a00c03500442d410610815980c10b544100350700840e40a034002c100a000140b05640b1030003101e007042d80c09410120307202441a485804d809208140c1c24150400e0030340d20010301c00f110300c0f11364050302e0b818003002c2c0207a5178064803284c0300f100010100040c0c4041c1c001000c0c081460b007060040f40080d0310f00b42008a0303c5c000c105041104501104480710b010190034600750194044400e80c20f810490440c518580b8641405154000b840c000243c0203640051101114210340c0d64114080c1c8504404050034041030f07041688202140922545105080c001440e466011045400c070008a900c4585c448090b6900401721000f40b00c4003000780360050059082051a003821100001d4841a008011030310915000c00c461003952010070046000e44801c10b003008072000528494060014600300c3d0291511178000404560149101038034100c4000301d807424804480000098010f500040100900c0c92031030544001440c5407107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 721139415 1250 721138165 721138237
    0x30403231b01021621080d020a020a0b0a020a170402042a09090203010b07060216080309160501030b0f040c120c1107080307080412080d020d021b15010605 68
    0x80c0103a9584941140007a0424000c410550403850f01c4800c2085480d0351400d17005903c0301640503030a803160722843c100303802d40100940903a4151003c2840e81c015500001c289845900480c100d101590300d080403e03040e842260404e4001031400503a00d0f054603810704606802c9440184003040b10b03070717180d2240c03803a8941c181611554035a4064452245540207280c00c03010385400c082c00d514560410007800303040e219104005210903400900405218400c503400305000b075124803d140d43e4108088820350311400311071440d201c202070b2100020316600912803030031500710140c002059640000d0411008105518040d07060090302e0981e00004400c511550072030400d5a00d4607508103880710107580c80c004a44c0c02200d01e646c1304004200c042440e0b18156005ca0341070151403204503880d890f004005005012079060b00c2c6001251740203802580303070041d01c4125510f602e0100110302601e100ca64410501d040103200c880c0d800014000341788120010800c144607041120b158130060301c070054581420b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 721140665 1250 721139415 721139443
    0xd230a05060f1e2806030609060209211002032d010612050105090c0a0c0f0c140d02010c02040f0b1206010801111e090409061814010e03040323 63
    0x52802c0080c040200c41d10800250022a012982460a20701149900313499103881800d4035162900c085001d51a41c00c0000915480101401240014604640039402c40c00445114084050840004410800d040300c3d008000d54014031602190700b892030025480500784400c80ea45800040b54088041510034401c1030f000700201d9440c1d8503051004000241c07203c00d0201840c1000c004020340d40c1c80d41c441c02c1e084001d50b045143d8521800c1001d0f41c40c69010040240324110740241c107070a001e4100324a900711880140c421020080d810b0805c548070038001c0c4001d000c6103805042c84094141a480a02c02c21748940c00010409450170000d5072001d91400414100d42c0b10310014044c0000a008180d09082c010040c02c0c100400b0100c000e12000c041e4040000e4100003064501c10b9a07501d40103142203980060041050f845240181500c05c40c00030003d654480450b81c035029541e005100307000c144c440942c00f81d8101401e42d92002d6500707541040c00c244800c80c888076413029100610100c030280100c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 721141915 1250 721140665 721140691
    0xc030c021c020f240a0c150e07120807030c24050a0e070501020a12020309100c060e1917070501020a0c0b010f050612090708010213050f0d230a0506 65
    0x7075104100c91500030307804180c01840300b004104001d1071810324002d280391045440c40e0719503050303c50480ea00c2c401d003c00641302400180398100021256800188403c0d480002d640301c45855401e081c60702d08541c04018030600c0200a0b60780803a01c1004420081c40c0314007019880030300e001918902c503502c07003240b40307403c103640d4018010701512910407418049034000c080e0040360b10300b00010707480c0c140c0c91a000e00003005006031701c030f5100d20034422202846c81c0144045000030400c08020301410384440101c80c00d40c40d00d06045664280060740d56003810a034070009284807142d03595950b4144200113074008854041c003003c40040c01c213002038800103215544040f07520080b410030028012061b40302010602500c8418810f90310780504940c941080601d481e0125240d051183e4a0302d40158040100c551022035042003103400486620304a840031592410818903440c100b0460320100d420007084965803c3e0750000d40201404811103141a0106481e09040da94850714240207040b0340300c0c120508 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 721143165 1250 721141915 721141969
    0x3c01020a050a03140903250501110405130e0705010c0501020c0a140709020c1c180b1309020f0a0e01021e06220b0a0e0c120304141203030105010c030c02 67
    0x3900d07120744c84491003240800141400d000c410b160b101d219610207500306000743c685a05a00a0305040460300c03992142c000c001088015006c0389482e00300b4025540704008504440304200120b0007000780a11214005d00b02c827503d007000645421030349803421215950280110341586600740318802034107014801e07800000c0c1031001c00c6820411290000e04166105100d031480d010380019400320210824498140c3c1038820300c006540d08100a440c40002c100d10744d001040c101c20150280c9041d20307502c1400c6007034a4032a01d250050b0f00400c1110f040784041071003204510340c03240c0d815501c441c4042c0161080fa030121084108245800281d0807200c2d0300071740500040152402003d9502a10a1200780212030203a880e01070500002c0c2844000c07a07290000046e0b141e000b845040210000107011141d21400c1024039501d98000d40700300301010060260002c02e504000080641e114411005546103a0038040190740e540030b00c140176020041c082c006500140c0b1201d001101d000070030011184121 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 721144415 1250 721143165 721143167
    0xf030a151b0513050f0d050a140607030c0c2a0303020706080106050f09150c010c0201140106090e070503100504022101050f03030403060203040203030702030312183c01020a050a 78
    0xe028441ca00c410081c04002d8142a030100000340d0054550407100c07118600c01640008140240d00c031005481d03409240e80d03107020040c2003c80080c0d0b450b505015150159100603064007100d150f8003145000ca4001c8022000088840428641c141c0c88070700c14220030b024840c2c83c403c20326a90740084001d0383c03080400740314098200305040e0050140d480e1a81c6000700306030300c40d11103010b6005454020352152a1100b10120b54001340e40e100c034000b60080041c08404100280039010b10b003030200719041c2c04800498141c0c4640c8016050b10440540c140d419260700c98200c485601c010328180700000e80200c0810070359a035000410860f004070603400180c00101c1400c050803941a40154441c00000002c80026100401a0313401c40350000d400603103903900d43c004a0b05520078144001c1d0705010000b1440414100744038510300441001204000c400c400c0160706603030354004020900d080086e641c50b8a00c84112a02a00312080500388076a041001c01801c40c0c01d9804c40480c1c5004108046445a026 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 721145665 1250 721144415 721144451
    0x3170a02060f06151b011e0614100f0e10090602010f0504050c2404030812150a05040b0310050103031d0105120a090305070b0106021506030303150f030a15 68
    0x41001c1410440505003540015103045201c1c00c0210013040202e010741400c101801600080740306000240044c2110396800307004110000250520706151280220704030081c0080d1024040001d0034052500c0c0640500b41d032100c5240e04403c0400031a00d6951a05803140b800c0121050307110344406042c00e040c20300280c02c0da007492614910340e600d01010440464000141043c0c4840155880140100e100e243c1c0e9500400d143c040e02201ca200080010400c042c0b0401099805688148603c458840d243c44050144000c00c4640c0d02800c41082440113160681c00200141801000c454441051184440650b81c09038401d4010403200d590078a110140d2000c4890205000d18000340b910b81c00e411040351800002e817841000355036410302c40701014010412504110b03008840e411466954400080d6a4481074414a03030107000c0f200810364a040000980c2e001e1819080f02e1403502c1d400405100c12002c0510100341d06204032a032420100301c00440910300c2506540b008a003903024490a83e203a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 721146915 1250 721145665 721145671
    0x408071502030609070f08040212070e0c07050f160527040b16090335040b0403020a06090e0a2d0605270703090203011407020105070e040c050a0c080403170a0206 71
    0x42c000b203c451b804051380d210811507403040c3e0441d403141d030b081c1300c0190491401c1c10380d80020680761801c0d01442040900d6801a042c0c692003842202c440000070026079899003982c409400b1380081b65070080c015071070305610910085a818961440070306400c0985001c1000035902a68501081c03010301c01612016803e40009030018180001424070390740c1c6e101140c40c0c02803102d01954128100800c90003190090500b0900d0445660b1030711107880f00000c03191580548022882500301d01000104039018400a004a41c821b01080404c0d580c1e030240c0e00050700c580100195090240d41040e103180848112850f0400030b0400005416800d22043c0b040e0051300003907070000f0b80003803080d1320259a400e040c1154010f04500d00070800c3c1c0801e1020901400700d085c1311603030b0344441c00c003002049a41580128401c80ca9691075908031841d480c14441202c4240e14000d001800802c200c00074503003c2c5002c0e01d00340c0e1042c000140f80960b240c0301c440b1540e0f0100d400d001c2c10540040d9508a1075810820340350 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 721148165 1250 721146915 721146917
    0x11b03120b0a06050a03020c0a05031c0509120708090102160f0e0901021303140a1203050708151f14030f180f0703030f031409160902120708040807150203060907 71
    0x4502c50800d40060810700900140c401019000602595551024081003103041c3e80103040320307110100d80040d5010b12508065840e002860030000810a020001c0c0c2d11050b0720400c580c45180c00126110141103a010209041c15440b91140300304d140d844050100b80200fa01e21500110142440202d1500b080050940c800310380c01801494440a640440c2800b01c3e9440f0320710400181c0760482083c1842d140c83c0014042042d6074a41080c07440d05500000d02c0346490b5520703054030b80d96082d070704d260b004203c07034107190000d034000c2200000c100c0460202c51003407014141580c00c5c603404569198180d104a904c150040c000d0003c1c8201c118540360303105a0205460090b0400d0840b0b94400b40e52840c1c24800a01004882c00c01c54040500035400300301c074a80384882141107484c101d0710450784e8038500b0035180c01c1c007084000009030b881281d1080c0c400c110590480d0302007a8a419804481d5114050000e44007548204800400903240440c0030341a41c1d14800701584038070b42401045649400240020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 721149415 1250 721148165 721148179
    0x50c070b0d06050312093001060e01080f0717010b0406032024090103140f01051203071e022e0306050a1d07020304050307030804150e0108040809011b03120b 69
    0x709101d6001025030b80b03982c60984203010701990350080b019444400d058040100100c0041f1510340c200c041d000170302070314003560f80030002c2d076a240400c5584400704501c2c280d41d904454020b11040508a82100507044060004290418050006400c42e160f40e401110102143d421580003150030002e418841d0b1011503104e16140000c0140c81e600f5000b0b0300c44683d46801c001403080c050f0303001c2d900c9410519140222484145007c0b00300f408803c5080c011035100d120044042d24034041c000003154260340c1d01c580d030300052012040c240501000700d40707001c07a84000346034017200c00399100b200e400c4c0c00040a0000001d1028901c500901140c0c01c52300841d0003490305100901c2040e4001070041d04142c5801c90714103080d9500b1a00320b04600860304200d0707060255070000001c2c000f0107800342007600c0d038000c4104031440e00e480083da01051420585808518500001008640d150007d00101803060620b0780100c21410010000c840805d07204902140002d50514002c15461240c030002d440b00341c400f1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 721150665 1250 721149415 721149433
    0x5010906021e0a0b010815011406070b090c0306041b0b040302010c020d0606090606020c12030304020a12030c06060608070e041a04020d060506070b070815060304060c050c070b0d060503 81
    0x25215520800c4101c0201450711904080072801c203c0030348001d030031051024155849254058175100011180c5400400b400c00106e140e0b20700c0d81d04809500c4000317090510342a880d40c0d0701104501c00a151500714003e4148007112900c090000744d10a038403d880004480304c001205881244041d009411401780620051005076045601052440d4040340c0341c4444a141e442d001d0701804458003d82c04260601000251981e00002d41c0040711500b120a100f804000d03420300c0c0c0d13503030104032006540b0106948040020144d42000301050600070301d000d000364200c503150a4192803c81e802080015591800c100103107900200d44039000908450600c070609070802d8080d02c0010f0042c4242c4242c2d400640d04106000c541d00100007060003030910780d200d1550341000042244100c54020100310b22000065400703401c0c040a080b1941d0081c401c1d0b00716121929040014201e6410040c28402c08001c4c54100000800c81e032801070606058083e52407a82688000030ba4105501650003a40300c078080c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 721151915 1250 721150665 721150667
    0x503120703021b0409050d0207050a0905040b0406020a11010216030e010302120106080c0417060609061203070609022e02010609021c0b04140f16110a030309020103110c03070b0105010906 82
    0x111006001244190144440c000000200280117014008145200f060b4003980085d8001c40d140c8115041118002840c9031340e00042c10540b2000c80e0010002b0404000203000552654040d0111100b58503110700c81950700d00c0300c20308aa1140d0550903480c8141c07401c0800f010f6010710b0540021a003880c09505000d489150305411900c1030260400348820500000c88800300a0305031802403990b5090070030140e4552035141d441d1141961186d000300241000640c3d5814401d04005000e017500b0000c600d804020f884640c0207101004003242c0c0315005110b51681c00303200441c10b824141451101c2c03880000a010061700b12101a40b04243c03580c010301c800a410050001c030010005000000410007840c16000a00200940490b00c1440d0341c044003841801c2110071120b0b48100a58100391944016188040c2c1e010141075480300c455a12806545c400248242c00c0b9800c2c852041c10040b82c10620004031590079006900044a5980081202e10502c044810b41500510082c01c01105407410070710 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 721153165 1250 721151915 721151923
    0x90a060513141305122a0f0a1209090c02010e15130f060905030310030311030f2208072c0702060708091c0e01231606060e090601050312070302 63
    0x11003000041001103414050120900c600b40e5942040c44200d41d9403102d00c03104102e003e4868600c60b5440c15200040d520710080052003487c460b00f004010f01d40c200040c0d55507a03400300c030600c40c10108819500005a20311260107214a16a19900040b0305080010803591130b003022111551180c1152009000c54800700c80300c00b20f0030303175000410469020f0660802d800540044240200a0711002040018a40c010059082aa4403d68802507100c0f1000c842590b280103050b8520f81e480700410400028400c20015402904000000c40d410156205e0075107041c004203510010080903483d184a081e4082c000e592000e00e13645480b0100241000c62001750748600040103178080c02550008943c0d000401c000300c5010030382c14120190030010340030005008a0400490b140481c0d01741c40c002e68807810718040186079100700b1042a050038103900d201520034052100a81d81a03a44070008079004e00ca05c1c220a00c180e039124010714141d450041030502d03000f030614204060708400c1c010500000c0e8045 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 721154415 1250 721153165 721153171
    0x801051c080f0d090c0e040506010902090310050103050c040608150708070c060519050106081b0a030b0a03060509070509010b09010c03142206020c010c0f050c090a06051314 76
    0x4840c0320001009252803240d92051a10850105070041581d414442c1590040c4c1203240c4181d000d070303400503500c800144807510b081c0d0780101545c2101005200d5840c0c41c1d8081e042e002c2005044580c80d81d119010741e81112001e801c1a100f50b0000e0310030185c2c60400e40540d00082c4040300042030400101802042d14920142c19501004069000719114034407503110201300383e802041c100024100b502513501400400501e50030303007506200c00016410f0040c42e45621800d800300d0b60000180381e00f9641d481560240100c0018982c1d6808405031949070001054080c40c85908006803504288010501d0082030703901c0544141d440c000180000d0141070300f80c070346081003828000b4440f00c0d43e28041c4c9160102d815070821181010550385440c00d40c04081c402c0c28505442d11813038854070741c007003240c0741c0e815484800c0c003254000036040c0c0065203103007034805142d00400a9420900d44800002d2450340191240c4c400c2070740301c40f02405280782098074213044285441080200052602c1c208004031001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 721155665 1250 721154415 721154449
    0x70f060909020f04080316060c0912030e13061e0504050705041202220207031709070e0c040806130308091f05100e0c2d3f07020607080105 61
    0x100c3c812007140e040c1001d80300901405010f50303407500e03449900f1609a01034800156245820601c0c2d4401326401001c074082a5088540c00c031401640c00d480603070b043e18681c9180c1b030b0000311f040c040f4036000c0c40501c580400f605081e29220360203014480c0707071005821703603420031445146010309000206070400d007210211000c0c3c0d100b1031418081c0d800000c0d0302088040c00140b014181240c1181207189550050042c06c0c4030340c40341e01107030040542d1002101d008440d80c40c072503807110000340031810482401e1584003142c824203601c0c143d11200303003600b03040c4140c500c2c0444000c0146603004043e007105200350321150150040103440c07103214101e035103990107503107000e2400d665030007240c2c44080b05d04451010b04200c8241e080907080c282105d049035801448100c400c040d40240003822201c0c000d04c0c4200b0612032420351810680d00c0c00e600300032070700076422250b051a0305030801121720044102d1070380c0030b40c07602400d07620b0b6180c00200030b4180360008240310104070802005100c2a640d2a00d0b1288502030303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 721156915 1250 721155665 721155667
    0x90503070b0a05251b061701050109050f03071e23010507030c02012322120b070918060603050c03280204030f14190c140d12090602070f06090902 64
    0x205130301e000d00514060009082410740e07842c04400441450010750464160395602004840e116001ca103c00d2402e0250b2400a150000c0402c46454090018224250004c041d28a207640e84c1b80390309400d8032100c46c08194041000001c0100da0040c2810003241754441c589003030103014150000300359209484000741070000210f440025a48a0701c00d81c100c0114480580c04c00240801421090f070b00b000d1003044140e800c418a070408100b03035960350380c1111aa01240200c9a0f442e6480902c0590010078000c204032400c100000c4010008100c116070445040002a00718100700000703003a110010003080d00c104041050000c2c0c3c06891824481e690381400701034000325200c4007040701070321450b40081c0c1030140c0e184c3d1223000d0040a80007443c040ba1450100c0300701700152440f410000c492150b01901c44901c440081024400c0500d860b0105000240790f020b01408941d5000c40c0b02d61034103415000915560002c0c01160b404019190261140d04603440c40d041c984640241f070788034980141c004407a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 721158165 1250 721156915 721156957
    0x915050604300b011806091d0c04090201050d0902030a052a01080601050306040c052a0d08010e16021002160302010b090108030f0f13080f010c0309170307110607090503070b0a05 78
    0x2100d41c1c04400a083e03012010b000c0c0340c1c8c500e1103140307004148a46801c0b0a005460100c2154601403089804095041e12243e06001103840c030240100004101a80c0500031100d010000403428040f10701403442407041e00c0240800c0340c0e88203100c3d2119000490501100c1402d01050303a0700882501c0c2d0180048402085802c62140c04039540d00502610410b402d54000c4400c00c0c0b02d000401c4040920150400c464250030009411603000e2402c0c031039490700c00341c05000701c0d87c0c420b0004000d00c040358050040340d4042102084080483c0c0c410004a07480f0070450240908041e420b01a60070b8005d011a40c0e01038035414051169104c0c8280c0c1c5a0607030b60300c000105d01e054000048241c1f480010021407042c2e10541e00c00750280c6a80c00a0104042940703071903980d040c418000e100b02030f0314541203055014101c4800350314108590015007803a040c000590746065180c04208101403207070a8556889030928a00b90601d403818403d5089130112140901850420300d5204044d10401c1110a500040c018 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 721159415 1250 721158165 721158209
    0x23190605060307030b1501031b09050d032304030209060306040308060609011b0501090c08071d0a1d01020c010f022d0403060f050610020d090915050604300b01 70
    0x100303551004010702c0c0340d85c0800c440c401d10012001c0e49802e0a8070240104c40ea070100c50b100742d094034280354005c00e00150b01444942005104044954404d040494000c944d900d0350030341c103120f4489403424030500000c0610446c205260016000300d0140d0052140c2e09103641e004d0545a0010011400f804010420a070242e105002d00c044e08008810704443c2d4030800d04225010b0440d0720825104001c00580c001682c00c00002c05c202106c080520130006410b4020380515807071005000c01c00e905454a06010050300542c10001203920320301c2c00141d641a015070014250b826152152403640c0c0f044c002010400c501c10304a94800540f009280c100c0120203442103454007035a000a8686450014416452450b6a10140c09407104491011224504100c1203a03a881101480b50018083c0c4908020744000c03074001d0b1404d0b10300301c0300d103100c040c1d00c07503021441325005a0301ca40d035180340c02c089c0c0d84c030105400b040d00c00d4002d911209225240344c0b591140360313903240107200d00003c00c280c0c6d00003031940c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 721160665 1250 721159415 721159423
    0x203090a030e0d1a09121c0507080411010302030712051302130c2703080a0c061103010302030a0308090120070b0f130b150402190905030d0f0509030c0904231906050603 74
    0x160448402103490340e1521580710900c4202c840d840070f00740d04d44008120305500483c0d001e0702c0bc550042c81140d00079010350045001c3c5d00b01601c0c68040c40341408a81c510304d006805030750f1091608079000446010780b8010010304143c04610008401d1600c44440b086030b0340b00c031100c40004000e40004e085c0000c40800110802050342c8043d00005003ca50001d107207520a550441c068014a000d00050148064640040c80288130017507040e8889415080024056211a58044285030000684030615101c107030803000002d504401118001803440d042000c0151a42e0b0003804c003100381c020600d40b00040c452200e215003c0507090402c2c1e800000e60101c1c04003556183c1c181c02802c2503442e8032608484100c203000c070a8500c0e001c201e5100011600341000a900900c0c3c1803d9500d00302610748038035047c1c0740360380001203c0c0e0b0140900b40c0081d0300c40e1034200701c4c01d004903c103241d002c14010100c494404242c906000100c00c6400c02d0190600d150095042602d00301d8000c140016540c4400c40006c1c90 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 721161915 1250 721160665 721160683
    0xc1606090213111810080a0e011508032a07050603101d010503061e070e0f120d2705130b030d080a0f020702150306010903060203090a030e0d1a09 64
    0x18250038000c502c3c009007040c01c06031002d600d80c030f409840d003041d11404105c40728400c254854000b074100d500080141040b03412401686c18820000969a4405c480c0c41107024034a03045225140c0c030006030180722004a01f41000c0314001e0014003140d085142a21648072170084c0f05441c0700303980100100d452800701110b80002411220251000b01e107180a1040e50b25009110700e910030b01400c3c0010b5003070444140951803a00300080b00303120a42e242e10301510320421200d9056005400d00c940ca01c9a038403220f03001008540d44100a012440c0803440c010105070100040503407144900f80b07540a8242d00c1481c0e413084d503404907585860088803481040007400e042c0201caa040c03240c010f80300404c582100000d4060000e80005001200324004001c0076441030102c025009050100d240341d0301c400640140d03811880524214018940da51500e4040e60030940300410140c12610b000410035400101000d00c0301019540a00a00d500303031912048005003417074100c15403121100040d0110021301000c1c403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 721163165 1250 721161915 721161949
    0x12140412020312070c02040501150c1b05030a0b0417070c03110f04092a030c0e13050618060a0603030e01080414072304090506010303050f0d0905030d050c16060902 72
    0x100c4d28002d81c000f003801102c20000e9000b1840e080011030300815804a01200300e2094403401c9181031180d8030f10040240b44124400240d54540740819169800d100344082540a450070804034246401d144403c9c1091135031a100c88141001a203001803041039004048030b80084030014170710131450100c0c00100002c50b5203035006107404c0c144801c00604010f103140c118170314640514043c0111100c1c3c0395440d89800054410141c0c40c0301001420f4440103039940c06109644005040c5da0302e9034601d840c010041e1107980c3d500f401d00c1e80b075040b1f80104210706544020b451000f80100c070310315200505509060703403869040000c03550000e000c1c480c0b680c021400d10002401101c600e207640d11040e01c45c4c0510355031040012943d180302e19406152a01421034807031740003000f4003820b0740386640640302940582e0b52010340d81014020000c03203400d43d1054070040b82c003401c041c6503500186581c40045800c01041e070b0f28601014000c1046104001d41135801056002c400041c02d080700d40002680b0341480c4403220 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 721164415 1250 721163165 721163197
    0x120703140307081b03060114070f080f03010321081503160b090909030a0203190e0612010e0702011b140403060c051c0204030f08090609030106080d121404120203 71
    0x60229888210030340320760f00d5005640c80c006480790009444e8801994040c7c009500e4140c0e440f02c001261004040e840d00c00d82c58103d86042d565510721031900242da00704103408010004000780240d40704180045c400303001c2201c0c00d511070860040c1100c4d10242001007003112584003c00b03d62401c01240c2d9000051040d00d0f0b4203140e9501c10a1f6031395010b403c0084c010180600400d41e0006d0000c15600c0c2c0c2c8000350061410303c05100001200262404040820080d202c8252a403907203801c001050804d403e407007041d08640c1089a416034030349001e011102107a1416801c600c03120722404940c3d414084a00e09020300c0e0081d405521543d0213031380c0024081500c3c2610702c4103a83d8101d4010700084007150200d0180314061427008080b8019844054200f4104c1842040044d12120081080100c010321f06030408180402180c02c440c856045000e5940c40b207400540310342d800890b0031400896543c01444001c1d2340c00300b510300100024100908484590a029500e18028419980ca07030345520003103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 721165665 1250 721164415 721164421
    0x1217070f0b090f21031515040609031e0f02150d1a1c0309050d030306030b040b040b01050a0f050907050408060709150318030c060f06030807060506010e031207031403 73
    0xa20b45a42d11503101d00300f2031094116021540300a60110b0304103050342400c090441d580d00101440b00380000c0c41480e408151200c4108040c410b0502500150185546003241300d829894044195201418580e651402c41d8015000080d65a110b00101c60750558458a100d182c40d000340c4003e016011200e140c8508021040d00070981088594040340c0d012104030417080c1d140c240440c00b6040000300500002c04035401071280707007040c50115400b00d20900e80010a169070303480e0030301c8410081e60708813032010056040c441804541d041e02e9000d8401212045042803405e1121140d14026203d028014854900000c00e40f6000d981590020000308082e960b9510740158010300814003402035035220003000d24040341041c841e200703030880c4242c040144541d01803130b0345050350308042524003100d00c0d944030401d0903400d4545000c0c660045207d80c1001d41c89103600e1800c281507a0006003240c4c10091400004042c039540042c00c211088104401c2c955120503d0404039004040102c1001c100a000024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 721166915 1250 721165665 721165681
    0x10e2d0a080f010501090507321902010c030b030d031109030604080705010c020304050a12060e010e0d0e090403091701021204030c0201020609060f27071409011217070f0b 75
    0x6a0741c42ea8514000810480c0c1c1ca40400c18101d55054603d440011008064448110161002140d2403009000040b20f803000350403002003c1d038080e110101407000780e03031816180ea42d024003520032080e5041c01c00f4400046c01001080e61010850b00002c10140c480d85405070042c0c015040320740e02c070b102806494091038103081112030b0740e00401f022102d030761808411f080018404804d4800341c80d0000c02c02c907002171030415001c0300203140420030b0b0317203855403034000a5401600344140c142e040001b03405446241d00740340d4040c044010b480d0025001c1c0d2400020000000c0d400141a001e603043d160021400e466042e480e680240645910410f00c96010303030500c400d064021000d06c80080c800d078200d0300c0c4c40c1e80d000c1c1c0107070b110b0b13105982d03c0444003c1d0501041a0044d030000400803108607142c076400c801e00c2004120300d00700941c0c2c840c40961010328505200b604001c401d560141000d0342404010520300da54400207007443e80c50300303008840d02090783c000f002980290035041d5600300035911401d0400c409 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 721168165 1250 721166915 721166923
    0xf0f0d1b02030307030203030910050f06040914060f011403070821130803090405010902071101030507023417190807050d11070f0308181c08040311010e2d0a08 70
    0xa542900d2b40320b01d00030110450760304c0c0a0684141d18804025646807500402d01010300010241200d800c9104080c0f26614031080042d80e204603050410b9013069450000c0d550003a042e00d41070079019800060040c0b01d403180000c2c50541c1d00649800c480c1c0c440c61074000d900d0113401164601812040031603c00030701c80304008050b15000c02d04032420803480e40d03146070240492080e07180042c40310340700c071007440302c01e6020303030700455000c0034a0051300c000c0c0c4800403c500c1140d41320f55900889130714000c0040510214048148040e2000101d49101d041599a041b50b903815045806008103090660190402c4004016285026440012641c10100000e4007501d40c00e5140d11401c49449950300010f41201e0900410040340e800100061a10001048041000c0348d1721000541001415034440c1100080c0200d501e5413600680320242c5070350652500c2c0d03841181d502c01c10380c1080301d2400304000c19a508100c03103150008007640c200000c0584c3c60840419220203070101d5101c0841c2c800020b40301e00100d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 721169415 1250 721168165 721168171
    0xf080c0f06010602010f0e0c0f060d060303080a0c0302030403140c0304180e010e030a050702122b020c0102011406060304050106080105090f1218060703091e06020f0f0d1b0203030703020303 83
    0xa0000e1120005000b03046c402c07110400d00090141c0d0080c0c4070444681001c1100d00c0c500c2c14081c1c80c0d03a02d417500a03045030058513040c0c1c1c03040340001c2a61b020000e100200c0c1c40395801d501c40c4d40c81c0039031031401c00c8d40b4002e014024408550403c0c0d078000520114000080044030020f041822241800340102c6140c50004d000580d18482c2a5082c070950020310407010044996040305511500d041007002d07000d00c00000302e040c61003125446405075a89001104000415003c0c11030761401505200090000f0b0034030203400000c9065a040c940500160042c03c5d0311580c1c80b410603207602c1c0d1a0340d074600b061405001c00e47c0c40801036500c0d25040c41901400400c0c0480c0c0e642c544000c07900304c0c10448441c82c1441c840e810418100800c0c402c02683c0c01d18041c0001c0c5165806071410810a41e103446c0204a0380282184089001503c14001c216890b0140f01401c014640200906038610900c030f81661504c0c40c290030345e07041040c00d03581c00721031420039110552401d4000c0c00300c989030701851901940c0c81e8029 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 721170665 1250 721169415 721169417
    0xa03121b122007090c050702120c0a14100c02030102190f020717071703040803030c040905160c023d08100810110906131415070f080c0f060106 63
    0x50345090851040d00b40c041101c80300060080c10300615091041c8003c02d60745540c101080340030851640580e03600140d0036806210040139041d05c1e21a8001c00110342140e512020304190b038548450300d40d903100d45004618030180d042400399410300e1310009009205d0758007091003420001428013002607025429544550454088a12103521703a1100008540520102182e5501c008028805051a03c030040611004031084a0509844122484c1140c000711002c1100d00004901001140302a0044541212824140f020206842d481c01429450441c1000e0301176580c031254068400c4001010246900c40c0c01810b5048100080000c1c280b4545043d1003c00900c54001040440c4510381540d400c6840c500018503204800d07501d08801750240d0703240854a00004c0c0710181c03040e101c00004244120b0745100c1d0300c1c0a41d0804d5a01f52141d08000321403405481e032507005400c80c4441c4030485030aa508540350100100f441c1c40c06021510684042c1c0010f4024401c280035108800100c080c140d07112 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 721171915 1250 721170665 721170677
    0x70c061b090501030e03040305060112051606050a0f05090f1504091404140d1e02030f0414120d0c35030115020309060301090b0409050d021510050a03121b12 69
    0x45e00000903a03c0c01140000342144d0405c000421520010206414040f446801a18039504d01c1041458070b580650707100802060700094803e078216401030003c01800703514101681001248400f00d84c8103c0140d062a0040502c8502c0280700c00d0160242ca00502c6102000d000310702c0c0002500f2200c80e0282c4048031787c0c40b004181015034100101e800c0c030004060343d07684100b036544100c00368000782001c0c15960660000704404549408140020000303012520075042c40540804107100309001c8001e00c0e5940c64101e00d43d40d03042c0c9681303d01c04158042c0c1040301d840e451442003000740381000644105807400c00c20580041502c0650710003541c12030706440a002190202098140c4e2244590380c000c41d400303041003006210082d0503501100300c9c000301510006952080340c2e0b44618169008039100e01580c040301600000100c0000803650111801c488960031500d0b00d0080350810079076000c0104104480d4039250080e45c41000b010b40619030a0240005814660800f681d6001512002c0400121 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 721173165 1250 721171915 721171931
    0x703091106030f060904030c0611031801050c0a0e01020c03070f17010c0f030921181410050331020a211103101505100c0803070c061b09050103 63
    0x1e8028162441482c40c4140203d00395107100c10042c01c000010411014004003004200219000f84203804401000c4d01009a1741d05010000311032606c500000807402c1e0f03050004002180840000366040d40d01c0b6810b08070450210030005030f003420030180101e074041c400c0010004080c40c0c41102801100d1380520000c0c24201c4640c0c030036003660760408428000c140c50080e40c0c40b9040c03195000d00c4246000781c0406281d5030110807841454500001c100000405c07a00e2800400500e45505000900300c011141c0d110a18402c04120954403150303071402400b0002c0006601c14140484000c1161081c000c0c0380102541c4401044200118241c1a40240021303100410540c420060040c42c00310401800e100e580b80c44da8543c8142c407400e421082c1c0501804600d00f0700d920003030040c3c20007000c0d80020f02a07403904200034440c99140c0e10464004008422000308040f030441c204483d040107003441d140540a00703900308030024040280c1401d038491030100c080781d40d0b070380e20001030015203000b43e9003403085c04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 721174415 1250 721173165 721173169
    0x1e0e0a0516020d080601080408070f140c03010b030c12010e0a0f05150105012f15041e0b0703050a0b2805060414040207110613080f0d140a1707030911 66
    0x1019a0580101140000c40885c8156001d0340e005a88103210303803511840c15003075564441d208030158030125000309895a6000c071591041c0441041c24070141d00070403050441b1000a6a580f0055501c0e134001d0ba00314803002d142d03c43c03c0d00000f41454189003107070404584c1c2d15041180b806000c0c1c041d940b90003428450810940c811031418100c2d141695140000207230140b14032000c7c8000700080f03d1409011896401c2100f090004e02e40141c070501d000c415a00d0142003007400231081800c080a00d0381207000000005654641680d000782c01c900d0005090f50b00c025050000302407003112594881490840b109410a9001f14421440a40750000070800d03524810300c515801203001c3c880d00030100d4242480d103030815602510406e4081c00d1031003880b11846004c0790f4030b0b6102103542405104040d0051107454030405c403ca110001150041030805034910700140300d400e41c000c400018040018402520510620007141007410000a016030303070030403040180047c0000001200d6201e04000d007d0018 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 721175665 1250 721174415 721174423
    0x31e0409140f0c0a1205010906231011070e040609060e0a03021002092209051903020705040c0e04140138130f0306050f18071e0e0a051602 61
    0x101c0b1080c0c800d0140d5190506058903540140c80418100000e55800e94000a41c6020b124000c00500f40e0018030355007801d0000e5040744210600c030701c9a100000c0015090b4031821010b2304022a1483e281c040c8021445506007040707a207501801c100c1c84108188018881c240c0c0c003010300c040c401d110070441c00100000e4a52a00e0341400f014000da0488100c04d0b60f4802d068004048440b8010700300003400c101c424011001070700900e214940d0560f0703a00300d03404004041014100c900f8452800c1128454583c0e0020341e0f8001d1801498001d035102e24800000c9801903c1c0b21003031542c001d10038048100e801070080c040031002d02c82c80e05408100500e039401c074210200c21000041340d10107520000d18444191122950200c034000340411510400090070000d050014005907101d518082210304006000000d03440011340303200c5a49900c428800106480020048200d90f504c1c418000601d002c0142868440d05035840456801303140c0d4104682030a0365803106210781402802042c6041c00442c080b42c0d9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 721176915 1250 721175665 721175671
    0xb010f020703021e0301090f0303050912090f060c15071e020303010b0309030c0a2405271e01060e010b340c030b04031d01020c12031e040914 62
    0x941c0103900180094200340c401a010ba9540120b00020311490101103821208201001e40d42800c0d01c050f20800c041d13140c0a03d0307030040d40501c0100100f0b40340a090f4035175449800003541c40341d0003020719441141ca03107009450741e184448094400d00d104242c1400c000b04030072644100010700c05441032010f01c0d042042c0000000341c59000b107066a0074900051400e600c054040311091000f440800c00c0108100281c442962040310704018500005c8000300e542a10246001d0300c081c03c10701000070050030205c65604c0f03000240c00910780c4031380340d818480c14404800c1900e02000403045210346e07180d00540081040750a5100803609580e070b5030175018400d00520040b90f550500d55143d000c070105d2420544d20440448010b421418001c1e40e50340840c08825900031100f00a00304100003c2c50b4000c030540d40c4000b00b0700b841044e1a0034010000b5259003420000300c4c411200b00d501d0108900c1c1c10002e84000810924040800d441c010704802e40d50381003880f400c5040c0c0d0074185071914504002c540540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 721178165 1250 721176915 721176917
    0xf02040e070e1c08032a1b01090506090703120206040809010804020f061801121104030f0309240e0a0e010614190e1e1807050d110408011410030b060a090606080a0b010f 74
    0x10800c107d00f19100402003664010118135034131401c1c2040411400d10607103028102c90f000038080e261a51070004800c240e403200030400d641046082001040700b03c000c030b4242420900c0d000800c1c0e941c910001d81500c40740d42001381c01600c08500302c6d03a42c425410409603084001d8071108e290f039107058140425142504c00020080400380803c00c00901c40442c00c501c06442410840300c5551110215080810198030840008094260000d40a80c00180984e1641030a0b14083c14407810100103041192040c8640320412000840090700601c01700c041d0781c1200c2d070250150131420070b400401460000e40c214418481c041c60034240b0f40c8000702422b41e490a440150946041036201400c010030100f0080c050014000108480c22140903184200c045100034650940d4030307503091102d9142160400c0c0490f512600030710041c8000d10080000c0001180d80c04032800329150740e0718001c01c60048040e40102007543c1000c00119441d03400030390a620502c000c400802032120b50340300445101e4483d0004c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 721179415 1250 721178165 721178167
    0x11506030e1510140112050a051005090f150103020f0714150f07050921010509070b0708040513090b0a02070618210207080a150f02040e070e1c08032a 66
    0x2003032040008030b1030413020505004400050031129202035440403240408010380d50703000c2041070741818071000090030301a07490b841503203010031843d1500000a41041c124910300e981480103a84240c04840300d9021241c06503440318100e1400416450400310384810b640600d0407900520900c05d0303001841440b480200203d2500c900f401070720240c1c8060081600251015010b8500d21600304203141d90602140000400b8030f44800480e05100b42900f00e4403010a0410410000c2000441900d05484044941440e1118030548070300040880d21801007642d50040704000510200c1d03800307000c0c4031b03001c2e407003d01a81da40c41c0c90200006250110041040d491101041c43c1c1c2466a84c501410640c036004036094603480700411854400da502c812140c8281d60f4000b5170042d903003405110034080c040003065041908001426a8030007004240604006150800b40f100365140f8008425400b00c1316020070701d003115400c2006c1c55500485070003140d00c513800000d482d00004448511902e4555000796 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 721180665 1250 721179415 721179419
    0xc130e01200403031809021611010203090d061107050f0f010f06050a09020703030f0e010b01031107110d030507120903110312031311040e06072a060509011506030e1510 74
    0x30746940341a072400d291605042c5c0c6000c98101c10b184000e007040305099404c05440242c41c58460982851080e955046402c24840d05036180c40e940e224445140d0b01c40f80100340c00c40700c905440c802c1d010b000c00242161140c0d9007110403641010541d03010303200809009000003c42100e82400307039802c0340b203841e41284220b41c0820441d4801c5d40540540340c42450082540340c0c4010f0303031000351216402c0500059541d14900380184d0b07014407407000c1d0043e0901c00f0341d040070f000d5100c408004820901031401420b0500031401018800c40c12101f0040c2e01022200800140342001040c0e8101d5020031500c07010328076407890246c81c0c0005c200101d0309500030000e16580c1c0394004c0c40c4aa10310000d040381c030300c0505c0c0441c45c11a5620701805120046c10001059540ba00079001800110b41c03021103034403c850341c0340d000b8081c00d00b8170780d030481140c01c06e4000c0364a8941c40794003801088000040201c011807060041400d560641100c95140502c00c101d508071031103031080200700c0b2000c0c0c41e12421842401c1003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 721181915 1250 721180665 721180667
    0x2030f0708061b090a03080310050910120302151006080106030e0601170a02030f0c0906091509060f0d050a12020102160f05010612060b1005031302010305090c130e0120040303 77
    0x34524407503000070f41d1203041c0007502002c00c4c1c41c0ca0040c1c02c04c6a41c040c01008105080e150410b400e4014030040320603400d103041c01616000a0354580c069008000c0d07030a1240c4040c94020000c0981100c0303014130400c6c4901e400b000c245c2c46c88003140520400142101c0001032142c0c464006e0083c940160310180101d13901c0d0440e07010581603401c031603026500410721410702580c2d00f030081026141940c0042c040101409041190001c1c0051019100d0000c80050010001c0030701d0100e4034406042d681104191504000164885550742c88a6130020300000b5540400402081c48409544100c22a42c0100082c240980c01e03405090780c7c0c0b0a0394040c061320100800d038040c14034043c0c075014a0000901d1500c84540744002c81400d001501d03080d8030f40141c446541803942c07815001202ca4a050760039801c0103a100e400070366030020060704058859010450300c0c0018440b10364031090042c9501102d50340d1000c800042c0c80959803110640d4602040349002c0c0c0003480b044944044202070007071405007943c3e4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 721183165 1250 721181915 721181941
    0x40909060f1a0f0112020c1c0f020a0b04020a03150219110c1302040b0c0d0912112806020d02010513080f03040305160c210803060607060207021c02030f070806 70
    0x455241000701d00c08a85c60000c43c0b40c4000e01d283c89400014082542d0400315400030301900500308800c2000c2c10400e0300f1500d41c041a81c82c12a030340a118116580c03200c1c000030b90181255040035108100706c03d1a00b100d001c15034024907841101c00c1c607040900140c40c40c182d400e528020b00c1d00c102608a00e5602071a86400c42c07400c0100300d0388840050a00ba21001050519040410100190303441381c0f6400c1103490f04955124024040744545043c010403550710480030000003079505002d00040c644804914200e036072804502079140030300e109041e0ba55400296510000542c0300099481c0c02d0110316040c5c01500c42041c0244c001c1541c80c80c040700090042025403008006408100060103000c4094900c1223950362450302941040703150342d08001901d59216404c0c544000c41080e80c069000005203418182e0340d02c03c400f01c1c0c02e1b5031500540d0510002900c22800000c2d8000c00680400d4845019010b42d050300f940250100c0312a60315440d4129510510b034028192a980664001801020614 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 721184415 1250 721183165 721183189
    0xe09010b0f070c1413110f0a0e090703060501090e0f0f0705160b18011a0609010504080102130e0618160c020d0b090f030405060f0f0f040909060f1a 65
    0x2070030701e1404010343c80d4140c1015140e0010401101c408030a04018540b045000e0041140c141042108032136807030742001d82d40300e904000418510085000c14415000d03042365048168040c001c40c40a00e0701d0381004000304003a02509000c1044050003080d09400030841074400d44040000b4001902c40981421b01d09a00503c840c013084010030210401d5882c04051111082c130682c11908141010404c00f00440c211098040e51030b07152000102100315001c2e02c20f285020192441076840c20b020780101c400e0300c1a90030508a96000281203d42448151070345003c4521940b03a280c402c1e140c8104001aa9100200d04422a1030030000726085403a0000641e0030010726080c024078401071a07010500f0440300390747c1a100c00b124001003000c000c3d01806983c10004142003c2c2d40340030704010004220340504c1c4586980034101041e148880d6400c0000c4641c0c1900c201c040d59151580c640b40c41c4060000c04008448140c14a44d000c03044000c54020000960101540b41c01d02001d050184650b0400c90 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 721185665 1250 721184415 721184437
    0x5090a020313021009060e09041a0403360603050702060703110910020f07081626010207051e011505061809130201030b100504030803090a02060406030504120e09010b 73
    0x2007540000681e04d80b00d0300410b042c000d403120780c1c2042c5040344c0070f41448035035036001b40100900c80800c0300255044218000c0080c0052050f0707601d485074201211146d0850315102e1036030422020508505900f0040100700b0b2034540724030214a501e40000b10269242621f046001da4480030201e2810760082e04450000441481150700380b040070f5000684004c103510342d500150f0806035814005200912100025000c40c0000380044424038081e1a41c1d100103114007108480c42e008082805a002c030a65080307210804001c0d17498002c2c9080c0745480391031021a100b07440b05191130307544413004103008600c8100d03031340c20150f6642483d04092200c40d03401205020f1040d6681109210641e480209050107061745484061a4195520001d001c0b00e48654001e0320450200b0380b840b240b164000c00302c0e0180c0b58010304d00b50300c4e070301c4043c0140e00c0c02e40e079040c00030760081020a010454a5160380440d101c0d60050700c059000d59407100c400da0300301c1007001540750461600001400100000c0005007401092 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 721186915 1250 721185665 721185691
    0x80106120b06030c3c1308010e0705030d09180207020105090d11040b150703030e0f030c01051e1e09070906140901060503090c040506120d020607140405090a0203 71
    0x1030710001042640101c035081134902000c20045072601c2c1888144d01949250407841c0081d210701440290a9408000c0c0043c0c6481e000450002001d454506000200f0011009100814070843c009403200380c0c81c02424024841c5030404c0008a2180c840c0000700c90440780d14044410701071007088081e44c0103440a0341480b404104844160303d6007204940078600520b90790b00001d00c0c400800052b182d0003c1494840d110a0300841c040041d0101150409a80b50130005901c90154402030306181c2031400c180c0e03040c01b01164800020300103401c00d5115003400c070815900c0724101c81e0503913864502512180e003146844c1d0104404d510030f40303850540100d1142e04071140f082c2d64a4110040e20600e4100907000d088030b1541d8076060034180c8c4210302419081c2000350442c17408203081070b0b5988101414522454490002c00c103d074480808607421501c6130300545408906860f40a581c2d02c506540440000b15010b8200c001da05440041e42d080d5180107000a00e0360300c4203140035002e504040c041ca40d02c522 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 721188165 1250 721186915 721186931
    0x1090c0f02032b060312020d020106090b010206010509040203010608060f04020109050109030302150c13090f0507020c1e060708030a02090a05060301120b0c0d060305062a09102a050c040c08010612 86
    0x80a0601006c05240d680101540c010b0035200074203446051303000018083c28002e03548002d81e004940c3d035043d50400c1d541c0c160070760369070f00001e8050300e050b03441010036000750340611181d520285203281c0303d80d000f0789541c80035a0b903e00044401403410300c40900107030030600461007481c404c820380c40d0300b1428200348030b070401840301c80c0b050403071200d58400020036542e10902c45c07560b080360040d568055902c5c0050100c0d40404800b04034009143d0038240b06150070068036a55503034691050b6600e45400004190b12860300b140b001000358402100c40384203080d400270000f035034034001c411681a00c46e000300050f1485419601e0340724204000e4819401030405103e2420364144500c01c0a00940c003480081c03146051010030021941784248410000003000c0c1070311644000c0345011560140019190400b8201d0008000c85d00001c40440f180070403000801c6a4446232129541207001c1c50084081c4d905a500b090100012221072900c0035020402c45001004a9405200503d0780d81c2801e401c0400c5840e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 721189415 1250 721188165 721188173
    0x1119020d1b080c190614071a010f330c020a081006150f0203070336150201050f01030f0c080f03031005120c041d030301090c0f02032b0603 61
    0x801c0e1500300800c01d5100382041007091510302030f80f9003004401e0000d40e4001c0d09141e401043d11210003e040c20020780040d0400030000054003607000c135030200c0300b562441d503140c03102aa54110b0b40c9c070680a031031100c03640d1550001c1039412400c81703100a100d000640c0021074201070f152100350390004d9901046440d00054501d005206c4905440ea070381c0e4001881908001945c8142141101e0402c00c0142d04102c1064050b000021181c900380c144c00d021441d20340401c2c0a941c054024910b540303525500300701c03031080940340340040f50995400880c000c00ea854024000c07422904110f030307111010605080104049081603110b00708650042914101c540e803030b01c0313500f031034170514000240156100204110041602a070441d000d4842150a08070b50191034100c04d681c0c9035032848051065a45018080d4004500b4983d852004090b000f6a5260360f940c1d08100d004010403215000030618941130036910b103101108440c0401c412240780100c50300c100300280800310500c0104442c80342c0c1c43d04044081 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 721190665 1250 721189415 721189463
    0x20a0204050c2502030105180607210e0a06050606090a0b0307030e0f030a0806010906120e012c01060b090a0306090807060f0c090602120901050c0a0b010b07031119020d 74
    0x1000f1000c8180c58804060300c10b2500b15040181a121040300740110307004218408940560410058a0310f10f034417100368920010062841d48610007c10302d00300c0d5440402c04041144a90140150000c00c01c95840000b441040d1140d001c18513848110b606041c45002d80040146400c11090301c2d00003450b10150340103503d030502981e03040c0c2e03581d48003003101c2c452994018078450740170344217182226040d442d182c005041d10118a550b91001034031034a007135409500962012620301000c4030706040e600c100b00c6205000601c241102e03a099420b003c0d0105100780e04408545030030001604620000f86541c44140092501c004112081d20041082c900824424003504890308001d030b034000303194522161b000d402c078151680840259084880701c2c9642090381c100b40c0301c000b0801e0a11a9540074001007560800000c68801801142c00c0e0001180403001d203c043c02e20503200343c440b401c41c402c404540f55a145000342ea1141148150304086006040294080131038621982d03140108003c90408144c0f0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 721191915 1250 721190665 721190707
    0x1205010f050c0c0606011b06020a111606020c060705120a0909091202011815200304060e06130b0c0d0209040603060b01030b0405040b060105090a081204180c020a0204050c 75
    0xb1548010401c00d421510074080b07180c102c4400d082c2a40b50080040c3c0740c041c1c42c065400007400c003560209080503468000c9038240c1c0d074500d200059882584192000d529480100e0203030b60010300c42d524030680c0a05080c01110502da0708540280b02400001078907039482d50120701910200100c811000800007541c0c0607902c007482c41104600401c00715214000d0850b642c0c880d6641000841903000b0010a000810325810141400d0000c1810144000f52022441d9a00c0c0049480c020004c2000107021050f44104090740c6090140d58050700e8081e0b0161804c0a1a403001e000d20302d1140208900b02910300040021560b00c16002d401e28419600080484010382e01c2039803415145c4210b02415a03040c81745250307a820480703081015041c981c0724840b00e0000207220038144280000c40780761a944841100000781a0b00c000c4030200e0441c90f00700790751500140b184500f01780ca101030000800c1014099200824029030092417010f0076502084040c00015100d50b1032100104580001e2560032102e200f0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 721193165 1250 721191915 721191931
    0x18190b1b0706091401020703270506070c080d021f051012110f0a14060901030b030a06150e0702061303030f060b0301030c0b0a052209050726101205010f05 68
    0x1880e40c0c52410099a20b80c21130101c8130283e44100001e10020b81c00c484154070315000e2070100200b03050401d00c2c5415002c41500301983c00b520101d045010418000d50140544020700701b030b2030784110a584282c4c0e0347e05005400c0f404804c1c194a8030200701c0c40e1a481164020600d240c410031481e55a5241054120094070035107105075108400e04003170030301607189009000c4c10b456659049141100700c0311099514800f15129071000103100d03041c0c0c0e20030307041403142ca00000c040c0c0d4110107040c907100000b80804010380c404840c2820001035200c0c1d41c1c120241c4184c030310703801404a40d661401018802014264120141036440f0402220b103c2148503270070150001200042d45e035410340c2441200100320b0343c80f560344500b04201e44188550b02c0403e450794104d40300e901d102506012410080b580e001c41d00040c40d502d00c4d240401840c11b50118004402d00c00040e10b02e481c1459100cbe14941d06001291f01060b40b00600c4410000c101e04d0020740800c940c0104000507403840be5100e582d040d200306503000710b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 721194415 1250 721193165 721193171
    0xc1608030a02070501180902090f04110a080903132106020f0c01050c090d0b19050a09030e01030b03060105130905030a23040e07050304150c0818190b1b0706 69
    0x3070340650100304040181c042420030403040e101201d1429201c4499000310300065402040403582610350f54000149450010010305c00c0c0700742001003011380e4000b04414800a003a480102e445644080211011740c031244000f80300307003802c104040c40d03039455101d001105d5450741540100030030070a102a24526505c1100d060703540ca0749205e13050075548003415515100e0001c000442c0700c1d0769003410883c0c2803940b0101c900c0266441440e000310243d585442251a142010f04000c060074041d808a0003981c825210107881e00c000500450407906803a8001c3d80641c4040c006001e14944a0310082c00100001400b107004070140e565107081d80c1002150101281c129880c0c1041c441042c942c40b04503403100c00d54141858030f4041501c05e5018060182c00030321100102040512000385031035889804036120074052440d00030002451484101d401422a102900c403a44418002242402600b0041451420b00e8940d64442110800015001c18104600d81240e035941003003070f0000e0300005e40201d13400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 721195665 1250 721194415 721194427
    0x50414130911010f0e1807090f090606030c030533060d0b031515061809040c09060909050c040b01031805030702010306140306180f01110304020301060f0302010807050c160803 77
    0x2510004c00c00c4141000e1080c20426041182c0b12803003d07000a50b1a2940300003507403603444050b00c5000302604071300e880c6d0080e204081450f07200e58218900b16100c50b41c08100380d020040381142221419075044080503110f8090b00f90f80b00102130500f45c00d0324461501c1860120f00c0300015000d501c014600244141c03030b000d0032011440c0a000040c2485829900c1107154a00400210110ba072242001c600c104030200e6441c4078203028840115000402034102c00042c10542040b403050401442a100b20b242004404280010305014a01d00d141d0b02070001c002240e007040030030028083c60140d0314101503030f5010203204840040c2d034078404240150081c40d600d613010300004003a030310b45800400b007045000d0000b18460f1000610b40c0d42c04891640391807131485907008100d06124225100714115800c1992a500c8000110300440c02544214000c101ea141c0d1000000c9554110b40f10103800700f0884400103039050f004000905214142c00240c602080c6448805179450302c5603044220760383d0000c85e103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 721196915 1250 721195665 721195667
    0xe0120010f0e01020a0f261e10050a0e0c0d020a0f0f0507021c052514180c0c07050301021602010f0309020303220801020c150705040605041413091101 66
    0x1081a2542d0100c002d6103010b401c2c4402809800c4030122560400c00201e203041030a07007045a841008904032103900707510381804a41000110f501c569000701c42014480490740e01100c010b00030003190b0000c0d14000c1c07818585012041410b400500071001400104007200030840c03648001c041a00f0a602c0e0340041c0121014005d00d1000d28030080750501008000700b8015945581d0411485c079005041b04600111a18055040060700408040d101049030341c0611800c007594002829208106c03140000440107100704840d004004160010341082c44c1e0108030b0b00058480207101040705103040307422599440011a0072079010710799200c803c40104248200310740e8400b1801e85010900e00e411f000541e09500080e072244200803403030115490402456400443c0d52500e00004c0000c040215100d80e009840b044c0c032485e50a0310904203000c00000550f8071400740c01a82d041c1c5d000f030b968490070b00741800d2341205045046110154000702100c4102200f503800d0082906840c450b4022000c80600b50780 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 721198165 1250 721196915 721196921
    0x102070e071b050a03180f030f06020c0322080c010201060f17031605010207030314040515100e09100608030f040b0a03020705030d1e0b0108040f110d080309060106140a0e0120010f 79
    0x44803900321f06a02e0100082140c40f4200c1c0e02c29a0813100c0146c1c5d03050380310000c601e90f2044211400410011900c0500d110306003a50f18001c82d0104410303520010800c8004900f02c0f1101d0090b0942d4600c10030007848640d0210324400b00000780c01b4216882d00009005401b00d148140c0303c1100d26a40004103501007503030500550a0300c164400210403e8145a540c2d551100b034501170121060b5401400a182c50720100c5500004000c113a0a411450030a455a15100c602141642c101903050840c0081d4588002041f20381d50200c2480a50426080c00780e01905030344190660402c1540038840c81001c02c0c0c1c1800148030800d40d043c4001118250120401d0001c2e440d007051b060103903e0700704480300d2a40c0244003030754050340c0240c111110070b407680750000e03200b42d134500d1071038105642010550421844c04002d5014112500441740b090780e944c4800c03611441020841060030009102c052038460042401301138200f0305040021400ca2340242140c9540c1602d0a181550380d1150103031a402d407d188 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 721199415 1250 721198165 721198169
    0xc03240c170403030b06040911070218041e03030f050109090201090b0306030307030509210a0302070e040c050603091011180301060518091504030806030c0102070e071b050a0318 78
    0x1050801400c1001e40100d4010341000340050103140d1649205450769070f40c0d50840d80900036501c8108001001000ea1440b1900007180032809070794050703281d1f981018403100ca14804d962150b52158030121080594005402c0c80da021010b040c1c41d8180444160228060036020707001c1080c0c00038104440f40001480013003160b001c00c40100040045c824251008070071a075102d500b606095030f568094101041001c0e807504050400c0c8000c1168144603070002051085036140a40d088607201a16401c0880d45044250342c02480012008010002420b0a10103150301001d000b084d0f075618280942c0301015540e48030035070b140d84040010714003021038043d40c030114001ca00350000c0003070700d04140128411031b03106a07442030844031003c0040c200100810006c000003801c2c40c40a1703c03d003058900603200390703030a440084c402e003e1611800c1241d440002c0140c00c980031100d00689640b43c0d80015030342456480710340344640c6242c020803400700718204001c01e0014440c0d41c0750012001865052130340b1507899 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 721200665 1250 721199415 721199417
    0x61d1207090207050703081210170706121401030311010e01050609060402070c1d0a06060c0b06100201060e0112030806030d2a06230603190f0c03240c 66
    0x20000544800200045020655161240040e511401070800d0351614030180c0c0000c00f80c01000030840a000783d007100c4140500505011323503200d41c2d1158140400d10103042070506859004180400102d403040e030f0746050221494900140c0411003001155184034240c10a40c0800e4076a6502a80040309104240050702e40500030045810868002401c00b00050705452050750041150014841a4150b200082c4422205480e50f030360080d0441a5081c5d0466401010034600a070020b111070007050005003459020b100c1d240c5a96608040100302101c150400e4210340da0f4500100b03034103014007940340c040c1ca4203030601e50390201d0341c0c50002c05482c1b00501c1a8001d07005101c049030003d800040d0500d03030300c6400c0c0000784d0011104002c82803164001038098a03040c10183c101085040d43c440e0404140600c80c04e40c15556201c00c1803581d1800301e100d0010007058802008004500110076410415110f450001c000c07550701d0b164500502000b00c0605500f504848a699a0200b588036150b114492 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 721201915 1250 721200665 721200679
    0xe0703020f01020d17091515150a080f1f03050f010c020f07030609050c1c0204050a2706110705030a030c02120a27120b0a1b11010b04020301061d 64
    0x40041c008000c5c489460083c0310b25402d490102d16420028004002c0e050710104074003030289005000d04a0010200e403410f401401d260080d9001b64808100310351321a078650703d5070062500c1d040d4000e259014000e02c551180800c5503e0700e0084000500d641c2d0007140902d00078050043c04181040c00c48001003109420743d0720101d44481d403281c02140e14400c0340e03081500019841210300b415810a19031000741179004260300805880e5420401e034200e1902e00030345007000a40d40b1011100c044800304e0308448105141500225a40150009030000c02c600c0b500c40883d4030007901c20058039079084100704852640011810210180d81071052140c40f1446100404074059425050140c1e0700c07451140380d0800c400d84003680c2103104081c40306400501041a05035080e0342c3c039001c100040124000440c1c2d500b00c02d4005c03841141190040ba0030f402d02521a0b01800311001e0001c2e00c0c143c80c8201044119521880041d45c04e54039440514028040c0d40ca0700c440412000b02d401c803800c01c82201c990300c0380c21 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 721203165 1250 721201915 721201933
    0x8060c0d1503030806012d0804060c08071e05070204050a06031a0c0708030a0b0d06020a030e0718020a09031406060a08030a0e0f060705100e0f0712080306130e0703020f0102 76
    0x644481c04a80000b806c0c20200e682c000000840c8841007100e203421f4541d0101c60110211701a88220aa071040c0c2c0a0107041000f02c54010040314118015501c0000103109582034058441c640480d040410f46141003a501c1d200059001c02c060b25411201136110550340c030802c0092204ca032424000c1058400640c0a0b1450700080c0203a51b40901c0340c000d08452008000190324800a5116808291004025560b11a1245003820180d8064400e80d40000c1c10200d0a6840500c0015000d0030340e00046000c1c200000b141032184000d402008000040000c510000000f0036500100120072400c0800a0500c40c94008280178102c98268450b49056000f04181015507910480740034100900700c400c180980c0700980012002e001c0c0e020050014040c05070608041d00e0203074018003c004025007660311520701000b200351695090310582c0c00150359000c0040c00141441c0045a1040001f0849a481ca092900380f20454551202c415825030210b5070500031341c030b070181c852441c2880910007822160 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 721204415 1250 721203165 721203167
    0x819030206070806040b061b0d1812050c060a0e042007020907021e0c0a050d0b151914150408070509040f08030403180f0b1602010908060c0d150303 65
    0x1c98010100c80030000070300040f40141d41d42d46c0003812184802000c0585a500101c0341c1000d48200018140c294840d0001200425010b00d401a041c00e81c3d420840805074901000080c03076448d02c090856142c02007000c2d0740310541e19a00501410011980c584e0707100b41041c1c00748811917440318060041c1d0400103041e55010003074902150100c070341c117071810b03112a02d840c0d109034944a040e045410100e1015481003100303041c0054030804400e01219500c508a075105c2c2070044842042c0c4000d04141e1480d4001061050b041110149112014105800c1446810100c0e11002a243c00c00401840c4080d03c62126141c103001002c42c202c03101340c04a00d0140340a03420303540c0e0580b0f0b1040c1401460340f0030024040c040700019400350160000c1c0199500d02d42890014034040310700b6140305d03c0700f01c08d2402050070343c400060a000d07900300124040c54400c41c10441124401d524074100d0400c1407420300801c050ba007c0c04068080e02641c03212a40321000e910401094901009a815040013480340400110b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 721205665 1250 721204415 721204423
    0x1906090314030f2a1e06010e090a020904050c0306070306081516030903090b16030f030509060622111812030403060209131a040e03090f0907090e0c0408190302 70
    0x80c44414041381400510710751590140003840740c010107140140c2030030107400c496180d00b81c07107185100340545005a0b241e1660120100d400d592140315540a05005401402c02c6800d0302e410601840c100c034200c1080c0000a45132001c12920742001a441d1841008421002c20006499282c031020703000d018649004160480707c46400d0200405449901600905008054280c060700c0d0400c1c0e007503929105118554418001000110000740314901c9150700d5a00c0381c13248170300841c4620302904850326041d040010040c00b900302a142032109620712222142a445094441e80100501a46a0100c000740c402049480140c0710b02801d00c0a0101c44800300201c100e034243da60061300180c03110700c03070000b05904216442690403a503182c040103034000f0003402902888001d08841c18452142c510800741e0b16801240c001c0c5d50004200310394a00302d0b19001d006294049110302d8001022070703480040e500c09550540d032443c0700140c0014180814441403050030a00540d025005104000716a030003552 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 721206915 1250 721205665 721205677
    0xc1e200f0312180913020a0609030809060906040e09100c05070c17010e10050f2809050111280302030708070804051606021501140d0209061906090314030f 68
    0x14810029840b00c15075401c003141c3c1000100504031080030301d003103100c1c01c4606803141c000343c0c464841410700007051880f8015010a813a40207010605210669092001641202d802241c1c4414181301c042210482d64182d68404c100c420020484584074002036012140c00e04409820400c2c10007a03c0040303080150350710126104e02c10038580c40d2240341410783c01004c58448074103403401601e504014100b55500294000d008000144089849030760f42c0b02050800804c0018607480510583c41c0c001d000c652050030711034011400441d06032100b082401c0140c7c010303800c001510380218031f43d002c040380c251a0842d528a00b82011031440c205454050005400140361808001a80c070010302080b505104a003103804800e0a100c240d03503118030029445d80c981085401e450120100000b41c2c041d00b2303000d400c0034084003802889004115400740b0000c8400200340700d8000c070030624025031400d0108000c070010261a40c4000301360b400c501d04120300c0c0035840c0300811035900a0010156500000d030440702 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 721208165 1250 721206915 721206943
    0x60f030c030a1e0b16080a05010f090507020703080313061a0a120c0b1305010f030b0114071b06030c0f0201061d04260307020c03010e0303070c1e200f03 67
    0xc212045990008150008620000c4c0001d03c10400d2200702d0724440314804078402c0702e840b001002e94460303000300b00311042441880400314005008100b0f5040d2a80301d503410074601e00c16038002e035459480710701c1181d0068840f04220171120800409210b200d20407000048400041c0341100700c0d10348001011499280107000c042c0c07105103100e8040180c0b01c0143c0b4014507030441c120b030301c0b02034202d4801c405800a1042c103011406503000301c01c001b84a80300311101c028058507a004104601d44c00b032400c0b81c21482d0122411840c4140d01290b01c0d003450090320081400390b6002c00c403c1e99010000b0a141c04101e8450250782c100a014008609651151502358001042003619a500c1c0e0030010030007105030030303009030351b400030216040c50346c4512005510800f0182c003150300b4003590030706150032180c0700010320346642c01c2030020034055441107405201c003d00494101201140c00c20000810310750150301142c072401d080c404544481d06011590034518021903c0313103845010400441d81703406003844190 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 721209415 1250 721208165 721208183
    0x40504020d08031e0a1a0d03020d03110f0c03130e01080c060706020d0c08010e01051e190f08060406050a05012409091d0f0607050a030f0f09030305060f030c030a 71
    0x781401d604007007041c018070840801e0500300d00f001d00f0998018181c240c0508550001e00100d00c449042c1090501f07402e99040d40140524500624103c000344000441490460010000c0d00d0918a0000c05044c0c40340100010b580d4032028040d007038800000a13842840b2541c1d9103001007141002c00301f00548820401d03504203030385891924005009104619101e003034945020005514990300180c50b9060302e5000e00100441e90300c4004000f5070000c92a1326951361090309411181504040c0e40e54015203a04d8400d00f02d409858466607014000250042c1c44c2950000082100780f00c03460042d550005da203008200310650410390649561114100c884110100014410841c80d101d01031002c024007103031170100584c040c802d2280108462640356801140318203a41c1c0c0700620004124940102419150145045441001503000d460580c80400f41213540311341c1c21501008500030207241c00d00c00c0d50001040d16020040045692180c4840f5001c0e611088030007000b5103000070344202e0650089268 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 721210665 1250 721209415 721209421
    0x10c0903081210050603090f010507020c131814100606030c052b020426010218120f1603060c031401051302090a0b09011e051e0c2a040504020d0803 65
    0x4594103e00c40d610040d0004400010400c1c02c11005c81c280301d40301d42c000024400d44c0c0f210442241c0c1c8400701a91260b03c0b15210300386040c21800da83c0014105910074482e00d0307244402e91215142d42c0c0c80580555416004481c0301c80d511510b512510010308090300781000302131560000108940201c0710300159040018084500110341c45800d480c1c0440405000d555482c0c90788100c003450842240a42151108146d00100610040c0280c8116508108030341c00d50760b804400b00030b00c081c0345000f100101c3c02529a103240d04001408403c22900020440010700d070700e10300d0302034201e03400308404030105464107a105c030030142c445041d1411030b242202e1031403501901ea07200400a00c03400e0700040d17020841e510005100551007024007050a0240c84020600c80b8a82c0d80145c0c0e50000014100051002c12036940c40741d00b00c0c140001e081c034072000b42505200d4024809803922200034000401c044901441da0000c080204220105a42c2034030107002c6410079a000c103501c0201d9110083c00c484000c000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 721211915 1250 721210665 721210681
    0x30339030a0f060312020106050604080a060506061b0705090f0906010e100b0d05040b06150f0a11061503010e0c01080114030c0306010e060a051c1b12080c010c09030812 74
    0x42000d000d01c028104106096076840e000345220281005c00c4059400c007000000d61345002801e5908030359131000030340400c0205585d1f00c00101001000e4a9003c8400d02c41d140d0b03c4400c855011060410329001084c8240c140402c000341110010403010040c0800c00070018241c5010580701c3c11600302c258007801d1030700c1e0040c22594211454010f044241c00200b0040d02c220300307036000300e401280501c0c2d0f20b602a40700c0e0418802c004201100107032032a1000c1003030159814014004103101041e80c07030600e1001c0085841c06040c00d600303071812156403907101e00d80c0308189001c2c41490305190011004001c418640400a031602005108015942d20b03224100240c903202804103c400070001030076110503685410003107920744000c1d51f04900803d1a0b40c408185420207032110890f090300900983c1c4008a695500106031010044884015052400c00100701801d100b807004400e2181c0a1a81c8450b58002d2460071114116100420880d5810003080441c0c111010ad82c5400a4840b0380401c3e69101d41c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 721213165 1250 721211915 721211921
    0x90b060d11040510181d190225061b0906050f0c010615030b0907121a030102030703020c0105090a030f05030a0b19080c24070c030204050405030339030a 67
    0x1100f0f84e0071010016605070126449011700100741c50003208098569190418440c006180c404d81c420b4035040d07900800c0303008668426954030788419140142c645404030240c9081c041404075940301000301144030300c1c204044c03406620850000d110000745103062001006114030111310448050100000b400e0800003114021a924503421000034400240d03070b101c0a030b000b2590242550b0002c0d290000030141450003002c0c0c14043c0041c5d5580710240b04046900c64010400c00d40b8803a000d100d0070300401d1268500b800a58070520b000d440c0161940b9210b05d07502d0070754400900c0312140b500840711080c002500035120381e49c0001e2501c1c000c0e07180d036120640240103220007098694007041441c0c2090080c440c105400c0c2c00d0b0355482d000d8460086000c01442504484203829030402004030030301108290400019080c0180516409400250b031b03500413400301e6030180c50a8030141c00c000200030000b1400c580000014504140103044a800e9040d0101c04580c52220341c041c40030000041005c60110307070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 721214415 1250 721213165 721213169
    0x13090506070e1005130501050c0309090708100512060705161719082721031803030114041a06030f04060c23090d0c0b13090b060d1104 59
    0x440d1854244828050300310600301e51098030804010059454242c80b400c141e4403480ba5840007003a40c1804d010064070142c201c150034a00d13034401400503000507503c0410845c001c8016440ea01d0480c1801c06c01d919400140d5000603001d003c3c001d0700d40d0400100014130990213081490060f448084d050601c080b542211040038000058600415010142c500c00400c41c5810603000c050f0080e80361784007910710b11b10440b00480c0810705958201010300224182440540109040d1034821226001128415401d0744041000180100802480d446c40354180074900040e90001d50a40d07142c0082040d806101100f1107014a84841c0d500512041c8a0124010100c0060600e07440f03282061a405031321400f260240d42c0c25003401b06104480e401f4464032914800c408078203044a401001405c006944026083c07a0000380d20700304800881c0c0a021070030040c00303003001d4140da42d17200380c00c002e481050681c0104010710300d003075040d21013642c0e40011101e420f014060701240d01b81e90351000f502503000e1a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 721215665 1250 721214415 721214423
    0xa0b06040f0906062a0f050102190e040c030e0a03030e030708031503100513080c030409020c0a21050304021903080f040627230a030b0906060f0307051309 68
    0x46900402c900c070460300039805a03501607131152200500c56003070b1071480c0501c1605040c0400f4641e08800400e4840d80b04c428941d00600001d458020210000d10400e070f0b24000c405c0020750044c80b292080c1c5000d0140f04110306c002d2601348900e1000200d02c40e1a0360341c5c071100500b8141d03155440c4011601c20300a079a985a048100192070380b40c0144449007618802c00300b180719004129561461058900c02d0368021100003d421810582d1603541c90030546c0040701c1290382d48811b200014034401d4900041200482c80300280c8441600c61800b140e0552443c0c035030210140d02c0740c0c0c145040030f5004058036401a01205c040c1c48030108018508400c0510360005440c034100000e0b50304203040d10300010412100c8940c0c503560002da245490242d0640034007805500030385802c80800c103011140c81315585e503030405a070320440030a0441c0001e00003d0103a0040350400258410070540c2c110600480381d0215003907a03804000d1030140000381d260601402814800c07074034124400055480c41d0710035680f01c0e40c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 721216915 1250 721215665 721215689
    0xc0606030203070f03140609030f0c1507020705010f1b060b06073002030c0c091e0f10080c010e04050702210d0605100906080601111507030e01090b0a0b0604 69
    0x881810b012081a01e000546d025041d51404c2c81d01c0350000070b0b10a114055a030302a60514082441c040303501d90201e01c05004521440340e801241410300032000e03010b03954540040066074608800501180c810303448800500c02c01c0d0641100181030300000c00c0095600c41800103600309444001803050103207541c080d0691a0340a05501841004010340404804010219540b25040a41241e6a11400c80c0030412a008407416060905054030350f20b401c15a0890012482c003050718098465190846a810745a6000c0c07050041d1108038000c00000b1f007001d0406030200c081c1d0007001801c20001580c07210302459540001070f42003803082c0440480d200b81c02c9200d141d0501c6001240c81183c21a00e60080191b150200000b0b8a02d0451118080740c1603d0310b844e03000030b01d0440113940c103202c02840d0394180201c3e18804441c0d0b41c0140000e181030015030421070341a0400c07510042c22101007180724061a03140c400d40c031011800300c400580d404502c000700842c8a050003000704050b80600c2d4840040705030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 721218165 1250 721216915 721216919
    0xf030803191d07080705010c020616080304050115061718120f13080c0117070e13021b07121401020c01060b04090c08040b0f06011710030308010801050c0a0c060603020307 75
    0x11003440100751242c1101100d01c0540c44590311500c0b0310741403040c103001c20780c60b0318502e00600723003c00a0302c0410b607241d000d010307490101d861740c040f59802154226050b075900c00301003151000d12031900000d005207181079003d100d010700c01040700e03500c09001083e041c0300085030000c05282c200801a032103a00d010040e40c4030700742c0e1001c0e528150880070160114072603010021a00b04400181c0d580301d003105944071208402c103e046551501c0c0040d005c10b0411034100f2038103116846412502141880e00000140d80740c1071720380300e02c0400343c070310010000f29045031070b08000c8250449184044030360070898101c030b11381c01103607424024800d0507a44420b550078110002070700300861004d0030440351000010710030394503480801c507421041294000e1101c00080c01048500c40d900e1251540100706041241403c008100503021200f02115034182070385460005004040e0300515880c01422028001c0c022418081120030503030290032101d0003004103c81c071450600045070021402190003a0a48080035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 721219415 1250 721218165 721218191
    0x30803060a050a18050f131b0e01060806190506032412010e0d030c140a050d050108070f0911030a1113090b10050c06010e07050904060e07180f03080319 67
    0x1001124040440d03d8600044c56400b01c0042507442020701c2c1c00078a4000956603506810220850001c080361500e0f00d50102d274100e070000388180600040d4a410100346460010040c0c44028444070b000d0980c0d078807500700a261540415241c000078001407541300e44203501245a0340303080142003554800e43d40c1204540221041d0712150a5400c4001036032204101444154180c0e010000c80a00046600c8106900110036101502c45c103031180c9852031601d0300100300081a10005c0e001002250040f40080141102c0078441400510103c01c0c01c2c030801010300c3c2115100d01004240144031038036802070000b0545513170212000c3c5800485402065a1120b50b00c00040a84180040c005c0a1501001da981405403095400c8400e16400411103a07081084040840c940a002441488000e210010b60b90382e50b401803e000e483c01b480301c004186040030b4020303e038061074045808c40000ca1841480003580320440707102600c5e08251042c5c2d89455861f4034004d0900310410807007800780790002280d640707 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 721220665 1250 721219415 721219439
    0x102010902220e19050105100e0601030507050c0a121e080c0a11030a030501090c1704030e0307050d06150509060a0b0a170103050a030e010206100509040f020301020f1c020a09030803060a050a 84
    0xd4090703170080040f6520451880702c22400b60040d00020031202c40060200d6100c6d030442c0d0b030b004003e0300e402410000d2030308401d840c0214012003142e9181c91f481c82480c915500c40401d440391018595040360903000508007400c4400068135030303403001c0400912050300300d009031948540e4181b0042200c0d40d40880300d03130080060200303001d030342855420040e410038024400d05000c00035038203552000005480b10343d000e48045108c0350174290140200348000402c1d039110305c542040c00380202e00c0824a4400c1702039105502426402051107040400e0611196440c0c6101035000e40794280300c05d40c1e035900303404070681d80081001c0650303201020320300012003004000b18003035070510b00c6901c2d6903280e40780e0f036401a0707220801151600306240910f4001c0040d890000072031600305018580000d40c2c1e01454021909a90100c240540441400914400c1180000e05038064040a0000850900c4191600102445000c0c40003407d40080440820840c2d502c29500900409004004d001c00d20b9031401c0310100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 721221915 1250 721220665 721220713
    0x904030519020c06250c061808030708041e05130219021f1104050301050f10120305030708151e040b031b191a180102010902220e 57
    0x1824880460032145800001c040700c2901004013158140311041000004002480030341010640c1c018284102040d110300c071807805800c055460020b1800451210b403100c03030141c0d020001c0c42d8820419100429110302c2074070251134000004000035004030003c0c0210301d446400c5164440344c44e405119200d45182d008020340014503440c1400d1100000050741c540d219510001042800b840558032545159170050701c011803070440443c1003689800c04242141d4080783d00ca0f542980500c01d01c040900507000c2e04e4010003106480c0d48140300f0540d002413041c00080d10b03a1003800070b0000800c980f03410001200e2080340000d008240c15018003c119000b40c00c40051081c0a0f5240107194940c1d03041c0031501200c00395001c528030300010f4289042c0002c0c640c503480031200c40c410000c8040345404103044001212086010300540311201c1c0d08007440850ba01802d030310305580c58000103100588800780c000e40034800c0c3c614150100801070012101810f8101d03035000050041a840e80d000745011260320807 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 721223021 1106 721221915 721221937
    0xa0b010806040e12160507080307080703030c0c02030d08040605101413020f030f010810091211010e012904060617072309031507090b0f0909040305 65
    0x1560340c0003104c6040071405c0000c2c0303035803e204040212401501e004005103262440725503c0592034812000e006003416240c610719091035000d1880d510700b058020301a00d01030072602000400080040f074003152080d2601c0040b9516064034bd00b16016506403900500c003c04041c0b0400c203001054444401c1f09507000c019084142c240319000d14000c80e06221012041d5040242d2642040640310302e10002e1864440c1d00c9001c12001800c103a410115420100315420047c402140504805c41100d2410340c02c003145a49441034904185e0582c14054860346520082101008207807200d9104800004400072003c07072100b400b040c40903402011070304021981302d4004414103901e40115801d031f00709910116955220341002d220049100d610a40206198509450050400000b074041d45c60302900c0860410001140c5100305d4213401c4005052070603e2410b40740042459000c0f144c104 = true := by decide +kernel

theorem cover : BRFrame.Cov 721043165 721223021 := by
  have h0 := BRFrame.cov_init 721043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 721043165 ≤ n) (h2 : n < 721223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
