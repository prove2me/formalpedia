-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0339
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:17:48.368578+00:00
-- url     : https://prove2.me/submissions/1fe9baf5-de00-43b9-9275-f434cc614f2c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 60791370 ≤ n < 60971226 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 60792620 1250 60791370 60791377
    0x1080a08161103011802090618060609010c02060c03031b03070816030b03100f0b0609100e01051303050106060e121c1407050a1707050307081b0105040c0f08010b06 72
    0x128550301c40c0940140d00d8a140240c0740c0710045070b0154204200381c103000148603204084140b0032581c0303841c3d540c1d0300001d10007600c0050640c4145840f80e080450004e007885001402010b40614011301c10a0064000c9002640000042403055000001f000007542c0f56404a02d00001c900e50403c4c41e5043c00c1c1c42c010300702400905440341410004c880016114000e0703001001d4280098260340741510318000c0c4000600c60480e41c01c13800360901c100301c0b4281c40c20408403aa4018000d206642d09004468100c8404c000c0841c038906000080100030101d1803051035039001103101d40700100b481414490000c10002c9800689070007200c200c4031071008800041110f01c00c800e4030a0130b640c00f01c040300c40d04480e11200c0d448032160202d000a0100180500801d000900310700a40c81410754484c105494160703441514406022a0814808600083c01d500010125003030460031506981050300c2c025400c44000369001c0329400c426910800081903103481d1340300100b041000800c80c180380d034004100b0310710 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 60793870 1250 60792620 60792637
    0x100608060402030a0e0f01051f05180a0612060209030c01080403050304200406030606240206070507020f040c0201090303110c2e02040806040309050a0303200717030a0801080a08 78
    0x781c0103c001120328031641e120b403050810038070171140984001d010582c0280002e03940c10303080b100c0a90001e80350300403400f03403041101c6000e800b08112050a000c00008a0000340c16107036084c0c0c40746c8000a400c0d2090070280c0401d80200030041e40ca003110003c061030200300c07a00650510943d10300f084042074002d029682e0054001c02c0340240602c0500440c125144002d0125900c00d203442c0c3d02000740300f0150701ca42c082d070b480d080b4506511004080319140111084120302c0051344180c002441062040020b400300e03501c0501200d1890303070004001016518548882d80040c1e64a8000e0001d06a05000b204000900301204600d0581d10300201500d44050740c03000b50f080f0580031001c5045005440f6010386c07207116800115203c50b00da044441d11072409030780036800240c240c1004a400e203818a0680c080349d505440d00c084a801c1c00003c0e41125a0050480310305009082e00021503103510f0440e00d1030005c801000c0d650355141c081014044442c103800c030500e658000321640000070310b44001c492140c13 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 60795120 1250 60793870 60793879
    0x402040207050f0d050903060f1b0c01021303080306030d0e10030e0c0d060c080c0406120c050c0f060118090b3603040303110c0123040b040e0a0510060806 68
    0x507502030a02c585032500b11520181184200d042c88050b60b9031083c0980b0f0a10070813030070340d0740342d803501c0c801000f60741400d2741c0340d00030340c2c503001c1d4280496200c5100600e00403000d103001509100c0d4000601c40404480d600640d80d07400000b0030003184d0300d024004194000e6890805c850b441c140c00c070105134558118441d41003030541d6401260b100300d4080051a004040c010901c540104171480d092000d40a905000e00c04501d00310003003a00d0b20780484c01da606031540c1c0d80c1c90742041c00a404e008e001a208030009242030000c1004540c01040c020311074644030303001d00002088994982491000c0111540c00300840d0280b42608000000b00c481400c43d802c40c000f0a45a0902e841c40b4298115085400030522080c1580d06a41c0b40c01d100c0c04405042120301a03154401648a01c98038240c031801a50040341c006001c04608000b0035008942e10041d00400a002e0350403d9210440d400301a44950049240c0341c03030060810000300e0060140070ba100100ea5820307040c9524080c000792600b1809451039114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 60796370 1250 60795120 60795127
    0x90905100203150409050703030206061503070804030c05010f1505010201020703020309041d07061706010e01080f0c041701092a030f0f020904080702010905010305060a030602071e051b0d0b04020402 87
    0x1d542c1d07421000f02040c010700800212905103041e603603d4410344400c07009070281d00c3c0020700314502179009101009450f0318117131070f5541d65a02224040300c014821000c0c071001c3c070301175400b1581c01d1080b020303148070301c0000240340c0110190184070120158086811680100300c0c5400007603010065602c55030701a42d008c0b0b010100c4c0f1488461401c002455400d2a10420740001280c40d40000000c0d400d1103826041c0740c25844031401160244007611030b840c0440c51010100f40030000901c02c081e803021a41c032219040686640b103030302c1d415140d84180c41d80c81c0c0d10303003c070201444417201507401346c0100e011003100404078503c3d8141408200384006814404100d0014090150390308070252140c1c4e000300200102d1400c0e01d0004940d400881040c3d000402088020550394088d10401d8007803070000f040c1407881890f5640c0d100c0603510450044500300b0002103840100070a0503841c0100300d00c100060442000d9a40c0d60000c00b40c10f54500901c905440c15044d40802c85480d29583c200381c059401698 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 60797620 1250 60796370 60796381
    0x30d020d0b1522030807080319020c070f050a0602071205070b03071220031302130603030e1203120402011101090c03061a060702130506012102070c090905100203 71
    0x30195010250740002d0242000034800d00010024400200303810b03d20042110440c05510b00c1c4950313400020305084040112201144c41000555031182081f64400c00d0703d41c0348001881660041c40d8007000c1a07000250031302100d200e65410a01031301703056521403413041c54034100030b59070302e55441115280c9035902c110700240b040910203c006001e0001c00c1c56520b081c8000001d062580d041c0212081c6072600d180c0c01002856000c20101e1321a40b000700780e04540740d11412128844040703000301e078400c1c5400b4109005206500502c0000c50080e04c4010031810090709024400c5100e00c18158150000c00c0405030340380c105c24036140c006070286090440304000340300350350051100300c802506100903801c00008014884d000030b42e020440014489041c01900c3c00e1026034011100000c1d80a1541c0104050400c1b0540c4483e50000051610701070f160304c00201548400788011000d10913940020320001401507171481c4400401003110100f085110075151a43c484c0700340040e0b40182500000407a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 60798870 1250 60797620 60797647
    0x3190b04020d0f03080709081b04020d090506010b07060507020706090b0901050c06090604050106140102060103150b120c2d0d03030b03070906051002031c0902060d05090a140d02030d02 81
    0x3280c0d541c0c001e0418559101c6418054801700c800c5030b0a03000911100d40215849101003410f40c450703e00300c6000b40340003940f0340402001c0e41100e000c041c1d60759a21004240030417000c1000074024015200d81d19903400035403c290041d210002c08140c19940b08440c2000101e81c01031a01c011030344c82030b803c5034039140d00000481e850711801203120101e00c00c02092000024021030f4503405184220f000700035941c1c2d0784019074411241c0da10910f026801142c01000420507039221002280d205000000d44a21503030001421594060f116a209603c000c080754550b0501e501c91913115442068090850400e041010b91007001800ca100d02401c10044030300d0425000e1f4119294030800101560320107611844048003d207200c2c4034003403140915142103812a4008401c170340c010003045c27580d251009484250720002d064807000403600508104410076242403144107140c091115103000d4441d4082c1418600d500b249a02d00308525500b00303d40c021010741c4c001040354103500403030f640580c80303980a10010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 60800120 1250 60798870 60798889
    0x40b12070c061d0c01020607020d030509010b03070312030b0d080d09051005161706011e0504080102030a0f0e060105130c020c060d052a0403020622030804050a0503190b0402 76
    0x10319190034058403440c04a0141004411543e00b0403c690740184144012a503984080c0c42d4680580c00810341c2500082c42600070640c0003280d04000f10302005210b020900e0040180e00075160242c3d030700701e8107075030b5545409020140e800440e610440c03503030701c1d884002161080d000000c9855544241a004001040c4030314980c1d004000700802913807409540c0e1000c0e21700c0c8810700c1400507250046c4140000441c130703030060056506a40d07541c5101d00c0b080c1c141002c1d5410044d5030041c84010320000800c844240011441070030411400b10780c0001d10a0b40900b6a01020520101904030300014092516080520b10390529442000715545000c002d050342010350158541d9044440054649152042c0c0d800850107600d07c5044107454180c01800b01c00c05000800420340d58a03000c01c000c001619210010b0704448007081074240020f884440c60582c01d21859008681798140400c00b00510702d0a50300d41d400400081d0080c00c450050a14070a1110440c000d00a200c8006400403605540303510014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 60801370 1250 60800120 60800123
    0x4030c02030a06021c0203100b0f040b0c0a120309021e1c230d0801050103110405130b03010b060403020913030903021005090915030607080601030b0d0f0c0b040b12070c 74
    0x181ca00c0641ca0303042c10006517000c44541144c4148141a0351102d810920072244078903401b09170790003658203250110105a010307400e0303240d59403410310000c200440170400401e88041200c0081140440c0d41c0b41c8000d10305512248501810f14064029025032900c0e034041204440b03441e440d44504a50800141d0350380b2690303514280103907008080074100b00ca01c170000401507d410401200c18516440e070f15a45441e10301003800000d82c414010401c41d40a80c00c41c40c1841014110b00d0708268890300828040090011858400b139102d1507002c0b0203040070320501c1a20307403098602520b018210b4010a020380006894103007006110329108045c94441d00e4600b003d103a004043c41980510150000c009030851100207100f0488078010412000c92034030000c0ca402000b9000d401542d0340d10b401550700f0000109154141034840c00031390925610401e035942000d2140405001308885d5040100b6031704801d800505c501c0e00c0c100b0091094500c000c1c142e451915030788036030901d1a42d80d03079001c0f11809a21b540 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 60802620 1250 60801370 60801373
    0x60102030c07092a0c030e010203161104050c0901050915040b0307080103050d05090d11150a05130803130b0d020706150302010e0f01091a07020a080c030d0c08030105040504030c0203 80
    0xa020441c0724071508024141d2424013142c200408080b450b203100555100031120114010000402c00170340030310200c411490050055a040a00b0341d101031140c00740b001c2080782d80c249000c40d0b848581c5010302c6801e402041446140e4102001c560003e4140c2c420151703014890340790071000034484040041220041c10075044915128103005101404000c0c0a01003121240107119804e40101e200304c096440d405002040d45842c00d0b101c0d10b42d44d43d82030701451066044401d00e12102d0b0086039040c000c1a000015685141d541e441c80b0904807138200303003904103035804e070003c210340400c81c00d12610100685039900f44459940c50004410002071184120080100342442c41c858608a00301c00b0442c1120b00030707280c0b0b001100c0260200501400210141404078000450601c007090350072003501d100d6603040040c18070f0701c59183c0004803a103442e6400b03c8010303806217044104e1402c0c00d10442903080d815040094040400742c0d1171409a0205001d181e008030364450021b01458462403404030456006030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 60803870 1250 60802620 60802633
    0x51005010e120f0d12091a06041506050d0b0306060303030106050a051209071401030b01080c03070306080615043804020f0c0a0c06090302090f04060902030f1605010801140108060102030c 82
    0x22603007500c50b030036a200c07000868100c604044441c502400f0340c001d503547c04800440e2111800c0c00c1c0301d01c44000074100b80c0d04150360300c0c00c090001d10050a081c0207041c407600c0d03080d00c46400c90118019129069071982c06500702a0500c8910340700003090782c0c1914010704025850343e0b8081002c440c280100410250b03400c4041040c8028890b0101d107001c140c41e04002c01207005803400b00194199080418501e00003001c40c00016184840c50380616084007680c6004a603035a5120260ba1500109640d141c04d40300c44100e02c140140740070b1040b080356926001002558689033380f104e88000b40b4600c819441c0b404e4640e10400c059980e0b038106c1c0c0340000c0c41481c0581740c0c080600000d40d200c58001d01140c964680100c041034107806100d44200301ca07802803001c0803d41c0da203460900d0700b540150003159515191081071005a0301808414480b4000c1002040a400418605000e10000c0c0e030115060245440042c0055800c0c0104903000807000c0c2401d00042d1145d4004070f245d84129031404000740980c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 60805120 1250 60803870 60803893
    0x70210050403020a09050702031911011514090702030a080a090c030605090f030f07031206091103040c0e1303030b03100c030e060c1303021302040801060b190201051005010e12 77
    0x780003924000c1d40c01a072030580b40c0c085a42210702c15074584016a1007405420507001890340d042e1105207147c50104c024001c00500c0c03500751390800c01035030205400c1c1c41007404144040b00140046000403a441071060400706030183d02c901c03035011348100300000000040d0008c42540c0201e405968414070b201c00702680ea003005001444165400c1c1468010010079000c244d00000540300c0c90030b1641013440c500711580d40d040e0303500503411111212040d156800010401400e02c24015006403005260340d403460a450050419010742e000904005150b50500c1034241c400c40314016080c0c0c4c1801e001031460b811000207441c20303940020110465050500700754109506800203038a00e01408101c40c0755840700b20101d0303514050b00304c2e1521100b59404040000d4644050444081a1000c07030040c0741c580c5030a0f140e800d60300c02c0c0d0410f4003804000241000d00d40304c156001e1401101c244001c002504242021030344030041840341c1410400e050104078800d907900c90b926400c50031003e00716050310041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 60806370 1250 60805120 60805127
    0x181518040501181101030c02010f0606020c03060a02030c030c0307030914010c0906020c031506060403061a01141c0b030c030f0a020307150f0c1109041b050607080313020303070210 79
    0x448080300d0315420110ba01c1d003d440001d42c06941c040d4401202c00340c019007140110f0013010b030f01050008640d2180e250141c180308510a02c4003414150b8080c140c0a02c15100b41450200042d08a0168038410820041c80340203020599401901c682c1450f33540e5180e04400300c0213800765210203041807d21a01c0340a0240b815400141118400d846842096a80c0c0c2000d9032141410102150150403105484106101200d07200b503004100400341400e25071a601e5100448010000e1010203143c004810403031507801005600f02018085005481c1c014900c4100c10041c01840b8200455034071901120074682d81800064108040502203800d04c41c65800303003a503902c10001090b8061701034000f0200c1c51300799480142040c4407a0762074419005480303250446034201c09100a13100b610400d992140d042c1d07100c02c00350340102d020322a050b84007481140e200c00c0d6000641e00151003450104003c0001a00040540703600040e500c15003c0b035a026800443e055118100c0002e50104044005d5020b11f9007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 60807620 1250 60806370 60806419
    0x306050f010e01120b04020f04060e040303050403030b04020c0c0d11220f020f04060c03020a060905100605010f0e04020f0904060b030f060a05090103020f010c0602041205010b060403021815 83
    0x2e80b0036640c10666a240094911404071500c0680ba114994001a0160a01008001116101030320000d042e07980c501c0034819517001034504600080d01c40b0140014180e050082000040080b20114506005070200559034126007200e903020701e082c080000c0501501c4410507200041c098282403600c900d84690300c5400c0a40701317000106c01d1400c0180c1001043c140301351780c04c4550842d001780c98a401c0c454241d9602511000480841c8601c3c02c60350001080f07030044451088c42000101403d2103c40080340039900ba03908884d042015000f00c000300d241d48031100d4203118400340c400680c0e07106040b100002d1446541206034000341440000140a54080000c41c824103805030b21000c540c844008101c03414003540b1880d940f14a00f0030050015162068049918200504040611001c02e0b07445900b680c21a80c84285447c034800150010b001080c0620040380764115402480e1900355800200e005e0004d01e40340c5450b88442e00090515201c07003010b111107940050002e2240080401640b11070131 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 60808870 1250 60807620 60807629
    0x21091103191511070206031b160203010507020a051c0909060e0720030306011103070f0c050a0504090506010b0a0207030f230613020f0d06060806010911030702070306150306050f01 79
    0xc854100d942c40926511862004007062500640340055035020403580c3e8101401103c0b04191282d000120301d546440244443c0c2d660003005008095540101400c440e0002c0054040d5000142c41c00009400811035012009181200e1a00c51031062800c46e004272480d00003040d040d250010108000c0c0104101510540300c6980d9807500d905240450492a51080700c26501940144003040c280d43c0200c08c108038507200c540071a0708140071912410b201c281c1c40350301903030b20051014007441a400c100c0700c080c02902064409004441c4907585132030b9a07940500c5102003949012031040313820f603c24001a4019a04180d0200c41480b2500780610544c55240b00c06240c0c3e0341c002f032200403800012405900c100c02001d000307014040030307030240304104654402640e400644400c4687c00150148600e001825242c40100301c41d40c10f00c2c608008071030b15148810b269103030030300400450380d600040d81d2061342d40c0254049048040004020f00104040e00005d00035810001004611182c5c107102a0480c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 60810120 1250 60808870 60808883
    0x6100917100513121b150606020601081609091403030405030901020c010e030607030c090815060f010203030f0103080703121b090b04050d0f050c060705030a030c2109110319 76
    0x242c80c0c000404041081420300100816980f4102604c01d030301820300303010841100404054040704903940c20b81c03540c0c1600c105c07140407952244140280c1d541003000c54050706514004100906001c0c0b4011102401e620880c58580d0f00c50036140100f000d848514120001940700b12612030505191468403600144c0b1694010b200700c1d42d6080656106030002102e2040140150040352610030701100a0b100b100e000c80144240c00b900040d14450401901c2194640c07c0f15081c0d8906003403042002c5d80710000f6900d2304541c000c2c0f092103844400b006c0401d04591740500c0c407a507140c425150503694408105080c00c41585880c000d02009039040e03000c69942c8415079904041d40e43c440c007048140340a18007955420058040103207000888001061210900400454012500c00400035509a100e00011240740e040842e50341102901400340501c0300085041a040600c2420038160508020303142c0356480d02e494004604c14844a000301c818078150150503200d104010f05a400452088070400302c0c1c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 60811370 1250 60810120 60810131
    0x80c0c030109151103010e07030e0a080d020903060a060e0105100c05060411010215070e040b0103020910021f09030f030525081b03010e0c1c0513110405060102060610091710 76
    0x4c01c02400100d90590341e0200c1110074988820f1007c0340108600113541c8101c1c4660028103010130610b4024140801203404096a20242d140c185800d1490103420315418900f004814800c0f25161900141521400d450b505103000c86481c1c100c40200d02c403200030785903018400078001404003d6030b07000706800c0203070210f4401c20000380c410107289108a6901000696618124042d0302e8580c1181c0850780c014076006d810452190000391000302101703010005688006007510b05001c11544107030320741150340420046007002d40c5010f00030344038146000e13042569400c00a1104038100030051f42520002c80c0b8103c010341140c0e07025000381001e840c8000d1483e41d00b07541400c051540d07001c803030503106d14101c24031294031088041080c075003000300c0c5e08100c01030224000003210001c1c4602c600c07521607108141d007251854204950144010180c0d540114100800c000d62a42c000842c540c03c48803e07599041c0307507484c0700c0b400ca9000c513003508200c1c4002c3c50401c0c1104520701c00107200b4012009808100300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 60812620 1250 60811370 60811391
    0x210209130506040b0c090306010803041e0303050d050705040b0c01090203010b0a120b0402010c170403060f09020303072409061a0109030222110f07051b0a03080c0c03010915 76
    0x4046503024018003a5100e0400030380007401056946400032890b05400381801c500c6030001c0e08210090b0040700341544040b40421604115004010421002c4a5020725042c1152801001486110390b07403136105844901158001c5c1c890b1081b20018100041d0050f00ca00da501000c9028044806059101e0340c02d202c2c45041034503010400c1c1c0d007201c400102603000d20300382da03075090703030444004006a040c001e00f4845207000c545000c0c2d00c0d01d800c003d41b110455a49007186091411244590303100c0b000c813441d00d0441c00050b20000121a01950460030000c944240c00c0f10540750841002d094080d15030410303902800304030481e0440364002d800c80310b5010a03005080300444901c8407511001c0e5008010b01940c0c03110184010342e2009100004c403000c40d690301801c0300710f6100da008031030400745440005441018024240b22484454030001540c040e203100e00d40000d03044500602018015040008070b01c5030102081005441da504050000d01a5805e00d0034100c0b080c640040b410444907081c81c81c40f10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 60813870 1250 60812620 60812641
    0x2090a0204180b0f03010204080d110106260f100207031106160804080405190305060709051003150f060e0a06050304030c060b180103061a090103020a050103050709210209 75
    0x5003660075981d0042c03145090700c4451405050100311480c2c01070510600742d4819242800108090705c2c4500082c0010004208005c00c0710381c40703140418082e45000b00902c441c0100a00558a004496803600450810041e12504000742900f40f9031203445031249892040440e600680700480c0207855150a104600c001c10303451303070400c580d1800380205170225684c0302030082c04d000390802c0c082c0c0082402c0644860200725605c00907a000410f80810070020020050108546a407003074a900e45041605e01c1e2802260b090000308a4840905454a1002c402d400300d03040044010000324400080d00740d640c0d80d015001c1c601c00114180244411000814101d02540c1141c0c041c0d07a2543c0d8100100599854000040040c614415488141a400841c1c884107192806018500400c0700040b55030a0f0070360b40710716803261003503103015540f4440100056074903481d0341c00071030f00b00b82400300d001e07134807001e0448590085e504103428030306080413842008405209401e4140740f003590843c00c0d41e101d549010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 60815120 1250 60813870 60813877
    0x807060903020303030604022a0c090c090d0803180304140a060c050c0105180409030807030f0e0303040602180604140102150411100201110f0903070b030915150a0801050402090a02 79
    0x2c1d400da8810000301e440d9050036401442e91104800c40c0721039061b03030030300c00b049501500c1c0c1020b2100c4d4001a4a00124901a01d0761341d0031500060b406c41c509500c1c42e0120b00c11141c0c1150240241c50040000b03100f811011403150700d054821800c2e030350b0716a1a202c80840182c00c65940d08c0c041e5441c0304003c00c402d801032200d424000d030840c0090280140301801164a075200c10705d00c40796212101042072558949009005076a440b80e01c0d074000502c0c0c407e4008003143c40d112650200e00c1c1c10b14200c00c854100100c205e0360056040031700503a030307031503820070300c000044440b0381d0035411681c0090002000f04182500710840c4001340d0980d20140f980d58100002c404060350080c1000c0881c201c0d050551401b003000301000121b030b00020400345103080f8100c0d1150801054002c40d003800044e243d4007031905202c400f000c0e005100c0780720301354200a1007891b07540064003544540050008041100c0800007d00c10b4000b0f032004041075481030b25000514040c240a480407401914860045035007d00305000342e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 60816370 1250 60815120 60815123
    0x6030111120403020712111219020d080712020a0506090102040605040603021305041e0f020c0a12020a0203060c0408150106050a030b040209121614030307020925090807060903 77
    0xc00342040c0d00e44000106070500074104a056200d0907000051000080400590540c050f2600c8a50203d400c0180b084801c1910302c4070f1b845411003a840454000001c1041c803c0d00d4050300c5110001380c9500d00740c003040c45511000b902500c0001c0100400c00d43c0060a1444544144282c55143d10b40c2c2100301d003030740100d000f4540410000d02003481894881c0e4050107107180450004218a940c0b5030100b0121842801c52401083d8042c1c01d492500c2e90340e01906082d005a42c00441ca0f000070404095103400303030003900518401c10840b0309400b0034401c101190300d00c4c1d0010160340d0141403038107245d40b00354030521541c0f04900031044100b41c001000c800c3c1d64100d4a00351103292a00c0040c4000310014020100590b601960a1000300c02c0d9444140300b001d10f44900200802072203003121001c3c01d0483e420703403098001d800d1105070807a41e9100402621a0a07a041c1c94030300e40c0e919a0001120382145846035803140c403d0115403054010b41c4443c0c42001c41d0213260a503141c19031034503401c0701c08041d01d000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 60817620 1250 60816370 60816401
    0x60601021002190c061d0102090a1406030705070503070501020c03070b09011a1207090f0606080c0310051c050307030e091602060c13050303040e0f0a1a0f010302091017060301 77
    0x5410f140c89019080100c061407140900141c08508007214514000b04c142c182e90040e0760109240d269410308980311707005030081345941201249420001102c510006110f00c040000c003050140800104209582e5020ba00c10002c6d922a0070181c0c01075a05c1c2c101180607a1450381c0340000c64030446040c403c043c4051101c000c1103901c0480c0b002404102e0030880800100ba11a00c08000f80605035840f8024090481d010040b82107850580c000b4140040a802005020b408200703201404064400c0724045480684000380c52040d1105039018004002502070000e00000415100700b5500034890169040d0440b1615101e840c0c804040005558040c00200941d1025003c94505050200503040c501031000d644078031143c441e000709046421941c44043c00884407024007805e105c0079102d0b5513019085e180c0811a81c0e103139003130400054600c258114041c0952040310401a4843d404985c0c550305d01030b04013180140c1181004000c0c1ca001c5040301c001e102900080342c00d506e010300070b141440e1044038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 60818870 1250 60817620 60817657
    0x20406081602030408011103010503061005010c1101020a0209191d10020c16030c06090b160f0201030b0405090d09051008040b0c0c0604060605280b13030206030405060601021002 78
    0xd01040148884900d07041944018000059080400d001c0e80003684410140c058032035262034103240c40c102c80904500300601407142c0501035a41d104425140543d048910b0042d41100000113074100960705002940048192080128400000b00385c41901017032020100b15400c44082d04102c408000410b0050f1a00840c10a10440d1442e801400c510b0405100741ca2000c1c49880071503101c1300c40d81e802287c010045903403c00c51190820780460080c040d4100075890f202c1c0d203201d10700e501004010002c0000b11301c07040322429648241e10550040101810402540c180203400b20340da2041c1244100006090f081c0c0440d203404d101c40e084111450b55101c114441e12103aa400098880040c40b140062078184401c7c2c85400b000c0180030700641c042c640c0051018200028045031601c1208954801d0b8800440314004111104a45080b120418407040e25201049440810b10b25941d10295110002105000510101241185c0141003d07000c6400c400000c3c00e40c80283d005510740c00f8011190358 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 60820120 1250 60818870 60818881
    0xd0215070e0609030303040303091b030312020a2f01180f02090714030a090605010803090d030e0a030501060305060106030b0910060318060504060902010e0105130506070501090c120209010902040608 87
    0x295122010301c04010702d902e061400b180080703451a00211405d40000f03031100b000310107010301020842d0a41d80c01c0080d4000e61811a180a040c0c0e031410308402e0700e02980050f140d14000c2c800c07890030b1103100018003505400b8a4418401c00d4105405180503007030751800f4024807010554031140b2051a0f440f0006003c201d542c0d8080006400d001000345080c003c00d00684028442554025482064560030000382408241031500844d10140c112500341d50042181e462079070740f400f0080c2c01e0294907207010410020807102148448216600080940d07007800070120403c000895400d0603a801c1d9038081016803a0001045003207201a03900309d074183e80800b0b040c400503119401100c0c64071444044d803624140f40e581c42a080f140700301d40130740320780c0e0f581c5038110115030703000010b242c80c29024680b1500f0407400340e070443d004484912405104d640c001540304200032003900184c0360b0b680c0281d001e01d060b03641c400d810804802c510400b20b01c161303240e00000c2005003076403007a2400d68803155200511503456 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 60821370 1250 60820120 60820127
    0x20409051c0f081605041d011e0305030904050a20070b0702010501060518180115090602030a0504090509070b121503011103010603020310030b0106030f05090c03190305041503060501020d021507 85
    0x24550708400700030003041b01281140c3c68800661030066800302c48180c0e5071410f010001900d003101283c440200e4414001c00210300000f0640d500004212800216500d4450240c1c0c020009a2601c145219640c641c07020041c90600c00b800c9400d00030207104030150f0303440c03a080703088440902400300403a90502c004035000c180740c0c0701300001101c09022068064032050088869100990214521610081600c03203c1c541c07058078440100b89034001982007400b00c4002602c540194019403448039501c0f0005038486604000c150021300001d03003103503a100c140a481e80c424103400c0311036481e0560b414442d40301c41d040511922030190040d0541a08590a0210840180d8400342000845a03802e000100105a840f0340c10b50080c0b8460b10300007029400324030100150390700141480344580142030103092076100414080100750b200c00c003d68001d0000d14003a201c1d40100c1d00640c2000f035540b4600a05160036601c40b0003910400d80072122190502c3c07070100c0c1e1721000c4000ca2410f41c090716000c91600d600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 60822620 1250 60821370 60821401
    0x8010e0417070c08010c020d0504090b01090e04050705190509011401050c070b0408100b0d03030504030c05030406180b0307140901020106050904060906060b04030503040b090607020409051c0f08 85
    0xc5000e00c66075840400350340510039001200c2c19943e019018100f044440e40074810b102000301640007411a0603402c40c405441801248100908917071150b2050420f60b2280d60441d014100d40680c1074910304140c10301c542e8a000e180515030184440d800780751284858103034010700700c401c001d01003e0143c1c06e005081c10032480781c80b0741038107014090200da502c402c001d100c0c2d040a4503c01a01c0d9407204c1c03614411034680840c542c09039040903c0d054040c943d47e192300b29441000c50300341c107010403103844502d0300326000c01180c00e02a26030300000c02c002c036070694414400d0b141e100310507980b05002d6840e00c4161181c1d20054030340c03002052081802d540420388910103046214814000003071030f130b5a2040401c00100c0304880031950203030b03104001410000644141001303800d40c0d0300d001d4101415603036541e64911450080034141500400c0d00e10140c4d03030790421582c1c0d069000d0810301c00c2480c00e140c1543e4882d101c20b1884880003140119004452107202e40309802c074610741d11005240c660392030400c1d042c80b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 60823870 1250 60822620 60822623
    0x903040b0a050a1709280305040306050c090603100e070503160c05030c0703030201020408011a0102060f06040b040905030a0e09071b0501090822081204030204020c0708010c050c0f060708010e04 85
    0x1100000710281e001d41c01903c4c034030501c403c10282043e0303043d4407880810409541d00280713070f800b03203503010402103540001502c00762648500c0004031901c0307019020f4000d0262014190b44890004208208126101c01c940308846522812038200d84842c40242d42c20b0004558145480f1040b0100300006072240301000d032913501900649160210b03594550b800c003010340c4c2050340540c0d00000c0400049000f4030954260510f00c0d500e02d8114102c0d000003d407600e20162540501c07084542c0850603d031780e158440c1700c1800005200b00400c81c9585082034490f00035000910120704403a0400b000c3d8200150340342d1041c10542c1c2c1e440d0108044242000020964003802d275015943c0301840000205144010440303030322060701c110109020055101d481e82a84d8105070825009a01c0400f08a141d41c0295010340354110b50250300c2c0c40307482d4000e524000c403d500034100ca42c2400091801e01e0b8110004003ea10001015241c1801e04810754695034002601d446000401100041002e4400342210a8125 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 60825120 1250 60823870 60823877
    0xa0813080102090114070c1e0f08060f012603040e0717012402011401030515010b0c0c01030b0607050709020310080705060909191104060809150103120212040f08060903040b0a050a 79
    0xd231a04014070101026001c0c01500034081c0400b8007806d0401200c841c01028550010000f0781341518070050042c406104010144500c40100c80c102031407400c00c0c0502c815000c04580d241c075940d80d40c0c1400d03281c05a940071f000ca00c482800a24928000c0442c40c1030724100d4181e0388000000140081c15401c80403d88406c40d544c845140300a90000390480e802503004500600200d4085041410351010690106803201c030108001d600888003c600441503c409080004010b040600810201c1c880e80b14024030740c3c0154000860b1814a80d400740d400756294001c800c88a64640e200741e55a60440d0090540c081310600010740d0320b1400761140e40e8000c118807e4608040c0b0070310000d000ba101c5089a0b400c803c0c5000c90180302e5503a005146603071001111000344801f03403010108240f880b0042c040a014003440c0300d00f483c0054000c0001c00380e020031078071403295074941d195039070244180769000b01c000314090400400d800315400000c0c1d500790385000800500c0e00700028000e440c40d501c03a07003848090 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 60826370 1250 60825120 60825143
    0x6040306060306050702063102150a080702011808040308130315050610080402010e0108040302030c0304090219030e0d050904060e0a0b0307060206010f12060b030a081308010209011407 81
    0x261a8001ea1004520820011407030781062200039003010401800c807000d103035103045140300081c490f2420071040c100600740c1d0070200141d800468048400c00300d008003007000c0060f003810259408090140f040402c1d500800c10300100c0c04442282e002c060101510400c2c0600c01480490301810041101103c480d00d000c015641d65a50442c0803840310b01d0000d511a52030f02001036505201220103864081464060342e2403410b0360000e058140c041c884281005a50340008041500800c03c441c820320a01040301e840d1607681007600041d600031000c4034400e02d18400d0300700d0300900034000d505030003e80e840030b024218410801118281c0100e1046039129440d440001884040014054080d10012038007042c10303450081850314040c07143d440841190b04c000010030580807464280c00c0ad86411280b01d100070540c5052040141c0090113000e50300d0300035900440100280350300140382c864030000130480c060340ea0b007115034200e02504403054042543c07030b0580a081003089000302038030740c030a000361601c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 60827620 1250 60826370 60826373
    0xa0618090c0c1a0606070f05011d0106050f120607050c071e031a150f030106080706020303091b0a05040b062703010609090f030c030c0512040603110c1209060403 71
    0x2a11600742601e0049808200c1500510075400700203044040110310031451801d10001081c0207110740c0001500ba2041500e030441041000c0d0014105094840040c0030032001c03608a250080c001ca2007158800c200084400d500c1d030078458129070b07040c00743c00040c0c210f1350365110003691650b002d00e5414255020303d22011502c20301031040705201694003520740480500b58a00543c00800050480804d643c12908200c0380d541d080700c468a40b01c0050310800700114020011a014000e41c1d00003020320b0084e89004100140d00001a510425642d0111800c000d03910701018131004c02064030741e812407480302c000c2c400e5042c070760850401c40320f002d4407561038102d20b440c0b02100003050200c18030b81c415910204008902c0d09002d00c8000e840c42590401541a6543e94141802842000241800064210002030500405007a0001134021055880040010090403081e134031a010311004213103001001aa80f0700781e4000e88803d90741c2e180c0105161110b81d40d400f032454001c402c0040c1c0c006d004020210 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 60828870 1250 60827620 60827639
    0x50a02091c110120010e0607080c090a03021e0a03050a050c1f0f11060906010305100b011d0604030b090102070b100e041722090509030a23090904050606040b030c0a0618 74
    0x14034100301ba0083c00e468180b641c0004d1841c100640300c2034044a003480035807101e43d602c40541e01180da040f00d0890840c11035194450303802039000c00d102c1e0300894050000007849401f0032184810b0384a42d056601a202c40c50400a0202418a05a9031001c078044c0c0c9244441c012015090550001d0403d00100c1d1810503000d483c0080440301c07072100b50410f100400030081c040020094580c520801030002080000008017004450800da0714a580c09900518141d00c5200407a00a0760304000d000d03025103030500016000c0d5015500c116252080f480c0040d0160000036400b5040e07820b001d940c17401e162aaa00d408440b06001d890442010004010300185801801421003003115064000c4d4103452521350817400302d43d0000d1007010b10380c04c108019103a42d076000c02034800c101c012080442e503810030300003608100d000b4246816040003101041c0814014006446482413038200c40c2031081e918401c01b410f807039410368082540c122022410520660740103003030449021248102c0c0c40c0702035942e0384105 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 60830120 1250 60828870 60828881
    0x60403050109020a08010c0e010e0f04091a0a020901080414011d0a0302010e070807051507200906010f05180102010b10050403050601060509030c04050613050a02091c11012001 77
    0x4903901d039920a800380c218105009200010700b80324000b04400c2c0841d00014045090082e515030401c024a0280d01c02e550342c0030406a10131101070410041184140307070111503004c612600034003050401000944103a000c3c000c482d00c10304181c0d220240c9840d81c0c0d46111601210f901c281340750355250809807140000e61000c1e800381e8000c40d00182030f0740e0300f2030070041d08594015000d140f0307c2d04052011300454400050810454805039801200114a40c140b644a03000d811002441041154811030300e08080003180b04030f0050413560303080c054441c0130054a202c1610714541012840910510080d010425401c0c10700c0c140600021031010b0392100000c400c3e04041081001150010a052040c04002c00c49240940600c4c1007203031030800000000380c0d803003502c0500988243d4580000032142d484100c1407401c48080071000703001505100b19007001035080010014054172420b1100303881108584440f080043d04045091521316039540111040342e042040c1c2e003201384040c0444e0500d22003d05c01c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 60831370 1250 60830120 60830123
    0x409050601090c051204020105090a03050f210a020601030602030a060806040f030e090702060412030f0c1d0d0309031b0e07031401060c02030d0f021c02010203010306061a030103060c0e060403 84
    0x340005604041c0c1200440341684604801c00c0814416400c0840c4044001a082502401d0150700c0d1105140040c40d902591f1b0401402c1d0301600944070941e0700c00140c4410503038074008004000e181c1e01791030182507028001c0703c3c90041e4003550040000c10103660003140c001e0042c2001003006600c0721805460402c0a0703600300c501030700020b1004140f503885060440500c4003140c60013030313500380000c00075566640a8800b42c920040741846080240c082c0d0302c10000305400d445d041c801c4850404000c0c000da495204840c011100220314050302e40b0740900c1d01030940784e042d240d14100c64110345810541020780d03e10000900708155000c9072041604c00110311030301c00d550700403500128650011000c1c520680c0458103111800e103580b0016900441c4d82e0149015901c0c0c4500004c0c21400c04038079050196405841e0494107802250382503034107400550503240030314014007003a952201116401901c2610903000c0290074001030002401c01d40190310780d6800303841c00c00390070218800003400560084d0300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 60832620 1250 60831370 60831373
    0x90302070807062309030303010e10090507020c04050a06081f020403080313111f0507050109020603091e0604081e070c14040b030105220f06060905180703050705041109040905 77
    0x81003000e44410306081403010b000f03a201e41c2050085d03000f05c1c3c0c0c0c0b070006006d0138080d1200f0b8000224604500000380000303020405040c00603040c100300c06511508a565418000c50520f8001002e540b10350003000d044030b90013401460150840c0704078902d45c500034114200c20079000c01002000c07902d45800b550080b550350b504c0d95403400042c584001102c07083c8900d14066030ba0300d0105142c0c004142e040b5014100c0c42d00740310341e0741c01c4c0503c0e000380108240e07603000758000c0002c0180185800c00140004680101c0540034040c2c41d03882c2c004643d1404c044500500760303082000311280540c40b003454100300134016168641080c54030790ba808045090381d00145110f1504066814107071030503001700740c9821400c1d0000c03c41c40c02d103035049044410601c9866011080030000d904108100a500302d5140f5801001c1007020030380310a4904080e1400742c492190200c0c900c444480800030100700202261742c04001002158a0681804013030542c11b00c0400d00550144003007401c0e500c40e400b615000502c01c50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 60833870 1250 60832620 60832637
    0x60105060f220f0f060c14100e0105060a050307031110020312040305090108060f0d02041107140f06071107030605130f03030903020607030902030303060d060207020a03061a010804051009030207080706 88
    0x8210f00f04405940c4005a0899441020030a154004031107104080e003290b1300c0460f2400c42400c040c41c00040032656000689800850802c040040d0710a5014030341c21112841d1840c0c2d0f480c20165240c2150101624801e01034004485a240803640004006003500503682403541090901c1b10b45142210b09501044001884a0580da40b00510707130707400354045816905002000300415217208010100a002e1695003244028044801065840080c0c0c0b00442009660750b10204945500c2d203108030355400d205440100300c405004a0183c9200300f907907402001c0182c034548401010303003005401c03011400118510709011030025001420b00030301944010a241c1c40d05d140003440d06000400d00c0e02098900003a000050340c01004503a0000402c481a901800660424000038420544020740c0301c41010000402c010300c5401032548030f005c1040c00d0003109071b07180055452a130111002002c907005064035103000c040e43d500c43c1035014060300c11200a035458403242d071718141e000d4101d640440d5084 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 60835120 1250 60833870 60833879
    0x20a051204080709060b16020105220e06060301030503070809010c0804090c080709061409030309090f0f01060305040c030f031413051c03020304061d0d03050a0806010c05060105060f22 81
    0x10000b0030000c1021302410042d9070310f054810396071400360340c820304010303410343c50701c80d040da03109070190758240140b0411040c030001030081800000c810b6100c1d0015030103001c00081d52514100c3c06580c102d9820001031880d140165454281d1580601641c038144919100c3c254081885030014001422080300c0c00607580940100160004074014081020020b0400041c40469800454800550060038489444071041c000090443c0a008a410f42004005c0200441210320b020550300030f40c50b0400084491f40c95050032401e030340f0100c402410040382c449080001510749112000c13210b002e40f401c2c05801e46114403040320ba610031601d46407843c2e2a10030501a0345402004840c0d041900041040300e2540743c2c5d00a512800b85102c0c010902100340003840030a01c144125841032a0f005180c5074900a507803801928540000c00c20030300050800000841550060003e0224203400400510741c3e42c2c0f0b080d08102c03950b440080790091114041c044848440051152a0781c085058110a0006400c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 60836370 1250 60835120 60835123
    0x8190e0415080c1009090903020309120105040308060906010c0f05032502240d0e06010911070b0f0a091a160f0f080a06030b0f0a2415020a05120408 65
    0x4101c560440c4003000795007000071550000d5100340000741a60810b44192000c0010349084042e40c1c06440001c4c200000340d82015400b1004001258040b02c14030881650040614201e5600b1180100491f000e640400d1440ca803010840f64480d10514020402c0302d855a14680000e030028801c449a910110b40e628128807503500c406007108071005800d11980081c0c0001c1d20b000400d0181c00c12a00d107400d0603014408805045030940004058107205000c150202e061741c500c401d00c1440072007480e080395490703008070039811038a001c1d070010700e84049905e41350100c0784078010162084807100c4d952f0101800180c6400c2c0343d801c081e5125004400036260540440824140380950309040002032010350f5115a009000c000002e0407902c0c10108603031f151000600144915040a0005040142040100d0805c1e86080340305407a041c030b0610141c00046010b60100c0d11200d91020014000c20303051081e02c054513403c60170f090b8180b04694488905071a11400c01803030205003046070b88001000d0001450 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 60837620 1250 60836370 60836381
    0x213090212100501020312061e03070605070605060d020f041109040905030310050105070f0308101a0901030c030204080706120f0507020601140102030909040323040b041404090f0201080408190e04 86
    0x1828000b1b18a0103241c940340140d80c84000300203a108405244500515401f0040c1c101006440a0f00f201e00340c0d45c48503c0607010342c04c404000c6440d06d00f03281c00148103061440024084da41d020380b0401c0381a40800800000e0104c0040340b28015a081c070003603503580e840e802907411a5000f10040c580d6410007104807407010041e03400480c1400410061240007503036079a01d8800395501031030404680c0d00d9a84d1070b10a122a19400010306030207055201c458180524010047e18000b40c80400c003a62400e40154168051b51141c40c0058000e64010007101d0701403402210030900c1d0280008016041800c005c00f21003080e02c404005070b11044c0107003c050012016000a00c809000071801d00103801c0002d60301c0c140041c030003000c224181b580328035500b1282000a440b032581144190300c4545900300d005aa400c180f140c04940c6d080d0040212003410f181c402d6180154100d96000f41d1204d080d001915611f101500441d55031108000e2070a400d00043d1240c684002d00c1d54500030340c4a0b9070020442601e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 60838870 1250 60837620 60837629
    0x10e011a04050a0b010801050618130212060a0e1801060305100b030d0302040506071103030d0516140310060f05040e0702010603031205060102070612061d01030309060f020a020103021309021210 85
    0xb4074008503d204c90703800c541001d0444a00311602560781c45010940019003a44090254102403411050120782c100c64016040e1482500008074050781d139a420806d102080f4440c04800ca0400c00200301c214820521124240d0000000807484541e00d80c0d41d80d01e0040c40341603522100341c4e1420702d48000e1805204d01001c500b003a1500b5800c00c3d007410005007140c412408005c00300010b141c0003081071b44080c0255403661510300c00400c014074020114482c02c82102541034000f560039030f08a1481c24118003524040e0703101d0480495490304041040d0303455841c0203425800d21505120008450401071081c1e480f80700c0560010450620b145800740502000c04110701403503042100300304140e60700080460448856203829600900e002008000401854000206c1c0c211070803030079500f4000c0c462182d4101e038031aa40b0401c000e5600c0504a81510401c036009005030444400d61000d0740c402e0300030340410701c0e801c1c80d1001c85e01c2d0f440c441181243e110b148080d281402e1401044152030301c4040010062 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 60840120 1250 60838870 60838891
    0xf07020705100203120703060b0c01091203020c100506010203090a030c050415080303040b040219060203120903040f0b070611040e090106170c0405040c03050a1b1d04080a02010e011a0405 82
    0x10b103030201c003e920383c05074030601c002081140e0b0001b0203070352090f04110000d001030901c8503039503110703542814080c00c8000021f8036012705580800c1c21a82c800e00c204c80955120700080c05000e00480408800307040041d06aa0451009016540d06035590070520002548520003584003146802d0a21055480801c106116580741000411a000f808400c80313901a0744491841069035481c80040c512660540c0f22504441c0d1505020400d250000010806d410540e181030105642e01c8841a81d00d01c45e9018220360b41c09a00030030046040c090019295440c801d41020481c9201c241c40b10702a5001a44841882141074042c8240007500303100b100701900c1c190740d0401884d010042e0640c1c1d00d101c0d90744024092566080003501740090607100038051644030003035038105627541c03c05002010719404e0910306482400e1000489548010420340f1072400c00c22040d04d00c0e0b03a980c035541d900340c0100a05100395500c070441304680d46002c1c800c000081100800f134013241ca44140610007216402420b203010ba = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 60841370 1250 60840120 60840139
    0x30306010c030f031113260c0d0f0503030a140a0606050301060f02031603090302091006020d050c0c0a08070614030603030403080f0f0a0e0405131203020a020a0b0f07020705 76
    0x100d903402030401c4141e03070301401d0801e810603090310110000e0803038481c0300301c0c1300c0e078049400805c0300055241d1000700c0c1e0058094405a403820312000e15a107070031303007070600240d4400300d0449000c0c10844c0c801515140581c0034069400030382d40304d45080d03910407a0440d0056aa84000401f00f8010b2443c4030342100c01034008110650402c1e0000c0c3c0944418041c000603c040040e401c108688208222810f00c0e120000384c00c104009850080c000c0a03807400128416046040010114014802d09000300c8005500801c682441071400317454503884441c0c2414140240c4244007120380720034001c00d00810b00180281403a07880c043c0005d2034031140c00605071890108005012042d40e001068406994022a00555520b021241e000e590b2142c0c100391158040d01080c440c0c3c480703400c080c1c8800d0b948015103083c0807568030492405140745d0b0840c4028007854140c80c0003104240b00c1d60107803009003400d0040310403c840783c0c0c44a9040d01c00c2220000c0910110200300719080781d0500c1080014401076510030074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 60842620 1250 60841370 60841381
    0xc0303012c0403110c0a0b0405040506030a03020304060315090e0a031d010801051002010e0f2802030303040303050408040b1605010e010b010906110304050604090c02060105190905041121010506030303 88
    0x1055034090030240c10041c3c0c41c04c0010341588240320080680d0401020080701075500c0042c642d10350841e201f1140314500d80000035034141001705005003500d52640c091071500d0b081c40f60940003080c10315400319244c2da030b4110200d0300400038451405509007000080c400002c05190003000940d20040c4c00c1c2e1041d40c01c1c072204040303903084458681501d40403030307455600982104c012070040c290005d2003180c41c030882414800344840070a050b00c1007105540201211180002d4007070380030310039a00094143d4420000140403074880c0e803205030840d128032841882d065030b600113405139030006135000011142c207008001c2049424803034008a000c880000780540020342d400a4504403141c4507c505000e44a842845a6401031007140c01501c4014111612142c880c00000010f280094400700075220703e200204103480c1c41c5c0d4010740780307595080440c1d0700c050401d407405026010241c000c072189040d2041c0d8407603039a520039000c0100c01d040140c0b000c956030b030f03a800c05007940c4024015a00980041040c442c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 60843870 1250 60842620 60842699
    0x50c09030706050f0d0203130302060703090309050f0f12032703060117010204090516021501140d03110102070807050d0305041703061f050406030b0405010803190903080c030301 78
    0x20450b101410701d1a220855070501480611070540c880c200584000100031040b140d003c03070780d0b074200d01a600b00c96403079071803000640c202c41c403026020f40852400c59080007240b8260513206565180034062030320300390014000c14039104154440e11006c1d040070030005001c020742d4044100ad41d00c2945420b4246000401080e1505418001c8204450400590b00a1040f094045400410303100d40b0030415440c00e540c0e40d02d4444130b01d031500c2006029030f1503100c9803202c0801c49241a2071308003003034810b6403080008001e0b14440064084040c490200e000c0620f40f4001c1c0302900305036008000b00f17540c85003141342c0709092990303440040d0306061501082c88041050654402400a01032114954030f4445000154031084920f82d000b2080070395003500c860907503118010b003048034415141400301d012100c0410051794000d000c0d140c0b1550080c0611140c17006001010204d1280c142403156546072280c40c3c40016912003a82c0d105e02d84c0c00080100461803011101e080184600444189041e84101920 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 60845120 1250 60843870 60843883
    0x20f01090f06050c040305030a03020d05060108070f0809210711010810030b1b03090f01061406030a0504080c16080d0804030c060b060d0c111608210405060d050a050c0903 75
    0xc0c00303031652000001c0d03140104c801140c010350380003c00c4036141c41c00c0e904001c010350300182c0080c0940e801d15003c504254043c1c0e815070300070201521142181c2c0300e00f140407107919030000e02c03a490a206441c0d07000c00c8008044011082440d94036a21030707036115142040c0d03420410065609041119001c03c02400740d600001000a4a82c0010040381d6516194920a219803420101040700e000000500000c3c0900213034070503850400d44020b0004503524800c020703402c110f0000040c0c00c00d0b02000001c003001c00617400700c0c1d4824462030300742d41000702041d42d10749806518440c2c1c0c448001403542c281300300760040045a40100040c038000b150392902d07990080c0440300d8000007c25068071001c01c24850741c2c0d00e4050710812907088201300040041c03060300929481482200079954010344010030320340700c3c0c1030380300c2c1c41910882c0e4010070f41051179034502c070106100a61301c00d0490354180b102241a03079074280100408001d084011450b8280880c08404a40000e81403032600d910400000182d9200410300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 60846370 1250 60845120 60845123
    0x1707050607211a1f05180301020412050a0309081209010e040b030124080105040f030f020a02060f04030501051f120804030606030f150b0108010306091b09050601020f01090f 76
    0x540791920000b2012401950314481d120203070401c1004140080804205295024200e860031004041a45000504008001d13401e000032001c01c01041901c01740071048800c0c0c040174000518140c0d032066441e01c44900100c00720f0303a41c0c210441c1c1006040d841840e02c405040c1c0407000c1d00b40421607a4101c3e0681c442d454126040c0b028a8501000c282d6880c0c0c84098441c4000e8000d102181011014140c058445c00c51180404042000800c0300c003c1407040c82c0c421640038804072210398580e201070340c41c2c4d40d0051006046100350f1810300b0040e01c41c0405002e40c040c84a15040d201d40c25440e0035421b459008100d40094200c4404019030241c08243c00011600041e0b80c2c9160111642800300c5a841542c0001e400141044e0303000003000000001e100480780522413016008402e10084402d59000e02c212600103084c020041c070124009500101c0000d02c10b505180040001d2030000c803100825500100b0003d650b10f00f042401e58051001c41c9070f0a080720003c015820741999442140e4824000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 60847620 1250 60846370 60846377
    0x30d020102040806040b270706030e0a0b040201110a080703030b130c02070506030a0b0415150f050702040c03090516050301050106110a120e130509120405180714040608041707050607 80
    0x10404a140c0c2c60104040000015960031944100b5042696111118070689c0000b07490b04589520940c40170800d4012030b0340c402d050300c1c1e00c0d88550f001110501401b90080003540250001c00000440013802440050710a0700c0c00b04030792a8810400c804601407580304284e15050a100c50007840d40415580c00342c0c5c2003101c0071612134441c4030741700008024038079401d03810a2420410042c4040584403140440d0054140c152800c1000c150403182800480c642001041e8144051801440d00e5004181d0540452500241c2c9450641314031b45400c0414484213404080c515044c03241c0c0c03c087c02014054031042c14072520103c0d070700c00801d960720010080138080102460302c0300c0540d486590206640c083c020b0100d040c1d0032640300c041008080036074841c3c80c00d00c50001400c107000100c009440440e50001c00140d001c3d58400d040d1f01d9260001442081080480081c440440380358402501c054903103941c541610346000d24041946000108044c0c00c2c2a034103102520001d03030f002454991141c00c518 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 60848870 1250 60847620 60847643
    0xa03030b06030f0714090307081606020c030a060c031107060e0c0301020906161a0c030106080106090302010f0c03030b1504030308010b030c1b1006030b0a1506020d050a0504081605030d02010204080604 88
    0x10140841d038040c0c01b40d000e506024018001030819000160218044400821210303003e80d5820240e0b074580003240056010b400c10b0080c08080b40495020040a914034100420003100980266202c0c0d4091082100d5041da900082c4da04424208480610411b050b0000c51400c584100028000e024160075940384281d808507950400c188903e04680c16a101240c0415500740748074000e0843e0001d000d00e8001405810002410f00d10800c0c90400b1a50180c50300306148084980072514001c480341306405141e284c01c2d1a20181c0c0300c00b80c8402030710b09000400c0e0344079411441d0040000d081a03001070100d2405000340200003055108644490a0302480800801c2250300c0c01824842c40c42c2000110900d414000010b006441060f5072240300840000c10240301d4209210001c64641d000316401a4442840c900402d4068001064500304500780f0604081da0ba20380140b8244600c0e20900c2c1c5514480d0741040b550400300300c07030f42001c41640020360a081c105034200d6910b001c000c1c000f608102840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 60850120 1250 60848870 60848897
    0x20306130212030304030305041a040201091a09100207090f060e0c1b030d06090e0a0c180209040608010c0323060907050702030105070c110a0305060f04020f060703020a03030b06030f07 81
    0x2c029480340d40700d10310156600c0385850b0401a00504040302c05075003100c040711516200c020b0008582d44241e5058480c0001c0508010514065182c5070100c01106074080142d085031740da8460301500c0c2d120b11580240041c1e81066075080984000c6030480c000309040c800c041c044140369181090b0301080701c035072182c3c88a44401070481c2c0e40015891070740240c080041e00c040705401d5500541c0030784080c2c100911000d01c08035681965001d1a80e4007401941c0700d4203081c0b088400500d4900a001071107000035052001d00300000d412a41c00d5070000c030251b0340d10072030310300469058000c0340541e248400d00503e040070342c880c5032001000f00800c0c0c107102c2d04004002070225405501540c0c00c03250050000c001d6450a20006801d40a800009880b006074010b035420842c50038121071015280d02102402c0d03c0d8503000d1003458080e401400172a03101d4400301c00300b9216102d81019001041c020340c018500390100d03041c0502100c3d02d982c0c901c1c1c0140410820006c0500328002055040482441c1000c1c07083c500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 60851370 1250 60850120 60850129
    0x1e1b15010303140c031902030403120507021e0d030e031c170105010905010203040b0307090b0f070311010b130e030d0e1b1c030806040906020a0908010e0105040302150405070b120403020f0a0203061302 88
    0x1275420060480c0b1001c50340900e220b42c44005898058825915200762008056204403080c000000f003560007a851614100084e2148851240aa8010f001c50f0284080544100c12508140150b10f0019179281c80002d0381c0340e103050b2002d0041000b0b0a1034941c0b03a04140000b5201d1099000b000110360000002c40c00d80c40c411300040009140682400da1180c0c800180055181d02048003900043ca03210621207010744181f02e42c0041c3d2900420100400360180246800740c5050050444035001c1482940740e0103402e0300901c1049800c14015040300001c8160807515821103041d124060703a15000349a0440141a84941c1069098101650150b85201c0010090000c8a600030080ca001080c10f41c44150010030300429686d484001f40701068120001e80e08a84003210b01400580c8100051007040c0c1150398250b80040c0103406039122140c4403030180a10b0345c805000d05a0500c40740c4100014954188458041c11a81d8009881d500c0c403035400207680c800700900303500c000c000915070200c00c5544 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 60852620 1250 60851370 60851377
    0xe070b071704060e1e0901170a0503030a050f091c0e061e0405010201060b07050c061b0a03200d0e06031504140402040e031e1b15010303140c03190203 66
    0xd0110050b80da8646901008000410346411300d40590381e545005220140402c0c0d0200782c0e0314018015070b20517842c05002c58040315400b0100f0261740215001d10020074800e00080d480341c170f032410010800782410070400d08510781c0144140401d0b01700c410180b41c41d4413407040481c8003803c41e240601103c905880003d505216030442c42001001c101080b910b4915800c01810445500341c008220b52079442c01142128450004001c020b034000681000e102e291407006094646041e280c0c50070303150501d0303d44620f841004d070002d5010481d03100910303400440b0301404c094401182d001a020300c48811801508031519225610f00c50100440012104080380301900d0007500010410300c9103444d13040103100c0101342518160f008a00b0701182140705103000045070031985282c00c07550714000c0002c5643d4003a070090f440c2c00030031508143c1c0c402103c01d0100450313458940c66451494465145103809024280c02068508013a03800f4040c4004445001c000d4804001c000080c000104000034002ca05610 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 60853870 1250 60852620 60852653
    0x281b030e12010f0c090605071b050a080c041d06060411090a03030e0a08070303170c04030c090b09060102070510050702061207020a03030c020303060a050120010e0309010e040e070b07 80
    0x4001c4109088202415000040640c4480f0000c21031000400c004480c0503403640100408105c04008400015200030a0003070b003105584905081941c690000405100680d40103040d10342c40900142c606150511440c250513003501c07403046442d4121210b59480c0d610003848a48034594403500040e150f01280308682c3c0c1601d0040100210544a00d00038042c2141d20140901501c60355001207240e0b200010800140c0c4c0d05900c0c1c202a0b8000c1c04892640ea100c001c2500030351071000d1000200144141c1c0910000d881c1584000c14088400d000740b20800c0310041c030031411540540420807854417010a040b08100702854040e50307400c2d2600215410b0711035030321400d1040b40c1c2038040008a03640420800d840307134881d50b0180080510710000f01c1c4d90380016142242d0001ca84e1808004960080b41a50700ea032134005080f680b1280c203000586c0c215000458500c20130707080013891600543c0d000010404401040301d040010030f45032410503980b4800c9010703004556400084003001d00c48815518040070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 60855120 1250 60853870 60853879
    0x10609020a02030d050105060a02060c0a11011b030507030501030b060d0203010207021f0f020f0706030b03010f05010303030c11060f01091d070305070302130c080a0b01030b04020301030602281b030e 87
    0x1907100340c0000750749130b0000716100029441d00700085010310b012400c840762520564018841c0c0e03183c0c4113034610740307510101003141880700c00300042c01d00040c00e004404400c0001c0d56007040d04101494043d050f1480207000408142c03a0600510000303c0c004ca1683d0481d03030070b942c0301b55030000f5880072a00910811001070740c4070b038030382e000949002c80030188038010b8803c076039480804585d480001d1ba9038039071041d1a0100e0b40c02205050000c64800d41c4051036421005002181c82e40d0001c107543d0842c2e40c2a08243d001a4450310b00b410f011360804619051a0b0700e5000500c080c1c90403040c8a06410018003508100eaa02c426229000080e1814020068030204058501c1550b507450400e5941c052880202e0080c03c01c0000e400e007694052080805805058482500f5551a241038174020107181e00303500d052680c0c601100c2c1300350b00c40f031010b1800385124280050392030461042d0440180f40e400b5006900b0dd5840502e500c2c8540c4c08110b0300d06100040f00000d54010251074203407001c00e48090600e411 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 60856370 1250 60855120 60855127
    0x11040908030f0603150c030402010f0e1e01030501060203130308030c0c030301060201090b0a020711130615030b040f0207020a0612020d05090a0b160903080d021306020a05010b040612020f0301060902 87
    0x140e249902c03298000e500450032611440340c04101d003101e03120115024440c9580130300c0024095406100d85d10044111490718050540e02c000000d94a00c8001004901c4581000c00c0b82c100c0d560584201400350032140000c500707001000f501001c031282e81d030000815840c1c0200c0842c00d45084207080c1e98a060114080c0da0310b1350f0712003400030300074140301c0700039a8021103007408210340341d643e482150380030b981041d00401522065028010181c2140403106c001d0756440e10b0004a8809900c1d420652424998001c20200c42c40402c00060740c02007618042075610402c248401039540400900848483e414960481c600141107030000707000c0c180300300c407203103007401d08125100c98041040310115201e800032080503196050001c00301c0000041c00e001150001c075060011031803102c0a0045801c0400c4003600c1c090458880459010107640844050384c4112050010405d082c001c0c401501e60031b03038080200350714104590f040c00005040181c0079240e8a061340200d51402e40110700a4138040c0320a41d40d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 60857620 1250 60856370 60856381
    0x302060c03030708100e130317070f020c0411030609040c090204090605130c12090507030203070b090901090506090406091b030809120309031015031b0e060402030907031104090803 79
    0x2281e41c8121900c10003e04201c0002d884544e070f85e50081d00352100700c0004901607030755402219910084000583c18810399203038003081c0960b0785100301d110390210b5664100b1490a410301916040022005610485c1010180107290b400f04003543e80c0000c044171003417901d40f19800d04c11124526070308106035a500014011a01034a940c00103c1140d105480c514030285007024101c040f129154950800604c410f01007400002c0307150040b08846006200341c840296481d07001a06d404d80b1a0710050070f2a0005c034494402c1d15000300d4250050204440c140110310746540013800c46180100001c1c00d49596106886c1071100c840412084001c112a084000a4580c01c2079103c64000118051242c030401940701402c1401009030f9541e0701e00a402811505100b180c100041d100d2040e500307185265401001020034100c18001d050000003440008035103003420310407040c40500900b01e90149004000b400a0311000142c02c0702180c0c0c004075686002c540120004002c1d201c0007001a214003070110a009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 60858870 1250 60857620 60857623
    0x20d060c08010e1f030b0a0209030726030310061407150b0f0102010207080d0b0d0f08030a06090606050715060807061e0c0206030c03101a030907060e0d080c070302060c 74
    0xa0588a4040e00d107246551100242e203440f000a04d6130343c0080c60701d07000420000c1e00c21000c2c01c0c0c004405000160400b4980e0022a18210140d84941da001130504080c9012100104182c08014140d402451a62808002040c900a041c6c441c10040110b415401d00c02003600c0000e481c6013551041909191100112042c006418503050701c07481400e8241c90300101d98014402c4038600703540014030500f45040f10030440000e05641c5603280c1c0100f0115031500001e070711054560001c5209000054482c00e0040c840011104150020048149441000d0019a80020561316099804000c49456145024031140508001e5104000500c46c015000c12140c0d000071100c00c07030b881c0c101020b000c50480a0000c07903c0c9000c010010750064170400120b042c8080707003001980c0c40a140c824010165548804034031302d200e4030400300d5001400100031b0100c2c07000c080c0036100052646240c04d2040042d000006011600e90100081c100b1500003074464031001d040c000c0000031138004160b651aa401c05d003109 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 60860120 1250 60858870 60858887
    0xe13170d05070e0603150915030307030203130e1504020a0903021e010311040f03080706060302090414010506181f0e1614160308190504050106050109060503150409020d060c 76
    0x8401003191640060502e061036802c0d40c2c4a01c0702d003031410b1006d03c2060188100d07001d014221481d02c070107141340e45986460401c01451070034401d40c01540c0e10030100c40880e071050f4103034011020166505040c00b0354200c4ca00c00070901d007003007200d005030ba51707801ca403003070798880c0b21a0f2000b0b401070483c0701c1d0101680e207410031226442800703881c00d2040b0502403030954901c0c0703d00c2c00b51302000d9108800600100744000081c00b9594460000002c0083c5c5079000208007240440d4221400c0050402031403848100703000b03c50300804103076411300c0c0c07244038460041c4c001c1d01d00814500d44108030010f4500508040400b1100403c0608418226801c12000c0710312412a0180e05201081007083e0361f0084403050021a4843c810803102050581011f640c101d60004000c3c0406a071080c0300c0c9085c00006615100341ca0050b4800c1d0000030b8450310340300c0050300141c6158401014040d00380100110401b540000601c00b8204840014800035181b0008070003c680c103001404440c6442d551040142c1c000000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 60861370 1250 60860120 60860131
    0x70605090316030c03120504030501020d020a0908030702010f08090c0a030807110130020c0303090109120c1a09030f120609060a0b1902010209040e0a0c0905010e13170d05 75
    0x1c0d2948000451030500454450b4400281004e10112041001c101481072001d1002d56a103022450700b65aa00c078240bea801560001c0c6206600084602d1107603006040d1400a01c8160007640c01c0c805640c001a00c0310500000040922520600195400c001401110307984500248412641d90322400d104426800c9454200e4140c0da110a81441d150b01451400b00c00c009980004210600086000d031024078100d41980c40541e000e0103004607014041c009107108030302c0c1130000545441e00e42001c1c4d003402c41c0b044460080c01030300070240c008030b480c1c0200b90821100d203c109107141d440c2d45488038554442c41b44410410003011a0040d000136444903118065034044a1a05aa40b240000c1003d034448911074505140b5007001200c01200c0603c040110020080c000182440c6290000c0740a803005042160641e4120310300d00c00800060715003080c05440c000d681040321758140252480000c02c060502104080d18140d88030400c048280c02d035907103403d003240329500d0f60410300c001000b41000303650 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 60862620 1250 60861370 60861373
    0x6060f0d120c02040207060c0e010810120f05070302030d0503040c0503010203010e0604091b090606030e0a0215030c040506070804030201110a0201020c040c0c0b100e0915061507050706050903 84
    0x1a840440d19015415602654010100049003521818207840d00c42d400301c4200d81141d001c0c0401c1001c28668030524469440310f4a94010190490b400181580300003002e03045050750b4024240712080e8120340b5429229400614100741203030314102280b50681c50351000754103100300000f46c0251540400618040d6220b00c44c030601494070350041600f40d020034051028414400c500080c49480d1581220700708502441807255031018804441c0010022034204568407520b03200c0400210b42e0500c190349544203034902070102d00c0c0c0580c5c0064000085c5022590781c900300400880c0341c60802d04115030007403500800b03081d0744584500d025039807600588003c2e800f0622080300940d10000104140480d6030f4164040c2110b6030010040000800c200080001001b0419030f0810020701d40f280c01901442180d6441920f1030324041c0c050710b501000808590582c1c000580c4a12800800003602d900320404940f01103207220440c412040780d0141000161140c4249440024041c0d0804d00a0000701130640 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 60863870 1250 60862620 60862639
    0x8120c070c060507020d150902032d060f06010c0302120a0f030608031c020d06090f150b0406020a060b150a030905101406042703080105010216180506210606 69
    0x1a920784c0101000030750000180070034840090501007001003403080c640750001e41510701d40c01081c5015200883c2011004003122104030b100458000d4001041c640802842949000c10342c042c00031002401c03240c140710200c91040f0415000303001d001c11000300e0782c010580341d541d801c1c001044904030a5032140813a113041008078809901104807810156000c2414100c0e2074000382e110001e5001180e003100c09035440501040062241c002c1d404c1d429071415000c50241d01d8200480300d518071543c030000e458001040308004903a008100020a20780044d800100c15103044040b40f5078034100c035003a116051000403407808103a0150f109480301400b450844580b100d883c000c1d4800c50304a10300c0c0d200c1082a140002d0707a02d1900d0340040000204880a107003c1188401e0061290041c2c100114080780d4140cbc01440701d540d0400155010b4515500035100207440c006072034049002115004e0090750b129400203180d52910840d44082003175070800072580740c52640c4030b0740c0c6521058070110302c1084840f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 60865120 1250 60863870 60863879
    0x9030f0607090303090f27020903010c03020903010f020c062202090a020d142e0509012907020a0918050609030408010b040b010e06030717100305060a09030f050708120c070c 76
    0x4070b40701007a55142802904030740e87c04d103407240c1d822900c1c54051400356004c0065445c40c3c0c0f028000c2c0c03804500f1507100562102d41c240d00701400e4800d00490f4002041c03040c040c15515040008440d03030040e0300c03c0307141c054002106408a07845296954040c1d00f010b1003505001d500b41d4994024945481c00170010000742029607001111010252900c645102c1455040c1d04101050030b00d034001c0050103038007650419955004900d400b40c1c243e02c10188401546104103010140300b0304600426021013200307151600c2940007072640f010500919109554400c01004d4044e03a5802401a15030008100c3c2c08601d007600c002c40ea03943c0302e405440f0641d420050124041d013024010380c1016030701615144001001c0c8018803006400050401c010080d513070b0702c2d400321010602d1456000e607442c002490703503090840c18000e14104000d0f000d05403d52811884c1804070350300c841d54401801462900302c7c1c3c5c82109082200c2e0300e004a10500080c0c4248a0034014103104041c020a0224400e4035101d58031a80c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 60866370 1250 60865120 60865139
    0x10902060f0c100b100315120f050f0309090115200d0e0306060a0b090a0b0408010203060418120e1201050a050405060c3406050a15090b1509030f060709030309 70
    0x154814545c212182c2201e030b0403800c1c0203800603072184008880c83c86070290b5a20b0280c061812108094406d5031030a4240b40c148503083c803d0070741c00078018004600d00a00c004c040707120114144510702100e141030340710211543c4541100100c3c0b42185070880d40e20795500c000320341c8803150440f803200414103440c1280c1460401040072803007000b0041441164924000701c0034a580d0000031620742c0498041c2c2e0119412450f880540003408080c4001030300e0b072502c1d03410301040303614a000030000240d000461074002040b00321408a60034003460b2400c00000d00700b001c0342d0b00070381b411a415115400c16003004202c1d0b01550020340700f18014012503109403a01920314440c2c0c400c1c014481040c0c2c0000c14a041c40d1440e810120510341c034842501c2d503140c0e005898000459006552841042e134a44200990f007401c0d03081d48001519151a0030010901c0900c0040c0c1d0207941841c0d5183e0400010030424481e650512641e58801050300954680d07140c07078040201b07031205600003140803901034000030409004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 60867620 1250 60866370 60866381
    0x3060507110c041a06180306040b070305010506041211041d01020c0106090b0109171203070201020901030501050a0b07034b0504050a120507030c08013317010902060f0c10 75
    0x40002d40103001e9240c142408200c1d0701c8902d62000304a1207006c0d2100d1600c04101c00c92040f805030750101c03010b0030030410003800d803038042c3d21252113860144418441c0034144e1a1781803000e81d002c8a0000c1c500b46550100f40034001031031901000b25400106008082010b400030240c054807030001700708654031442e107101110b60100034a030000341e80305800d0000340100c14078500e02e0043d40e81181d400e406402018021940304a07184c0c40184d401149602c8a544c050140c0c0b4017500341103d50344c403658100448811a401a0040a820000c0b00c1b0fa030082c01c86204800c88110241540400c00410302d144454511049010502c04c0c0c144650400c4500081c070ae9819501a100000c0c6200e00326854140801e2924665010584045c061444000005981140718500510995001180c460021281c83c40240d031041e00080303001c0803003c07070280107010044007001607810b4813241e810910705948a1074010100e50400070b4022200250107078107030351f41001820340080448101c50788564a14405c100f550b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 60868870 1250 60867620 60867641
    0x7030c081e0115020a0611070209070c170f09030d03060e0106030902060a05030a02090310051906150503040c17060f09010e15060111011104080d110304150903060507110c04 76
    0x8414200510140d4448800c6140c4000b03d841143c040031034649840c3e0886900780c1c40c4000b200383c000740010850030403000c4c440d440400e82c281190509020340302c0c0742c0408440c07003045944581c0050b03d0130072400004c0945880150103000c03901f000750084000b0300100424014446c4510607240001041446400707940c0c14158054100c1c0e050203000d1400352220341010f00442d80c465024400c1a085440400100e68030100d021000b01da83d0400c1144040850303408076180c000c00d0b09001040c840314550060f141145000d03071500c2680e0b6074850130031035404d036450f0300094000d03400303121808060400015014001d1442400020207074031990510341c00c0382c3c800c82c3c4a4450b42c10006240b0b00c007149900c1203552048042c144180300b07103900300d1030f6400c5a030540c1c1c0c041810000460300340703c1c802c0200003c0100c80028182088a007160044003075172805a440394400c6000126540c1a00030300c03a5049000850340410144180e0030100809000c05420030f071072580070b100b100c0d92005075203024050b00d54040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 60870120 1250 60868870 60868921
    0x180f060e090a02130f1b080c0c191b03080919030201020c010e0111030403050102070501180c150302251202010203010b040302010305180d080906060108010303080c0d0f020307030c08 80
    0x2c0c000b075400e202078054031040c000389a5036100c1074850343c90114010200d5820390a01010b4011a40710300281c10104044c0506012103014461351201d6031000030904444040b105240c1c0d1090040e00e000c4510903048544d080040005034000804c202c500d00113844060781c1282c4200b0350200310440b509000b40c05101c00390042c1e02c003450205003540503030034001c01c540c07041c034002c0d4031407a41c3c5a100f4550744c0154411680390394001100001d1040a200714080208803010198a20301e507078403400a85e4040b4010310a406e80382642002c034072402a4107d41045600300d200403544461404072a0014061201c02d0750010307400c0000280480c0706100701c2c2d050300d00f50040c4a09050031a00110000c01c8001c1041040c08416070080d58060b400300007541c0300c96402e5489601a1501e400054200f050142070b060600061600510010340c0149c00103034850000100751380c40d210041d5161001e00b0301e00c1e96007030413544004140018558180c220707081c800c0c2e560303c8916080d00c07084105038810b4014411190b11 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 60871370 1250 60870120 60870133
    0x103030f080f070302221502010b090112081c1506080f0f130c0b040b040611030909151c0c09061409040f0804090507030204050a05060306030d050310180f060e09 71
    0x1d60703010b680600900d0b01a09a40d1151010205800042c9038060b00301c5255030b902c1c00703030228200d81d090003000c0f149207092f0341100055140c100100e05156240000070400c24000c114002620800c000034400180c4166003440285950417140784000702c24000d41001804200000d81250340c8880315074011110a039040b04540d0300e21200b18010b20300c902d0304840840c000d4800140000c2007601a0000c0c1501802d4035036180c1c549400500445050032029066070018040d04540381d880c24071040e0300103010107501521003054000038100c11548045840581a041002c0083c00b00c0822b503078050724211031041100980310003c0e40004d094001206e54800300034400900042d40044041c0800d81c400c40229052039255440130080c0c2d40d04440420010742d01090030030862510301d2442c4010282030714068654241400400e0f190441d0b901a1028000c00101103415000d178107080d0b10050140f00c250016540851034840c0242c4030300783c560f5012034200f00380450610112500b0310b000e400a80d008040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 60872620 1250 60871370 60871381
    0x207030c0b0c0403020a0308030105010305100305060601030507050c0f0d080a0b0306061309240c03050103030512090f0a0302030d060602070b0a110106050a090b03061b0d0f090210080103030f080f 86
    0x2001c2004220740c000324030a210010061b1107286c0c0e04000f8600c59041e440c2c9070344c10040018106c920050514112100c2520100080b50000c699945c0100080c41c0c0030034156101042a201d9202d4003d10f41140d1040503440e04036400081100485010140d540c0b01c02a2100844e2009640031034050702d905421500225034103140040d900c0311442420302000c51800b403280c0302e2100c81c84810308943c0d42071203081d4084580589500c034981c0c2c01c00380740c2803c206650445c0c90040c102c0c024035201400e19104c180101c2c0310a0820001c0c1d04041c5a241c01320360035002030f894001e489130131200c80d54403102c4c02d041000c1081703400400c4401c1612005150107050652005040725480741d8442e050105540e982030204440d100c8545450103450303000004140c181e52042410303d0814003c1080d6410350040c030108500112141c00c840703c2032030112010030600003407106200101007141000354001e1400d08c1044038640c000c24154100d170b000391504c801450440400341d03001c0c81c040343d1051141481500140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 60873870 1250 60872620 60872633
    0x91203110d0b0d1e15020a1d0d020303180915030c06180405040b090d080106090612110d0e1006061709011b03150f03050a06091b0e040311010207030c 66
    0x4040c807400801050032044203442e01340d078109a24403100c02200941d9240000c2c0b11011082d10281c0e103014600314a4609014001010f2090707141c92032804440403081808070356128114081100e400030241c0e40d52b9205142811f280c01d20119586000c1d201103400940c3c038000d00071040000c2c0c0b002402a050009503002005066444141100d00c1c01d20710021031421a01c803481400d116500c40c4081c0803d07410714603242480d102c0025104010000c2c0d83c030062048035803112100c0e0444000e41000389074000300303c080c3c402401001e0001910fa5901141e0010b10b1441d07030b00722101c11f031031850a41d00c03041310005091040e110203020360390201c5c800800702001501c01c00c142d030364041c2d146000081d0200500c005e096002c1801036031400020345552582d082c05000044a0000700415015061003d01d10340c2e61549400c0c80780c07006000e003030707a54885409006082d044040f81c034543c1c4e0400c44800b0384421707a240b80b003482590705500003040140c070120160b205100303c1d505280c1540340c48a00c4200ca0795260b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 60875120 1250 60873870 60873881
    0x306020304030903060f02040302150c0706080c0708120a14071704060e100b090601030b03101d0706091a0406050d110f070b01140303091e01030209060d091203110d 72
    0x84080000420f0000003103138091285025060b1720001c00341c0e80f285140108218500d00f5a510503000c07500b00004180e1000c0001c41004442050030020115914a405401c150181a00140c034400c0000340078001c0400e07860b04030344200840c0d1030400400c0144540c01c03204050454a80c80070a400d40f00c107441311140c116142c0e5026100b0301005c900e902040a440e410400400ca1000c0c00503222800f40a0358a098001c065102e00d080c40d042110030720002c00281c0d161180d000000603a550b8422801d00e84005410004450720944103d400841e0382e540c00402950701446442a210001481003043d87d0036141110129143c42d0b80e46428a504900314100510803074142c1c41801c0f204001400d0480062405030650900030303441400258500720800715034a11940720b0502c01d0300104812000ca64505211544140e100c046001c1e0304d861000060f4001d110300100561321900c003003140f61004d00c05421076070542d480750441d143d0b054404d400c1a400e55002e0080401100000e210101c0488120b80c480c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 60876370 1250 60875120 60875123
    0x603070b041a0f1b0d12050601020a03110709060605070605010902040b2505011503050601050a05181803030f161103040611010902060304140d05070b04120c0c170d0e0306010306020304 81
    0x3a98907107032140c3c400c1201c106690803880c0d03c40d0011110005c9568010300030710048007100710107001ea854a0742c0000d40341c140e04000117040c0101c0955515164108120a5005e850360f0101005070a88504c0040c0888d041040704441342e038200030020842c40500d0081d00c0444007048019810b054076051b0140c44414024010014040207a0004002c11005d001d020075118402c0302c1e407004142542065030900308140c019030301401c1a114208030303d4503a80c0070401c0c186545030802c03108c2e0300c4130760002c400081d81c1c100386d910780c1c40040144039100985a80d0940209180040e200032000740340d800b0b9490500c83c50b600760042e001407208020031402069414044280480006040d10a650004001ba002500e01307440385422128207641c0c0080c00c0104c0803000816050203800c000d0f15603600801d9140081004000091808070402c0007400384c01c01202c0b10b540025600207503a140c00005400e11040e01c029101c03882a140f901220600425a100d40d1000103005450075a0071a1030307440196001400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 60877620 1250 60876370 60876397
    0x2d03080c120a0204140103060b161406040312060501020604020108010306020a0207090f0204030201080f0c0405040213080109060b0406170a1e05030c2104050906090c0903150603070b041a 82
    0x4100442501c0d100e80c418003460100581300d074104540c1000c2000d0040c03016040c14504001404040603500a80c0c800b980743c00001161400d0620b0200901e40300586c01803440c1c8140000c0c03008060300104c40800b0741c41001010066140c0d0b0b00c1c0120798444003602c010340850035401c01030001c100c0580003007115804e50700407544459581c0c100c010407102000e80340c0b4031b0103074042014011503030301c205a5a00400d014014900700d060074482000d1900c80c44c82004c0c8100c0d070001e4480c000248070390f4200d000344240c0340204060416418150003401601e554a8400c520784403011406040245540c107600ca00e0f13500800c44245070f6519910340e83c0000c0c010100b2628a84034040009608000400078408108060400f1120001c030000a5251510000e0207844061000b070001e03031200c1c40c6507a409202180d1070300054942c05111030407485031600e82e81c0c01d40220a00e118400000342c00903805160264201d0340d003d56207460841d5140a98000c5c107107518202d4624186070b090100240216914844 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 60878870 1250 60877620 60877627
    0x8040209071e2c0901090b01140d051608090c010804062a08060d120804150204090b01080606070803011203110105070908010c020c060301060c080403020301050702010203042d03080c 80
    0x104969112100000010300190b00d2071182419811003d03848900064603101c03010703082c11020000f8407503400c14081c8040e21955044804d020b03a00c18440070384044003d5500b15034451130507500c4005000101c0308044111031402c404403003036214407145449811400701814950358003400454550101400546006403642c82c10300c10780c03084400503481031550b04480342e18801840400b8201d9400142003d2156680241c01da000c174280c1c40380d08000040900e008081543c071031409031007054030351b0351100e40c0324404140420b0050444d800300448071403d8071211120f40d11142000308a1243e107500814070300c0140f00420062000903032201d00640310b81440c0b0a400300c0c0c0c0d0200c1d0300b1110201c0b03107400055043c04c010028480d0030f10900f080107180d071014201c580014000300b0b45030700c01803045804001d400006842480246000e0300c0145038020b000740021308061000034040d401c140c2d0140c42030341e1000c043c50301d10548060480c040780d1148014040244854400303841e03586008207c40c0b500390040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 60880120 1250 60878870 60878897
    0x7020402091314010603050903030105060c390301020717090a03080c0a0618050601060f090902040e0702160e040b07030b0d050a17040b0f0702030a1208010504050a0501060804020907 80
    0x100a034203400c0b455a000094070383d0103084111802c0d941a80b0030014185000d060285120000c82181e0540f4821b83c0d0b21035a9252200c07006103890001c80181315028440d0030300c031510307407036242020440f0464a144030b804d075841c0f030080601301c0c0710b140001000e840b00f042032b5101c0811400064540100000d064800707041d0f507a113400000d40d000d01e04044140d04500182410800148583c0100306210f507204402c815a59a602d955030806002d14001c0c005d080c4860220f0a00c200c8a850281000d40e1065489598441c6003400011046c1c4104001d80640c40030021242d058070050000c40340044940d4820f51101d440390780302000c0242240f01016103582002059841d01c5000502042c821000ae1032803120340d0805015a070281c0420700000802004208000c40a65003174550140307110000c26640d80180c40003e14040791b13058003d01250902100311600c41e006103800d030484e1001d0f074003401181d880034049012160240944400315100310b02003405401c1c003403007ea0b444400740c10110541080c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 60881370 1250 60880120 60880129
    0x403050a030e03060a0501031109040c0b0a021c0f02070b031e15010201050a0b0102030a03180b0f0f06040903050d1a03030c0109021203070f1412040e090f0a170702040209 75
    0x349001a000305004142d010400d0504014aa504c0502001c00300100c0d411a5656040e131000315424610030130010b0081401d122554282c98000e00c0d5400260f60369280303c0d00069101c072500321078400040da40014040226002e0311400000082d2540500703000303410030030204110380000c1c1031001d082c241804200b42c2403080d480310038043d00b007500400d0210310800000901b59030000303004044a0b03051141024a49e40c00000340d5040400900b00841c881c3c80662101202d26001c52014088110070410303c6442e18a8140c880e00402c881050468140e40d000c01748000c0d141c50000c01400100c0400c00c17000040c14642c00720062200941c3d1010403a80402e00103461a0090420704200c1d9640b0480b903021032420300242c0003801d5a101c05107040c603283c0c2c0c4400351120703403002c1c02416041c12010301044000d0103010216582802c9401c40c1e0703c95444a01800d0100c004948104541c403800782c40035511140000c1d402c80c441e0744901c400b1200c0d8a2100d003446250001001241c01c550244444801c0b5130380d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 60882620 1250 60881370 60881383
    0xf09070e09040510110408191709010e090403030504020901060906051215040903050d18080d021b01090b0105090105060c060714040509090a031404031e230d08011703090f06040305 79
    0xb1000c11950301c503070800c04090f04040c8005050f100c1d00d090131030301c40001008901040e03802740843d500251603000c2e070401601e1401e03030503040d568030014010400c000c140d0580e00041c040c900a5680780466a02c80c081134078100c109006800108405203c1d1380380711a45050a01d9001000300349950048140b203011070b0643ea82007400720040340703010505601e00c55003407290280300c1d08465461000710b55591036a0f100c0d40b1407203201460440d00002c501041c000340c0c038070f40a500700f0988000c0114074058100800148003c2c010144203003d0030000140300e10381070301501c03481d400d6040544034507100c8000648038200006151000e080c0c003404000303850b580d0134a580c2d01c5040307400e014040e0fa00491400501c6a51900429041c0e00828441400491030402000b921042d0b1071007448928081c50504a2118460200502000d000304030461201200401e07140c01c1072106465043e6141d0700d8501c914140c0d011040a0314156000b40110403440c9445500b61000040140c0494a002c1d00ca4617030074207148 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 60883870 1250 60882620 60882641
    0xc0b040c03050c0d080d020a02120c01050f07110303060405060112110d0c020a24140106020f0f010209030d180e070503070e090709060e04060b0301080c0f09070e09040510 75
    0x800c042080040c804148030081c841d0004035070301c04d0078004035510b04419000355036010120903030104460100e00e00820014480000c0c81c0c2c072050311601c0f0004410702800d011200f9050458000020030402c0740504143e14012880c003020314210781d120b8040c0001800000c00040c1000320022520f0111704036881094400f1a42010080d03032105030900301e0003a100524a25000c560041102d0700104a52000048950005d00c522039103505425a8140241105200d882042030a032800002d0907900080d50901c940701c11000e450190180c000103900301c7c040d250a642c1c1580002018000903072181416001440c0d81e091500280c5480d15400d000c00b84044920402090f4000203000700d89801c0700d004022480211880c0a5034500f9410040881e225886100c0900c1509201000c82e565036421a2000c0c09010700e0184d241c2d82e50309401582e403240c0b25510350040c00307126110230190074109a214840c00f0183c640200092000082c06600c1d603000f80262010b0240240c1c0070442c8015005245940 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 60885120 1250 60883870 60883883
    0x323040f02030a230c0f010206190e1c0f0e09060d080d0603060624051c021b010b0f0607050304030305030c190e120c010c02040e010b041d06070206071d010c0b04 71
    0x5842111304240b81c1058040c015216614507110b03c1c0340d91f039000681650004c0d035044429207014549210901034445840b95a02c1070207269171039829030380d00b030034545500c08881e030702c917105400741b02019603c1000e000c080f00d03007110007000069120308005007100c1056106030600c0749404c0c403680c014000c90710141c000300c6d4000c0d03e80380b00300110055000b43d49001400c0001102c1800d03450f2901420340d100780040f030001040c5074454100d80c48019410340c0e80d400362020b513902e00348030100c0c152802402c0525119120b212000c1d01d030840f505181094030241e076445002986800c4c19034400b9500d68200a040441918040240900ca48006c10300d8442c14007a1341c80f01c55108180104002c91280160019130303032640000085600d07680e1049200141c1d9806450014000794001c001a014004100c81c03950018107000740c560144003503503070b030311a02c20080d0182e032001d4031006012602e0302d00c1520041c00040c8800d404210380501085803861611050400d11200c1c00c8c0351f656550300000403a003e80d06e4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 60886370 1250 60885120 60885173
    0x4020304060605240a0804030903020607030e010809030a0207030f0219080d030c050a02060622140103020a06090503101104030209010e0a05010603200310080a050d0323040f02030a 79
    0xa04007050084820400074114549003001c0728686250360180c0d140c00020441d444000c031f018503009051080c051f5070080c005503514005420040d140505010300d5074002505400002c400000120275a140442998060001079181d901c0380102d00b8000d5500303036400000b01c044d00c000c1d40e01d0241d10400900c12040600580c0c000000c4c06001c6880782e02450003840403c02042c1445940031074001e601120894080c28074608a020251200f0750107822003000c1864000d01d4120140c2012210741200c0c400c4400030350710398072a2001c856a140511815805910a4031401e91500d02da03081800709404145d0a10704065036a00010306040c03007a40420b075595041402c3c024090024000c80e8090280d9040510485641a690b080202c41820045101400c044040b40c2c000007000c007684e00406905088503500c82150806c913845140d410b1003074003c24901558610544a241055a459000d581404015954545410404144603001284c0c180210501350b000100d1805007480141449e0024028 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 60887620 1250 60886370 60886379
    0x50703120e090105010f111603050f03040303050415020a0611040302041b1e0e0301051e1602070603020c100903050c1011030a15080304060512060d050c0105090609040203040606 78
    0x1203a5014000303041001a00006148540c07200b51445045940030720348a00038044c8844101c03505c1c10714a0101486025094020b000c100c0514a03034403d0701e00075410749205402880d80f2650324425032000801049080c4400c101e94101c07804251400c04260050300c8070399005684035401c4070101412020020400316052085d802c192181c40862020500c0e9102184d07641c2c01c004e4081d0501c252070214005100b4800242603114064406000300702500a02c154101a4800a03141075004904070001622900040703880741030300b0050f41000c4194001d8000703c0d0400304200d01a40c0300c461591503606c00e031030041c003903501c0070b00c200e0240b00e0182d035800d0b4403400c852000e02d04081950303250a01040c1031562520115001e441280d412075041600001e0074001640300d04801c0031150f0110116020104000940f1904500148400382d00c0c1c04000500e959003100304034494814010103001940007014401140d40290000d00300010014070981c206680680001c00340c0c3d00491301240c00907180d240400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 60888870 1250 60887620 60887633
    0x3050105010c110f040b0910031a0115081e0a0b0a051504050f03010b1201020703021615080901110408100e01020a14070204061206050402120705010c0b060418050703 73
    0x180940024079284055807070715183c04141c2c03410a24482e2140c440e051440115175110360001d07400c1040600040082d1500f04144110841c403444250707602e0440d001390b62664245c4135401416101c41c070070794614454411404a40842004101c160a10f010030300e2680003801c507030b02d0f8500c5040e0710701d804541800c498041c0711944e122588124000c40007910b4030071541c910b8105580980b5030544014214030031034000203024108112405030840c3c0b00c940300c0784601906400414025009030221800381500070358a0480111134440c00c0301a18607180818091481046020b42020304100003280207002c0c0801203000d40e01c5a8415101540601c11205419072603015a00b061020000210b06081c400b44016000800b4220200402d000020745002156200c1d403100000e070143d181001190351072898140001d040c2070342c0692140800d107111142c6900c0018028080e00c0701a500e4410100c29030384c40e100704610141c0075a501644514404ca8500180d01001c3c901034040e00042140c58614242034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 60890120 1250 60888870 60888881
    0x161e0c08070602032d0309070906050d030804030503040f0506190609020c07060c060e07030807060b120c060a091206020307090801020f0901080a0b0d0804181e0b22060603 75
    0x40030241c01404081007065004400d40b00c903d41001c00754244400f50070b0000420081c02860b0126502010040c841681800a0306100b5184448400c00549485508203c0007225003040200000c0c0c0c51800500007a00c0340c4080d51304070380300721443d5005040700d80d50b140c207181049904904d401800106000111014000c060080105002c00c520b45a1740030001034440c8410301a55003400600b50b503a104010850f4820000346d40180240c9408548030300d44040035520400042e6203860401011060524001d041b2141b1820f000e401420180da030704040c415160094000c00c0d050140141d00001e5481440344107a81c000d01c1180010f0780c0e40740c440030281081015030010040c4e81e1040c08009400602c503021240541024205041c4c580d95122001001d421803075007554108150846510400800700c0145c4107445c1e4000c982c07040300071048656802c582ca0f100e1524140c0d0640302041e0b8114403641c0c84482c1c200809080c50b1400c08140200603020080300045440c2c650f03550604009156151141 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 60891370 1250 60890120 60890129
    0x10b0108090a02010f0207090c05030105010f0809100e0c091f1d04080d02040902070f030306080102180402031519141804030e0402161407060504030206070305161e0c 73
    0x40c10508082041640d180000c490084c1032103151101071201900801240c401040c10500c103201003c00b0000042ca00d0304280b091602003800324002e802c102307005490407071180361070000400611484203280d42c00742485484100a034010051442443d46401030701034071482a803110440c41c490980000ca45088003940901356103407a910000c2c0d003d082c1001301a410070b40003030302140c0305e100030f1081c10020b01c01c80d031021041c94030001d00030b41042258150190183e003c0d4030108003c035620b4428600340d20608545081d140c1c45409004075070300e081d50146400c00d0041f04403203070044800003c54032120703000f088880e528040150820900302042816180b404082e19100904d1032410500782020201602c01000c0c8610105041c095450300d134161070507041a25600c1900a075581440300c0101d00c542c5540515000300708001c070f91383d406007048a044a07406400103141c081a920221001d4200c8003c84070f40034204d25105010800301c7c02c200c42c1400d800801140074480d0740c41c054012144a600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 60892620 1250 60891370 60891377
    0x6090a0204050904030324030510051008030409110c030318010501050418020d11090703020d06050303041406070f02220b0f030d031508060a050106020f0c100f05090d080a02010b01 79
    0x2042c03059468a5050704d40103545030902061343e036040075070b0902000500300003803001c1c84800400000d1007000a40341c0384250031a0000c200c2c0740c0760b84182c081000310364001c140c5a640200300070403041d50940d02261a06400748441410b11031004103190440d03000340c4281c000c20040041c092400c0d0780a108a60042204550402c03400120303000700002c011407600003901c2040c1070340d9034406110014414515545004062145500d04040064000d40000c4030902e0110703e04080483c45042c000129001d44001c454004540020744081191030350200300b0485008450102c00d03001a01e4809504003a10001078110304036800c1e02e034410048800d2800b0b0203220380c0c0c04074a100d030740e0b46021803070b45107164140c640441c0d03c4080c0303c031081c002c0c000d5038403150880c0b18031003c01c20240401e030320a505031062030342910342e59040d03419001d5a03204810100e580c002174600c684111700703006980d81000d200e55400d1181c1460034400000e24a50b02a0000342d81078200050301d665a1075084c031030f20b03040315001d09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 60893870 1250 60892620 60892627
    0x201110d091a070501050c03220213020703050c01021305090703021c020a032c0607050f390c1009120602090d02030313140411090409060b060c0606090a02 68
    0x12030081468000d4800e0300000740700b0b088011075510002d01120030082d0000300911540c1003404416109600131141f1524402151108010740491441d40c5001c1680003040c4043e0a116a52120300075840342c0d200310180a0300304180c1050341003c0c0080c040c0d241c80c110a001c955454a401d0126404008121204051040250381c80002d85802d03150040054000c0040e140e1140841c15402044001626252810003d100310213a04121520a0a000c0598144c8019440d8140192010300172000c8200822006002450f10528004405a070f6503441c188224240a9914610240c040a54000c0201c641200c1c1d01e402d054107207041140c40b0744105180c10700004c2d1400400004ca040a000014041c90b000240300c40c050f41e4141c0d5840c225074009040d01e40e5000b00840345020810301d44513041c0060524840700c4481c1c64644a00303404100399060f001d180c400c51300f08000080650314800c0f07400300d9907241038000310380f10b40c0040d01e101152a0010615130405204014410038000c04040e82240100b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 60895120 1250 60893870 60893893
    0x806100513020f03190f090804051005040501020316032a03030b010e010e1c02040204080709050105060703171b0a050a0206130c030308040f0b0403030506090906100b070813060507020111 82
    0x20003165800841d405c0901141c0b4002003154000d85450203070b10b500e2a0405841c10305000300f00000f44102d510803070714451188480b11341074515001d184500ca0158005101107809032001c1100c0a1115120389001c0000305107a03440d02000350a41103a45110111511403502010b801d072084400e41802400d2815100051100007082c0040b024502401401d400340c8035a085a000c41c1c1c00d00724658024420764803a5120111136646103080d00c90900564245800061181081c03002c0b14015509540d92000c0c81e40300552060940101500240c10510311905080c44120402d02402070107c1969620381d07a0714500900030302d040d50181000000b101071580d0540010300440b903c404503507040c18581e5081ea00e41c100580706411185000d02400324040c104001c0580c154450340c40359a04503101d03034098a45c00209a541c0700111a051500c0c2a9501c003807046401c0c1902070101144101985403405403101700403100348403a580540085180030904804640e04a080d14401c110f130071340180f02ca1000c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 60896370 1250 60895120 60895147
    0x501050906040e010e01061d012309091905031305061914040306060914011403072601090609020306060117011a0424180605040b13080610051302 64
    0x28295500c610350300c03d81494000820b400a4a99600380340c001c02003190b541c842134070403154140200751050108000412084203109800101000c100310541904000405224841c40090f040c4000c5224a2038001c100c1c132456201c41d88824402c03400b0719120100c0782d40713490f4204800d4004030300c00e12044c040c0044050041c0c04400108003645001485c0da4801e1a114040348145d8001800b817a04080c0c0214903005280c000d0049000003891145441e030b03039001640d00e0140452100d6905800401b001c1105000400c00f15880305414806003925414888045086500390324044071016190070081d01549014030030303580e001c002800e00b2001003d00d565071168000e01405031121011140c14107081c1c100d86501074402404100d54554454181960318030820b03c00310004100059104c4000020313100264443d0046449030b0711124109030428a1390071564009104920f6040350440c00000d59950400c511802600d81d1908a0142820300381031113040d4500805400b02d16004019041580a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 60897620 1250 60896370 60896389
    0x329060d02031005090103060c0905060c0309010305060102160305011d060408070605040302070b03010e0f01061b0809040902061b100c1704021207140111060906060d060b060f0304060f050105 84
    0x1651401642e0b41d44402e50031400000d907800403074012801000110400070a5840b0b18041d00f010b803101c20180355182e0400c9003902c500c5203641199001402250810b500030b40040b900028140107039845d8800b405500c2c00c88040170362069500e41e44681c200c00341e81e07802c01d640e1b4070b01c680000c001c0c0c003440c58540c44070760580c420114020310107507803000000d06041c03083c883d01d0040e1002001143e030300e584d0f900254941000658002000341003280001407032600132010416003403200ca89d54030f50400c10741c83e1244140c1003003606c580c0207915900c40390b0060b51141d0052182c10555000000020000105140f07021129141052024580090b03ca00d00f500201c0c0c9441c40c1b115440b40e02103c0d61148046442c0391100080c0040a03c00c650005c43e40302e201c0014078a54060a07030350342c1c0e010402d2690031551044152210340c0c01c2e800100105416090038100c5002c2180181400300b042c01d90b42d408100309a102075903150f00e010002c010b20003001a18024401c03000f640c44814800707941404002040d801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 60898870 1250 60897620 60897637
    0x50405060603040b0a091a010608090a05101503050703080c1213120201020c030607030501140303070b0a09050f06040305030604050a0507120213051203030406062403020a050403050a03032906 84
    0x9130080c0014514618a4101d500080d600c89081da044071240b90140d0840c010070700909000c0f4640e800043d030043d000084000030903821000070241318607056481e00c014200522602c680f1406640007101080341000114010f5101e1100140c0c2c4161890800b8140321034841c00c005455000c00250041200d41c802e08000d896284280072040001c510040c1e10380752241d43c0054141c0210002c011000e03030180d104e107040701d004110710010162828105500c0c2e108014004140c10301c5107000c11000b044680c400902984600200c40f0400a10810145844000c480c11000250000204003590405000c0e1503001480501d042c031044c1009180a0040c8034008440d001d9147d000c2180c420541a11582c00001c007405007400d1203185131030082940b81d41c01140c3c00d590403400c09200044500740494248100c88962601c903100c6a2a81c400310040e511003080c4c842045803c0c000440421010320050090741d220352400201c900088084012410101c40c15a616409640c2a82c4094940300b04590320b00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 60900120 1250 60898870 60898883
    0xe060408121e0405011506020109081e0c03040305070f0f050612071416060b06030403090308090105040b120405070b0405030a0303090602040306090803040318051f090503010203070302040e0105040506060304 91
    0x180d40340007505210a5890080d5600100b0410920003444010342c0003171028154040d18a044580340c035016401da035155600200200c01c100251441002040311508d9030074440017001e450300740c084008034510382080d00700b0347d070036007040c141084000d807101e140c1001840225101c0404a00c2e0a000403507d008000d03041c4c5a41760140005214140309245040600400142c00e80d1120091007200c114079402003801c40780686445141021032420505403407269900d55500c0d0049400d40e030b075a0005812040c00a81030140500c0040780c140c0481c406002c0b10100460f101c075561410303080451500000d64082041c5485c20003090202e510301042440a81d038240c240454200c1051a209009108a03480a40b0b517074a00801740c0d0030440c0a9000754001c0d4001c1e03464001d50300e107420640074402598071030a6440300b40000601d23241071140c20140030000107818a110802c0d42d44000ca07007640d10460342c14000960001d0248403000840340d80601400055031b040155240180c04110544070280025248 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 60901370 1250 60900120 60900157
    0x12030f05090120010b030c0a050d150b040603140d0f090501030221040602091207050105190203070606030b0105040609020c07031719120c05090d021003060503120d0e060408 76
    0x7590094101c12014815800c4001e040016400601c0c001c0200d080981c0c030034020606c40400034134103220000181c5d00000c0071540c5020696880c00f00b100b00740910115419105e0040c20600d030f98038420383c3c001714012804490781019001a981c2842d00321240001840301000110705120360018004058403c282401079448031100c0c00102038608803110b40d800c10000c0e0701013100b00402a00a800071070025110f114804600e4074420303440ba90b2030b00540d40001c2c0e00b441800e0080000801d0700600084500642e440e1041c191545001e0700c00c10340013039480390000d000400160a1a00c516802032a11030011420702070105446511411f00c2e00c0090074420041007401103002040084032504102403a511194154000025120410410246103064030305a081c4441500036021105041d00c01010261100303038903800c001071140c04400f050101541d171400400c064604000380402c20181c052880c2e02c5081c40401c42054400c500d501e50160b801482c1072000141c005d006a91800102d11841e695 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 60902620 1250 60901370 60901387
    0x9150903040302061b060108030a0f0302030601090e160e0f011b0201020f190c0e0c0d0f021e09030105160f050a0e04090f0303050a020f04050402030402030309040e0607020712030f05 80
    0x1641c001c50b04003a500c024005101c84844d00c0550380c0000c0480c40000b81e03a4180e90704c20440740c8074000e82d00c4000224100c0d084040200e8400d40c0110b512181c141018143d4a464402101080ca012101418100c000010510340306410a03690300320b20b0421038811400d44901c0303000a00c43c20311408000c20f0440700007080c00031680240700802c4076840b020304a81400000c5c05071140c42c0550007606035103030f424000340410700c0068034414601c5101011111454400b40324401002080c4203010784064a0b4240552210014107901c0d00e524a511010029120310051081500315600a09034040900c03038404085071003a040041840d0726680ca00b010350719000c1442c402c0d00c100020340d2401d0341c0149081780c00d100b044069034903040518004ea03020007050741c4d2010060200d10540300e030068540000c0c01304003c1840c0603002143d119101070140c81c1011100c0001c142036800401f020744690300040c04015115a0411254009240110400d80800c0301902d020704407117500100c8104204000840d400b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 60903870 1250 60902620 60902623
    0x50705010f050f100501020304140603070e0a06020a021201020301051f03020c061e09070509060d020a120602030610020705010f11010e062d04120c03350609091509 72
    0x1030079950881d50911003071600700d50f0024103180072500e000044400003004501c03540700200382e500760766240c10565031482040c010080340b034000518203800c0050304036004050361940180780d401804660028201030525204021603101015121102a0320501c0108141c2c0d03551000c1da04581c0a460002e1150041c00404401078400c070341e0060741c60301c034690920002e10b114282e840d02c1c00700024081040c684030491061345030b80e02d42c891b2a41c4000d440c4085101481c00f000b8184899200402c0481c8140da0b81e100c04220440100f000d40380598007004000a41c2840c095444001c17056202501d0700d581002c0c00a00b18001c2041c0d00c06c100038266101c1c01c00c500c402d601a880c540b24040807140c80d4034001c5200b10002c030340b00600780c40b803044003034604440700e0910040f0703801907030b116a10401031031111108032107090f0030709415010899900d032030120440c3c2640455462000b80103040c0b02101e1805040240d0708805004240100030300810840e07941c1d00442e81c2c12041c801e10030841155140e403a8100d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 60905120 1250 60903870 60903881
    0xf0b060406140f0412020112150b0f120108030409150e010303080613090501090311011a090a18141b06190905130504021008060d11010309060c0e011211090105070501 73
    0x100c500400004011580103075100072017000504c00d0346c400c4c004011803807800d4240c541040040d240440050000e0242c0c0348800007808100030030408003030030a24202c0008100040a900080050700001018040c0c415180103d45906200c10f01c0c0740c040d1441d00c010413901050500c00070b000c111130b2a010132681d070f8440403648071305100084280705a040341d051681c020000103030f0490115032044240400940e040c014909101002c00001310185400814410f840782c0082c8940b078a50380e42c0c1440c840301b081d5241403081e60b034042c0b40c0700042d503944151400d10b80406803d01b0b0300c0200410344111001c0e550081102c1800310341e8140c80c0766008075180705803101d1800340c11030755119240320000c510000ea07543c03009100f0b60080b25424003c4c40440e07001e5581083c2540e41d19048505441142c000c80c01c2980d41d01410710040c03500107070748190342d2500001c6a071450700bc0400520075840d4440c440da4058040f182101d60740000f0403c0703180541d00c00285101300052541481030100c0c0c80001e00800f075010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 60906370 1250 60905120 60905137
    0x121005030a0b0121020402070b0a050109110403060b03070e07050d0608010204050a0306020a0915111b100f0c05070306020304050d18050409030203040e01031a070e0a0905130c03150f0b06040614 85
    0xe545454061a200c0c0c82509d044074525000ba01d00341c000036261145005103440e41c030040f440d01c0d14003400c503140d0070040d20b012805560144100980040c0001310240c44c1d51182a5942c0c90b9502ca180c065401c07000e4075001d45c000b0541e680180300a00060b51503d00c1e01007100d9202800580d0344480c0d16082d6202c56040e0300500010210b44000401039402c01110215035201d035061304c0312080300d084044400c910396148590895005018500c015020300283e0080c00b0840c20801040c16140c0c0d6032903d01011900100c07960394000c001e02007042410400850711460360708120903449102d6031040103049440c400c42c0d10032a2640990420b0500074011a00030b002940c031100d0305503860b41015041881100c0018008110040008009500c1459100b0b03c590004103206080c91509444402400c0081e0841c14806d10a2030300100041141e807520000350302c1820101075801012004900329207000c1104101c0d10f0912401c044a43c1e10842120140c0c0d0190402c85101950086a03040b0790241c00d41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 60907620 1250 60906370 60906379
    0xc050108060d0c0602010b010201180b04031b150207060513050a0b07030f091407060503012d0801050f010501030606170f070c05070807050907030209031f0b06121005030a0b012102 79
    0x85074440c5e040d042440303000700c2a00240800b10400303900c0d040120403108082c2a90062602050004e807003920354030240d407010380032181ca1420988402019240080b280c141d00741d400290305041050038011940d100e0181c40c0213103040409a100c1680304c01404000a041c0c3c904c000016040c1030099101040c0843c080a040002c2ca44915104c400710180215001c4075200d000d03c0040c46a110b01c0c21241078450160100268030101c2c002d908040c81c1800b04007d07691419800410b580009104003403040d80c801c0380d00c42c83e551601001504940c81c580012080124000d102a80440003e80c00d44d08040000440312407540d442d801211600b0755004001c0041c0902640025103080000c1c180c1c05230f4004482c1001e058440c044203604038860308090380c0d0140c01032034581d44812804566807071030100800010401c5d82c1d150000078500e500810100315541218000d000000750400c41c401d000e0a004d030020490300302582c884003000141485100c0e942c0a583d6075400e42280420250f00c9869400352 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 60908870 1250 60907620 60907643
    0x90510060b04240504030f15180b0105030304063e061b03041515090203010801021216171009060f06080601140f0a0507021e1c0c050108060d 62
    0x500c00c1603642d005208400544910321505460220200e002c0e0902c014141c8500e40340c240b0319503410700300d805842c0b019150400702204c050304480c41401803001440a0002c02100c0c0801d41c80c0c0b21454101c1a04880d019030f1081c003007800260f03001800ba100c120b0103140c20120380d0f1302e100c03240e0b84101c0000003107075201d0343c2d50001c02022000000d00316024010f03a0480440c0259115000003840c041128090700c0d8252506620b42c02640c0c582c001c0140510204c40010040d4403010b45000703a0380b013a403211035140e5000a02520803051003c0e241d030012000079200400e041c0c00080205101e0305c0384c1500300c50351034840105081a4100046030003c01d510081403008a070303184045da40c0304065102c3c20300840c030340200007000307517110355413402a901034000e441d401c0a0201d80080c9040d00700c0303519030b0f09000d01006201c0240e5980d54148402c0c0b804104000e8801a800c401d10040c0b032102c0407413408000d01984220000307003500d0586410350b8001e182001c0d07281e980c400020700c03400719001e01500240052 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 60910120 1250 60908870 60908879
    0x9020d02040c020607120b0102060109110903060702030c0f03090d080f04150309120e03060f070905030a06060317070803060904030302090414060a0812040e04020609130603031805100309051006 85
    0x400c01300d10400312502c91094100625100341c0c16206d40121140c01078100c040140416601c5a00400e6600707104032800d0300309038030040840c0c03500070180c48510242c0d0001c52105c0000c41304100c2d05051141580c0a541420f45101c003040c4030011410300149900c501080301408a41b80605440c010000c441d450f82141c000c0303104c090001c02d000f02d41a60008206245005101e000d25007418511fa40070700141000d0351800e4000b07000c0a0058109000c01560080010f2507641c200040d42d2814046e03080000e82c1d82c038514000400780e001082c03022041c1c80500c04100407a5401c4180c96000f081612084c08507512464114024132070700c001e40d035009141104121980b03041d0713041a4070449044c0e50b0300c52425100c4800c1540d50030500d80c40303006004200b0091054000b07a008440e0000d1001c0d1109084c6604200001d843c9910041c02400382996000200181644640181d0180118000707010140c0e042c0341c0820140c0e110800c0700000c1c107454405480030031101300000041c55440e800b0030000c03180c44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 60911370 1250 60910120 60910123
    0x1504060203010915030213050604060b070503031e0106020d0c020f1507030305060103020c03070611070501050f090106050d020108060d0c03020316090e010b0f150f03010b090112060302011209020d02040c02 90
    0x80c003030b071a0f425207001031408880640300003102c1501d40007410b0403910440302111202a1400418044c1c0260300c03003600040001441c0058000d00f445027002e552a81307041d80202d07080d044000e1104400008a8004028050300803400300d035540b0701850030180c2ca100600214417140d9040707080580003001c0c1c0c3e031034a49884204c005843c2c030502c00e07a03062000303896100045051340100e8581a400350810031140c40001d4003684004d030300d02c41440015060031540d031200f50031a0403c88581107020700c6c010400550071000e10460000d03060881d804400c06c0c1ca0343d00001c1020324000c02a80c0240070f0080120184603100780c442000303590050444050b500009449043c0540c43d218081032a801e0100e010315650f010b0044003640c00c1c02170020710307005048404004055040e1092689041020491919010031690055028080e02c40d00a680d94282c1030006050f1a46580107a141c07514200c42800140e911440ca1035207903903a10b10104256041d0b000244501401075002903005160400b01e44107541c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 60912620 1250 60911370 60911377
    0xb060a0c0b1003021c030e0603040c050111070308190302070203011a010e01030e1902180a20070c0605031e0415060b040602070b0d061502060103120f0e0402070515040602 75
    0x8200100e4200ba1100e503481000301141e400000c1d400a5010485a4096008600c05d00d01902070301c0e2002c000f2030f003040452050f900c151411307100044001ca00f800039507001507103000080503000c010f1011030b245440340c01440c0504540c4001004072400400d40340385c03207078058402840c0c009000300225000001c00c0050446d1140c100345c04680001d40f500e184c1d6009108070550310950030041c00581c1116070004801014800041383c6c4076401c0b81c110201c2d0a400d143d55440360b44824000100d91f58051044454244a8000103489201c200103010024080d60000d8048950908196843c1c2d100c1078507c00c80c09068100c0100c42d0a001d40c10402804408421402802c210400401007a612901301204600c03e07070240b5030140e8841a0204001c0c10403100a0100c00f40302d1100080c9180c80340d00d10618059020045001680210010b00602020090684108200782040d1030a01041c1d80050000c910b8041e07a1442245d0104441080c4502404450521030750340f4005200343c03401d031620300000e40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 60913870 1250 60912620 60912623
    0xd030e220b04020a020a06020906120f0103150203090c040b060c1203100f150c020112060303170c04053015010303120b0f0f030705060406030b0102010e2e0b060a0c 72
    0xc0c10403080726400e003410300c216504856982d0140c541e403082a00c50402035031103003006582200d410002040c0c0d07560a241054000d0f110701c400c20140394950309100b441581541d451513040791041083c04018400081e00254010013605c0200362480c04100107840c0d0300070b80100c00403602510b6a415021869100294841d4983c581c8550704103854184203130142040c0c0c003408070100b56010301d103400540a0403000315a80e205140c0000c640c048888030405440742680100c021841c10141c2c000c01d0200181e117030f90700152591409042500c1e2500041c0803802000b47c90003100601900c0030149852101100942d11415040b035100150075094804045030910040e0005011584541d4006605015490060b813004140c0030310f01c3c40d60000c01039002c00c100e89180c6d1512407030302d00203180e40314074002d032006190585000519455040c000380c20340301909003a40498200e5030b0000c2c105185c6080310148801050600555007050080000042080c00140c0e42e0150300400c0703103090a54401202c1d620302c0e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 60915120 1250 60913870 60913939
    0xb011403090a02120d091e090c03050610030510060c05100c0807020601080105010e0f06030c12030a17040515060a081209040608060f071404050405130209060306090c0d030e 76
    0x2071081070011502c90003801d03c0080021800711b020819180c1400c1070140c0d4404225881c5507480d40c0f82188012154a1161a40400e49550800140d86021441e1901259203420184000d00d800300e034071043c02035613028242c24070490944000c244201005603246030000e48000b0004842c100601610401c405c44205006200d5000081884001801104d04035907241c02441d0040d240e030014402c2d2280000c1c013150701403240c0c4170a20309507614151003903041c1030040c019503076a540c80000240242d4048400208000d0b01c4000e1100054000a440030701948a0000309807036180c000008650b140c481d40000c1c41c0e0700c00c1c040d00301902d4014100404041100325000c2001e6a80d40d000700f41c540030210b4bc0b19800c0340c05140003980c040c0c0101040010391640844140c5011b03284e0b40001c00300e46d4251900045070007000c1c01c00341141008100290002000c03001000700e440c0c012401682e404021880d1070141c0d9094001e0001c050003a09800c0204200404102c0001c0d615007035003100b1a9110003001c000e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 60916370 1250 60915120 60915139
    0x130902092202011409031f1a01020604020f0d02090403050406022a010e0301060f0b09030f19080c0703060c02060a1d0a0b150a030c03050622060b011403090a02 70
    0x2407148508140c03a004044014907120074107500191a00b01580c840d00764100c13800c0090301d003079950503c6696461302c04055078180b44188529008103c441070800c20212035403107894085244c0e00000e007a070703020394101d583e0100900580086000e6006c6094002e4110030414203000030503070000043c1050b00d150794204d481c2000d50851410f81c260f103400242a26a01e02c42003240346500c5031140002602c009400420515621803e503030b141c04440e4001c120301c4401003180381003468240003d00d80e005940707000313011110b144059000c541c1c1d0002c0005041000000d034100c041e090512616004640005041000d03100003080079441e004200c4466070700b146002c00188000c1d102034160990110a40010040032890303a030390800b908000740491012005040b000040e5a856002c1038000c1c600c14801d03085c0360341c03441c40d08034036102e0301902440c0e4403041c80001399200e61007030700600040c0e504001c02140307103621840180c907040c5407150180e865490000810482da0b0001076616026803007034850806 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 60917620 1250 60916370 60916381
    0xb040305060403082406070302011d0d1206080309010f0c051903030513111005070506090307141504150b1e03070501030e060708071806020105010f050108090d030e0106030213090209 80
    0xc0031148690ba1700c1401504010125440c240700001d8803004d4424000020440061a00c464001c080152080c00c280c0c03150101d00b0501f0390003030030000d502034001c8091084500b0142c07601d0710780c00740f10203003410404084082209540710341140006039400c030054803250311540d4400e002181e00400d05402003401c140100b00916102540000d200390401e420f220441d11100800180400070002c0004021050084201192041c01600e00613451031006607a41c402500d8202d0b002421100c14165a401204001e08400d4900a181d5803080e070040c3c51320300c10081e00c1c0b01c01c0004c196000110f030700507101c11010ba105003103029080c0c0d54038004404032462159140011000d0707943c072162601890b0483c50110ba8000d0047d0903c0380c0107100d45c1400c40c1406032050a2420003941d6a1250300143e4440d030040000c04003090b01000604420300c1c20080d14035200a0346a40c80c101c14203104200340d503585007664040030030b6008401031507004140500604200a002c2c001d0190400b00382e10940110000c05d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 60918870 1250 60917620 60917641
    0x702010b040c180b0a05040b18030c0d1e0609050d030506030c04020406020c060c03120a1b090e070804050c0303040618080a0314130902030703020a020705010e03030d150b04030506040308 82
    0x848038288a5144090581000c10304c10058000384004000c0c04400e00c4040703042c0703071a0406031600c0e140c0d44801501e03040e400010186048401400c042c001e00c040c3c0342c03010101c0c00c015000c22080358845c201103980809454020000e2548144c044c28130701071810101c6840358150002801600110304450b030314446201004124480c911404000d40d100946021076410700c01c01406062009406403828044c400280d400e402c4022500f80d900c0320381d00d140701d03020001c0400c070814076500c0901d040d21407141003400140704e0890182a0704107000c03c10001400b04076003086003241203c409001d983e00c640e80c9440c00b60880c0d074070000703804010980c0c3c0d80104449070000b0b600740c42035400d55504a840f018869040d4507581c0500d00d9580240d121800c0420b141443c1d00085018414030744e0010b9440c6071f1920021b0510301c650f00040d04020031050385040303a0b90000141c17091407150440004180300051680c020800f0710790702c201d283d0b100101d000406d0080200340f0341d01c903a0090312800d141d55039840c5145c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 60920120 1250 60918870 60918887
    0x6090f0d02030901230304030906030e06040807020d060605030718110a0903080f09030a03080414010603081b07081e0601062105070c0204050a05011a0c0a0201031e050702010b040c 79
    0xd10050b4018840b00e00190b10a0f007005500030f89000d882d00e0362811103078240c00e403640205e030260007040b004482000380591511400600a841070003800f9207042c075985000c49481480c40c00b03842500c50350040c0301849000e50001000f85002812034488698940800e240c87d8890296138180900d441c4010a60360b00a0046070086102030b070f0307000e03e0389081d0703503c0806c0ca1300607403a050003110082c41042503d49040003d400810701030f0b03c917041e85140601c0c096107510030a00c3c848007241d0500b02d08200003001c503c1500d4042514441c00c4a05104070701023075203080129807040b901c0303110391074504d10150080842030782c1002415064410503a2505000d44000440050400c0c02c1c5184401c600114843e940c0480d40003070281ca0100315420517a000241550380c180c1e600300e5071559610041103119881c00d800035008006001a6050641c40050706899031a01a80a414140c03600142d90300e00c40345180345801150402c03402c20a07420f000340c00a000701000710b1194001c5103800540c0d070b249030144076031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 60921370 1250 60920120 60920143
    0x9060c0f03060f0e0403020f06010b07020a060201020a081503030c100209010e0a080607300f05070f0503060d03140c0d0305011202030303041b050307230402040e01030b13080c06090f 80
    0x10208244c50883c51418031a80104294114000c4540e400c141e42d20a1180f41c0c02000844038041e2500094010083c0b80141940b249066a10400c181c0a01030380005040f9401080c007290302018141c0d55010030302f103205002d41c0000a0003a4071680da00d4035070f9907004c2c0900d200e00ba40c07454003020035141808400c1e00315005041d040c0d030058000507a0b851040d0100b01c829030f0244030500059003c0c01d0801c083e4542206007140d020b4581c5281c050540a40c46a6a40000c07940360407a03515846a00250691001420316400b661102d03140409150045900d00d00807803030f0b606066075503005080d0302900d84110b4a50790780003905210000492101501a0b81440740c0c00030702851454641d65109250700070107003002a44c2002c0341c8070001e4140c1c0c2c14048034004052904040c1101810211910810181400c0c6507108900c1031100b4400340a80f00102415254005070b4030002e6182c503101002c80a001c05002000d00d800014030014081c1c0200d2030500503c43d207812074504400002c4059111403410300c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 60922620 1250 60921370 60921389
    0x2060403060902040f0c0203031906120219030503040f0815060105030c0702010c02060a05040806100b0403120504050406090e1c020303060d0f0206030405010b15040609151209060c0f0306 82
    0x4203001050256100803031a82c03009200041c0d10001e43e4459003034610ba10034000150f0404001c014075098080c019100b601001301c0104081409d10308003146401c0401006402520381d641e60001401d12400c60201854100303080300d48960707660011882c828a1409900500c0c0909149100c04003141006070313000b01c60585406003950f4540c98019031a8006a5040e4108a1310010810140c0c40e6107006109418080d95020303603030750030039a1591030a0720150624442c030010f400c04105401620003590b00b50ba9002c03000b0904046108004c4699000301d40110354414940070000603010b60741d1b8060759a41d0420000d54064110420301e5000c0c0d0f001c54030825005d6041000080c07214070340700c1c1e048030f00c9500c100134450407070005030045880380d0001c0354211034a80d59544003121600d0701c2d0401c150700034407043d0a0780c0360900b001c000820310709143c42441d4a00034042080c1e501180181078503103603001c42140400c480040c50603c44060514600210301051500d802c800d00c00d8070a01601c8151240c4a8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 60923870 1250 60922620 60922627
    0x120c0801050c030117160e06280e07020f011503020906090432010e1006170703030305070e031b010311040506040b0304050a050d08060109090501060e0909030c070f030b130206 77
    0x808088158200c00b05c1d0000742c002c15821003410f07003070041c22001401e040003180009103400c2d0248400412100e5a451044030082140c0758100810880d540a5502c09017490030030391101c803400da150055a1448104a509100140d480740d02e01d0049602180e0003210103401c10b885035014446080b006440c007814501c0001001643c2080c1e14008505522101c05600305484154504900319124019a406240c006a1041c4004081c0d40680c1c80a000c290000001101d40402e41c16607420003403100605054a81c000100c40307074003494014aa2800c0541503411544136034404c04020354155000c240801d2400240c180d0b0740d90b803441500c003075640107004103107881e01b00a49080c807604004d00c1100d40b0b2080c20216400501c0502486840195641b58031a15061010014124200c1c079046111903619000042160301c1d40030712106a840f0b4190364030841c2c0d0302c80721720013400c61240c5d9041a00714407805800107980700c130b03c0d0303199070440e402410020555150b2101c215507030045a94080d501503001d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 60925120 1250 60923870 60923879
    0x90d09050616020111011a12240a140103050307030f0809030901080c07020612010608070810050103090c0305032205030111070308070c12080105090601030603170a02100501120c0801050c0301 84
    0x401d40a02c0600506000c070110402d01c1d036003402d5560071a0006112099049112000d040040e9091540707910540070380b000068000440101c0031840420004010013100030485010741a4451400c040d00100c01d2010380d078403410b1082d0307240c0c031450046000a00004100003003a110344403080c060b00d443c0e0069031400142000440c0c818101401c1c4580c00082000000010ba840780c1c018414900454002d20b01503151101c09420600c0c01895081440100300030081d8842c29480000d051311004d00700010007541c6407c2641242d1000d400050040c8800940e1000612102c91a00400b41c05243e81170b0805d61200141400d0b102085081d500d1f0500610848000034090b05105600048a15000d50003804d1900c0c0c0420300f44600325500041aa002c2c0180590b003000007030554002003e080034400c45286649800c0b0322201c0c0b000c892114400481e03080c03503151090002151000d60520240302650312035400900708840c844040755100d030110780000d03a024042c059540318100e030700b50850841e880d2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 60926370 1250 60925120 60925147
    0x50405061303090504150303020d030902010504030f15050903091c0804030305220e01031e0203070506030a0b040221011d010618030803100e090106080c06090d1208090d090506 77
    0x911400b1000d00414500100e03840d02c60303124801c0344580d2090401070892550070081e00740201003000d401014248060303800540d801008850031250311450461064582d810202c0d17008060000e80480c0c54109000d000c2c0c080d4001010305025142116080d40b8030103941e1641400e080031860051184005100400c0800c3c00782c400703041500c800e443d0b42c50319488451084081802690000d007424a41d0000500511689034640031081182c0012102d9440c0700340c00203592420980300d410702c5100d000000518a20190b0000c83c0b40313120180003951101e102c848050f00150020484000580c40c130000001e01c210a000b818064070041c02080180780d003080000c98103018140304440c0c6910890400000003500d18004612400300782103003400c0305080c89205c4e400c241c0040c00071229a8140402070061300c00104440784419000c440c415070300c034010400300c3c0d2502c060203400f07000b4620082001a0240d04114224450400c13201522604ca142d100d003994204050300074149c00c0b25082c01214428a403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 60927620 1250 60926370 60926401
    0x1080709090f021201180f1203111e040b13090c0203130905060f0a0b130504020c030d021c0e0601090c050a0806060c160b0702040608070e0f0a09020d030e1305040506 73
    0x444000200700b1b00c1e11700070395201030306115104940380b180c044146c42c1800450309440e00030180c1c41c41c041c0601515030502c0d0000e4000e5a08000300c44180b4100c000e404c0800e902118001c0c040c110754107860351800e90301022186075038810018064142075040c1e40d024800300032034400031600407001402d0350814000c0360003000014069234010314290b0f61a8483e0b40e5081020004101d040b0185d680c071409c103c00a07028084030307800f050080f070050054140108010040c0c8400b41000d07400140c450462044001c0420418100d90185525081c081425242d010403414161050f10b60244600c00c0307200012a0544503141d000800039003ca0003040c11340c44d010000300160386081007210ba6a0f18030701000c220b103610980c441d40b211500000d001c6c0c01c6081901900004046090141410500d851070004401d5030040245403164840302c0041d10b464110f6001280035a0007920610000440c1c1c030300507101c045000740081c41890001002c3d400c050060054601c565449400f91095803600e2172100306400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 60928870 1250 60927620 60927649
    0x1103130611030412020c0108071d01050f070303020a140304020a05040c030912090501120207110d020d080c03030a06050d02010c020118032a0803030c03060f0f0603040b01080709090f02 81
    0x140c03074901016000079403402840c001c500442140038492510340c0c0c0603207414404210941806040c1003044462600494407070303840048541d103007405a0030003004859501c680802e44403151401b19003081490740c5030f4007604882900b078440714070700c01202c1075082c618081103030000d6106407801000d208604094019042c0341030b07542004216420f007aa21450081d1004043e40000f0306801801c106da0360380200b01c09002d148866086203000025203c2900542451010700d01400111b0356100841d25100b1425940c01e410041d0151608208120305840354025204c804030607080000102e51441c10b038000c80303400d980c16100c84420690f40e034010342d03510014100c019a01070850000001060700700030070401e68611720b6248980340800c000380420000080d04004815442481084030318488441103a800c42e07002c4401d04c5141040300000b8511003440b0807100e8114401005000401020640242c1038412704010345015075122843e9104940140202418402e6801c40900150402022150040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 60930120 1250 60928870 60928883
    0xc02010c02180901060b070c03110105120103200609030303191b030b10030216030e031e010b031c050406050c03120c070c0e0c0405040203090106050306010621110313 73
    0x115038580004600089803020001d008102ca400c0221604081c460329025080b02441c60b4101480703500e0340c0a008049000090440003c840c052903160b000303800745e0709940291404400b1643e160b01e04031405464400720350420058100c1c0704072451520b0070594541a20140040d03013165030341c070b4220b05401498000001110b0703a039101039007241188c1c1070402d00044140c60101d41c044120042c000781c682a29440720800d40b06000950090142c8204012405d41600d000c801d800032000000f41483c1c1e0304030600b40c1c440c443c860018050b203819040042503090840a450425003203c81c01d01610720000151400100f0402041c0041d41c060400f0f0b110000c0c0c8401100d013003a820b100038240c0e101c01520480070848001c034407001000444c074900700107010000b240806a0178034031101900ea01072030155522464000c0001800684254800e03001410020212119540d440c0c03005801030506500004a0103104c807142c1c0008256406180502010300e11441d241d9078580c02240800c00c0491700440c1d0f403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 60931370 1250 60930120 60930137
    0x6070504032d05011503050c090603060601140903060403030c0210060608010605180904060b0a120807020405070203070609030918060b04090e0f070303031b02211b06130b010f150c0201 81
    0x1046017403003064081c0b0012000c0c410418154201207152800d075030744a510904010081181e503840100710b46400003403e00b000d85801d103840610b40003900800802c00d42520410007000140b680c90b0700b2200c1202c00710317001c2d03a680c550001001015680d01380660070216a402004000881c8200010080702c4644c1d01c881450b03466000000e03566038410780d800d89009450304140c0c0c6a9140c204601801480d40070900c003505803903542d900c5202e006800b406840789a6a20005984500a1044480315a484002000032124901d00a8801d112a028041c21001d010310243c02d203034031901c02d0380c096503401d21450f414545007501d070300003a20103062403641c01d009600303d51003012404c01031a00614401d4070041140300f10000c400160726029a1705008643c05900055480b9040c480340360304a500c0703501e101d40d41c1c0e006d003a0004004800c0c40381002040c425201042020640001c0b8203018900c03c40ba2614584d80e03424a80b070f41604540203001203081c0401000d07106600411000c09280d2040c18074049 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 60932620 1250 60931370 60931373
    0x60102030f031504051f030803100e0f040b090c031504060207050d050d0b0103050103030807080c0912060f07080c03073902040f0c0903060e0705030115060206070504032d 75
    0x700360015035403000d01c418411409000c92a103400b5007036029150341c0b00e405029280f02c2c02d8800d036054510000e000e1210010110f407110f882452500080c1420300c21030344240c280004644840c0f0806c40d0103070b9038880a034000c85c1039510302248000c006000180180803240c100a484650948040c00032a105642000503c00003103061200440b056199200c00e91502260f411910a03030300c00080d483d04141c984001400040e810000d4190020308601c4d0200d8207546000b091341070b07841140c00a03544071342001480d485030306000900d140f00b044000688005600c8022065910740b00a88031880c92120a00000e8401880b1b01c4084860002007108010500c410b1000800c401140701500f188292541d203084c019420f05005864030400040710401540052a10061000300107000080482ea1551a060401c20b41004550050302c1300070000c01c80c1410000480003511024410080540110000610b895000b242510100c0b03400000928001d1200350620a90b1101e0490f1116001e410300c80080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 60933870 1250 60932620 60932647
    0x60d150e060915090307120305040c0503070b130b070c03030f1b0c0e1008030a03090501020d061e0b090105030604020307260108100504050706030b13020c010f0b06090307050906010203 81
    0x28012001c44010748003e01d420f81041c05260b01c001d06a011036401000803100141d00e0240d98040ca0700c007450b00181940700c0f4501440c86034030740e500c01e0b941803082e02c0b00411400c41d810300500c120180840401c04807561101c83c01c4060092a0014008146e100c20030400b1901034454503000000740c3c51b10040030304c025544042090072141059446c005841010f000c040c0303030341001607001402c2c2151225000d15100c0207603643d00c100f01100d0101602e480601d400c014013501039420201c2c03821400c0c44110b486c1d810300004003a4800e01d1040304505480000341d452030307a42c01c4454408040c0c1d0b80c1891a6035a90070f1101a5002621030003c100340f0100031080d030030704d070342001c0c0c050448245044c240394134201400385807141e04415410800d03d024144400034100182c002d00f1660581404142d8991200001720315204080400480c5400041d49424082044d40320701c0344844184000c0181c0141001880b80714001c04c1d080c40d07095800b48500780858a0b0018090307a02c6401481200e02e42840110f40d00f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 60935120 1250 60933870 60933883
    0x6010c0c150906030e03092803060219021e0303010b07021c0f030207050103060806010306090804120c0603050a1e0504240e0706021207141903020d0e09060d150e 71
    0x500000b041c812041c40501c0c4d040c0111102c03500c8600085040458400000d508141030325402d00c04a0745004c599108404108680070056030802000c540701c0d401c10105e01e08040d4448071038001806501061100c1e0401200c04403002c050840055086a092290164096115010031707070b841000c1e1041d2141c494008210760340368920524420390a0780c00c80c039000e403070100550802814542020030030301c4820300c000340c0503045030b0308601d010496036642c1c03e0240c2c10f4400c0d50010283c0d601c400e03041100307010320745000604407182c030f90b8108404e075156040c0c1022985204104951044410580602c0d0440d503040243c00c140980180c08000000c40843d2802d241d4116103200c040d0b0b1030b0040c0c06000041400044d0013000d140c000307007500c644004031001240c0f11f03a61000740118105850301c141c1d92401c12500c506a484005030b04800c83c0c403400c029540308100001c0343d000500e5140407401c203080030701c1147e010341e02c0078108051000c03007980d810348811600289003519607a98005c02041c10000c0129 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 60936370 1250 60935120 60935159
    0x3090b030a140612030702090411041b09080120091302030a140c12060d0309030c060306080c040603080d0e0a0804030f12020f03070f03110601090204140109080606010c0c 75
    0x30701a4140a6180e42444004020f58419500020340384407050020049400c0558101c03000040e0787c0c0c40703143c8102040300c0e45000c160414908440d0443c1d0400720804282c80b080c6030380b10400e8081e40c44040341d003600c05c5941c203040d951150703c070350b5401a2070781d4000d030a00180041151001c100741c1c142c0c4404030b80040702c06006e4a9144c065007043c40004c2ca43c803507040500b00b00e60f5882c0c501300301c0070424022006448a400b4400a103518000e252082a841024660151481500315995500200a85018010700109010f402c2c0086400c3c1341601c110000c0301e5100046905009803d50104002c080081e8540c0711070051514490001761001c00a001842c072403081c12150f24468100041c0141082140c541554400004110140740000546a083c0d034041c503030440b0505140f41c05c603107a0014100b940c200740b08200000c40c15038043d4001d130043d61301d520081010142c0550044508800c0e51080140507005038010894030b502c950304590045014114001c070b043d40d608010080c8071001d00d103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 60937620 1250 60936370 60936391
    0x100f20060703060e0105030604030e120f030304020f0d0213020d0612061a010c081204030c0b07020601030b0606090603010e090109020a0f0602010501050f1e030f010e0a0b06010f140703090b03 84
    0x30811002d82602c1000050702000c1080f000f10742c14040826900c0801400260910001a003244425900e490b50020760350180404e582008401c50345459a98006880c100d02c59610007444e2100c03801d0042c0030340ba01d1034000f0143c050407015039170158021750200003150354080e1150808a108412000024a0396100d8100003624240290707a00314604580b10700e04c2e04110260002d50089080c0ca030a903140d0942404003d403180e12589402e5039034640050004010814640c10808626000300e0603038100ca0203200403d0782540d80c4000c00c10540308400d50a42d200e1410b000501a105220004950041c254000000e00b05219000100d501045030310542c0c1d81c0c9840542030007416420f006580c014001564803007510010380c40061807181c0364288405880c0c80c00c90111500d80e03010090b2031101e075100002000340d83c3c82c2c100c40c4e80e01c0744410041a106061503c0c00308032654031440c882e588409c0b071903a440300c8034680401d41c02c00319402490181c0400404200100384c6000207801180240812030303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 60938870 1250 60937620 60937633
    0x180506010306110406091406071205070c0503011e09060b1f1710060c060b0a090905060906090604030c050f0d030c0e1905010c2a0501080903030402100f20 68
    0x900101940d54810245003243ca0a00013003081c4d541110291040e1a852441030791901691000309207680500c0202402600c00c4020200c085908400180300403801040104040394030f480c203042c00d0320041d2401400245020054005000044c0d20408440d441030f5004120580f01e000000e0000b2a003a08560256110140c44a6141d400c40400b42107416000c00724082807812248810081b460343c0710300010b08c204d041c0c050f0104415544103010205005043c6510140c944041a0007419904000c503058030541010403107508000421074401d107955030050400c0d9680390340464140d088024211074034071030f0704940e0407240341c14481081c04034010391b0000b9000450500060140840c0000140180070909404032030880090025054540a0915000102c242e02d0080d00060514420050284100c079120384014502c035107440461700700740d80e681c20380e8490182060300c0f8402514004d501c80220011401843e0180c658141b000f6501c0c100311200c41c0528100d40c003480b036000c605210603001310 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 60940120 1250 60938870 60938873
    0x90307081b09150607080d020d0c1110060e011a0f0a0203030609010b1905030712090b0a270209060609040207050105040309080a05031b0307020312030103060b1804060506041805060103 81
    0x145658002462882d183c5941080e101040140c40307490406003490070001481158002c1507012244486601760b820031984000c42d90082090340713952651800746c0501c03a5142035582c0a400f60000b80d030b1414246500700e07403a0111480e030040002401803d510030900110324615180030160507001c1040e0091940d914045c0e041000c80b100581000b4400e10080c03285441481104204030103d5025042c81640c90b1036003030003901c1e0300c440484000700c00c5051124550410070502e20850041040200600049440d00b524800358984070b190790260030300c0d2400110141c0b8000f452030f0380212029004a150030070402c0442c080c1e03440100305070dd540e9180c03014081015406181170004210410161421160907950151030b403051001d24810b2051b1195514030280080c02211411342d4020200c502400104000c01c4003a0000d00c4162861450882207682e43c2c1010301106d41c000480c0d600140c510b80c0d481e44c4600003040c0c041c1249402c070303550780304656464080a0901e41c440b40238400429a5600d076 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 60941370 1250 60940120 60940129
    0x150501050901090219030b0301060807030303020d0c08061c060f020705010209090606030601050423122b0e010c140d051215100503041b090c0f090e0606090307081b 72
    0x182e10140000d48100407002d0b040d038205c1810100141e1518000c107040c00340b080000e004d07041c603401081e0a406131100c00020190150b00400f010448131030180010300c00d96000366142c81d81207035066002580400782c001d40b04440302c02c9540301fa00c80c0000007071030025004040100d801200c3c0403501a1760004800c000b502e4002a0940d008008940030fa285141403000240b403806280b040104901101a82d2800e800360f4200c14242c441025040e4035100f02c0310403a00d582c0d869a24020307841000500728108400c80000100424107159441d402024006030004546002031900c059032030401842c28059014030900c1010740244003503031080c1d119040e145840d00d1104e800380052203501c0d0120600d40d280d4a400800c0e0344030405608081b40c032542c81d810150110751035900080c181c460f8000d07001c15504a00e0f44440d001d82e003103980f440d071910a6503505517802e0344203001d00c0d650414460005046458401c0003000f280c600603090740c4940d5582c42256107042030703052515484010041000c2c0080c00d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 60942620 1250 60941370 60941389
    0xf0102032a010c0e030c0d03120b04061206051e0103031e020f0106060306140d0b2703130315020c0c040c050903010203040507050f03060c07030f05160c05090115020304120c0315050105 81
    0x400c0380d410b80c07a420355503405032142d040013892740d9000c4c0c0c4520040b1441d5440f544184010417918074200c500c100103190800080c00c08540d4514a400e0310710f40e80b800648a041d0b0a4103907649034a0300c1c0824480711a100c6407420310303050008114414482030480261080c06400010300c09a00d01145203070800e0028180d011080c408035000ea040c2d00100320208400b041e00075041001d40c4c510103481c0c6807042022801c030140b8121020b41e44070008407030503240c0d9403010440480340507406036410240340c014660240e01c00c00d1001401680000340d541110700e8a80d2003030b10303000d059083c41c92529034004c1c003180c26070308202c50a50f4150080310040060b4104500386404c94902100601414030380840e8021441c00ac1003806404c10101940500303d1074050421100400c5000170001c052890f50300d0045480d41c0507009031030140043c28000280d8480043c1691400c0c4000d0f0061818981001c214050340c40f0441c0d0140d03850348002b0b0b030000100311115003480d01d50600c01c4000ca007560410050110b04030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 60943870 1250 60942620 60942643
    0x92b032d060e06270703061208031012020315090705030d030e0c0109030203100c030b0901181103090703020105030a061d1609050901030602031305030a0f0e0f0102032a010c0e03 78
    0x140307036031425804240345010100613030100e04e03c207046076195a00110000e201a8201c00000300740e42c00c110081c4002c0401461254911000030703040182c840345c4e5491581c900b60350083d01588000950b540421200503001d602511481c119141a50380341c001a191009500c1148003180d40c0d01004c0f1000035042c8520401c0c00002c2c00c02040301483c43d03002c0380d0386003112900955000d98604041020078840e802400b90484000c00f4200c02e56120945110450400c40170903c0346441c140148140c02a8002034a02c240305000142640b41c0c5103400650f56603000801c21f41a40750356000100d1303c8984845c1e030708107400c42008516000c3c500610600010501e07848903405200d1076031400c102a90320702c0010b5040da1341c0b201000d62262650340d601082561224001081c030b000206070303417080b1039201d86800c0e4000b40c1a6500c00e4001c00301c20a00c00506010b0840f035006800c100030122980f0540b01801c61042c58100c441d01c201e642810304142150510b2440c8000501040319101d51858204030354404607 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 60945120 1250 60943870 60943879
    0x603030901080106050a0210020a03060e06010c1101050c01021303060e1509071505090a14011202040b03040803041e051c080f0103060e2103092b032d060e06 69
    0x103403040001c0c0400505209031010080001020b03516640b00307009030410000a4181503440303600340b01001d80507200501690700104610310005038a03620403030000c459580c02070040098a100b000045555501213070402c82c440d90200041a181c9482025050065015010008942160403d840e04194614003041e0065040c01d0030b01c55001004200700d02241c40c100f0344000301015880c001d556900076002c206501110160b00041c4113903007200c089000110980e034459207110f4109120f412400340f03005043e1008020300015002507281e1009642150090070400e440444d200c2450f44050140c2008880c16084003900c0202240c0c0080750400700105400d14500c10b141c1203483d50030121051001800a81d1980c0e41c46189030b401340310b00011306403090860200c5078516034044a2550068a50700c40921400c90b0340b20b440316002e1100f803000e40c04d4815160800402c0c1000310702800c00c8016644071005010800c982d8408201180400708000340804907a06191103000c0b01d1a010080125008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 60946370 1250 60945120 60945127
    0x9070b0711040513050105041a010909081213080c070302040b04050103051f02040b0c0618030913050a11030a0c030608070b0f0c0708030705031b01060608400b060303 73
    0x100d00c81c81c1420003500c1650001401c0c0d4a0ba10501004000c81c20b000c0c0c915481c0200784824031802c444038104008429140c0c0350241d80ea4641c0c6411141482400f41c8103500501c88200c01c407a00400054214485040c1d2088044080d25682480c0e03204e02c40d0380c0301551094804208500b01070143d2a80d41d442140c0400c103540c519104e480e140d0101e140184610901000d40000c45039031503042d100900442031030a61070b0b00d402c1c2e028a0303030344005036188000147c4501ca09056180b0003c211441d620026081c040b00640a201103009090050400741742141c5034052140082541d00103141304442c500f80104003105040000b0302101e5a58105015503081f1100511420b0008001c60310740c0c005031108550f13180b81002c809400e003405070300160164000040c80c40284000007003c1c00b00701d800a801008219012001d07d0700301e80082c858440810040c1d000109a413008542c0c50a21440005a05070820309d650036842030382d20030211201c80d0b400641c00d08003e000348a110180d00210640c0290f24 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 60947620 1250 60946370 60946373
    0x40506100b0a2d0201091e030e1318060504030e0901062703020a0b04031203020307020a021011010c0908070e010302031506030708030418051302150901050403020607080309070b07 79
    0x1514420000088180282c000380500701e042c5032080301c007510030140000d0840544141d8005d020f4030140740c040d900c2d102400000e10100020012216244e41c1c142c9443d03e01d455035405014054800d4460024203d03076070b1140100350708401c0c090402091240c0800031303c601e060300d800b40080e030310021000d000d00c884100501040f0341190301c481481d5044403c0051804407280e6900742c4070f5091b04025042149001c0014040000c24003070070540c0d2140c0c2d000c449594005c0000c070b00f24001200e1a03001644078120706d40241c100318054003003407035180ca0410070700082070b80c080b42998124504400041c11440701001981c030280440d10142c103103102803004551443d00060b95450f1803c462a0346280228041091076030100a098020942ca100b940c0e11790b0b55521000c848900c112420382451400c0200103150352000051081506900500c044205400205101020b23007042d6681703414007404100100141e507409000d842201e1154002ca9036a15240c4641030800304181e00c03010302c580040c0a22030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 60948870 1250 60947620 60947639
    0x82502031902240c07080c15090a0f0f0317070e01030f060303051e041a220503100c022508150c160201030209040c020a03020f0303091203060a090c0804050610 70
    0x10414003442207210306511013584a120354030664400420b41500010300d00380c40c1e90b000c1041c0d458a80e440d00d540303019654802500780c484404590090200050f03540910004111900503800207009141c210003461503a14003404002003900c0d00400f1644140b0161685d69040c01407804000a00d001407000d20b1640c5e07006083d601489a204103c120742520300c501c4201c2d105d00b650020904410b5140180c40100714012066004840100c154103007038240d03130000f940465290040319030190041100c0340424407500018180400711200b1401400c60106102c8080030080b5440320f60700c55045030080ca000003640c45c0c00d0094000a00072000001003201098615040d034031550320410b400c025411052004034000d10901e400d01e030b805440d2903480d04005900188810f04140b080d02120001b0381c00c0742b100350396400101c4031400303258042c00380703603003640406006141c1010002c1e080541c140c0d10b82c1e2a50003622900400a00020b80c52001c000501c08104403040d040640c01c01d440c1ea07d00d04180c8050b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 60950120 1250 60948870 60948913
    0x90105030f0709020f0904090b04110402040b0d0905010b09010b0406110f0a030c03090e0f040210021c0309060b12060403020d0c0c050d0f020915040b041506082502031902 75
    0x1c00683d603003c1012003100104004803415418000d000b08514011490400c88000b0281d40c00c0e50301c40c0380307010580c011342441e10840d002e48200c8035003241000021003040d00502041e03402280c49540320380f0010041d44500c180c280c00781600d003c48a0319141024002002502201c0c42d100c0380303a101a102c5000b124001ca40000d01940507c0e000e84207040324241954648072982c040c10f4040c02c01f004000c9200074250307401d4062807013100c0c0c105007107540030301c1240e0320002c0003a0381988665424140200754040c0e07010400d81c500c24003010501c1b10740c0344c0020b803a8101d4050304502a4020034200410554144001d6803040e04505202c0c0381c04a490300e40303042c0c00c000c2c0d01a00d0301860740031501c02d081c8080803089403441036009128020354a80403a00341390311554684030714011070405001d0a003524081c05000000e00c01c0864200401e46040000c83d84840084c10703007a01c00c0c0408406c4100e40300d06210703038814020769030021541d81c150030308a5540300c00d082402d202150001c41c1d822004413941c0c20304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 60951370 1250 60950120 60950129
    0x10e01060509061b0607030b01050c060109150b030c0306010e1e0907030e0f01140105010c030e041104150203040e01060c050604061d01020c010b13180b0703090204090f02090105030f07 81
    0x5500c5200070320203d40e007449100301c420000360713403c0756040c0745044c0000c10038400c6926a40500079109610015140c0d4018110744040c0c5030041c50040c00072120542c030000750024400002200c0c00e40d500c0d082807c66009039144001400c0c00010026103503000402c0b801140340642d105441007881d0018100810000c0309158410014007000ca04a03a01c65001440484214401d03035407501140540c084c000d10130418680c0c131002040000180c0b0707600503416080000c0d05034841000c645924401c110060400c411003443c00c2c8002e00000c242c402203498a2005101150015030380c4e10b080140009410005a1040c0100a2032108040008001240c141c1d040382e0b0080020403007898014480451040d4030741d8002e0f04c0d42c40840e5441c91082c0540002031284d000341c500020581b01c00020700103a40324402d071064590014038000c0c0024074040b0710140d0000c407a11b800a0707080c03c6580000c056032117200c011303600510032280703c0e015460010740d12401000d0840082008080710b40500d40c0b22100c5103c2c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 60952620 1250 60951370 60951377
    0x1302031005310314030603030a030e031603080f0123040902030a0b070306230d14011107080a020d020a110d030507050a05010213090204050607080306060d090309060215010e0106 78
    0x1080100040000442c0c12401c900030aa00b0b100c122482c044645010302c400b5000078000424041c3c015650b8400c6038040d1030050051443c04650700819409404829000c20591200708001411504903000165a06100350395020050400340714629042030306030041c11050f802d80c900420000c20343c4ca601400d03c0b8003134502107881103060000a013014003901c405007402c0c070040c0410103c16415031040042d03c000c038540c2000b0019000f407602aa4282da040c2e20340201640d08640b0109040329004400c503620b2a00100c1d08420000079140260002842102d03e0311000c9030345c401d000c0d014440d240000420707200502006071540c07512140010b150b180c5c0340c016003843c1c1c614000c1c940b04400320b44085403c1001ca5a0f0390519117801c80c000e511805280800720503080e00450500d020703000702c2d021a14002d00b1541050003940726907002d49d06c082c0c8042d0740100100131302c0032688101e010342c1c40c8060181d1030300303448146061800713410a0b68400c1003d00d040c007540b0050111040701f10784641507a00914 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 60953870 1250 60952620 60952631
    0x30f030c07121a01060e040e0a0812041e080a030c030b2b02090c0307030b0307060807030b061b0a02010305070c0f060c17090105090d05030114240c030405040513020310 74
    0x4001c6a0850b4008001204081d407030f0001c5035160f00403000310840181500c080001410800040c0e881c0c149070b007401805c8000810101d01c000e6200380113150424001c1103411890a03403800c02c16010302200e0411a41c20b00d0218841550765018071450a6a0b05a8101480802564000100250709040d649240301c40311854102c040990402048183c6501510445090030810400d6503c0d070800c41e580f400185c100361000c0410b043c045441d01c100d4995444801e01511342840903030207814290840d40d0028020b00c000c0081c1d000d5580071602a91014016001e450404c0c0001015100010024414402005041c2d4001003104810aa04c241c000350300280340d4500420807640d1035011560f1180c0b000d1014107024a002c810f42c49113010b4030245003101c00100780c2074410f640e00c2c0024030901d61495410001c20400741800c540d085c202410012030001c1c1206a080b4a5107203410010074001d20354800324017440241001e10074650404846003140102031200d0340080d0340c0b00c000d1390140d00d005d6201e0303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 60955120 1250 60953870 60953873
    0x1618061a0306280e0603010606030608030d0c020c1329030a020103021303061415040903052209020a050a08060a0f0506130b0703030b0310060f060507020112020a03020306030f030c0712 81
    0x1d0009103d00c540d81c084400249a03100140c1841c40c40660b8800c0c8a5441e1500004d0410300900c900e604565502000e10708100d184450381001f040c2c0602010298003c8500d451810b65826101103980054a1000901721503006400c800410884121064804d0941030071480c5903000540490699824a000f40e03030b42d09404c407042a00e600c01d80c0b005140c10300700746102c40e4280c03004404502c5480d040002117640c1a241040205540d4400d07005004140e08004410750341c40354566020718206c0c21100007107047e03030b202d00031400ca0344104030700400900041100c4500c00c0d4002c2d030321900528102c92911340c40c2d00300f4580515a010303c2c8180c0b13106410002e00c0d000000e031503c03000c10040c90642c140340e8480c01d00e4200a4007902000100c0c4d44a4002c20000c440810702912401c0b007034900780018440c401c1d04000d025981c0703138864034042c1d051204c8201003094a203100e000030081501191b90260b240d04101062505e8a0032240200a9580061158014a420008203001219001d0001d04480642e9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 60956370 1250 60955120 60955159
    0x3050c120c0d0f0b07050702090402060706020702030d030b18060328080408010f060506120106140708030a0615020706050a050f09030a03020106030308060d0c050d03021618061a0306 80
    0x41e03824a54101d140ca103018820b0090b0036005007003070360003808940e460303981d016021030b024400c600c8025807040140d03001c0b80c00750a02d500902a814801c1d440140f41940c42e40010349131201c003800310340000340c450410342c04c41c0c20100707130009000250302000301c42402c200c1c0c0000d444500d020030403290101c04c071400280040d200d03010244020342141440384d0f00e07034692508a02810314405220003550420030005500d08000e0304072503801c0c8900502110030707401d200040b03078082c441800408de40d08050100d50041840000158060300c50300314001440c1746402610000311003645c020b2402d6400c484030401c40982c200085640341300c0c80e8a0426907a81030720100440d41d000b601c1c41d070754045c46045800b004041e01540042d055901988628589654200400103607145c248001464884804000c10090820421907420384d4404e0043c1e98040b0350082d244200301100ea40901e028103401110040400f02921810001d80b83c0b96409084c2610100040e075454400503010038011040300a004414402 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 60957620 1250 60956370 60956383
    0x60902010905090405010c080705040501020c100201110c0109020a060309030516020a0e010801020a1419030908070f03090e0603010606080f061201020c0106051203040501020618030903010203130b07020703050c12 93
    0xb4000c0226055040c00c1c10514000d00040034844042028400440c0501d0b009106840884005130300422102c4030070130030b0000c4421404512003d56403030b42040d0078071418100180620b0920745000251900040c010807000c84010b902100601d4a00080074009c01e0707000084034003140d03030b050012800c40958800f0410319509644692081c4400c00008a2a00b00640043c85543d030789580b0020341144176440c0c0b1a25100701e07130600d40c1065071017240c0780348580650048130005001d82800c03814981e13561541c414500b5008411000100414010300c0080e00e05008a0340112040e4000c208690400b0006011540060581124500700800165955a130300013800f1060b40000001d64030380255151780e80c00381c0f895000301403007411840c1207119050000000c0d1800c0301d00503401420b4645890041007090b010114512085010406c8a024a80c500f4001503000303180003100c45c58003e40904100c02c41c604040c101c8070441d006800b081000c039900007202e40e11218115085080c002000000c02c2c038042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 60958870 1250 60957620 60957629
    0x1120f02040c08040203060609160e0102030d09050d080a0207080403020f130e06090d0c1109061302040b040609080d120b0303071a04020a0f150309060e0a2d0b040609020109 76
    0x9082a0540b40141d6000075a240103520a400b00c40385902e50340704215410304201d03920600100c25040125040d841000c0c00103203e481801074074a0041c1104c001d80c00d64130a005c2c03d0325158040602001040c0d07000030325a0b400450120110300388021795861480900c102c1c0700291040b00c000d946200c0d00d0741c07102c000e010740c6184540300b04107561032100d00030b803222401c5035280018001d026045429a00500140030480d5011401011020245003005a10480135010300d8014800c640404000f820b507100600c05000810560780d242c13841d01100038420a502e030416590f942040098808180c2c2220103400d079030700300303000c00320701d11602d040402d14500030f00c0c070054080c02c1003095403800c610540700b01c18006d900959048a06030344400c2c940c4620441446001251107413650011400e600ca5070000582074407415010851400f0681c220b841c0168604054400d11078503100c10440c01c02058031140881c40700030488107403086c261140e84032010300620142c6065150661042103a116229240192 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 60960120 1250 60958870 60958879
    0x2040915050a0501060e04180b04030203090d08040f050d0f020d1403130302040507030c0c150204240e040516080c040305030301031a06031605190801051603060e01050901120f02 78
    0x3860070b00030329400f9080a2085001107003200413005081d080034002c04001ca0780306c0003080c26098181c5da915000800041c801c0c1c04500040c00220a65600d140100d0b818070300550f01c05c0e803510308100e814241c240c0254041480707485600344500000300b03c0360b42c1c04492601100d68002d07030300032400d000d0140c3e40d800c1c070100c005001c0001d0600c0302c100010b4400c0262030003680d041010b646d83c80001da088034201102180424101440080000c0030301710303039400104c031211001d42050799030b801c91001640d600c4801a07803444003c50400f03400b54008018610b640d8210743c180900d0800d415400316081140c91004108420000007440c01042e480c1240c0c01954400b045070b90b82d6035282001c07034401883c98803c00342100c17020089101464000341004a8002d0203242030a690318101c2008082d49800c0544d4071207043d00500020603040a1203180d100c2c103100c0e1030010004100c2000103040f18450741001003201d004000601107511140141819284030340500300c1011143e060844001c060450001e622 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 60961370 1250 60960120 60960131
    0x7050406081b180612010209040c030506090f0103030806010e010e0604080d110708070e0a0902030601080d02070b0301150309051c0507060c0206060f1908030c01020403030e06041202040915 83
    0x19007000100030359608400100d6000650b003040801c1000318480c01d4180c182d01c810800b007007051412401c80b0904402c4400018500658007002c00c064070607504141022a690344c00300305143c00c1041109a0000e411000101c50358116a8045d0070600083c4c0a1410042040d03040c0e00c05901841c07406c1a445002410192142c0d41d0b543c109a8030300c0030070326000010341103060480080c080003404034141c1d002d00001c3d00c11075052049070026400014440b11156407034105007005a00d05124050180c9140c001614003401980c1d00039180c503070710b5803181030a900100300400a5074075034204007060450500e40801c2d5620301d42400c9140c85250890700c011092005040d06c0c107a500b10005103da00d109aa0a222100981506a03288c91040720120b80044000480800514000c6443c07080a100210f0801e034054540035003514641042d07000ca03007140c0d40010148149a0003004000200c4803c130740b42480c250404041c4c080d40d1400050007030140d9103485c416410840402131062070000e0300e0030304001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 60962620 1250 60961370 60961379
    0x1806031009080408011503030206150402070f03032403020a0312090f0603020403031205070827010e010e0c0a360c020307060b030c0f06090a03050102120405160509150307050406 78
    0x140c43e80144036040340340d0310741314029111042c0c00404908598040e00a48003955030706141400f0ba150720042c00703a0cc01d6080101000007154500b001e88101c0c029a400105808500d41141d07542851250307000c008080d2400400059440c192804180c0741d20010480000302c0060007a00d4940300380d00030014101502102040d440d92507030142c400c50340203035107210300c131517039031200c10100c2d40d00390742c00c0d800641090006030381400005040f24120a5440302d40300d040072512036280c00c64115500174240740e51a075454208480c1c00b00a40b1844d104100c2e1610b40c0c607850300c034041d61440380303010580180740607520b403907441c0c20840400f41c025100600018801c111408400071f44035401150100c4040d803401611030356504000482c1007940ca00902804d50b24504c143c20408681c120307641c480e83c406600403000c40040d00a0004d031501ba1110381131483c07203092900c0e040381000000c10389582c0102103014104025030700e8459082d0455901d00c0c2c4000740f400c1c1741c00132909001d0706801213904281007040005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 60963870 1250 60962620 60962633
    0x80d110408240408040b13050a09061a042402071e030308071701050402090301060504091a090d02030f091206010806100603020f0f03060d1a150603061806031009 71
    0x441c80d149503150500e40a04a604007401240c0586000d0700e03102c1c00344800e000c406c036010014440d280d160000010001e684400140e40800c0c4c0b41c0040c10082d803580710030446803122917071060244500000c61030810f03050210801d42d0802107804000407802049502141a000b4401c0718003401510414241c0060f094801a0400380640300031000594070340000342c420751181080d20440c45408451810f02d901c1c2c0010413002e03400c0050000e81c1550380b80c100040c15615841000c070524420045000b828103052084d00c20000010702da00740a41000d94000d0344154040105c504540b4880c0e001d0307450b0f002d081c020940102c1000842d503003610408002240002d00000d071144035003a40e1018030311258407001c0031800c3c0d000740d00e041c03100b2075401e1040c400848400300c040d650103a009811000b403186507490301052007400044180d00b1442440a01c00d407281a5000c00806004c19918245581030190114003a403941107000303003100c810180419811743c0d0520483c10100f071502c43c184100002c504150 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 60965120 1250 60963870 60963883
    0x11060f070b151002060f0612030f03090f12040602060406020304170307021c0c05030301030b07030b030601180b0402090f04090c051e030c0306060907030c05040506040803092b080d110408 82
    0x11481102030f0108041541d10014090348654840c060913426910303072806122900160300040040350100b4010348848200c050055403040c00008000e00c1400a200c049505020301100c0103100000700300814043c2035000105140c1182e4080001a130365941c42c10a44007555807000ca118200c2e0001092161260380025525203000c403401c00014400000b6500f5100c2002559006065800c144010000706c0d05600361154000d4030307802c004c10a03650100000781040000d80200018201d68202020701d01034620810305090803d6074214a4031060200081008180762041403045031605054010014424049c000500d0090309100f0528800c03860303001d000d100041001c0c040c1c03043d07402100451400090f414095000a01130001989a0540c114042c203452035001041c0401040009015212a40104000c214000c080c580320f00c020310400c0301610824450203202c03c86003480c8042075422407000742443d9070000b1019952020ba1058070003a19108003507045480e0302040003d000302021400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 60966370 1250 60965120 60965161
    0x50f031324060905010602070501030b030102090904030504031202030901091205160902070b0a050c090d03270312020a1e020a0504060305070303110105100614130906080705010c11060f070b 83
    0x380300b071944a04095046035002d2150800580c40316000b0072142d4045c2e4043e0000342005030025162014400c045600e44000380d504600040c5c0010f010028001c000d0041c0e114100e052000c1c518001c140d05c002082c18aa07401004440d803d06900682002420018502c0070742c555108203041541d903d80c1c240007500154000e580b10103800000415058503440344901c98030070356040030304040102d0103008180210810840030b001e25485045008504c281005140d103054040d00b8000034111b14107071001e9232075203842c1010743d440044500002642c1e05501d0a0420a40000304250f159500020340340d103c0c03c0c0d02503a0064a8010044240035000c00e41c01d003900c2c020b85508007140e8035041000d080310802c64079480381c998072100030b118244c421501e40500300044141c46080ca0450300d030a036030800d01903110300d141030340c0c9060800050605005180091009007415021000952503071865030514100140c451200055105000c0f4494015100034a070481c003911030604e850701d100791000c01075100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 60967620 1250 60966370 60966443
    0x6140a110408120903070b03010e06010e010215190f0501090c03050105010203040f03120507050633060d0f1e020406090e190b03120a081e0403050f0313 67
    0x10100a00c642541141d0840741c51600030704118141c0e0242c0304558012009060b030600a825000803036491f1200690b010703094510081480e414640000351460034220011030641d000051902e511591a2450a81c0203582040c0b520740c0d001c40c00042801480c20401c02d071099131038500082403e0701c0300d50150900b1510764400700543c5e40c9960059a03240a6440745110340501218140005065008c3d922030090040c1056030801d50143d4820b824900115050000781c80d078282c11080d88500403940034800900701041c80070388011800881e00354403800d01c01c0c1803aa83c0311400780f1070651745a800080051510052851040b8103104200003035401480b6070000103840000c049404490744030000e010303030050039001280c00000d0170920081c208400d000350781402194031049201c0c0d0f1240c000c0c40c545145030344005480c80d000151030384080204600c81040d1041c201003000090304041215880e07044519601d8981d502c0da07104a08491407400f0040852004801003982c20450049400f1048403810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 60968870 1250 60967620 60967631
    0xf060621060a06210b032a0f09061e0d05060405060f0606030606040509130b0109020903010e0c030d110a0606060302090f010c020303031902040512030901140307091701020706140a 79
    0x40c220741c0d44000c0008210b0f100d003c121311001c1c44405501020b02c944010b01a6013013070101c00540301160550340c0a466200321b0280c0240301074600040d140d201c2c00380841e00c50f109800c0c10780120f142d041c400080e9000b09040b07024800541d9039980f800802c010340c004202c545a28052420a403100000e46201441c00c05a070089140340c40e090003a288120005420542441d2401d0b0422007040b20180c80c05198450170404c0d00c01041409150032302805d424100541e45035500d2052600b1105141c180c92026040312110b03061955001c1481c0f00c40019610b40703003c1100d804298039081000000c00240400d142a00010701c0341c2d0541c02814030040d04440211554510000546d104404400025459041040004c0c0104884203c290100c1c03622280142090789410200b48000c0c1c50400140c0030f0780c1b020440a203e03682c0b0103074240030182942c40503821818400c40c040c3c00c1507024026070b05070306010144040700c0d0b00d003581501d81080e040344040c0728144c0c00c0f80d5081070502c010f94a80c0c44081c00c15 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 60970120 1250 60968870 60968879
    0x604181407020a02011e0513030620040b0f0c030c0105040309060f05090a0e0a020904020c0a1e080a050901030b04090b04020a0503070e1303020f060103060218040903080f060621060a 80
    0x443c68490094060315866103074100104100000503102c00840c003031103014000010b10340c0c0780413502c001a52045c5800211454540c1d50f944c000144904079500f01141048180100c1304100c040d60b0f00e807150b520780d031074440c01d07449412403c0d40920301403644190318080801061542c413040b56000c841141e2904041098040812a4244600c13055550880f0048600300312450089040550080e401940181064030500000d01640c0c8404103021a0383d20040c800d00501a072040c4031148040c610303411901c03880d441e0355450030328060b0a184170140700300440c00d2416a4080c0c0c0088140303041c010400c00c06039850745001e500124041d1010b07809100b03c488003040c1801c00150070826074035201c0b410030803135031503401510f0200f00900046003107004021240e16010b1042181d640618031401c030142c1c036800c507011403050b16201c202c07103240700314200040344e4003013030304000c8031600b001641d2230101ba00d41c2c403a00805c4583c400d50721202e40001105142402c8603a602d03d0302c0340201c00032940401200d0f502d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 60971226 1106 60970120 60970123
    0x2061812070f0b0708060d060507020307081c0c0503090307060b031213060f03060509070806010c080f041e030218090106030c090615020106080601090902060418140702 74
    0x20b03550002c010540014641c031040c54500140b09180040010f4050180148058920380c3d41303002152101d803081c0111100c1e550014036a0359a03a070300c15440c1d0482c0c14005a0311340039030b2138144440f450600c500210390280c1c80340e0b4021400c01a8035120030006084001034241c2c50300c00c1204141e042c00c1542c000c0d00000e20b050540d907410700d15001e006011901c01040e09003c240c078000040c4a55980d6075074490308000c0b1071401c4001a664440140e60785280150b001c0d0003508042509641000c0304401002030341e00c030045950148550401521250260740070081d44240014005c018858400007031551008181e4000f01e4015a03039240c000c08001243c00a501d02519814103010318294019016070480c141d100070401980f6185140340c5959040c02101ca10035152408603065613254020760340600350384120a030007003c04603010300007001040203000d500340350303c400039412070300 = true := by decide +kernel

theorem cover : BRFrame.Cov 60791370 60971226 := by
  have h0 := BRFrame.cov_init 60791370
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60791370 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 60791370 ≤ n) (h2 : n < 60971226) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
