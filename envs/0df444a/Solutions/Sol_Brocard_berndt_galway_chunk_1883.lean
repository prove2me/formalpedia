-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1883
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:01:24.387873+00:00
-- url     : https://prove2.me/submissions/2c1d685b-f1d8-4fab-bb88-dec58452ef2e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 338489208 ≤ n < 338669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 338490458 1250 338489208 338489233
    0x2120a2304091a13060308070609051f0c0806090c0a0c0206090a08030d11090303040b09040204030b090c012714242203080307050c0a0b0703061e050d0311 68
    0x1a9006801d6941242c80803018001c424200076800c01856400842d00300280d03425036461099510550308d000e4143e80e1104404020b0200c213202080b00c41f820580d40046145206070b8080c0070b4010700c8007000100740180000b58803420035850161050350142e13640e0340761925030b05041e5400710380c2c2402660003580511125410b921400ca000c03014081d12802161900c00d080c40c8201034415095a464807404d051080d840c240c0c500205403410740303007418200d5813214034079000304009000e50390010344900042024041038120106000d1a0030001fa603420300512008d0280014101c1000704031400c0d1b101c01c11013008060400802c42506060003020700a140184044201c2044071081002d03006a0000481142c10701c0f4a8030071419621010321040009841c58940603001c0c0402404281031102c001003510b41c4100511420042c10303030040c14100036041800000307004142d94010300100c29003019040803031800742c1c41c0da403040f500000c1c0f1200a01086a40459062644440350741a9120702070383c6006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 338491708 1250 338490458 338490461
    0x190305100305010e030c010e07050901050904031e03060302011101061a09031e0d09090902211005010e1801060b0405060f0d02072006120c031503030f0a02120a230409 73
    0x81071301d4400055450340005102c02c3d08544248000e0705a0b540b0224080041d070f150030802074110b0704111600042a03031103040954844106001e0f914207412071451030612240c059000c00281c034002c0e038034003a07082041c81595080318504c3c001e224514007450150006141110010b003a01000a8142d90081004c140405d43c072008001c0d00ba10303640c004440f002116540320304140300030050250240690f1005070003084c2c00440a481c0220341c0f90465004104542040240c0c0011300102d5004102c43e40c3c1d24060608615015503018200b030140d04006401c081d41400341c94182d400d40b00302945424544400c0004582c0003a0859000314020700c407202e2021400d1025015a40c000c00c801d01c4030252060f250381c092078924a05a101e070900f44102c98075104128120b0703602511100429940751078500c403040161404216040c1d0601c400130700c4815182c014000380c010001c041e021103103845000010f20006d40900b00c240300024188080b014117218001041c080c5031354500845a1130551240180710 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 338492958 1250 338491708 338491721
    0x1305060f12013918032a0b07020919060e090304091d0c040911061605060f010b0a080402041503051c030203160509040b091006030b010519030510030501 67
    0x91070ba5941d00080c4100608200715035020f1540b045072807001d040105901402c02c004404403030070410301181020b007003400c2c03d546901a5420401002d8002d07104161003003140c01680b03688810500030700d000106c2d0800c0710241c1c5c1c0e00c00c7e401003c2a00c15070302d14034000c12100707111b000403114907110b040000b1100c0300410501c0c01814400040d43d40c840c20011000241d0f52000e0340288140c01c5040200380c14000480d4111140d4000c40d13011520000700d04014071145d02c1607a4180e8800000140c12900301ca00e1903011000901c0358050720b41607920940201d0a41800b40306105418404002b1302c00c2d104d00c03030114254094401000040c285070b5000d015518403d030354108171110f03440706202d00100320780c1c000e503180309206a00e001d51461030100600d13030345c80c949100e02c40180b20002c9a880290398803500f00010940024020007586c1c68160704d20024810540b14000c0802d142a81c00030b0f541d403054040311030200541000f80e213044c00c4d80508074000e100042440d042c03c0c110030340100014100b8090038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 338494208 1250 338492958 338492989
    0x31505011b1109010e0702011109090103080313061b030e03071106070c08010609050601020c04200c011b0e1203070812060111011d0d08040b010905090a120c0b0c03061305060f 77
    0x311174a2810f0f0001030b08440f6111404160310304180306000940e940c003458a0f0559900015164a0341c4441210f02a08281004004c240314107140601d20f00c2c1003440060145100c0d5075800344481010102115102e04c2440c0c0e0143c203000c81d4228054050403d81c3c0200006c07840364121030400c82d0380ea000c01e030031600aa080507a8081d144c9003400455a41000607c081c02c0d0219000c010300350340352024802030041c059184079500000b08015248803000c0d03103c103d07940f02641c50891503121910700140f83c48a10b6014074468800c8040004003d40c0c008240c803645944503000c6441c201c541d820041c68000000d2805c0c0c1040000500e941c2040c200780101c071045440450b5103c9203103698801c01d818000e0100c590310401c003030b403810803022940203000a811260141000103003a11009811420111401000383c2100c7c0d82e542d40712030310380c1c0c0511440a464060218a43d45403520006000703207100950b030341c680c4000f0030540343c06034419591003142c000e05c0041201c10344c035601201140f280590740c0c0c2d00c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 338495458 1250 338494208 338494229
    0x1223030a0b130623032e060504050c031e0c0a0c02040603081b0708010b211c0906080a0923030d0f0506090a0504030207030609020a050916031505011b110901 69
    0x10201301d802243d42da00b0000700c00718050140c200e0802e03400c0c40c2e1610341c0304c01070f5030b66000300300081a503d449034442800707030038058010320a915140b01000c005904c1510016000c90f040c440906030a05070709401c501440d41e00655078602035a400003180d1520420400742e0707100b0780d140d03000070008400c0c400404800000001c1088500e10101800f420191507500404450741041d80c2c0356125a500c000034240040b040071051041000355080741d15040b480c1c0e2444440c030101421207220103070070480c0142100c00c0c1d99078070361640d605c81640f002550f0305050001d01c0c2c800300c0004480390724400183d02c01c1080c0410116803c0111001005007501d13641407001c04816520404d1003214109032240552080984005028a08140c1d034025580d03a0a4800030f88001d61f24455031b0115036422429030300522006141c07903030b0303810700b0b80c00b0b940c4100310f040107480442c2c0b500d0710300c510f0a10144016021610161650362003001200702c051b2440c00032181c1254282090300a4112903a00d444c0c0c101d01820141c4003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 338496708 1250 338495458 338495489
    0x2016060c050d110a0204050a02070b071701150503070f0201110a050c07091107020d030c0213060510080127090507060c030210090b070e1305041223030a0b1306 70
    0x18400e0408a420649000700030140d00a4415603c0000381e4031641a4165400181076980b000d0000082c014840003c103505182d1044c009101d501581c0c80110f03000541031002186d0340e884206610052a03501d0700c000c50410b00000700030a0241540c007100c072540740004113402c002d01e205040143d0015a035480814030114a1804840f001c00415001c2e0000c00c00411020030342044c50138240c02a00002031240303a00945407001c0500c20101c840c02035901605000020314484424809405117000e038a0054503a81c4404140701e200340d01c01c41c121040e080c106480e861001c441c4000c6020005c020768003642e12036401c80001942084044004e04441c0c1d40d160001c076991800a05041c882c0792005441070801101401254021404a4101010b403c0041d46134001d9000b003412555500f13a50f03802c0924040422062040f40c012040590140d9030350042c82429180d115440221b000c402001d14440910010307007400450351010304c0002c40100240240050f1040c2541503814680200004110600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 338497958 1250 338496708 338496713
    0x70206010801140f06041805060c040911071101030c03150b0a09050306010f0b0a0c0b090604120c0b0414030f040b040503010c0c02130506190308090907030c2016060c 73
    0x3c1400401c103030400c150341043c10328540b0000d4000d00030300918810b030f949117070302c1d02c11712001c06181400c6540441a125180340081002c45240c000f88205c0c40d545091100703200c1c0c44013040c000c6a03031113070388450501d41c1d4001c12001100181010400c10081c0355a030280c000c000081c1030090030081c04009030b0150381380300408009241084650010340640d00a100600031001d131320318080161030191010396180d518150084910b100c0090016015075250710511019000c045240d41c0300754003a00804280840f0000225144894502c014200c00002004140010718420700403068004007401c9908001d50b500b40c001c010b901a500145003040001030402860801707018200d2400341500301038040020503000b0a80c41a10880164201540d070300000b1f55565445501018600d900e16040e442c480d20b03854131540d290311070707070701d142c86002c6080000380d44511a002e010920b19103641d810b0440301000e9800c44075800d02868003911070181e24010f011500d48003031110700504180d030b40c1001500c441e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 338499208 1250 338497958 338497961
    0x70219050310021e0a0203070605070e01050d0b0d2306010b1e0a270e0c031b030903070b0f070e090c0f0c0709060e010608010e070212031806070206010801 68
    0x15581401111802010000c554012441c464140841c610140e601d0300880f400052003c03101003200006100868010303155139000000d0f04207103200d1b5004208070340700d1160545407450540d04a0380007403400c000420401704140c210466504010346508800b101d07650b10b854032199a0364403100c1107490540055111789042100b90f0041c51000401443c100c0b04040030405082e240c5602c5800c2d80d0f001841d40d5906100b040c2844146e000705040d010b024040440300c0c444001d2030b20403451603491900105680c2c25400d0200c0340203c0c130303d6082c401c040d17034060040880d03608001c04500c218042842280c000c00c1420a05030300c03601d403c50895019192010001d414003c903000f81c28080c1100d0300400c20200400c0b03040303074010780b002401c9546800000480500d41a056001141d0b411306011000440c20700030181103050320402d48a5a0301d40e0b88455254129203011100c03100140d0044202065480d4079000075500050b92076601101d100403840d256141c124181c940f5001a0301040041001d45000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 338500458 1250 338499208 338499229
    0x140301110a03141308091002160306020408010605010503010b090f13090b01090c0206060d0b100b0403050c010e031207021504030204051003060b06040501140a052106100f020303270f030702 83
    0x19481004c11480558030385c00740500a2800e0180141c01104010035120700802c00c100d10384141001d1402015203900d0b104029400511a4803460340c20084040340560259064078145d400340000d042c14080d0304010021100c0c2d100100d960400000321802541480741d0145202060003468080b01c5c95240032680390850725814907200031900180107210182d540d191010f84910b41080141c542c0740c84100e002e0343c18411f223610070f0360140000200001003050100d07081e11000026241c1c011088810307001e060315051100428000002d0810003c401407508011008860060a105078203250701e82e4085002c54506880c00e13905240c2c0c020003001080002c2c0140b1620007000e0f0341837420a40b03040b001800b400d2001c000c8405100c40410781114880c0b0030700c140d804064004c800d90307400d410088500100c0c0078041e18040c0c0594419030031000c0c1280030306800b840f8007800b54025807071551003d81c01990403082007400c480c4090354940781c217245002007088490700c1c000b52000e5542e4031072901c1044400b040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 338501708 1250 338500458 338500471
    0x90302120702011d12011a040507020d0f050a02010b1810090209060909061c032001050106090509061f0906080a11070212240103030305150a140301110a0314 69
    0xc0041100603680041a00d044028104c0900100c98080c80081ca072904044013025007580b0b80084105600050020040d92032800e440c10806511001c004036181d10381500c3e100c0220f5039096880c1c1c40a40303c1e50003494080c00e20f1000048503500400010074842e0007041c0303483c0caa41c461091245c490082d0b10301000406c00301d0710451501d00090003058280c00b410040c24452215600010740903113542545164170308100310620710001081c03038064940301906480740000c0106d4110343c40715840c1449490b05a4200361a0245101c1c0b41c0f038100020f00100030005a000350400e00d20842c502c1d00868401d05281e4079840d201d03107c50074218000c1c00200c00400d20202d6500b40041c01701c004140c0030483c3c0c00b40b034042c0c814003c03544032134104528141d24410340c82c160b10201d031b900004501142c400036068130300c02ea0382841a0346070715403c071035030340b141d0090341d980584d003030100300000103103c401c0d10f044071406000440c070345044c42e0614000c0c1d0003170603006001c00d86070f04e0308074126500400c0b0640d201d04e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 338502958 1250 338501708 338501743
    0x1518070e01061808120904090606080607090803120105121c1101240303031d0609030405120604170903010f0203010f05031212010909020a0e130203060a0902090604020a21090302 78
    0xe02d0b08211310394401c1100d1890b850813500142207403440d1520380260b051560011000e00c2520398038144140c1e40e080490b0b40303000080742100082481d400c0030048460510902d0100030882e424002000b165544881da0b1036110311400304000d4030008940300c000350104054850155007074503c1503c600b0358600742c0804901020315a1659001000e510f41902541d406281c00103a69003000c042e40b01ca407607416a460380c6845400d04000401400000170320941d8000e5501120984440310f80345e940b0071060320000c00001c0319203d415030910882000c0c00c034224000b40042080454030040c20103d07442030300b040142142c0400c0a100c1400c08200303110711141441d114a03d4a481d03c800c80750100c206002d0480c2254a9007211400d5559a403a40f0028204400a0741c0e01d9041641500800c0044c00d04124020300460002405000840c414280f5007500a0440142e0303940700340400000b0741c0101038503020700003050f007014020f880000a90304240100310b00001d51844504000c0d180908203c140311949 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 338504208 1250 338502958 338503007
    0x10602010b2e030221010807062d021603030c1109010308040e07050d02220803041a0705010905070305060414280201090e070e0a05060406021518070e0106 68
    0x1402a540c400301c08030b802c4550100c6404540110040c0c8201079000f000d6940b07805a000c11031648580b80350488001c1d0046550065403447d0585205002202c0100302c0714401c2c00c040e941d071000824116400b00f052040c3e45006003e01801425184079400a42c00582c0d29600ca404002a2107107540d00c0040c101da0320b01c00d940c0b440c2c0d00c07524144101d014103c2d00701d05010209103035500070003d40c0d40d10a8800415521000707190460495100c0518000000c11240940018202c0000c0700b200e0a6030b4060418201020743d04580c22001e0b0711040e012900c540d0f880007c80041581400001d000c0c40c4030720054452402c250800800000c01c2d01d43c2c0150b01c4d0041000100c0c400185002000c0101c140340b913042401c0c9190005172000f9010754006150b540e113040030004140ea002e070039038503c1c0c0c804581280c03100b501c030703030600245003e24062000076031b101340885a01d41422400660340328140032841200625200344142c01c0c40000c0e481503950003c40c400603c030040c0c000d81c9c11400d000c1d0015030107030f80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 338505458 1250 338504208 338504239
    0x9010e040209040f030c122a020102031e130b0901020616170901020c07180e0a0206040303030e0708100b010305130b010302040c09080616020c0d171c14010602010b 72
    0x684201520081c04100441305000416000b1207a900210390440d110186040c01d1600c0540300e08107810102d4003111070360078000700f03054204015a40294041c2d0003582010410203010100107200c42650b01c2981041c0044030b0000d142ca00b480c0701600701034a00036180c4c0c50b04400640781c41d84c0500300c024202d400254a045040d0f102003605d1400c40006001c644a4659403141402132042540e41091802001404540c5c8000b003107502c851107601d82001c20503985082416a02d922200d00001e512181c10007003000800d1103a0480c0741090346100580d141d40d5941d802031840c24034404001d241e400c1e1510b40d90840c943e09449407941c400301c900c0801c03001e140c607583e070304104031385c1401300a06c220b503a010b143d03040d00d10800550000d04242c00c100c0390181030071403030005084260460b040041c4a0b820a05002d410900e00d0350404c40d900030700881c1804200500640705410418440d9a190244c504800d4016824002c684038002660054404c1c0d5040100003420342d4003c0c0802805840c071000c01014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 338506708 1250 338505458 338505469
    0x609050a0311040f110703110f0a031407020105040f03051b0901050f040e2d01060b2b140c03040501060608011215060e01081f0c0519170109090209010e0402 69
    0x849060480380041c48a12030707680e041c000c00703c1840c115454880461b0340400c1540220b1518806103620085800794240e4501e40347c0d50f0343d10303040c0050019808562130280d00011034041c001709407050600a0820b07071208000140080f03242d10968461f4403904d207204195642101199940750305031503407241981000003180d03040e40e00107130050045665140c4030704032950500c0402c0e25494a80a5011144502c40400c0c000041541d107601c569440c051002507400345070740c120742003035182040003880059940c5d8044036045203d019100c50a40312690b0075004800100490303c00d400701c140441e1a428207081c0603084881c942c03c8a020300c030303540700144900c80100080040342c0394003078550b038030085008414501400c01507110110300f51812002140e0000082401441d0078584200c4590011541c0c0c1c64500350380041c82094049042001120102120207102034010600c40c01e001e9500d601c480c0c1c00c020a60001d80c00b0070ba00c50b0b0b403019020114604031011a00600400c0600800b40c14141c0000300d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 338507958 1250 338506708 338506733
    0xe0a0204050105180a090c030c08060301020909040305030901060914070f1701050409060f2a08060603070804060b130b10260405070b0703020a02010908150a110906070c0609050a03 79
    0x71000f5500c650800c2140d490b044088041c02d1b006a09220500c1e0502000c0c019090420500010a40420000e5014207051080ea44102c40c020000002a2180d450981c1c455202400d01500c03952184808948404a40138000300000c5200e1040c41303a14100600034030480c0001d0808040041450985e030b032000c5400245070641e00d040710001203842040c5000401231404929042d180d50603c03403036448a800403100442c4140c80198080c1e00c00303166080c100e41c02c40044403c6035000e4420300105600785d10440090354000e00c2500c00051401c143c80001c0c44038200710700c0c9549004c2d1907002a0b912070401c924032002c04c0445051080081401c10a100e401400b100019140b102000c40000d090260401111004102084150390b8540707880c03c0c02034840c44120801d0b404648101e00c0062130000002d100008440e1002e0810b0054580078404006031400070144004801c0038000e0507a150355800051000c648941402490f017807a00002500e0340070300c2e6010b503100740200c07107041000c60342d8440c440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 338509208 1250 338507958 338507977
    0x120703020c031308010f1b050a0e040f1e1d0a0602071b09021806031311041d0a050105090105040201050703082205010905070b031003110a1a040e0a0204050105 70
    0x562580c1180070750354a18000c0100f0500c1c030b01c4071035500144031503065100d00c2caa40c1e003c02090141710240317000145400c540540c4080014820442c040056104a0010b1140c02b401407012980c00c0b080c1c100b40054401c1c8641c401c20540d41714101a1403200c0e2841510110034843c45400d601204901241c0d450300e42e42c0070b01074030140e0001840020003260440034070602c4094400c01e03403800e40301c45810380290440b00c1d50840d00a100c43c6600c100b450306d01d00741c038410800d40010501040e2103a841200c60500098000c0e04a40c5503000111035000600030840c648803a60001d000300c1801f402c00c81e0948101811000c45640340c002404050b0741e00c20100c980c01a01070510440079101c01d080145a51091780c81d0301c400d503441d0310741d0404009064000b000194050011100140c3d00c600140185110a8981442d010440c0c0410000134402e00c4020000c0c0c48010801c0b032805079603c9038541108464500c04246c80c0000600303001c081020101584c10181c0c2d40421803e160802e40041e1403071091100c0c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 338510458 1250 338509208 338509211
    0x20a1511030f0a050601032003100e01080f0c1807030f060e1306050f0f1b04050d12030c020c0105040513020f0f0c0714300f030307030f020f0d110d09050706080c120703 74
    0x807007080d04041c4a500502c0749048104c0bc940c1c0d1451080d49641103c01e54500c1801500310140d56032500f80310381c0300c802c8000703110701300e9030b807074040040c0c00030303c0010074180100742ca0703402c000391118903070303074400d120741c5d00000d540c589502c07039151800483e00010401440844a20140320076102080c190f41e83c44180108400140004c603000500035000e680e000d03692064000e01c40e0420455400d45400300b45e45640c9081c4403890b50b42c401031341c42d00045130a0500080c03050004215501d08124444840525040b0044c0360440720408802290300051100e031094034001031204051000b082880d009000b01c2c071400f0350500000c00040d0700e05886541005244c825903c0300d00041a030b003003410a1941c080c0080f103101c5180ca1003c0c0340c50303401c00c6890b00042854100d445a003c2c6e03e90080f0703102c0c210300908203403902240c20380890081944801703080c2080d20510001e90148114461890500d01400082c1816032510708000d001803c0106450085201488090b4840f442d038948e00b5042184c9080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 338511708 1250 338510458 338510461
    0x30209060607050a03020304030303140f040303020d06120605011505040b030c1e0c010606020c010306080309060703050412050a050d030b030615030f0106061106100303020a1511030f0a050601032003 87
    0xa12500400801078a1402281204030400d1b4000004004482c401d49051000360b222040011101e1011680c41c400748244000050000340700707a0040104548618001419907140c0d201c040c1204c078140c4040303902c50f640e000144013111300d20640c0110a069803030710a241c2410711a080456010141801c2c00400c00420780d0b594880c0340529102e1a01c03040b14446407a6403840541c240604814071425003d4026404000041c1d40b0074081c11090b1a880e41c0110301c6c0c5003880d01400b0755980000d2050301000360a00010480406810500c806140210001c101410b0103040c064103201c0d850301c4620505150406c00190754a000c207101d40e001c402c0d10142030301c04c3d103c000803e003440d0482d0407010055103822404140030f40c0010000140c40c0c802411120940e4680088041048080c0809405640010030220018104251180c05103907a00c034081601c0703202120201c180e400070f46810300303804414010421a2100d61040c1e42d803000c402d02c1d007030001c0600225515420500d0710080c0390b180c3c00010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 338512958 1250 338511708 338511721
    0x102030c120c09040e0a02090603070609060804062c0c031605090a0e010f0c110703030c08030c040f0e010806070c11060a0c050f0105012d170a06090308060114070507030209 76
    0x2c02c0d00c0c1000d20180050140e50b400404036600c41c0c5803410224415880f01010520b182000030b0444207450480c0c40708481941400300a54403c240140125541901c83c004850400d120100c00000c0c03c00821800d030700c03c01c0c000000c0e400d00c0c03c2a0714460007a80102c5181d8a03001000928030100c4505840740d06440e220b900724040a400c40039054401d0350f08210060b69804100e91200c40e9512140da9111486400040029115441032001900080f8441d20010100b000000216084069500040d24143d80c6008030881300b049a4800c514240190004000c42030090290643c02055460030182034401641c401c84a1781c02041c90030700803a004205405802e0023081608000c0b0b81201c1100c992440c07580d403141c080e010034003407007172019800000620703900008001c0b02e08001ca010201c242480c02c1003c80d40e5070300e10b4001030308401e2091034030340e60100b401340c454941000e019a0300c0c544140b4041c400545224940069803010540c03c204400102e20081209000d582c0c1c12078800120f81ca0380d9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 338514208 1250 338512958 338512981
    0x3010b090117010b03060a050402030f04021c0b010303020109030912020a0611031b060709060c1e1a040533040f030509121b091501120f1104050f030102030c12 70
    0x26001c20810ba9006001080d4104804080d500c16082101c2c120b43c0030341c9a001f4802a07000c161104940800201d01050051800720326000520001d01076001440040e6240d4000040307080e8000d0b80980d55a040300010b042d402191240a4802160102060882980401c030103400744d11848040011a4010508440c003c2c004c0b9140801c8001c40700c0069406401101d481e06010b40b90100890340c00e000000b03c05001e13a0071640015045505076603008000001004107507610300c0100c9220388035110214240300c015a1040c05a80510001d0003040d041c00b006078218101c003070f8100f200c81d8106240e001e1249074041c000364071550040300304403210081c4c6429252800351203131032a40400a43d108481030f6a002417840c8000150895650300016001e0510035144000c0e503004402041c01445651554091a6907103d0010b110400042040080010000f2a030800c04800310700710700010204428500524846c59024049000318510f0520301103008803841070900fa0056030010b10001a58503150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 338515458 1250 338514208 338514227
    0xa05101412010204090f320a09030c12020312070905030d1112070b090c1c06051320190806060d030908070e0f0a4a0d0206090d0503010b0901 62
    0x38800500000100c840c4140207407d64078282c51210000700764400c0c85001c0080d01440c0e40c40041a1140d40d900c801e610080688001c200540034490f228070342c0320024410b2218808111566400785444000b144441ca40c0c082000c1c083ea802c028a4840a005642c0c011580d48492426418804400c030405110f040c02c00c03110740380c00d040101e004500f100030f1141c40c0075194820594241660b00a6407091b0400540d0f0904c90280020401050740490001d5200c4d4811078001a540145000103d4070f65907182800005006001c980c0181c41c0b1044030078240b101400c00004071860510301c815040c548065551180105917a02ca03204001e60b030400e2501811445010301040c0040e0f0301e0304d60302c4141e48400e10406031480061a031812000030070211081c81254540041c40501405441090000c071040c3d0340d036625030003403118800c40154084041000e0031400c6400380405401d01150317600b00641407ca0090010680b81c00c040c500c1054580d001e0200e034156081c0031006611152124012140344030f1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 338516708 1250 338515458 338515469
    0x90906130c052106010b0403120c05150109020a0909140417070812060f011704110f0604090504110303190f0504090e0631200a0e0a05101412010204 65
    0x3a103c50f612001005046018600c00904202c80703c5991341c1c85682e50500c80c900c030242c0040410806511014810700c0c00c9191140075000301c400c009050f21116220b8502039218400c102d07400602d44a05035000013000000341401c040400c103c0c80030400d0b41405a0000780014283c0320450705201440300c001d42612000d40d00000043d8540c60f42c1940f01c60301000560781a84034481183c0c00c103503258032565060403102c480b40b06610058860759100352030b00b49940d003030580c400542c1c036030703050700e13840d175030041e00c003d1100e88008907060034142084484601d0802516000342c004200440f1a0329411108080c2040300c2d2610b4816022800c1d411119401030b50081502141000c00e40c0e40c02010016509006089a00e40b84010790303684160f40c189100c091030504044000c212910011950089510184219410282012881c5000060000750194004984110052050042802a5204070313540003199020000146080850603100002c3e0b0041c01842a200701e9800030501c0001c3d010f4400070700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 338517958 1250 338516708 338516719
    0x402030406090b040b01051503070f080702070b07050303060906010905090f04020103150602010b0a06180611030903030a0807080a0b1302070c030c0f091b05031b130b07060b090906130c05 82
    0x42600c1d003034900545c207200d01791083d03160281400040351140100c074000c006a0301c90400700588581c081d01c031110014296029401420000943c45800000400169118a02442d074074075261040041c2d100016260b1f50401c02402d10500484d191501300710340180030704c102007281c0da445100407000740180b5001c058450a070700f00c00040300c1d901504204400310b01203501b81401e0341c0720f010031140281610005003003000c640c0070030072510b4001c018500c9482c8091055030314100a0704082483c650140c5c000310001070101c01000206648101c1064003c4243c0700180804a1044005901190050310b00a64254002001d80030030650b40c00400007150302540d0500031a603241007050264486100701f5506038201020b00c59460303103c0007101c50038070321034035140c1c02c540702c8112104005400c8107a45241180400c01c0200071407070303032411900400007800c216503075043c20700d0000241c86d552001c40303000702024001c2c440418400304105134001c00c28201903281e21610708000c072741035075240c0c40650040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 338519208 1250 338517958 338517961
    0x60406090911160209190f020408010b04050411120307080406020c0a060c1106090f0a060201020d0c03021317160e010609091e050c040b0316090f0f03060f06080f010b041b0507020402030406090b 85
    0x7c0c04075070060401c4814030070080003140b1012051000786d5204813001041807120400500c018505101048d001a00fa80112400d121083c1d6400180354096080710002d0381c0f1048091085250030068500604280e147c180040380d111b50301c0c5845032030442c00c0284204404561b008848c0c031490a0310808000051220703071242e03603030785000c0d000354407507101411100d0400350006031007800f9000300d51fa2260302c28200e00f1540d103403800303100407000c0c10f010707016440c0211100005502c0c0800b5020001d4000081c0301d0b185545454006842c000c010340c028041c403410710b001c00441c960a0302854852030b44140e0301044941c1c4042da14101c91180b50007141c1d01d41404800c1c01060b190105400a160102e511000c4810340c0724200b4020800240c451a145c81d0b42a0005000050241c3c000f040c1010720641d0103d01192581800c5080461124804400742c0d928202a82540b8040c01002c119016282880020300350400b0000c195104008001e0f000c0c0b074001001c02d0402440380c3c48050307459003020b403084a6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 338520458 1250 338519208 338519231
    0x41802090d0519061a030a0209042108090d0309083703060315051b160f11150a09060e06120c0d0b060906070f1106040609091116020919 60
    0x2803c55900c41540c0c414685030034420050170082c01000100c60007001002d01c07042c150708110196000820458100544000300c01004140900c0d80070010b0840c0c5803000c0d00c0c41c001d4100d525100400150004042c00c1c40c51650100d10390a003114120481401c20002c00300c880c1d003024076010760f007003c41e00d00300c0c0e100700120a03490b5060b03210b482524071aa41411401c601e12000009680068031042d8103d4401d082208028491000034000d00000d111380107085e140036101c2c584485c1030841c0951700403250651043c0d46103080a00740080740038090700c450900030106c1c40141114654050fa01c24016000f440d00c8080e9210404e80d5404039000c900c0c0f640626081120300750b0741d004039110700100350a02c10503508616254081c0c540510014028606008860302c540060114210b410740e0305022505482c149525680700800181000d51900900186861740b0501150b4030385042445882c01881400402161020084846a0119140d1a40d5281c4640036414441c00b0054405600d240000c1440b9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 338521708 1250 338520458 338520493
    0x901110f16090f0606090b07030e090403050d0510030b1906171c0503070c060902040b04050901020a0e0d02030601060c030219050a020a080102071106130b0d1b0203041802090d05 78
    0x15110210b4080c003110108254030002e507003032405060301144000d50148001d20748030340a4607925010f880e010317005a800202240020070181e4042e00000c400142d000281262402010f80009144120300107452941d1200c00a03800044e000345050307081d2040d00d10301000e0a4100342e016151202c280c2c684000c06070039071075407481c805242480410509903440d1482d4000c4080da44900340b01c0e01d41072100d203100c0e524080140328401c4200e030300c695940100c00300d40c0c0b41d506c6200c1c420820f0310001a51503c1110f000380c5500760007c80b0174410915900020b0041e10082002811103200b400c040401e52404c1c40c1c02ea041464100e04800c4805502d0000c1044c8400000c0d03401c034160082d2641c0c4501038440c5041c5090f13200b5072a0190101c409941c800b048da04101d00103010703060100c40020085a1110315000c1d03183d00c001d80d2440141d80300c141d160b1100c3c115100c042c0c81000940000c0d4901032400300184e2051040c5804d0700c012960100e500d07215902c9034500c07058966400402d84d010120b00400d81030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 338522958 1250 338521708 338521753
    0x5090d090b0a0206060603060d080711040605040c140904241a0a1d03100c0306080c221a06030a020d0e12040302041e0e07061b03050901110f 62
    0x90008045038400a15401c0680031141c0210080c0e000d0002962010103110003030340098603994112130944030b05070102e201c030340103440003910502440103d41ca040d4104000d4600b070350841d6100310326080e0301441854001460425203400b040502d616105404002001020030035401d50b0b00d1050348000c40d48201c00080d000d0155081c400d202458a0150400c40642d03015040311103020862150001e00b0445000c031103220304041c0142110001d504691668042c3c410042003100801e40f983d0301845004003c1c8aa5440508143c0300e1010048842c9415511012400c00c20b40e841c07580e60a10380e045803180606800c6400d0090f0103182d0320304040340c58000940c060942103c015241400b111090680401e50343c0c090789020f414181400d003180c0802008000207614181d13400a20800513169011501800820100300c0f00500007291400d080074209508900d40e9141d010f0842405200090b000300c1a03c8052034280703028028450340f950032614216035600c0c00c446600c10041d4290940d0020703072411 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 338524208 1250 338522958 338522983
    0x5040b0403080702010203150f030a081303140309030a170c01090f1e020619020106080708070e010806010f09050a0209030f24090d05030615190e0906030d0e04020d0509 74
    0x681c030940d01c0e010f00320300300d000a40b200b00c1021504c024040b49450140512402000000d05546560a0319540d8072195801360300404840701000100f00181311048134212000c4900ca000340d40f07040400000251034000d8180000d006110b10108001481c440005843c100844400200006041070a00d0303400c40f1604141210b90780301c070400b00d001c0c000442429001c1541c1c00340c011400c080701d142c84006404030001d4540c2c210f650301d100004416404201e820014640c3c0300c00340c621181407400349245000141c014038100d0307010b04010081d8000c404032070800c9428504001135283c4404028001901c501c030181c682c5849030700e02e01000c60101040c100318002802d2464100c4401510846400000448483c1d10b41d803c18000003d00c10302500c002e69001030001c0810140040143c074044079078000c0303441c460340000f81081440c00300d500003140d009500c9003260100c9152400c0d000103035440c6141c190410403c914255072415580316501914942c620126040c09140341402e1015a1082e190000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 338525458 1250 338524208 338524217
    0x60801090c140901060e010512130c0605031302060f0c240a090203190f051f0b040b030c0d060b060f0306030d170a0e0c100e0405090d0c0209130605040b0403 69
    0x14010750b030a2101c0141c0c2c500504040440e038607221040c0c03070078084d002e85035050040400c10324114461090717030b241c0714805008459000410b58146601400407a40000c014050200107005407c0c02846072054850340c11100c0f9540d8401c5000d10b50024061820385000510480f2884201992880e00d07101006660151142c2030360f1360300b0815415216150030181d00741c0c00c05127a485c10303103261050001d031460041d80f003400cad070075983d6031000d15040540c144c0308146041803c1e405240340b954000c1344003c18088500b4403003480c5002c0020b4856802d00d841e18032400d1546c40000c200901a0031160b451600285016203808030b58036403249551045031614424001c1c00d0550040c40c0c0100c0c0b141c011940a80c4c64017a8907a10001c2d8400100340c4920b0001e681d200d9080c114049644035884a83c00392031955560105020001c14070040e19005000c1c41041e400200a43c0c08040e031003448804002c3d01103440401986401e948030340e40e1104000007901c6a0b007000108028840340305c0b145400383c0d1090780c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 338526708 1250 338525458 338525483
    0xc1d01050f04140103141e06040e191e02010801150e04060602010204050310060e011511030f0403021212180604031407051302040803180f09040b07020c06070c09020309030d06080109 80
    0xc1d0f54103800d003114416800645003840500300e00e5603c7c0900c2d40000064000120300380c41e00301c1c00740703005512402091900703030b03140307500080126581c0291000c81d03c0101c2000011720f0b03540081d24421050081101ca40a150110b40c0c4080c41015544285840540100443d6496a20087c049c1d842801014060f114482500040a8103442088100c031200254101c0a90910610000c1d144100949408215000c1f1140810340c0c000e20090054400300c0d0b21041d0340314a94410311034246120040048103030800280b4608421a110032a508644444e011498003404a00000c1450140c0c0c3c00c040d000c40e160f468040400341c80002c0c99000d0b41c00480b40c84188008104900c3c0c240c0c030803405a080f09030018040c0c0014001c0701c0c01c095074206401014a5441001c00020508046040381e084e501024188140401d86c2e40501c029040c03480290340755450305100d900c0d174950700626880780882c0d45a00000240c00c800b03060003610009420194144002070341c6186103070180c06144c0055550501150 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 338527958 1250 338526708 338526731
    0xe1306231e1306020903070905010f05150712050a03060f09090309050d08182209030f110303151216050906060c0d0c080f0703020708010f0c1d01050f04140103 70
    0x15a4451903000040340b210481c2c5960304001303900703c05005901441072080100b401885401428003810100703c1c0d50030018504410402d01c50420300c01c50107106002c0140c50007040354400c0d002110380040c10000d644540c0c502c822001041e04c1e522200041e2486400401c4480035a04000003c0d4000c1d46d401c526079445400b044041c0d442d103607000b05408410030100f4120f04030200c1e184001c00d80180000401100c0f210f20854810341340c00b10103e8075680e00210320415800120280c0040005c0c50000244105514800c1c1d4911018100b11001612001c21070219610003003e420564502d405884118882c4142d50920403a5401114801c44110000030307040d0800320305a4121044040042511700c150400a841c0500c51180664020904119642200895200409440b442039008103000c5280000c000e003121603803004c004c0e025050100401036240c1c4004a51007001d000041030b0700942c510001078820380715601d5403291030240410b00042401100a40b0a2440002e8806200030391080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 338529208 1250 338527958 338528011
    0x903030504050f010e060a0e01060906091b0318110f0303120a140402010c060203090f0d050a0207170d1d03010f0e0f010905030f09040b0406030803011701060e130623 73
    0x400b5038a17026440307100014101d94040d08104041410f00c8000600c06484502c0a81039031803c1e04420401a00c0b8220310780141d1200300b042c12100340b00d04e0100030003842d0090f54203144841802c0981001c890306034a0030142d603031203501c801985d402404c407640c80c010745810002018080702d2500240d480d003410b0110512140009510440d4160b6070040900002d684c1d243c001d40000d40050403a114040c4030b6031040d0710800981d500c00403191907480d12910360030b034024946502900b20980040b0103824500140e500010201000741d258284840e001c4602c501c941031850f0800c89465140d070804001c0200d0681c00d0707000c103410385144020343c0c40880052900314280c4900c64802415a8001c000c10703128070f08001c01920b810a4002c101003444050f00002070191030060b0020fa0b400d6800000401c42b54905038003d221a0704098000e206461510b0150103150600810740603050f0b0800c50020200038041d84148649241c2c0e040a048460200700c0d8840140e0044504041040350600e81082a5030740 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 338530458 1250 338529208 338529221
    0x3040509072c0d0f03110d050c070b090a060c03140d020403060507020604020109051c1a0106090812030601080c04120b0a11070b0105060918010e090d08160c0809040903030504050f01 80
    0xa03104a10104403035903204130f6132a05100a070100106400d4802c00110180580b2803040c440382d96841e2600d5000c82154200407940d848104216810014240540c0700c08050301c045a45a0600c60052000c9013004d560651000c03005055080d8006054455040568041c5c02524040c0307108200b140d5a0b6442640c0c0c940080d2006800700796001410051403500c21552940c0b1001e1540650350f414040d0b90f1042c1c2ca607464602929042a0301d0b0050011307075444280b8400030098000203081210504c4090a070704e201c003902d1141000b20001c0050b00244803102104c1c0103000c103500f21842030341e55060040040d8802c0c0c0f036561389682000340403545028210b05a400607a045001140d0f9a442c01042103510381c04029080d4100728090044c4543d41c2a41e01c14600030400031402c00d100b440c2c0401828206081225a007091203c408140158111110354005e003004060414141140d22400d1034041070140d6105158090b0070650b1311020140d1507040079028912030401c44000104111400e400e0750704 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 338531708 1250 338530458 338530547
    0x9050d08010608181c02070e060d02011e0912060c140408031c0b060c0703110a0b0409090507081f0e01062403020904090c05120d08070e030304050907 66
    0x42c001141d44a4a14203100741c5110442c0201c2d20050f502900d1501c00c0292040c1184c00740c0c11110017048101f23118618180d120744200c8484100e40080d0340060141d141d58021061070080704a483d0050318003030155070020b000207000c0c00004101502c2c026001d0009818100700044400d00110544948401582d055602c0ca102449c241442400d0000d8405d075140c0c0c80501050300c41000d03d500c0d844e8080109200c4a14601502100f03003181442a88403403100c003a9801054010400c0025040072410764050700e642c0000030550703015604000c0e1400e00740b0340114556010310714115044c01d401c801020100038284030b042c00300c4c0501d20101801c8a245204aa24044040c03c840c0d0b802e0031540550300509800d81001030801a101010400302e4510240c1118000540030040c029450301d00c20202d400d2910b0301c0203140c02050180c1c0180b40d0340740542810144012400c02c6456a6400d00981740a8031010f05449010720782000e0042c85c1e40f1403400d40c0700a4203945200c0c40345020540c0c80303034000c8a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 338532958 1250 338531708 338531717
    0x2306040c031a040804060e0d1b060f0507020901090e03130801061e080c06031e070903110913020f040f0e0309010311030108070315091406100503010e0c060a03020909070309050d080106 81
    0x745007610a49800c80641041f43c0d000000101c641c001841c00426480f440a24450710742e10181041e601901c40350040d5425424400c0030b01003c0010303078840c28171a0664400001c042080c540a00000e4030703500a001d0301034909480800081003003001580001c007103401c11091840c0c40354546070f5400c0c0843c82d5004034841030b0002102d881c55810302600940d0060300000f55050070000d4112520300e0220247c440c240000c500c1d1104105001e4100103001c02e00c4400c44114005d4240101040040750200038028040d5649201c0b110441e44e40383d0009040d5501d195080c044940099515030b20f03544810443e13400b1038a4580380510740800e00c07068038140c800341d00040c0303140c50554481200c09281041e03409080c1c0d49805115000030300b8003000c0c1404001c0750000704010304001d10300d00301e175040c26085075000f45c0c504401c102c2000d000113608142c1034415280b40d070360742200010440c081c0c0309544100d81c014009400740311000b0f0345540000c00960044007a5180255131040c11201c0c046e0a205a00009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 338534208 1250 338532958 338532967
    0x8060a0608180f0f010c0f0302030f04150e01090c0513020403050d08060310020c0a0b090d0f050c0307120507060f05330301060b121b03042306040c031a0408 69
    0x907148a6000c1e0070030144208030b80a16801d0b83e074151a00107501d121070034a9440b40c07200ca910640040e42d640c400300c0745044c25400e520b45103009480321030000340301030008044040c00300c5c03140c001356214000540108000784506074280c1002030410807507114403030140107621051f961000b2140309460940e41d016025024202d4401c1701140e038030001074000e40d0b042c020500c08030a0344107030748014509544054050141d0700b04030704014080c0c7e00000c0c12112076800400c50fa08400e903100d0310501e00780e4400d04105403925981d214851a5004000d8001c10b04144000080c0d100740c1c00501811041d44552414090f0030502c81000d8140c2e80b05641a14540300f000403105441c056a0001c078114402c00780c980b8400761404030000b42940c03401d0b031048034001e00c0091110302000c7c01b0380360141c0c4004105070821818034a0f1054034454440240007804440d84182483ca141a5080380c81c45461644002c0b82c0c890f040606040030414858401161004801c0340c0a6010b41244441244500d8100c615103041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 338535458 1250 338534208 338534221
    0x509032125110d03060824010603090f020301020f091e01140705010905070f060f03060b0313050f07091401080c1f0e061809100b1e0403020d0f0308060a0608 69
    0xd03008441500c082c004400040c14401c1c0003003001103060303400e0396804590341d403914001c2400d14000b88101451503407240000e05030188031140c100d045a00903c0c0001c4d40525a041a0b01c0c0020910b9009606500000b0080120550302d4054007880b4012564084c142d204040080180009041c0c01030100d02d20000b0504840940ca0151102038010800400c0880326591381d40d0070105103800c21582c9141401c424003115510034140414034045050811544e800c01030030941c0341c08003c0c0301c40d10300154010740d802040f80500c04004042c80601c04c43e079542c2d8850110f8000f90007104207048041018100004000c000080c0007042408094028021881c40ca5030b51412040c07888068814002403032080003054030b5043c010300c07600b0b010300030052101d12510100f190180e0080c00c44584240300800a0005030885800c41d0b04414002c0880290140c1464407600c05002da030f40040e41c070201030301081c0207000d041391518000ca4881c0d9921040750341d8803000c1046881c002d0207250001400e440010741c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 338536708 1250 338535458 338535511
    0x90a030819111504211d01020a200303040b040e0a0b0a1202040f0219080f070807090b160221070e010b09090907081c030c02010507050a05070204090605090321 70
    0x2080382c0175003600c1d14182446100c003640c4449200440700010303040c1010f900c2c0300c560000010b1b410802480680603003200761325012003061580d075000d80d8440200850340901d66041044800400c20b10803802d031200d5950070070380c100b8101126150041820558140078a03d40300c241c081c141d9813000b0805051301565020711000300442807200804a6082000f0101408143e2a02440f040540d44800462a1500304198043e901401c81c0d014062100c0511140c650484205410f4516146400d40c440010a415401d00130031000065041120360800c96010419501140c1c116144c082c1140e041b141d03140e2528254100903c40c02d4160341e001d01096055150144103e60001e403d50102c8803115115071000f8100f080c0f24861001000400000000154040c05049449480f070300003008113183c5085c0140c00c0307110f140c0f041e00801034001648411036440f64407a02986410400412142c60700c024082d80d03a520481102107004d4040240c0e006001224460f684181103a070301b40c0f502010f03002803890 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 338537958 1250 338536708 338536711
    0x6010e0a021c0504020103060b0c0a1a1017011e0507030c020a020604060e1314061804020d1203021606020405030f0303041106090607050307110103050606070c0608070203090a0308191115 82
    0x1b4100341e1565070004010402c03d0180035040c1107a4041c02c4148814503020103521240d00c1c0502050800c0c004021000c42221001811503840d070442e03c0012807054003070786c0140b580050000000f0072003404445518420340c410340c8102c2c2c107a2070402001030300040507a610001410f00030762252007084140503141c840c410400807100054982910440908203c0040c1c454a4202c21000000801088640d141c40540d0750341c079022040000c3c8107410f154002c00c0c2102902300c0040c0a650340e02c1455100d2500c60b5048030704a101f11040095071039210310700200a5846071140074428130581c4420307490100003100300c07806194024440c210100980090100f01d402c0104c1080d40884107000200204174180000c01405100c1d920f00c0740382c0407038400050b080341c1014206d140185424480c2100041e0b400175070700c041e6500c80c18250b0300c40c0c4d100e0300201d00e10320420030000c1d0402c0303101c4030000c20032001e500034060600100707200c45110908840100c0b03010301d14070040d81c0154171040c030f010305000001082a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 338539208 1250 338537958 338537963
    0xf0d0f02010e0f0a23061314160305010f0605030601090e0a08180301060b04080a020424030b100905090d050901090905090a0312020306030727050906010e0a021c0504 73
    0x22a242c4030200e4210708205907090212030310f070015600081008008038030000c1c942c0000c0101120004002c0500703607034050040149810400295107401800110001d1444160480c02203034009070301460140d031a000d040c40200c0340c3d50708015190036418154003c0505842000e001850268a0a804007000d0b00c101401d00005020f03000b0300002080640000b03041960502c024080200b00003c149400c68455070301c40b418504060000340300d03003400810132207d0f0781c0c2c04580101d00c111400f441410011402c2c1c031041940700d48400004100023034080254454180700d03030308444032603546d1411030039035408490203140307904400000700e110f40c0204080d0080307502c185041d0200030781b5140f642048480542c4d001c0003a602402c29001003680c880c0c90318440a94180e000d5086041c80008269540c7c114001d4000011000c80c1141301c01d58952115004400d07070010030301080c24408440782d241c0001703004a445000040e0300103505040203000f105c5803006440c121050050b10042168000c01001e00304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 338540458 1250 338539208 338539211
    0x9061e0a030602130807090507080604050405070f06110c09011a1305060f040e070f05040b0d020f03070e18070807030b030c0406180b0f030d03051305010e07050a080f0d0f0201 77
    0x20002c541984080c041d101c41100341c2c0401350341411111440c001c4107500034401103050004000d015603000c00900c0d0400019107011a10b83c8651030924100036480d00202450711341a00002180ca901071a40c02c40440b514041e106401c84450074843d007013100b4000d0211809511482c84220b4518000515940350b20142660007281c940b0000341c3c4550085110b1103224001080078440810411243c1c0d4100c0c5d85410040c005828050025106004038803800900b9500840c205000c01c8840c0c04440710032800820540d62403400000280c60300c940341280501032564201240b241c1c004a8020b280905403d46030030003141c2d10302000301c010703100945046030180120b00d040a1a51111300884000e4285414894070028002180c64100d40400c00d125204002c00035650303900340ca0100d001c0315004828600440c9d00ea82d40203102c2c0b094500c00a0040966180c9480203031000c0000c0340040130344030300b241c800800d01c0d030b02d00085503921054588800780350041000f001c22140142220304600303815000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 338541708 1250 338540458 338540479
    0x150d11040b040303080910051608090f1b030709050a020d1103190218100206190c0c020f1507140105010e070509010c021521071e05160807060c080609061e 68
    0x87c40010344001380c0f0440303d207680350400b8030402030700200403540c09a4200c000b80918030b001c035031941da541c0081660342c0528286829422032a2403d01c2540c000d00364480083c4030f941812159000294032408580010510f0008400c4c655081076046074002c0010314508504803481c1f0030350303800a5000c0c09080201e40ca40c11395032a4551100ca081d860550503030380203000d0925000010240941c5448241c01d00346107407101c1803c02e80d40222440400d60380540703604410080d0071012a420b410351741c000500102c40030030321104010000c0b5050b1041a1010001e00207640d0ba40b540c001403034025102c1d907010640902401c1583d502c503e000d03910031400100002e5203003c0b000c1c0410429480207405030505054815240300c4906440c02d03d80c0c00401615040314020403515107a0f00100c520072a101c2041400200341c007400000801c0804695040320f0140d0342c3e03400038030b0b002004048007030702c5401007030f81c45001500070300d0200341140c402d40010300100300c4c66180c0c4201d0100b42d02c4640746203074054201c91 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 338542958 1250 338541708 338541733
    0x605061e0c031207080f1819141e010b01020c0904020405040c180204030c0f06090e070e04020f030405060a05090c01030c180801060501080108010504050304150e150d11040b0403030809 81
    0x83c2a0f07008151503160300526042c00040086844401404625200089200d0100034a4001111a81107a180c08105810101d525108900385140140300d002880b450720100c5644000000c50075084402e41c1c02000440c1c0700c0c0c001a61500c043e145c2003541300b9040e9000901509160304a40d6002e44104100c82c0002c1e19a0070391005003070300002020050358041001e00030025040d10301c5e009030541c0c41c00030441919101d40184103d81902651122100c1c0c200481e400c580510309907030000c7c000910541d1150f01030f140c40c1e0820307001110242c545100d0000440c46698030b91184a00a0011001a00443d882e0400640150010011800400031400701026041600b0500080648082e0740041065450040010580001a0031481c02e9034900014040000d0000040300c0c02c660203002d00c0420300503010000d0303441c00e400d00b20040c3c0000c1c10003d034100c1c09804500401d145000c4039800c00c40c1d0140e209005145000d14010300c007494200704401d1022a0240b02d10030761140750039003100c12a08941 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 338544208 1250 338542958 338542987
    0x105150d020d06060806040b0306010b090105090111030a0305100e0702070522060306050105030c03031303030c0c0312080f0903090d020427050604111804120915050903010605061e0c03 81
    0x42d881400060700703450600c08a860240605198a88d08400800c8275504048041055105c0e1012181c18070200040f0280c0350f90250741c0c400c01d07000c00d8006a80d01d504200d04003030082c140880740380121442400c00440c440d5007000219004003150760042a095085c44107120902905040c0c0d03050810181044403602400307401180060b510508000c2602d52405007418600301c2c006103e140709400034480c5204d80484142d15100702c0e0303018034252405041504040d03440c000d640c0c10151101c80400c003184011500302601074000c010411110389140c1da80004207859010300c1c40100d40c030510030081c0306c0243c6000d401a90b40103060f914061005103000180c425003000c0c4400447c0d480d0448002c01007030211909034442c520800759404d4402c143c0c0020100003088001b80000c08103142c00d00007403181c034400c0482c00050412490b0f4a03a08402001e40505640c0010b170055100390300340003000c5223a05002042c2c40c4c510b014611895074246910103610030903007007400102080e1000f80603040312040d01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 338545458 1250 338544208 338544221
    0x72f1306050a180e0c0913030903140309030601050121020f131e051c030f02010b060c010917070506190b09010e0103230c0d0819090501080108060105150d020d 70
    0x401c0a81d034903000400000506980302c14401010640040c0c0d5100c1e41c40d141e005860781d1140587c182c0401c08009482d042d60518082c0c0c00140078400d14181c0c0c2020044004018915032008a044807c3c0b07a0340c131001111000c00c16007102089520a600407181440c980e0007400700280c040312014109810b0011003403800805901908001c003060701c10000c0341c040340301d09001070314040e01d00f00028800e68500404190029000400308085c0706044a1510310039400032201600051443d035403000f400ca6040e004c0c00c0e841c0c80507030300a007440d010410b10301821030446006076800700141c02180d86074a070b1006801248411a02c402e500c4d400e81c00711558403080102e01800400d510900306504504200b10f038801d030403031101582d45020031283e210b1f40300014242142e02040f01c1071a120030039031810b80000e0240303d44403110034280380200c1320354540214540341945c07001e03a1019074681c1d8901003165680e01c2842500c1d0020b0b20700c810122445032002c01407440c1080490b015140410103041142140da1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 338546708 1250 338545458 338545469
    0x20f061e0706060e070f0c030806190e01080d080402030d081807031a0604020702010e040f020d1d0d02030703080c03180d0206060a1703030f090f0a08072f1306050a 72
    0x59400c41407011300891984590024901e01d03015040244002d0041e01d03150030b0311b00280c244901200010659a00c020035011091540100b1061155460a11104a000a0007200441c0c001c030f60300d4851483c4142c0066100341d4004005122800034100300b074403140400b0b8561745000c922245540d942e2042082440c0080d0f110b0032584032030305e2020b514011489006403255109a00401003000941ea1120b510543c1d064120760000c1e10b0403203100030000920400c084600f842d405d04c0000810300140d543d6408003112544203940c41d1204149040361244910140100131030300c43d5000c924010b00d00e1000d9a840042201c002600070101807206103051160780454005920200402c103086c01c003404035200414a040661044907400b03802c03162240401030002c075628581500240034000100321a81e40c0a5181055680000c1d003030802c10015480540c094585011a4403101040143c00d00c44214a5038a440340601480d5010200460300d13115405c80d1400d240c0381c0d03602040350780c0d405035850700906 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 338547958 1250 338546708 338546711
    0x9070e090c0a061b14010f060603330b1602130c0908120a0e06090a0803070317070903020603040f120c05060a02040e01030201140d05041419020f061e0706 68
    0x4015000b00541c0030340c66000007040122080c0c107107140030346009001c88825444110007030700e412030307030800ea0050a010308501e00311b50606100248058040d40b24079142e85c0000c0b00f54a40113030903805c204014010380d10018654209020410445101d0300c050040e400b6012001d003101c2a0503000188080c05844d1101d030b00e0f5581d0980105141d411400d0500100352070740144c61004a0200d940040d8014500500240010003039140c1c40d680d55130003140c107281c0009003044071032034892103159607a800a0710101c010803c0c0c9541e141e4001a15035000344a460107503a10050780d170039035081c040c1903000a0401c40b154154680d03060006000180a0001e010065582c41100c001d5800c02c0ea240400142032205080e104000a12500078081100740c107498080c241142d82520701e440c52000c520030080070042080c41c001c1032204000b81c080507001c440294808035645450500640c070700d0503811a00095102e03164185d006242d040040281c141040f000b0100c07000c1030303440c4800482c0c42e07019003005c07644075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 338549208 1250 338547958 338547973
    0x80a0b1509120a080915040f06022118010e12060f0a0b040204080a020607080f03012601050f07110a021e0103052202062b06061b170309070e09 63
    0xc0c02d014102410038044207000303003c0e152081d16030781c031144105250036000b00b0241e4007416801009204850003441c0751100b01a039159aa54001d48440030141d110090798482001d030001394407a01c0030b03100181400d00c40c0c49004915040159115581c1c4190315400c816020400701016a090103014803d5080c101c0000280c50b0107a150400c40d8150388080e03124610600017403200f80400142c001c0c010340d0503a51640c4e140310b07a040456550003461441400c00c41c0000001c100f9130250a008101a9880740010410815000c2c04c40d0a032070302210041c10001c503980004829503c0349a0051030300082c1c0c400c0d10740682e0306401013a56445014208160400b6800482e181e6583c94859558814141000501c1460950b0840042d0115049000c0c4c841d120120701c003100341b11009802c078000b9100c070051148102c1d492103100098100fa200d10008911b02c200d0b000d4802c0605815030302000d52010400380300c06071054040d4010341000e4104010340c030441d1400b164a03003c110301e00d4000c054a00052584 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 338550458 1250 338549208 338549227
    0x904060801022205190308030705070803010f0e010506030f1906051005040f090209090c0a09090504210f090b070f0b040c030507060905090601050318060c120a02090d03080a0b15 78
    0x5101c000d0f4016030143c42d4080311104524034406400050300c7e8440440d540d00c0e15043c0040303c15018000380600550b00010000a45031010300300c0c2c000700c0e04241180c243c2c40e0703600d004100340e40c00301301c4915020340203180028250207007880342e2006200d243c180015019440ea00840c492110800722040813030000601409211440c0070707404000c00e074016041d8034000780c84d404a1181500039000304e0902c0d81c04a65005107a014001c001d014000c3d450040003140340c28207183d1010407403040140ea041e006009440d07681489542405003c020710745900a0092414010724a9a40100701c02d0391b001100030810700c00190181d072501d0149010300b4080c440607003181440b90030505254011001d1001e0000308010301c2d201c441705103a100c407007400d00c4d50302c1e603841490000e44100182219040d42c0642420005400c3c45540601001e05607450002c0c0150345041184049118104000754091079942131200000d1050f0265940142220400f040c4000c10070f0211701400c3c0820421a1100c1012485808 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 338551708 1250 338550458 338550517
    0x4061808030d1a032404060b030d05190c020102060c160510020705120a0c020607061b0203183f0703050a03080906040201080f33010f02030a08070302090406080102 72
    0x840c0030110b021785840310101c2410034050300d100d40380e298008251000941406047d0780011510440501941d104c6010a0b400504560000000c0c0000002412010708098800d2a40c1500207034103800902240d280c0c1d100803145a044030340180c01e03040640d1024800038506100b443c1243c2000540981c9664161030321a080c04040400c1025201c03060180448040c0d10148003504031350103448031580c484040c1008409062291180c2e0044002d000c1400b05140e400002042c4070441e002c0a0f5503180d480c0000c0010081152048092000b400710204076401a5000e400e440051a82e811031040c1a00046460800c0519407064405401400101d028507410000c8580e000b00c0d440f01903d594501a400a0554030019011101018101c400100801c00c62411100d03540d122078044a198042404080d244483d001001e034001403c0d00d0002418900000584a446a0b281c031400696907404001704e000303400100190754016200d4400048100080c8000c08c0500c00c4603c44005e151040c018481 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 338552958 1250 338551708 338551751
    0x3180f1c0503070e1e0402070f03030b06070f0206181017010605030603030d0b120111070219051008070314010b0c1204060f08041a0123031204061808030d 68
    0x1041c41800c200f004001c0303138400002d8100440032249010800d000011030808080e10490182d005840000c0e01d00a00c101c2c10480403030b0900c20f6609021a005a80600100340200280104031400d14581d20005150a0740603205c040320b4040c203110000d40030790000b0075082c03c042200000c1000705440d11101c0400c400304ca030241120b42851495418071401003980c034400c60315108661695078501e407615940c0c2404c07885600810348001c3c030401c403550703008041e280d2080d041284a000f0215034002110740300b6030f25100315040105180618000c048050b588540c0060007101015170701d000d00b0310303040398803070069010b0180e03101d403140c68207a4003001d070b0320303100e80034501410044c3c003800100300b07060303000303442060f05d01301440c2902003611a0b103001614100390f4802e11000510040c00460729514045040d01c0e1600640c04a00059004e1020306440344002d0442081e0070808110078000a4090600c0401120030f00d030300861402d0307403222040d0654000e0640d01c058181c40340070302070480301e4054048 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 338554208 1250 338552958 338553013
    0x28050a030f140601050919140f09060f190509012414090d1a010306020a08070309030801121a0702100b0f09280606020c0a090e060c03180f 61
    0x802c405800400e00c4044034000a001504001e80000c61200345c0e1560402100220243d24962990f1038580049080b010041d4826030f0007948015542011490140e42981c02480e0151540c4045451403003840601202c10501942d8a0240b0074001855102d043c403071802400e50700c1542c142180d004a4211400e03419800c4441042640e042d0542220826812108031510884040540c1c41452600070401250b951400410320740c00c0d000003060080359001820f40712039558510301e02d0360724803000303038215121482c018001514010040c006d0f41c50310305407038a03410301035060980341801d9454040c134030300000c44100005030090281005015154054050066001c8450075041d60101010640688009084004400d33608001480a410107507400c0c09840007900305124041d22035070b000e9034130103240c1c00f1140130741c0824000050401452141c1c400d449145030161400c3e8850344040c00f0f00f0b40024042c04118040c81004641c0000c0030480c20064403103000142c071116442a003003480c00c0d200010700 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 338555458 1250 338554208 338554211
    0x90b03060613020a11151f06120c0324080606010e01080a2007030503040309050406030819090f0306050a060e07021e150103110f0f130228050a030f 65
    0x34400941d40300c0a41268442d1101c01c01616244110021603484009107144201c03405094407500c4180c80c0d10001a204441c103410141c1041c4801e00380c1d40552415200307000015200d40d81003c2200c03110742000c0d140a00f140380105030003503a036a482c2480b800001010f13840c0745000000700403062042c00302035070100003400d22a0f204504038001a01d4401d00400c0b100c959513031503002403003808650003d41c07141450002c2c2c80351a40268503002e400381d813044c0c8055000c5122160002450710302405100b0a5a0344810b01a0400d46000e4070307001c10800030560302c03091001943e004075020001000c0200194020940440c42d400c142145c001110011f40041c0d0071040b01d0003c108281341c0008040b215010403448128074020062201420704030301c075039038102102401000105010407000c40091110341201c02c4440c04000200700008035400514940d041943d076001118004001e034041d0403180320a0400c4200015504030142000a00281341004204080741c14010140d00d4440d01c0c4076503e10810 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 338556708 1250 338555458 338555461
    0xc020106050f042004120c05040603021003020304140303090c010806031504020607290103050d0c050714040b040f051b07020f09071b291608180703030801090b0306 72
    0x4201c8103002d400d081d9020b551206400942501940072a103d8496559151511141c803884540039017111828181c0784052050310208071458144115411079a00401e40c49802c21440000c1c0c0194000a000b41ca403814020f03e01c0140103801d000841c850143c902c040c00300204104000362405c034000e8030081c000d074002c5006410791640840c040341c1284c0c040302c1d056100e01c00b6192016040c00c80002c051521b00f0513051000001400f954000c7c1070704c1c807503015030b6141d0b04030901c115150742e4070042c05081d56010003410003994211800c00215907001410104468800030041070503078103412541c4501c140d40d0800c10043c85000c8050500214a101b107140c60004150000b803403441e58206054410f0342008007059115001d1403a0754641d8000f19005c50606c0c0a9051030751700741c5a404600800105810422284200c24a1003c0d1141c0030b100e4a070300d000308860504440d110002062124010350b0038802c4814050708004210045110740e849400d07560400c600c02c01500c0b00803900c640207601010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 338557958 1250 338556708 338556719
    0x3051e0c0d08130f14090a090209161404030f0c06020d0203090603073b0d0b040b090f07320f0906190314060c070506010e04060f140403030c020106 65
    0x1d041c0c140741a082036085455440d95030640e01149aaa4010113051010040c0040ca41e48080f05200f08248102e90114040c0c3d00c12400c142520074614009500001a44c0003404800545d10480d84000b09840c04500d6a19003c0104a041c1d1098200b645c4460420403e10204030040010034050201840500340628031940044d549000c1c01107010702c58100400000c0e070540c4241c9210886d0000c0a03040207550100d502030a000c05c15602000017440e01d44c2c8610340f000c1c24017260019005074403141c2242c455403a1b4980c0d81004c0009042c004c1e03140103401c042d811460007004141d01501101c100d4090441c8116203c80544000313036030f90360040d003482062a0b4a81d032507080703203c450f8806030341041269983c0000100d5510340d00684156103020704c9004414007500b402403084941240c0100c44050300c4400040d80c00e4082c54900403e554054030060001c14401c501309a0024815030011458040a0f02d00505850403691140041a81c0d07208000c1856494080c2402c41d0402d400200450350512 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 338559208 1250 338557958 338557969
    0x605010210090515040f0302070506130e060307122a0b1c0e01060803040f051e010f05070507120209060910170708030c0109021206010b0702040b0f030703051e0c 71
    0x4642240c1c07529564001041800024081036202003009000701c002c0d40303014a40540780880100382500188a13011010800741412001c40f0b19500c241012461441e25142943c00f20560040a0503098001c04400187c14414107021808082c400c2c5c948000d808112103a078000004003210201a00d880788100300401945001110b2207100c0c804108110343d001901164050420b0210000e100d41c0f0701680020f0b00e810200c09801641d00702180c014800d5558000c0080c5801c19259285907100d5515000c5803660003003110095401c0d4605055040c0100c9845050809003250b109940d88a1101744000031807818440c103550240084491340024100702010740d002240a0043d05514500030344d40184c5020100410300081c403031030089a5503544140fa0081c0a0840c82201324042c0d4421032040280c03840109545050302e03128610141441095002c00015019845110b50042103228100f000345d00c0501290011703500500c01084810003004061481d882201801001904102904001580c80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 338560458 1250 338559208 338559223
    0x13030c171c05070e121c0503061302030105060d0902010e0907050a0f030608300c0303010e0c0315010e030304031b0e100303140901050d02030907080c010c03081906210507060525080f0a0509040b0406050102 90
    0x40034310001e410420740c4010b80c1c80d0300d07038810b0b119404500002001451030b8000c005060a0342103079130780c41100003603480a4040d503150f8001e15483d81c1182428600980300f040d640c0402c900d4036445400031002544200c0701c2039000a4032214180c0000005001651003480b0154110816990091545ca00004d1034500704a5100302e04d070402c040e05179468a1036800b002550040d5402503005203806d55040301b100802c42c5240f00f00ea10b25076800d80026040d40702c0c6800581140d0b016224050391035081940c80c0b4983d480200228103014042c41074107000d000034405540714201120003801207506022055140c05507a40c106410402600c00311000a503200c5105500401c6e03881c0c841c403540c1c0d0b4504842001d092a41c200b008000180081e0040c91110850704028190203181507134812500c40804840920030070394030400400c04203003803040d0100d1200d444030b140780c001c000042c180301000c102c1041aa00c07202c2004001000461499151f1070107120324142880116001c002c5286030900207515101c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 338561708 1250 338560458 338560477
    0x628030f260d0504032001020408010b01050403150e01090f030210060b040513270f0c060306030b0601081018021c05070813030c171c05070e121c050306130203010506 73
    0x11920082010140503802c0714111b4000b4400b00c81106020380c1d6072078000c1d0400d109104c2d0075070800403494a154001d800701e0341604d821290104151214000c120050512885110281e650307c5000101142000880c404000d02c01e030301a2a50041c401e007020180c8840e80c1008202100802c020406035844817148040d428a040010441c807034010112005108401002d990741c14080f4114010044e00d0200d100308240326851410350561250421003c6842902009140f45c280d800030440039030052035160f0f80f00c039108108a410b01c3d02c4e05614807800000d44160000140c010030f4040910001070401d2880c400d681c1405c10041c50884401000f9110190056040c044009880000d061040d848000c400d80c01c2142c204215801070002c40840e409a0703400d09d0600c4844108490f460518000c003401030b0302aa584003a90203000c0300b00515501280c123180406d100b041c107a51079240e5481c440c4440b4026548440380c0b42e10708001801080c0c604c245501c14403500c100014800c43c0e440000b91800200b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 338562958 1250 338561708 338561711
    0x2190c031133070b16080c09011b0f1202060720060a020702010c080a08070807030e0703030f091d0702010b030303070c060207020f0d0b0a0b030c090628030f260d 71
    0x9004540d00000e4412030b0405480404400104031040201020040580c1c1803661a1101c1f0769520018006502500000078005503104404044940302c0c8200e010400d0700401c00ca4031105400c0d40d80303a00c503040017521840560000000c0214168100ca000e0200180f220204500c1050b118001501c604005005220007031340440c6030015a44901003850f00d07640d000e242c542e030340c521101000d0102e60307040f01c05e84000b9000c200080c07410cd119010b1038180c041910010114541580c0d816241250010280701c1044142580000c096940c45138101c10074203100102e40305c46c01d003800f0081c00e480301d11401d28043e50041040c07006035644001101d400c590080e50050325500f643c40094049c0c0c146894817070380440a20f0034502030101c800c1e102401080030032820001e03c58034005042d110b400d4078002d1588100c050000070301e0380c2000c00b2000f21040d02c5111203014900850100e0306525500d8209561f040c00c0c458400b01000f1400400303407408100e45a683c49104500203084209105042588440a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 338564208 1250 338562958 338563039
    0xf0302060f0d060b0705010515011d09180118140106080327061207170c160c0504050f0117060f0712060803031f0f0608070f02190c0311 60
    0xe440b40d4040d001900110051070340da803800e4207120f070181ca0b06558140d610144003075080020360189403031b40c5180080c040b501e9908081c620803c114520003c2c003040c000b04400e1500340c0701c00c40030b101d4002c0b10102900a20341c0c000c00f905000009444200c4c03048440c0e850a0014081c2800000942e8100e028800102117031020f5207280340c9440001c508003903004500801c0f15101b21081082a070f114140603039610884402c0d0309100d040340c12041d5850000180100200c6010444039040c1d00c2c08a405158003c07006551000800c0403143d08a8540301c007109968010b000b0000e08030740041c0ca15a101008020b14240701480b2006550094030201c203201800308000400a41500144001c00380f00007a02d4403440c10042c850380d030714039907a0b0580e554001c074003011580303100c0e1005001c1074904541c0d503615141e17500481904d08021034404241544202100e188144072580f4000d04002c0c81902002400c52652500218800f0517070744092284100c4100c1c0480b07512000c0b5400100201c40101c01504e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 338565458 1250 338564208 338564227
    0x10207021c03021606050307020d091a0a051603030608060a020307080105090a090c06050901091a0a1b0c0b2a0c1509090901020405090105010c150507120f0605030105010f0302060f 79
    0x1458002968805805640d110016013103800a000e123104401c0c035001d8600f05d04c90103000301c9490742640600781c0f40c0410030084211341c154210281202c8202828010720b46041c1800681984010384811070000361510418003001e241070104980144240e8429800d505010fa4090020700050040030f000c0e56550000030004000754010071122500108003015032070b2201001003c5070f0220400c0e502051901c2c0c0001105180450a064491904041e13503080c0515000100c41c10b881d4040301c03074065102903000310003290f144001c0c00c00500c0c0070400c0035a5403801e40d40f0442c00104000001c01c030203100401c200304070724000c074841809410445014800310001d03010710f00d90b806143d402c503400600702c20402404900541c001d10603504101e4a1454583c0c3e00d400449010304a0b120090060b07011a00900034004690401900048203003041000450615014012104040c41c0030444940b030b03040400850400784640d9026001c2d920000c0c41e0103045401107281d41c884c084500c1c0c0c0d10080001c91545 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 338566708 1250 338565458 338565463
    0x501080c030a05041e0b06101110020a02070302130603061a09070806011107121713172e0f110901081803040b07141612020d08030109020a02060108010207021c0302 72
    0x50001d20100300c0717601c01001742840203000104403a03480c0203128484140040c80d000f454960039042034840189a640c000c1c410b040c02a4000d0b116020540c0b18400001c8010b0340e44030b90959041196100c006016840c50400d101614041404220300360081c0c42800c00e141c56161035107a0140c110b0130f2101c2c0c0741e1075000048510b00c1304503c40c08828007407400c0111700521700002402580c2d000c3c030101c100c0e184003034056500700d106a2041800c1304810a104001e8403030840042018495128107075a9a06020800c0c10030042c404500d503519554210050411440d0728813840e60307102e00b010010000707055803011191052107610a400e05001010300081c44441c0c1c000c8101e00c41c1040001a01c0d00c0782d9403003207408415080b518048598011070110045103600025022520211102d4a00e01d994903046c02e07000e094a084006a80028006030294080b42580e0001d60003082400030050342c4440d140c40c001d0400740180c0241884c1d03401000070f0405a40d408600840a2101110081030022245010781c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 338567958 1250 338566708 338566733
    0xf0e0109170f010f06050a0314070e0f1e100513020c0109080703020706111504111509010905010302030f04230604060504020405060d0b0a0e0307061d070501080c030a0504 75
    0x412621491001004500340802d0030450140c2e0b0703800034410180e5804003882903070b01c1070242c80d0b040042c98030204042485030f50401c40c103000c2e00040d2000d8580b241d07503010700c541c02118010440d0141740705024542d40641400000240350710780c02203190070102c80144990301c5600c140c601c10409040711004421703841e4102d422000e200c9008201d038061030f282c034400366007022006401501862500244490143c0c50030203804404401416040c0c0807054650f010890250041e1181e01600201c152241c41d8804290910004410000d840e43c001c02c000400c51011600100d040500500a1001107551640d80f5504241c1c42901e4004506000b801c070003d5580402074130101c1d200e0340080c04140401d40d80864000c60007600d0621981c5d07601c000340400c220003104003c0440e2400000640c0e201825448250000083c4c801d0b02e10b050b9650f00e0f208243c0e014585026440b0b0b558603410007404004000201c0140400e01703201002d0b19040001c00c1d901d0100922400f08252a08001410000701e4103030784 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 338569208 1250 338567958 338567969
    0x9230415030c15120504080904092102191112060109060e06060f31030804080f0a0c0306050606071406040c0e090c0f0a0306050108150703020a0f0e0109 67
    0x200800416450342440c058a103201c19144186459000319520700d614520400d4150140c8a200e88070783d04081103002010014401d4030840c2e0280302103041a0b840d40900030901e030041c030b4000000501a01c12040c1c04040c0c0380454103640c06482852112110429050310242d0480d0034004214881800309006840b14420401d660040d8400171641118070f500c032409035003030300040e58015560042400300902c203001d080796121200740b00420b0025019001c00110355144920804461040000d00094100d40d03002103440240100c5e06100c8035800f000100e05c059030003002001d801403103884600104000e408080c0085489000141a0740c44640860704042e912100c41c61700c8020240d00710b5260901900d088074a82805400000c281d01c1400402e802852281c01405d20758000c0410001d41d00c04041c0d03036030341088480000102085c00c074800d06c1d000304030040141c1a01d100004c0305003400c0b04001c104800f0f052060015094092b842002c001007842a030507d0380e818802900103039444101513120 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 338570458 1250 338569208 338569211
    0x6070903080c101e060b0301050901140f060d020702010e0306011203140c100608060603060606030c0d0b0303120103030801060206090607030e0a0c03062715050c0c010c030525092304 80
    0x844004e029a8040c20780320780404008000ca552140302585841c40b0a1007640d0380b1801c4580148a2808002e800003084a401090000000d0714400800e010b500300d2281000120307404a600c2e07066507000508001200740c2107001d08815070414a000c2c0301c1c0c09021001400700300303200c10b40d110402503003821180b42c000300d0030131944008049116a40a40389500a904560041c1008204d49040c001071541c054100104468211303600c606551455410442540182036240d0301c0642003030f1028402050285481054440c00b903040d030601516084040e4403100455001d24100104d114020a100c0d4001040c1c0c90041182c204100d1201c0c80e011a84001a1510154103000001c0241076800075840600c00800382c0f1250104904100c80140b800328064840703c6210011100444540e1019501003518107202d4107107451001e0300ca003110fa801c40ea40d80401c1e501c0d0b003408642208044a5100d55001d00c00b441d02e200301182d401440716100b80714010400b19284070401803008001e5040c541030401420 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 338571708 1250 338570458 338570471
    0x60703110a0b100302181603020a1205010b040e01060c030f0c060e032d0f1c1d030406021c2f0d18060908030304110103020403060e010203070e0306070903080c10 71
    0x1014000c41c5094070049101b42e140d100292401100b00b082248221020045003500501800b416001795106c10000820001e140d4032901e800c003060300c22540605902c40d50f0584560a19052012030745040e00407000b0b10a03c80c0c0c0c0d5400082d40b04a030314010342071500e0031045102c150310b0402c01800300780010900d83d01012a1805c5045000360315085a82e100b0b22200f1001428658665054410f01d010f08107a4803081000c01c10020090428202c00451030a0028420244180c00b01c916000c40010302e40343e800005042046c141e0402404044408011919440e103150700405002440400c0c001d00082c1c0d40070404803000d4041e0413503409d00c040c441065070505040c407940105000b0101401e0101e5800d0f0080c00300d001482a03400c14181d6071080c00842c0307180c880741c0300e0b56105a20300803403904240e000c11000c00010240c1c0510396174803656400141c1c0341d081c50000604a0052820494080e5201500300103074268060340c00c9013126007042c420f030341d0742d00b0144d080c5040203038039a04104010700f00709 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 338572958 1250 338571708 338571721
    0xd020c0f070f06020706110f01181103121b0111130302090f040b24030d03090201080a140a0f0b040504030c030809010903090501052206030b0f040b060703110a0b 71
    0x5510900c80d0005030903125040d4581c1e0440a00d1071141c040c0100580c004903042c03020314041d00141507250400c0003220680c0010b03008181c02d4031548504c52101c04040c00b00c00d0304000390140811200b08046010748150307a2002076011440c010301400180605440d5454001d4070320a501036000d00fa100441150741e04084400d4085480b0180700032401010008000340b081e80b00f00b043c3ca406640d00180d1481c0302d4a40d03d0500021840798101d510000496404100c156541042640c10803551901c0200d0120203e000262107540000c08074071a441c18071010f03401d40008440d0300d65125550340c10008101c0c590b00151002010380c100d0f030700c2d04a490071040c4814960414906000e82c1c4c031a545401d4290380d0032035202d00362000010003c01141801d0310a00c255802640039004039000d4101406005004200209505880703600c60b1001c03a59030041d803001428003103291380d820741c000c4c1d8092004052440224030181700c0e840006d8100300c206154031000d003d041c400e4000040d00000e41d0050303030a000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 338574208 1250 338572958 338572963
    0xf02090f01050a050d021c03090e1312020a050a02010f050d090c30030305060d0f1202061006050d050a02070f031e030c0f08060310060902031605090303040b07080d020c 74
    0x2c2c001e261103a403484000180c545031501a10001355405001400c04141c000c4465541214101045083c4255404042881080c0c1c0c060144152036005030388003007100c241080003890300305010b20000c5401800200d000708800140104501d40d0a05c0c0044040182c400b0450305800b840550502d513500701034002c8140320b0784006082c241c4036444240003003c1000040e8680005415060000079200d140541011074040e030302070ba600100183c21105500c450341e4800d01080d100c0c010480c1d164042c00c1d14006400d6041281304d0f44103410103041602127007084400360040c082d118020480c03940318000603002c03000302e13010345420702e44c444099030317444000d0f00c3e02410604424000c40fa86008540b00f000140e41319000da0400042c0c0c2d070b2a4000000002c00e000c43d04040001c023021703010b20480b050440103104031300c581401401d02100060312400d048211800c9880c2d1581c20800b0007c00b4400191141d4001c01207500715011b20800030346d54071403032a00c03074001c0c0a074007004142903201007641d14070072002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 338575458 1250 338574208 338574211
    0x90a0608011113060207030b011a09090414070b032e09111c15062003041403060c0f030c03130c0f05040f06060206070309030306030512070201021506060a05070f02090f 74
    0x1d03400b454101c1511608100e0746e0384682d10018041e0b41080d0010804c0d0f802c10050919020511a28149840300304000701d0308c84e500944048802000c804c0361840d00000a00c48107010b0107d40c0001403440c104544000040e004c14a0701d0028001c41c9544070300c02208250ba40f8005242201d010300401030441206451600b025040b110030341c1d4032036980c62400800388035184421490000340c1000b54100744049512021484e07008516a5001940c105040000c00140004241d159000b29071406c0c04c00501d1304008000e025540503941c140140c01e03011100c401a82d510141c4100019100d6440c412202c030316050511000d0610f505912010603084086680b08055800541d010310011824000100071143c3c58070440005070401d1011606461081d0020000c840c00392401107442504c0c3c0e11554204030307800c044210061030010701201156014040c1b064140c41e6040300e1a09445c2c81800302d0f00c184141030480c003c0001c006201e03000c100c0614403038400c03582c018203452a1441c00100381544440e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 338576708 1250 338575458 338575477
    0x5060a0e490f0e1f0203120108060711060f0412200606270a05060105070c0b03040303050f01030309050607020a090c0306050f03032703120309100f06080606090a06080111 75
    0x4040c414101c0043c010249580d5120000d84098182040000a4502d2102400135441140030030881200c4004070354040303602924000000c0e198600b4441030281c4003140000c0241c0305034200c5803c100e001000350f200c2580c020f400c0030004500d50400340d0215259100b00c6800b99074240164170001d0b902c44001800b502c5860152800c01e10111411000c901c40e0b418800b06580d20301100340010050000c035000301c0d0b00008107040450070120581c1c0c94411004403500096030f001c40100030041496410300841c1c1d0803c801d4410507125504585004110300300c20f00586000e84030014042085403101e010b050000c280e0007008210004020f00014041c110a00c0b46078400c00c0e0051880c0f900e07240c003208841e0b04a800710f00b0304000d0000c51650030010b01e1041d4445500d4010a040103c600080388020361096007001c02401c20807440180b071004483c80690030420300c1e0710786201030048242c0001c1040c0c001c1d4040344e900103d0380d0703840c108102400180d04203004075400e04211140c02042000541545c20 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 338577958 1250 338576708 338576717
    0x1020607140703030b0604120f02040501090b03070311030a02091e01060914041503050114040c090b060702091015051b0309061c020f1605060a0e49 65
    0x88451000300ea10301c8103000c1c5400680820010980020700a07403042064001c0500154146540ca04070300980c80e2500318151900ca03612012401146090b01c28a8050008a40100a449081004031b0303a186c5050000078403001c010406040d240e42d0401c500c504490b8024941c1d1043e1170301e1a100c10034107031080d183c0c07401c1f03c61050001c80c600d03004e8500d010031789880b04c0c1c40d8424442c0070000c0101500d20a1480c1204064408c40880440c8080c010010601e80003c0caa61090915103046134500744141d010314000c43c906041c0c0401c81d640c0f00211805242c0482e18444280c443d6807041000101c1035000c03410070144c031074007091081d40001c068151000030002c121070001d01903640722b45a12402c1c44030ba030701c00c03006c02c04501681164801c1010b980c01c040001400c00c50480503189055000c80b0b0102008480e0b58040c0042203020090305070312001c281d40a10540c00e201e65019030b525031040956040500304072503003186401000c511581500e00044003c40d201d001011381e14603043e11156a00000d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 338579208 1250 338577958 338577961
    0x4030c050102103b0102030906060108010f1505030402042309011401140925090f170604020906030a0f0803061804051207080d0c090906080c060301051e0603040809010206 75
    0x108181e10800c4040404180d031390034030b80791000c240c21803507100d200014403451450101c0c00710850244059403180440c40010001030030a0700000d44020b4050f404040c4403108180140680e81c541c0030780c40b0385c552581c244a5144c1e115440010060700584464503200040601038984810030048030034000e4060600801030072034505609205840e09004440c48455404040a074505200d10300d5584501541500b1034207400d030b0801c032100494500c80c100c0000d12004400c0c0643c42d0041c0003000104501c542d00c00b0320003415400782c3c0d26440002d1001e441901c0c0e182c0025480d0b1000d00c42e5500c255070009035240e4040e21b80c03030714000c0350b003050f20080d00810761012245c1c80c42c4145d02a480c0a9600113004010342c440321020300129511610003154208001e1006848030300d800e0190001100f01902e46a555505101c080b07012034443d6807200041d540840c0b581c07400c03501d5050849041d61000d880100030926800000000c10002c010038542140c0e0010400041c8420030016040b001426425a81103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 338580458 1250 338579208 338579233
    0x5060613020717070602120a0506030d030507020d0807020c04020703030f0b060705070e0c0904050103240203130318050a180c021515030c190303030b030604050a03180b04030c050102 80
    0x100d000b900c8000b05418042000500c1d61490040a0b050092054102600d0300074650440340e4050707016507441050351b440c0e00900c031941c5002e0090858040300d41c030b0104090b142404000b583c8850382d40040c03041c89032a001081201d4070a200c02d110582c00608107541d0340d10980b4000f001400c00560714452140342c100c1da00840d18045080710945138004004040441c02d080d113800e0104c401134580a40071000300400138170398955000d89802540542050581c1d500c81030300c0100d01641c601c00740c0c2780d168410000c0155010020701103200d07098151414031100c00c415915400028030700d81016a00c00030704140081e40c2d4030301c0040044410000101840320290301c4409a9540e01a014114040c1000c0c00c0050240b04141c49103d166800050454000682c0715011803140c408419407036040e4516201c091003416010b00803000b194400b81c0003002603103851703290262a12000800202001107200714000c018070520486009440c0080703445594903070341e02d0201c074800c500d482054098046d42102910 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 338581708 1250 338580458 338580461
    0x60f0f09150a080f0309012001150509070c12050f1308031c0204030b0402060705030d1b1803080d05190c02010204050a05060918060102100203100509010e070507030513050d05060613 80
    0x211310241100842c1803122a400550f040c0203180072121640e2a4486461340c0c04509016501102c0340b8003000740e011908020500c817800303c00030208414001140c088400207400000014002c03c0b15180c81a01c840b0b19aa03014044d00c22000480300c01e00b155080864016004802080701c010403140c802c0b035501403038140c041079026502c00540030171001c0c1d0024015081c581d000b80f0b6200d2041c0e0a8a1901c99030403028022034190302c81401504812076144880070303400c111020a24882c0c1462566004d14680c1c44602c9481002c42f881000b07038486006ca800001e82c22000c0040f221500010301c14141880c0c270080c002d40080c86024030440503840d00150070300700141222481c0002610303044084081c4070010040b00b8028042604610618011f4114804640301450013040d0464a80d0801c0e480c01007042400101a005065248404414408000c0d000b4007164a2246c2c182400b0740c60f54980d005107820f0f030140c1c2e8043d907006a5000c0c03131320042200128403a88145011a001c01a24400740340d000c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 338582958 1250 338581708 338581723
    0x9030305030601080a090f110111010908040504020d020c07081c0905010e010c080c010227010905031009050a1415010e060120010b060403050303040c050612060f0f09150a08 76
    0x6010880400100b940c55101e10311056003d0031003240400d005807aa03071840a980c070040e00503250002406031b00307481503a001d0070860302c113900b8034001d02c03007100b42d03885000440c8120300c03404e403003075500061810907000c0c6501960941d034150303029115501d0792443c66a40340c22042214146d070000300e0369003981c0701e400342400d4801c0d524107942d0500032150403c01560501461103043e905004184420448005c00740014802c203190400c0800a1200da11042c8083c003084040c51414000450001c1c001e6031030009180004084040d0f0103c4d80071302d582021418003016a0018214040c2007030305208490002501003035482141d250641582e85e10b40101c49040c809690b20740c0044c1030052451800c01d030340360150b441d40d18441c4c00020300007100f00000f1251b910907801101d0a41003c400c120500c0340480701c00c0024082521810701e01040b0b81c4030103407099001070016204500c0c100c41c42c1016196800c00002010014026080c1400c10024803055000400001c40c441c0f1070011010412080116400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 338584208 1250 338582958 338582963
    0xf04060807020105070f08090a080c012f03061302090603010e06120a03120c0921031d011b030c0b0403020106140307031a1305011a040b01030e0606040b0d06090c06020d0903 76
    0xc1c003450046079041f144800c024200301818895a9440008268103800400603894400000180d011880310301d03022504030746001184e504503d0300c4507900400c450040307170303070103203086460a560386000705040000303000310742d031550300884088004130320006140c402c2402090f04031140d450b81c680344010584c0e50080001e0050005a09450b0240220b0890b0010a07a000c040e0421003a91764071a6201d0303007403d40f900c21854802a4451164080c540c00050340340c091002c0001c1c03000a40d000c0b030000307844550360b4890300041c40400512002418869855041345c61b9102000c400c5604081c2070003406814280183e0380c3c1003404282c44085441c00041c4001100e80c800e408960b044048981000100001070046c0d4150510b003c030180001d0307080c410440c5c2c401d0231284aa42c07a421010610084030f00c040e4409042c5860144d00504050300080d0b1035134440001c5402040d00d40010011a401000801e0300812042c00d1000c448104150000d245040d6444c5500303d076030680e410340046403c01c3c540e1201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 338585458 1250 338584208 338584217
    0x4050115020c06091201090803070915080121052506020c0f040207060e0709090611040302060d0b04021e0715090305070b10030f0305090a080c031f060801020f0406080702010507 78
    0x40095802c0480240404c03a00043c19480881962000d0a081d605409021071301900300204100c0e500d90006a5100980001e0a1a83c009032203000041c204c188107010724010807512860141103100840281031200d40e01c8419074020a04111101e0f06540d110b0300711803048845c0e10f801003a11480003885a001c3c020040486060081074030520000b940411000e46040362505c0e04130454600400c00300e001010036100c00603980459040c0181100c013040c44010403110b003080200f0140e0344050540b07801107017100b03000a000d0b551000140007880b07841c242ca51200c084031800c0d030030f107170704940604849805400d054144418100e000c100711030343c1200040110300705000a4020502451100e0752010a03042e2003280c50f6241c3d2240ca10f110000c40f0106c0000b00700280d042018100000c8980040075a400108851410480029120003c081c807041e40c0e940e01c0041c44520200d550019001450650021980e5040900503080d00b98041e001308408919030001042005d8814070400c1e02c42d801035500d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 338586708 1250 338585458 338585473
    0x903010e01050c07020d0213110d0b0306060a0e2503060f140108040803090a06050f150901030b0138090315100902180a060807110304030b0106081801020403060504020405011502 78
    0xc0108044000e20142c2e002050041c94230b00000c000d01c20142c0c90194070010700d4036045184014402c0c0c40c604c0c0351050080d08107205001041d11008407000a5070101c422403409a0b17141344800c803074004c0740c0500d0316200020b0300c00c1d1317404140c040d84190241c680916445e00610b4840200ca074501010300301e41e500280d510340014020440e680301464000302c1110603254888400d480d26010b07150180d0383c402054043ea014481c04080b24004480c0d1103000340ca0880c49585191541e2448403014441c200c4c04600984011806102e150a48030842514400030801200c0b0383c20341c0d07a02c0e5000101a01d010b0301c2030103c0c10300c61104d500d0300140304120b8040b00740780481c10022040003941001403180d1b0f464560507a041c155a44d9984840d01610751135481002a00d00840e00404007450b203001030500e500b0400092001c40c049410b50703070545840f41014034444d00c0345484d01c24942618000b803491940f01160200c100300842d000580501d0003181d0a000d2641c0741c0d40c400d90901e14624010025902101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 338587958 1250 338586708 338586713
    0x41a0a080609120a0207090218040f18080307020c030321092802042c07050105090609040515120105010f050a051e0f0d05060613050f070c260903010e01050c07 70
    0x3042c4c54203980c03064840c51542d0b01024020703a0001e2011400b03035500e04101130064101b622076070312110800306061040900318030704010241c2c00c4800c007400c1c5020000c00291118000c012020400401504070f81d9030714004001900c0241907503a9070540f00c0d0380c4002181c0b60100c00a602002042d042007a45e03034007911a944000d21701480501243c01c030380c07a4180c0f665003484480401004100b18001c0d05840c01d100078080303050440542045040c804107012081d195282e45080d20828401550005401e03161090030502142135204e8041c0c1c0810b05442030104010190070841c100d072100240c518009441d402004581184da0140c29080750310171854041c0104040d031001c41251018155000c020940d80228240c2034240e80141d940c2d500000c04d010080c10b1610460b0401642c05408200da4280081c61022403c070207000d1000304880450800c081c03100031074100406500c0300030341c103c1110845072038900f15002500054480d5290009036540741d076060007598894003280c90400d00d450100da = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 338589208 1250 338587958 338587993
    0x903060f0f0c070c0510020d08060a06170c0405030a03200c100318050102040f1a030402060a082e03111e010c080708040b13171911041a0a080609 64
    0xb90107813045114844009540e0300e4808030004c1e1a04564088c00d2210840d4a002d040180094230a60191080d00d004000895102d0001c1c09161003105030301210380c580760b07a80420707401650041d40e89406505900c400309a0071070781140d05071002032142e0038041300e000314068603180c032900f0070780d04040c4400c1040741c5d091182c7c1c00194040c2c407030342400c4800409504c50a0881c1c00c150440e07140c0d031b0203400040c03202d115080e403600f4844020342036940c41c502d40340d400300e4100d000f2021490244440c21001c0381d44680e4014010400c42da0307400e12a00b01c91268800c4d0b100ea980b140c4419110310202480481d941e0809034904510015010800b070000c01c1907000444a250000e4000d0310325010500200b000101110000c000800c80ca03025103848540e4400011034128465118240c1e807454003041000c2000c02090148081c1400c0900c44220b032128103140f80c424581c002450350051030851141d07810605020544540401a00c81b11140c0c0d86522071140d403424140c81c2652950b0092801d002580340d42e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 338590458 1250 338589208 338589217
    0x82503110426010902210a1b0f080106030c0905040c09050a050a1413110a050a0f170d0c0201030b01030f0e0601081612021c0b010f18022110080f030903060f0f0c 71
    0x40002c4461500413502c8180c0c6010782c100303070326900708e4109400304132000704070303a40c10040c1403150000c004291450b40d440303284016074404d60244680390300c0010280040d032036242c8010700351020140030600e001a0000002c01007140c28452061038581d8007884070400b9503640b4864140710329400314100c0d550301c8802c12000c07180d680b141d2024081401040366150040a000246044100c1c10400d03030030708403600b0b01040d5210b402c2d001503005603204811181c0c0286445502602800d001408254001c0100d015260704c1c00c40301003140c02c0151180794004001400d5048440080a50f4280d0200009d10b00a4504911070340d400c804203090602c0140c680212080707400750740710009407100c924070360300e80101007402d0740045001306c02c0c45010010020001d41c80c800030401c1c00d200f14600008003d1100c080c1142c50000000140350400140d443c0002ea1000005081c8140c01c0320045001c107a10300d660380e0f00000c1460b01a02504000c81c9181180140b4a805070746c0c2c0c145680c0d040d981d0340d40c0c1146d0b507800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 338591708 1250 338590458 338590519
    0x3011701180f0222020a0c120c02030d03050c0702040204030f051608100b03150106020f2e0f090618061a01020a02090403090f06050901020607082503110426010902 72
    0x10041804c4034201c1d010310007842d00004548400c1c50585c49824000d090f5048650f81005004004282500598000c6a03680342c943c2e80e818005541e4440c0c808401d050b0143d140000c2d0031a10000703021081c41103203401d0358440761286048403080b144250300f84c00401007601c280b55096000940e034441002944d084101c050301d001d401c0703449490b00c19090482c0c003e0203034814405a004044c004140d40070902030000c41c1c1c2c1002d8040b104d0240c2c0b0390305004c20800c403c0c8010800d640c0d240c000001420103904401e0180b50030042c1404046080d00c40c052804002c2c150898030355180c809241869442200c08415140050300a80b88260481e001c2c80f40750340004100310300300500c02001048000c00a000400602041d41d20151114030810001e03107001c02c05008407041c0b100385030402500c141601038081450803030444901034400d519406a000c2c252040c03a0401c4d2490120b004203020709030322a01e4207440e8000012036104100307140300500f2038980e120081e400c01d190b000b0100b2034006890b0600c50031507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 338592958 1250 338591708 338591749
    0xf07020414010306140705090603070e0d061a010e01110604060c05070b040302061b0304050d050a0203041d0403030b0d05030304061509090b06011e2f0303011701180f02 74
    0x4021000715922040240c000315243c1d40d80d40c0c07509002002c181c5080c2d03401400d5081c090f29190701480095054000107241100b0031600b1404500582c071107100d030100d0b4544c051005c0c401005071048000c1c0c00c0e000c4040003070000e90042c40b940c0d040e602c0394500fa0303c1c1c4603c0202522454031140c56030005442100818014882c00304040b400042c1008070040c4114001d6005d04214200070119031200381e03200da060040b8a400340244800b0440200b91000741c240305080c42c6030f642d5120350042c0c2c250302540d44110645183c0030b801c0c04000c60b00c6100188114407960b000c011045a0004105003148602405492648180002030003d01541d03c42c80b80104290254266141c0d0f59070b040b07007601c7c6034920803182031320144184030b00395820044400002141c508049142d4460000041c1449070768400040600010a010444488030000c51083c4000d00303000d4aa403076840d0180b000c0300101c03405000003150f01e0408a41e10340c001b44445031804e01d0303001d501c45d13451121940070010316038040703a43c3c0007490 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 338594208 1250 338592958 338592971
    0xd17090f06040603020702030705151602010e060703020a11040504120309080417010c030f110702040902041410060f0518040c0207151d100e06071a01090504050c0409080f070204 78
    0x80d034032540500b00401407541c01698802c42c070702c103140c24406554040c500414841441c0017502842100b40c0e03801e52400b0703c861080070140e00040ba00700c911030301d0058001c2d40000d410818141e0114007401568016000c10008442500a000480350104c0c5d001c0c00c080002c100c607420003480b03a004284041e0180e6071071784c200313078440702c00321036000b0b20900c01c010b01e0303559072031580c089900760180c0b5507801f520f00007c011004c95041c00d00700314810001c00a1040756a84005030466481c4da0181c003541ca002000040e0601d41110344a28551881c0240f0740854000c0c0101101380e40b058003140d059050068480c0007812008c024000a048007080820540c045c240c80414580c04010403000b1441d034070355803400504550f40e030b027484592200d54454020b960901000c8640303900405101110b081c00d0b44c032995a4409400c1c80070a00c040e4442c0d1300c046c00c0c80ca10002031880d1507908900e01880c060815103c2c85000501044211400080c00a01928080c041c0d1072200a580d00613204150000d000462304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 338595458 1250 338594208 338594239
    0x1703090907110613020603070c0c080a06050106021506030d08070c050607050406090f0521070305060411010f3002040515040f05190b0702011115150d1709 68
    0x2003021516480016103088582c0c075400307070400031903030800041c49640000c0401e903000729441d44401003020043c001c10500744070400c80300c8844040200264010350f04114600d04c1e00300f010301400c2c070a5200520070403191003105150301580364051040200206404d050054007650180b1004100c0c80070b004000c0a904007040040c046148202419a5291369a50410a01a000f1110303070304080e0400018034010300880d10303030b06a0440c0c0c50940300b80d021003001c0c1c000d0855150115980008040340a000c0900c020000c0c05020040303082d0098940c0000c00c0a001000c907020900c1300c1944050000c20703103920002e0082075841c00310b40c0246a0002d450142c464012a00c05541c0005440740d615000030108405d11074001a40c010705021245152600c854110840c0100074900030403c1c00c0301c00290792000c685c095810a4509001c910550300c02d402038500c042200e600c122046510940786100c280c00034a041c9405408131548040100382055404054400c1c40d0099054240c1100c40b400300d0200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 338596708 1250 338595458 338595469
    0x81e040212030a0801050a0603090510051314012c0303180c040e03030402040c0e1f09050a0314010f02041a1308030f1e040b0702040e0c0613030311060402010207170309 74
    0x43c4610030b45039a102c552420040c0320b520040c07940411308040c074002c614000144040342259500d142c4642c007052640741c0074440c4100b43c644100050100c5a800c110480200040d001084800300b0143c0172020902c50380901c0144081040c01c07404280c20400000d130207140040c1440d40500441006c0f50540c16000740443c4c12900c0003100b40362180e10102c03c0000318546030151003c8814585400c00345403048401040341d10324060050307402c0a05a1030340b40c3e20684941c03445802408001c0445021030780e682000c0300e100c842d0016800036942401c61001c5048031900844040ba00e289850440c03200005042282c540c11445100300c5804a00200085603181000a055400549083c00b503440d4400c480500f0204a0300405407444441800200318851861060790f0207035805850216002d034071403111501300312544003016400000403800c0d400110b034001d0044c065074840d4030b40c0c44030010060074040d51581300700c034000e005a00c402d41c00e000410160003014000501c0d0400c803818807451000043c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 338597958 1250 338596708 338596717
    0x1121218080d120e0c0306042a0b1b0706141c090b070f1d040c02033c0f0706020705030f0a0f200a03030513080415020d081e04021203 59
    0x40c00f105106003004414815803a201210000138400418110040b9440d1318000f0b00203000400340c5680890310103074401d01c5c600440412041210b0031510742603802c899401c840520700c52612a01740c011410310001444505540054980508108016840340e1713156202084500e4010062541048100001d00030756a51034890042c6618501e480003008107080d031904940c208000d20506060788074015203c100101c5082600c011650b20720a00d4160719610400500c202d06e9859225030304840300384031000d13030502c602c0b4040c5a0080104074a00010b640202d08000c0108401000001d000038059030003403100f903100304140d81c20400d0b441c0c030a41d0260080020071020540d9400c0302c0528650000c0c14104c180c0d01035000b0026100005c024903502e01d6400001401e060b03075039000c035541d104400208003507079a0101c4900d58842d101c1c00342d00101800c01c0e02e1200035108a00c01008414007603140a4858035441b410ba001101c02c0780030018000c440684242e0708081c942d10340541c1c4603010310052 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 338599208 1250 338597958 338597983
    0x215070905042c0303100315060e101503020f09040902180f01051809031611060406110c311e0902010f021603030c0507080a14060112121808 62
    0x10080d83d0240e4012441c01e2511070100406030030070010050070320192688881600d4200c460000306020818801c0f006060982065030084190010400340d003809803944420b0300ca010002083c0c245a091096082c0d0280b00c0c03600c8000141400a04940c0c10a030348a010307030320300040880040d4810038000301c408040550f4229070029200c0018402c500304806404601c851440407415189042c0500039101c2c024030b0203407140d11748201e46110a0124200402c07610b281c00030455a0786964138070014100d141100b8174680319002e03280028240d480d01c04012420304055101107050140364001c2d090040c483d41c00e0003a601952041c0b540c443d50703c004c030741c20713a004900c0200050481550001410a0030203004503030855014a14807007003154409081d5048035851305141000e0301a80c03030714034100400342d0048000c51043c0f58080e001e0020301d01501000c0c142407030688000703980300d05e02e0603400ea0000c48040c01e06440440c840c04890f1240016081b506030020f100114243c482042a083c0b01a0b58580b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 338600458 1250 338599208 338599241
    0x1215060203032208040506160b0c0904050112023709020418050103170903010e06070c02100f0c080a0519020f011113060327030c03080c0a021507090504 67
    0x300040382d42d1400309142100d621541c07440d0076a441c2c2c0d50b210211702c07a07805410301848020603c0040126007a161151842c6d20801150a602d00580409001c1c1c0007100c50b1845a8280b00000590800c80d03200c0240d50ba40107070100480300c403005c01c010968088881a801c1a0103100070040d150382801d0b0007000508403006025030b40b946000c0c05101541c18903403603407201510346001000060a82c1c06041c8422407282920744d00c4154060010f4010314813942030010b10b0040ca4104001c4590024020100c0761080740c004240d000b00c154100c030044000564000841d118006c8400407800c4034019000d42910b503d401454803814000070190400d18542d4600541d00100b090f1040c85021300518003001c011550140c1085c104200800030341a0034407901003410342e14030740c0d40d1800d031fa003001c1100c0b401c40c415a1070b190035845140c0204101e81807802680001c940a010444c8841c0c118103d8948819603801810031840c0408040d051a0010b400c060602c41e860310b002072581c403a80201ca6075440e201c01c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 338601708 1250 338600458 338600461
    0x7170a0305090607091413060e010e1311010518130f0501211103010213142b140309040e01020909090736020f0702041a030a03121506020303 62
    0x140580c0c402400c890841d0304103c0400900580c040300700000ca83d4403c8a40340410101d8001c01c0b00c204001105c0c86420342081c0c0086480502d07581118101c0b00841c102d84603a61310945a01e07403000707464100070802142035a03d40c40c1584136002518281151924206503c3e600e5000a1a050256100c4e01065a1100340c51240c0810b00d200d461300401000013074035070307203040307001e1040c5a84c8500c03030010480440d103502c254003520250b05a40326660201c41e01030390142c9403401e200e940083e0759400f0744110f4482c0c1c455000c40d65541300100b1320036044451500340386650740d103503d036841c0c1c00c40d0074001510003844482a583c1d00d5002703811401030182d000590b40c0c1226030500c03240c040000c0858540e0742c05840c00f0400b403540c15800e1004100195080c150980319901c1c0c080803980511404c048407400800c000011114442c01880d8032482203800b00440c07140c4000c0015480c00c0c0100c1254190407055500002c24001d6528000c2e01e0900540003500c1e00311130400c4012a080d5030003220040c8d20100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 338602958 1250 338601708 338601727
    0x20906040e150d120806100e01030e031b0312070302040e06040b03010902031f0b0306010503071502030403050a060e0c0904020603070e0118060306050307090204081b0111060405061504090f0f03050717 88
    0x281c590010700c01d87d601c150007041000f0180c0a9551a000d00f03042685c1d5072080c0941205c01d00c04e961030f41e850b42064514105008000c0d03a035903000702c00d50591150000c404113015900034400c840484c0c0580040c0ca41a40da81e80c1000020040f03061480d405540724000140141d40a1000242c40d02c90b15071000385900e0f000d001e4804454562000601a5011070018099035900081039001c807074105030380d1403405281e25012801c42c00f441d031004120b442030303601000030042c1e180c102035090841c0b03000300d942c1c0700d100104010820005440c080c0d000781042010820361072045032002040c4c80181841c0c06810000e05150250ba0760581c007200000e5510326041c8414541484284001c00100d00158180b03030070300b0403c5458918804e4100c406110104500100d64042c10100003103461003401e4400a03e800d007880c507140c0504950a0f002061f00000c04020362600344102c0300f64a8200010205403026603070342010303400c01c01506605220080c0300100c00246005440e410200300000d2890720b444045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 338604208 1250 338602958 338602967
    0x901181e020c0d0207030203250b190e01030903090611070f030501020405090601050c03091e0303070c0510090f050f040603050609030c0d08150906150c0c1003020906040e150d12 78
    0x1140e42e001190000c00d0201b0269030001860203032401c00d500041003428004804e4950581d0035400304810b000046a58003140702118880c16034800b0340e482d0346030312209a4004404840101d00000e004c50040c0100340004c5104d4503001000b607840302c01b290409501e40240d058480000da000315460b039000a0140804d081610b00b507904080e081c20882c1c207107058010881c1d1a030241a103610300490700800400c00c040480ca844000c034071800f8003603a54540d01410b0140281c00507026690180600900078041c2500ca45c0c0b40c00d0450f08007214240441c0c0c00c0408102000b000720720050780c416150755000c030201d0014009540140a10700056940b40d20300c00c110340c02c26006040000601450004000034180c14074078418004030111544815a03031190001508141c141000c0003049030007240d130150503500000c8500704038008131160100d10400c520200d05904c51035251980040082c041044010041040c3e03c1c1c003d080603442c0907060780484d002c6820410b01c82c2c2c043d106581e8142280c548503821 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 338605458 1250 338604208 338604223
    0x121527060605070305030a050a1e0c02010509070f14040e07060809070b090a030311010f02130612050103120c030509030d0914090903220519080d05090901181e020c 72
    0x10342030882c106030b0f031900d01070030078080101181c2c4041e840300005030a5041c990300a400881d45000980e0181d2520490715009200804818006d980781401103424550300045010840700084809954141002071049a1070010400a0340050305c415400704030901c18040c184c090007180d030b200c04151808610760341c9010100e51001c8041c081c108100312180d00e6000605080e43d0705400c240400410259035a0300401c031040d036103803580d407010070340040074541d51b00800115940313503480340890b040e260740072000c03164284001019000c44408a003190344c01203464480043c040d0410f24140b01840300802c1c00d10301071030b91b4040041d001d10024030000c80c5419116030307054401d0761191168030300301c05030710f6880c41202100c00d0b0300c1c0d01e01e000c1c441c00c10074140c1820001d44005030003c80c2c6005030130441d140c040d4150240c60700c603018a02c05028514070400a6540305c1c1d1004227101e6081c1d19100914002030081b00d410030302ca40c0c0b64002001c0302060b00403020482c0d41c00e0040141c0c0c0f40068160207050000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 338606708 1250 338605458 338605469
    0x1320070b2202031c020c12100b01020303090d030b1206191a010c170c07290304031e050d0e0703020319020a03060f1b0c03090e01050112152706 63
    0x24180706090141e10005944115030080740b56460089000c200103a24002e050982c0c290b000c04a5110024a60f0005c19013070210b11152100f84001040c02005986a000440740448594000d05040303158500c44d420a800c0d4041c060301c81c0d00720702c2408014504290040b0b400c0f103040740301120540220400352290b0300d4a000c051140303070320001e043c5000170140407403007070301400c070400c0044010105040c0340304503654800075034225000c49681d450140d000e0000c0144440a1011051a005604481c401124405c0e50b02d030b982c181189100010070f80d14000104805401c002e001e000310322055401d8070a100781c51070814002d1500920b10b06c10903142000320488201100481074040c401030f00da00f62448142c80d8045408a00305030000c41034001806d0b1601d0215000c01c10030384541000703410202a9110341e020b03554209030552624440400c072b0b103087c0300355400224561050176000041d0350251031501c03401c009054189503102403104a000c426440d0070034010100401021605891003020000c14 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 338607958 1250 338606708 338606761
    0xd17010305061b090d06060305190c090e1005010305061501090b0f07050307020303030f0a0b090411010c02030c0405010b0a090e061c140102070f061a1320070b 70
    0x6066a903a60b40b20300300500341c040b10016006100704001e41602c140d512022000e0503078000701c0400e04040018201074801a1400d010300d400704044098418000356401d13402000d5110581c2c54014004010f190b2009046407a000720004085402c904e40605402940540000c00c01ca080110012046a03400b500d00b0b814010105010048801d4103810b0340ea0209a40b841207440e00c0f15810507608512072100020f6260000000f00403a403841090542c0c0200e810440410090310240e0501241e16800e03078026000182e20282854158450500c0d05134461002c0d050703444181c8028046825503500b03030800d0f003411102082c0401181d5200503c040101005c42d8907001900b0074401058a0804089000c10086065500c10342440041c0c00812135034140c40c0021503586c040c03030510f884101c42d651070468456080040040b003000301c10b0203e514aaa008210300594072005120745e004240464400c0396000c101c0b41c0c920038107803401d07016001050050000c0ca40916050141c0000300000441104008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 338609208 1250 338607958 338607961
    0x30618060b1f030b0114040e07020709090b0105090408070507090b0f0102030301120201080405030c19030f020d080109020d0b0a0b07030e1e0d0825020f044a0d17 71
    0x35200b5907900001c0000c20b080000700314510b02c0049070301c03112100d544841044001800250517084a851078458100341e8252211152500e4102c070640b08180c4010700040d403100b0040c0801c2c604042900c1d0401d2043c200603261102c00c1c2c2d1603600340600f980c0101c51840d030f120015070050512510070403203030909101030b41c41c560400784107203044056600043c1c100541c0d5800034003040410000c4500650780802100c00c0903d03072074400504184404021000100e0707240d25092054000a0348026a80d500d8481c0d01141e8240405075000750000000080815150280040c0070303182c1d2018000035050400b229561400741d030401070070001031090070314012001740d2141c403100091070420162a03c000c60360700341c010f6002d0130421180d00649540743c0d40d040c114100240200d1a841280780e05510035a01d00c49141c0038401000203c840c2c54035200300c2a4268100b0880c0843c111303035000302200c142e40c62100350020250f800280034070080d0403c0c0c00e0783e00903c4a4078a464000c0d03100d080e00d1101c0c00e0004021f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 338610458 1250 338609208 338609239
    0x30c03020705070329011202180705121f030b060909070303140a170f0f070e0102031812061f1a090f01090e0a090b0a0b030c0118030618060b 62
    0x29080c20b440003800600c10040074801101e5003101000c4417548141a03640e003561161680d40c2817034a4000102c1c070032940d2030250220302048010352480f802182e201d090400302e448c59a030402d02c3d40105800c20309a0881180444c5c0e2580046e108061402900c800c2c40c2840e1035814007941e40405406203080e50302140c07007000041e600ca50b2040c24140079a0100b42c44450b11082514208080110100d0641c0c00004110055140715076140c0f1400100c031072400c0303c0e1200030703003982c4900e5002c420a0058000b045400210050680d0001d841c0002420400f041e1490b0700401d42441e0041d075050200e58074084011205c40700a410541c003900410b820508030181c41c036107001240c401d0511182c010030f80003052072010380c0506000d10003085095a140018501810b0b601c0003080c04150854040d030303980001c68601c00843c81590782452015000780000e006210040d07483c1c1d5004040700e1040d50741200c0101c0041e1641c003500c001000040c074103014002c4a80b40c12002c2d500300300001806082180561400b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 338611708 1250 338610458 338610463
    0x2040308070818030604030c06240623030a0203010f1520011803030b210c0105070c08011107020a05040c0c0204020c0f0a0b0619080a1e140c01030c03020705 69
    0x410341c45820260740d03002100701c51110200c41c03c0e0640d414000c032402c00c014150040c484007621481000e04012141442e40682004004050203605444000344144601e500a02c04640126640c920034000051689000c88065108446166441780c020004000c086a0080c901c800741031609440c80c0301000301c0c0d40040200e0382c5001c2c0c29401c01c400c1e13a28041c2c16035080d0712040d0042841210081d0341d602d2410041e01504002071040c0c051121100000b011003240c009a1500403400d40180208041d0180119041e030840306080c0d440d64030750140002c000e0300911031017546074070702d04096464907a14010484203411940c072103801281040c0307621445c0c560040c2d0030001c07603a04450040c0ca83e2410000c00d4600035400c1003c416501c5100c80303034420703c0f4204104500c20f00f8101c03040c40710140c4984a0300f003c0c07806445100825030040c96024005201071624403e60041300d0b60030394840303042e03440d040d00c8041c1101c0c10f0003c42c0c0040b11184000c2d40d040c01040004015410254900b100302c0d0743d981e5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 338612958 1250 338611708 338611717
    0x7081b16030512030615070f0221060411120d09030605150904020103090303110f0403050f07030807060e01110f0304050f0d0e01110a02040e100e01050f060d1103030d020903010b0402040308 83
    0x486286000001175900e44d1400f21007000000c200c000551240011b02e80580c142036001001c0e031141042d24142460b070060200b0400b95078010101500325500c0315520344540c4100c00c19090b41c4005680d1184050103010014096034101940d1481011840d6042039000c680014041c080b01040c1401c03102019110301c80d0031504540c0c2840c000905184c41d04044004000904500d9070b0402c000925141500c2190b0240c02603074000c03820360741143c0c044000c00d5075502c0c0354400103150440911000d40410031035404a03c41803005000464290f20642141d00765501c103490007500c0c88008014442840000c00030440d00c251002e00070182094070081c080c2c002d034025040581049004003504003034140c00d000d5000f4050780078100303111300004003083d5034a40c1101140780340f080340f41440c40d40c41400c1c14001e01c0d00510200c41040c18913250b032410f00141803000720040d100c120b00400f0880d001d440800040680e90407140300181c94400d07500030035095820445ea918810b60041c0b20520201ba202030444 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 338614208 1250 338612958 338612983
    0xc0301061701260f0105130302070b0a020c0d080c07030602030702010e01110d020f09030304120203120915070203011e02030105042d2408010207111807030b0607081b160305 76
    0x1d90800e040f5440700f524090101d501041a9420078051040d4140842c0007004c3c420b01c07a4007a1590b4a88a0744403002c03d0007401005c10069101d409425224140040f0200000d405680c0c0c035841c1940810203141b07880440c4e44200c03000350f0f00008000b000ca90a101d542100048034000344030000b4020429202e90040090001c1d05e40e07400a0800c0710590050200d8501410140c280d0ba11199518002c040103060743c1001d80c041d000c0e0041036030b141e0400004880b68624010701108401101c44004d41650b0425181242c1541d0380348419540880008411500135045543c0035075603606140a0000b9600b014040c160794188590f21070310300c9a0302ca442c0c01442806682e000458107451038060400400a0b00000100351109401041000040d0010255a80100003004a000103c010b008102112140003581203840384003081d82c09102c1d070032240be141c6005044a0800100b41c0711800780e40e01c86d120104500940e001c090440440501240040e2212541100081c0b461a00c8854564500716101e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 338615458 1250 338614208 338614259
    0x603010b0906040f060503070803040806090609030706020714060a1e180803040204240303080105010c110108270c120a0305121f0605120105330c01050c0301061701 72
    0x1484e2445815510442c014040107003120f2441e0b80d10440c554032075109020b0b801d4180607410004840f8000051758600030007280c002503103840d00589802c0c0c02034001d00c000b184e10084c03903081e58803016010001c0600bc0c11803844000382141603a0031441c23801132104171094035542812940d001800c20944010700e619000f411300b603030f203079101d00c006030040a0408011100409040b40d01c40c281c5518000b04055921a0302d9203034499803640b0054403143d0040b20000c01c0c2d211000d000110652080c1d07011600a4500d004c0164540304000308111340400c008040e041a500c503c1390b0503024039280171034000c02c41c130b14806854080c180e610002c00c0c0e44107000d8a107041c55024004205030f074407603000310000444403050100b491031b19039000034440c1c2d00034060000f1403510345002103000e03c0d240181032990100c003440e070f41581c0600c460041c8101c05007030f142c0c089544203202d186451842800b4407440b170ba80e0f4440710b0380c5c2d945c14840050180c036240180940c0c2a40b41d071005021185088482c0203031658040710 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 338616708 1250 338615458 338615471
    0x108060d080304050d08010f0e1f150e0306150d0b0702030910031406220e0109020d0c06120623060c010f270c05060f07051609050603010b090604 64
    0x40391855400d940c00400c6510300000b04414040b0100740550b072910640c0d940c2400ea6a00e03445407002c401240506840c00d0008004184a403800c090300002140c0002c0d50054007a0f0754048030504041113110f4200031604941542101c4e18007401069400320080c190041407051031400308400300040c80e00246a0b00c2c084c0040b512490080013a15001400108090008444000010060301a0103010345145030700001040705440e044004100384a01420744598518bd6400f80301c000c1d00452180e003020b9540c4010010240c3c0720414280303c158001c40c40b54407444d103800d1009000749818424144100d00c1c000040c0280510350002040d00c25038041221620480c0e10000345161083c104092003940c0f8001c0710252400c65900482d59407003040740c424280b03482440c807208650071400d100400d416410300003445185030003000307070003000100100d0074104000d43e5601858080c000944000c50b503014001004211906d003d815817020040d002400003d1003040469008040a45100e102d252500b4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 338617958 1250 338616708 338616721
    0xf04030201050a140708040509011203020d05090a080601300302190804051e0a05030102070203100e030714030309010b0406210809040212271902040219020f16060c020108 75
    0x80103134401401c1010607a0f12000391410017040c3e8418880d00c0d000350107900001840e180d0710180b1800300b54042d0007074040401d2111044a5560100700321541c0300c00c0881020448440400807a030280484c080d190030304101d48151030100a412a410905d41e01400341040c00095010070425482031194051f070303500d2200d40c41c207001d040c050b90f0001500210403075441ea0403800701380e1190f29181010359030144001d44490502d4207034440c04c0740c0607405500031701141032041903903402620795202102c1a42e08001136513881d0743d03441d206010803692991022003402031841c0207110381481100116800c0100c640707040c02c02400d06e2540c50260602c5d6103440c540d1024004210300701c800d44500200110740e01c00c9205010024201c0c15110090820f02e01c00400c070101440040c403842c405180350042c40c220542c0811049191080740041341c0240c2c007030054044400111000d040c1e00031994014010080c0c5018030107140803102d881c61070070b0f05410b9200f08050340d04406020003407502880c0c056010780d200b4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 338619208 1250 338617958 338617967
    0x703050a0c050a1a070510050c0d0e160b2a03040e0708100e090f011803030b09040804051318060b0f010c03270810060e01090905030f07020f150d060b0f04030201050a 73
    0x283c2c0a61f504000810042224160041c459510380010403c03800180d85110356855a45507002c2074101803083d020301185224074041c3c06040855450500d5401400e61560700c610408540b0011517800803174280039210503c841e05a10003841d02e4068a10724001c0b00c2c1282240380e91095181f840420408151740940500c040d25250260300028484280800b1150b880001044026030009203880042d03049407414074222030003640c101e8a83d03400c00d030034002003245500c20324034482000c0d5960701d010103940381c5500201c2d0803a4010031000070390301c526905000b03030b128803071000d1030401c0416500d4500090704840d0139050a411601d034042c40303e07440e0304444d00d480115000340d41240305509900d08551071a400000594180350ba24069990761508840251010482c0003841c40d0000e00c403030100301040402500300107000801109460b1130090100340401400d4407580854500003841ea03008800e540281d9008003841004030b45003038282c407a51402c900450000904001c4001004044a40f04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 338620458 1250 338619208 338619223
    0x1d04020310180506091c020102040f05040e10140103030807030e1b0d06020705010c0f141207050f0313020405090c28080d0309050d140702040b030106080703050a0c050a1a0705 77
    0x101240c0c03007400c00e41704142e60b480c0b106d200090500c0c01500300800c0342d4810300030346048484001604403050b081ca020000a0300c10131052000c0f901c5801c4034032000c0788280c0038de9440fa05040409000c15411400c002b81206401000c00091604117080c101400707800007281c482c0c6405448400050503111400600070301003900f4080d140d0390001c034403041440010f6200c4a0501c00c40d0b01c0d141c10054400c1d406480c25284901041c2444405000d1040310030b002880301a8000700600c0c1040c9421101d81210404d50015106640c60744140031300d10045050a2142c0c60304860748a00500042130f8800004040c41e0385c1011318480320340640d030f40002c00c011300604800640300c9242960300300d21071094010020b26a12006035200d00c14200202c16440c00352104c503d01940c810840f501e40940c41d002d0001814008001d140c05650380c540004080300300b404854051f511803000b50000f0101800c0c10060b102050b000716108190081c1d0810814948000d0440d2540c18040d106071104036a01b03146041005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 338621708 1250 338620458 338620463
    0x1a0708070e0f060c10020306040510050108070e010201150b27102a03170708010b0f07032106030317060612150301060626070e01140c1203011d0402031018 68
    0x5641e00181c1800c1141c01031f611542044d24204501c0d5102918008150a14441c1b140440d0140002c034604503c201c1440098920600000c600c81113403824401402d00366a005840b0100b000c101c02c881d19141c0b079984070401d8031f07080e52140b502d600a00000e00c45040326010806101012130308001c0310141c50b180c20700507140c09401d40c4014180341406005455002110f8a0b0a1060400142201d02030440b05050f2682e8241c034a09010503012340d003107079601c985401e8052240740890100601013a8040010080140101280451441c0307000303003080d5030094181e001e0441003010090340351a03210603070b120707030366041d0f0b00c000b01d500d503503035124142143c26649513055420001d0100c0c001d0340010703014904070b005c003088500c0c01c00d05040203502201c06440e80700000b1100c600c00034040d80f040c402d800040d00c01d24066803900011b1500145060401210f610243d41c010004000a00b00d1031101045540340501c2c080140c5070a0380046d0f1100d0b2861b080c0c90006583d402c0b45030782c020304494060003580e03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 338622958 1250 338621708 338621713
    0x2091302130f300218100f080318060a050f0c060f0a020a0206040b090313240c05101505210616092607031a0708070e0f060c 55
    0x141e0440301522241e15000704005808003000000d586030402d010307000c106150707181c86184a8055204041a80d00c52401603034400540001d002165424150490080a0800300a00f500d468100c1d10700c81d0b07803c65400b9101c69082072003c08460b18103000300310201b0342d044507610f558801c108015149401061100400e42c0310201d08109d200380b001a610780038400d10f40110741d1030381d50919040c09a01c2044502801600118049400102c20401d00358110f96500244d900301701c038100b400720f034120303031036110100c00f00a9082d803070701c00040500016103003625440d02000518813522040c0d5280103480c0f032a4607042c0e1b620360640c0b180400d90300103409080001c20300d1030410a14201003640901c50041c1a680b03010b15400300f40111410360f05200b204140c2d03202c07403814078031b003401030500034490071141d160f00328031162400182d180920005001e140300e03110b60040c0305c8660700d084404404c01030081092050b00301c00e000301035800001c1c9082070f000c100c2e00c002112011134041861070007908080755882c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 338624208 1250 338622958 338622967
    0x803071103040b0a08010909020d020f041b090f0f21052109040f0b130b0406030609030207030302010509030406050d1d06010f170c060702120c06030403050703020c01030e1002091302 80
    0x401c03c14008000d8003074503596400301a6211a1810304403281002d00a51000302d4a00240040c10510800c110320300c00100001a40c1c0c00d69000d030f10003041c030300380800002401400c0070700103c4440c5100a010309605100c9144844c10041c58513000310031011100d14907610308075018100403082298040d4003102414103c149010a41d11004642281c01d841e0710590600038000394055480c8500d419988008007400074221852881c20020400380c203140e5040758840c000840441c01500444150717030b200758000c050307591440c100242110406042045560020130007042aaa400015280300c0e03040d84c400050028010b41207000100c441e548120000c4c000d9030000150f0540c01380c0d49004450803210300c1c4e469003800722005605d0320b68075910643c0c0454288050009410028403140c40c80507040120341d007200104d40020904d4000301e400300c0000e01c0001d05482090303810300c00b010f003070002800c007880411344800c409900e0f441d01e0404034180a0380462624665078400d4284112201c400d80c046548 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 338625458 1250 338624208 338624219
    0x2150924010e0601020a030e010f110a0f0b2a0c030d050a0203071101150b03040c170a02010e04050709290301090f1104061413050612091612080307110304 68
    0x1486024820021001c5040b4009050b40d400481c09100e43c40e07042d928610700c2d600e180700554044107420548001c11a015104840d071000c100312040f5400e000b001d101e51551824588400c044000030f20b140c480c0d1007540e0440103035800005c4100301c6c10690b512801e031030391504032800d441e5009120404042600700018030901098039401540a1415913650a49080302d082c155805d960400508280d02150a0000c12030250071901440c1c1091086054802142d07840345c003007001001e00c1ea850096900803030700e01011503030032140b1110700c00b8041d01c090041c3e142004020305100400c0c4511140002c00d1415044000484011078000e0b4046002032500d950315007291000030116030030782e08003603031410612004800a0754140c800b201c00d95510b10540045604501c1001c1e00145280c1c4102ca241540200b01642c079000a40b03404180a0b0f100c0c079441c9806414546414210314014620941440083c00020804c0c0141c40b074503a08401942e90740d40311507000b02c2d41c07082c0130550742e0218080894003054 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 338626708 1250 338625458 338625523
    0x1505041406071d030120070203120a0201050a0b100f0c1b030803010504050f010e0a0b01050706090326010b0703030b030c180411010806010c1b23031903021509 70
    0x340d15010701c803c110314039512030a0608031080c0c00d41c40f0000b0f003c0c1010682c03d48040000030485036101409480b060f059a098269040c2c10209040d40540d458100b001107117074081c860103001c0b1000310761066003100c0720180035003591100b400c95010054060100418420790b401440a07041441001012050360703410003200640080c01268455800c1002003264448000138443c1a2121821a4502c1c3c0c0c541e07442031002450840d0405051200038445100840c605204440649010b40c454980d40b1014440801c02d40e48804040c0b0b0b00b2050540040c0408071070802502c0e142641420700103540c169070b40020f441c000703003144051340c0026000c52820390b41607440c0c00b1902892155180d140c0c2009800700554254404569907030001d020300b440e1a010508a01c000c902904003aa8040603aa850703040101d021119420110300c5248480280d0045040030408010202c1600c14102080e00c0c40743d80003500d0305070001031f0210085082c004107a50351300c240700035218842800d4a05c2c850042c01c02c951078 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 338627958 1250 338626708 338626727
    0xc010c0e421c0e12070309030503040b0910020f0705061e04260703050a02090c0d0f0213050108040b0604020a02070e0907050a080c030d1b300507150504140607 70
    0x112034419914590018070b090740034070641c010181c005480c0442c031003035484425400041d02039081010500740000071440920041020305a0301540603a200510401c3c02a4551903094a004640c042e16503980c801034040b98007003d841c000c03504180e82e0f421401816007a6030a0416007e9964000140001c1c20399045541007030900280110b91501103814a58684502151201800c590484002403006203000e03590303243d004460031043c50034a04050445011200307156805048107034002000c4650107044940100200805d180407006850503a45034004a00090003c9020b241c020400b221503500a021031320141007001c0d01f4032818984422100c0d5a80014442d081c064040003c000c502900080707025041c1c43c0d800b0700181030a548049084421404c54919040c86103403000b1a8800918202d041c1e03070089805866003250190611040d0403109181000f074009d000041202500140340c4403141c81080020313203000102d943d81d6081c00305418206860010700c0303000b100104002c5c150415407a8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 338629208 1250 338627958 338627977
    0x40f020706062102040c05040e1602100e0a111c060204031509050c0904051c27030c03030503040c030804030b0406050105040e150c0705060106050c010c0e42 69
    0xd022580c2c0d103820101c42180303d1055016401154007144001d0300346a0400412000c140c07600a203061342d00ca140c1408507a0a8070510f0745507040b42a00c0b50305580c1003200e03000e0040300c58020009450451a01a69600c1e015030040108001d0101d034903055941940750010044003041c8020010300a15115000b94014001114000314407601c0a101a2040c4221070206501000a0040d90b0484042181e10200180122170502c500030040c25004090341d0002403020031902c62250b191000040ca140140d0504a5100040d41c0340704200081058900014220f941600300b19540e0b071a2420406d0040203182c01c003502c45400010000108030024141501c04d0b8040d0304100991b03621041080250b0b28040d020419961000c0410400d03038152040f09900180310007207c9150050380d03500d05091031001d91290003c280f0104200366020000e0240c0441e00600c0e281c02c1c145a80b0310710004450f071050100300c100d0400054010803a40e0326280c205064040c445001d0b900e100100c42c511602680403c500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 338630458 1250 338629208 338629211
    0x1a0f04080f0d180302090a06030c0603020c0601080604020109060f0e06040b090405090d091a0915070b01120206070303110c01090b07020115030c090b0105070f06050f07021f05060609040f020706 85
    0x2002e44140308401e0710294084803900104120b10f19001c1090613a009000c0d100c2d004d50b21580040000e50014041d4014949601d0141c0c54103054082c10703051110517403000045800003020480103030f0784154003000713072025410800e040314100c110440e11020b00020064200c070002801040b441030349001340440c1c01e012181070059565104c04243c459401090020120300344c00c80a0016542c7e52509512800700e41c201d2908200030721000880340c0d0360b0300d01c81a01e185000a14034041c400d4201c800744c054240307001411180030300c039400700356a4072504402804241d030307440003d19083d40e054101c440f84100c1e9002030044950a080c450074911094540101542c80d040c0d503100b9402e0100c480800b1a0780000c0900781d220704e0308841030b019001c800f00e031604100c003c0210340c0004803000c10000c0668014040015103103407100d0800c0024001401d80802c3d5070000c903e0800c440a0450403008003680644007142c40e4582d9000715955003d0b440d61154000d0030010701e050010040d82c094410035008540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 338631708 1250 338630458 338630473
    0x5010603230318040f0906021305100801030f0206030414061006030501080a0507030204020f042409050906100e0a12050c0f0f0a03030305061306080a0210181a0f04080f 74
    0x110542c2e80c0c810001d01885030400000c00301c52502c1e00f0f80c010100148180303400b0441c0400c47d030303414080364425490368a10b07040c200400c0c0601c0c00c4c0300b03408440b2041d0504040403103504640b15180c100b400741d8002803103030308000001003c1000403981803484007201d9040f1034a45c207003006a1881c4208074000c03680040d10b894000100d58000040c021003d68002d4081d200c82c608507000c0c0006940840004031403801c0404c000a520385003c51503100c25466821001c285004a26008080700142e40c840c0b0f104058800a2201030b90380c08804c441582980d00f81340d0715644e0900d01003044204264000c00d100000408800180040031034203030380600c01150000ca0429000b801c005600e000b5210280d0400140102440028080e030300841c2c109400170a801c0d03201d00002401816a10180c000400030b4104044110440c00c105052400d884100c0c1014181c00703101c4107200d20103031003d1098540000000d41c14901c0e0b8216031046031020707a601500699219140c05e0015521b002e460810403103441142d5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 338632958 1250 338631708 338631773
    0x3030804110405070e010c051207050a140d05030a0c1112090f03060405060c0a2307050105060a05030c011409030d08101d0711011401030b100b1e0a0c05010603 70
    0x460503100713180b20381760500c0d6884107100464000c65007902c11641f0f44038a0010050342c41c110009010b071544039100410700f03200140741c148410f8500c07041d5881150300036034070496200e8000003a03950003070000d100051001100501100c035101443d603455000e01401640c500b145e0f071800014488103c0a0b20130702070081e650400d0560707802080350003502d41d030085004161079112510040120800d64585101100740d024001c070042e8090008200d07000348009013401c2040700a0240551280c4100d90243c5c04502c0e050110b40c4035081d41c51154108000d0f55640314000c402d8030f0590750030b00e6025040b641c40c90820800a0306540d01902c4480d034090f0000320001c0c002011024803c22140721368440c40300e81d100c051041d540540200c03001095035403a80c03042440942c0e850080c60081d4000d20f0180103e040c00702d03481d0181c40351500701c141c280200b00702c190302c00000c6001483c6060418086150fa800c3c9650085a085484441c018043e5082c4403000050011101c2c40c4514102c3c0f40c00505282c0e00c911 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 338634208 1250 338632958 338632961
    0x15080706091a03041403040603050114040203090a060c020709050408030604060b031015121e0c020a020a0b0d020906120601021902100804330b010801030803010e040c0f030308041104 80
    0x2e00c00c14581020b005010004008804080c64001d88650703116030008045412036030858000d46c01520010365540e00410826034040400340c145d16094400310300d141410b0301000d44403d0140300243c4283d17210a030842c812442000964005d01c543e00082040e401c10f86450b2906030f00030b5800364447c0303091500104031a01420110f90040207400c140482882c905120010b03841c006108620070b0040d2480958107040741405103984014942101e4840799000081104c11207400c0b850007421540907a00500050b118600c04a05075034440c951140c0f124403d0844801910400b14015049007000c1000b807103d036901582c290080100740c09541021503850408040e030f1700d440e4070282d03000020310f04038825a40500c0311a504030b80a007905807504521800162401c030060315507078020036034010a030310780d282d0284107049440300d09290886665145854071121404107000e0f426024070894082002c0084d010324550013000c0325454000100d03602e0034050503c210884040e89c48031148a00016946850b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 338635458 1250 338634208 338634227
    0x10f0507050d15030807050102030405010e0c150d0e01020a080109290d060f0509072c07110708060f07080a0507080a110c120c070801020c0c060a03020d15080706 71
    0x303948140c10b020950b101140502150100c601407003500c46008008030703030b101e0010502c090103240007603528101844c0c240d08542041240440716001020a5044c540e101c0c030302014680c4c1800002515a07600c550b1040c01420a513034002203562000454401294210900c00c2c102d40070f082d0108400c0300e2112034a1410b00b1041d00c444581a82c59048402130300d072000c030110460703024200000b540060145040c0880d1005d4880c00c0041c1e005660030041c03e410009031b1004040401d0301d40062918111b0079541d41c58000d000303501801010100e04000e1641005000d0040010104444c0641001410f4000d0f5680596084001035411400202486242e001e0107000c1c8000e560f4552140d968a40d13240001c0a10341c2d4680003010042100c0c01c0c401c2400c210041c122030b400d18a0b01d50791462030744481d10b480e001d076100030000d0740144044502c000300030a040001c1001070359590740d20500448110024440d60200c1b201e454079001e890900040840c2540c0c05460200d0100d0340000d840b10000e0307407800d02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 338636708 1250 338635458 338635471
    0x1003112806090f17073809242d0f0406030b011b080307050c03130510020a051506060712020a020a1d0420030307030819050403052a010608010b03010f05 67
    0x4200b10420900b104090b0128003c4941c07240c101d01c3c401c1004480d01c00301c0241000c40860003021500768454504202c200f80060a0744841c004d04490b02d05402112703014074080a41004002401800c034100d05030040031110240180450f512319281c5988845600b182c050ba5001924000612440307500a8508075980800d40f1030a95a011443d641c02605601c0285800200b110503c200350010340104058107403640060201313120b0301e052505206a203100502000f04551001d1031034004100045448078034002c120303040114503580c02c00401c000f071061050017441d40110041003405a51301284080c08103108442c100026561819a040b24507640101502e2040032a000304c1c0000b140070995910907954200345000d80c40b5202d00107819508810410b07000300b0892020060b94140c41a15000e48041404c0704109038205030710000c1540c0070741d0820398405420042c191102c0c032544a0b40ea11152401070007400016292100c00c0d0107005010106402982481d10f40010154540160785c444c04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 338637958 1250 338636708 338636713
    0xb0c030301060311280302090411040e072105040204020f030a1407052514070e0106090b040f0608061306080a03260403051b010207030809061003112806090f17 70
    0x4028902c0116030030105d40103601456420486c41840e030702c0300d004500420300e900d0106921341e0302c0c110401c1450310000b040ea0041200d00c0c400c8500840484181c008501c1c0540c00025040c0c0d81d40c800f080091141c1802445528001700030005e80d0400b60708504606100000003d800f6180c0003070954450040303641210b202e07001c161240c54140a00716126103500c3c080c0341204040380c004181a4140107013a044030102c40d10340d0700140105c54218230030000030a52a08030740c1c5442e181c042000103c886074014041000119400f0171055903900c000c26080d0740c018041085000d996140d515074602450004401051801104940403031080ca010880094242166005039440b80c0d000c803800c1e80044c1030501101e4505005a0341c8400910180041502c00d4032110a9424002080303454120001c2c003001030740744560300c03e0000500003292600e0030a81501c0c4000b18080941128600301c00c0d00710b0740c2400e41c04580c2d00080403944544c0c1042213620b0b0000c20001c258a45607045440c0c900c8105021065 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 338639208 1250 338637958 338637997
    0x20d08042c01050f1507080c071401080a2a0206060f040e0606010f050c06070c02041802031203060a031a150907141b031c0506010207030c031106040b0c030301060311 73
    0x50818848100d1604d01c01000148903514240480810340c01a80055821260204912040c40410400240130349440314403080038850b10000203012400041c030265295850307500490140740000c50000060500703084600111450690096440d44101c5140d4410b124034680507a05044c40d20558183d12280320107481c1583d522001520091490a980c100300701c001c000d401e10041060020302d00400c0a40d4841d400d1030200d004210984010b01410303c5445400c1042c1401a500001c0300900da0221a001035100d68030040003416030485580003030403041400214003420240d943c486072050300d0280c0f1204285001d0030610080b0702c0101c03110004182503001104821900f080603100224007039008241c410180b00d0078900b19003290911000620135200440014907817800b0b030582c00817080c402419080e10356118003120306d002d448040c0990750040c5000c00c0c80d80703404045a002c3c1c0007a50b545079841544262940d6a1713402441400002490200314980d42e4a9110844200038200c0001c4c0c241d2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 338640458 1250 338639208 338639219
    0x60e1b04060e1816030311071a09190812030124020a0602030a0f0c02060612010c050915040f3305070602030901061707090b040c1416020d08042c01 65
    0x35001000e0780310340d188146541440c0b440d040340c81513000b440c8207644610b401a94121080d20f001030315045041150488001a4401d55403441070300c0d901c000854007021700d03c03201c05615880c0c0ca0250004a024011107851115103101400110f04980d210120116941900301082091905074865000180c000d005401c0204040f5000f440e0080c0c503080c8005529500c401c2a0000c4881034059503001d80c002504108492401900e0408a008080002d11005032030351001402c40c40b0380c90340c0300d10075500d8400b40d4640c0070117482910060042c480b40920f00c45e8507150352040c00159900b031000c2000341c08a151040f0405804503140468841c0c481c0303410281d440c0d42d20806504010b294020542d1395a02c009160542442c603410b034098050054803656040400c01c106076500d50103c0350107542800100038a081e40100d003da07922051000312a00d8106003210b5141c002d0f0441c2000c0d500c1200902e0103418803c9138001407003150030340e00300520f020b0980d0054055000304091140241400700004200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 338641708 1250 338640458 338640481
    0x303070b0403120207060b030f0703020906060a020109150b030d0201021c05040807050604110111010902360403030218011b080d0e01050a15060206191107060e1b04060e 74
    0x1005442400e1000c6803070100c0c020f5504980110405881070740d03c82064000d507003814030200700642c1050014000702e904580200304003100c00341c00c0078020b07207001802e050101c0c400e61110002507440f06110900d20b034400c80c0080a001c104540703034468001c02224030a11801442162000c00915603030b00581c1e00546103013030013890010000d96070500c08001c50030000f80c0a0103080d1046c0e10811700340070a00005000146618455100d031060b0307a141464140159440b01c403081114100b101d0030f51070340e50481c2c0309403035001710100c0803106c000c05a4003808105038041d006068403140c0f2100c04050700e42c9401c01100c003082503180408003041241074400104003403600604480711480c00100d03885446652507800c4503011034849058a41c3d500440b0f130140345000c1200300911003132004150504040c1c00061100b4492b1007407003141c6940ea83e440711503242040c02c0d60a03960300858104807200c075040c905034542d400003001250440400c001001d8518181c803814095070306005943c0190b5031910a03e42 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 338642958 1250 338641708 338641711
    0xa0c05030c0a0807120c050405070f0810030c12061407020a0501050709140f04020f04140a171504052b030e030415030b3105010803091003090c1e0e090307020303070b 73
    0x59511b440104040fa06440d00c0c060140108611380d42c0d40c000140c0340000900b10a0043d00e240107074011258100080380d000041c1d2020764080c10000108440285042c0e1b0042128000c4810090b500324100281d082c2c020621804c0140144000d00482e49d55040865544449020302895020b00310600300d45814610002064518090001440c100256080340c0d6180c1040c5d01900d08040e02d9000d14555081101d0600000c01000341c0c140c1003101480b00554560b2581c8011070900414880054280b0104001411003429690840980c000001c0044c3d0720700d6904440c401d01003402e041c266000290300000325021903a203034511819405000000f01c001d481c0c03003c2100c0e4004d0121900050548038090030a083c825a2950010790070f803514030140580e07905078018080754000340b1281c080ea031182d07034040248001034075000440a0642c501008806582c1e00914090800441c04210012038a0080c9054564072001c0c600f0039a02d040d40e142d600e10030880300a4050300280480000101040c0c15203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 338644208 1250 338642958 338642963
    0xb012c0f0a0e12041e120318030606030b040203010b0d050304050d050f06070201020403052509111b06010911070c090b031c081611070e0703020c0a0c05030c0a080712 73
    0x10071074500c10b5694a250905000c00c5080d808000501045540d40e41180e002c103c0380f02c20b1140180c145020b11041c0700c60700030840601400340d121520004055507001c2a07001d1a0f04c03d00c10021075441e030601010244040303800720b01941c0f82c03040752211440c0841e03343c00c603651301000452400341800203201c6003543c1c07000100d030b462141e40084007805000b848200c0c40390102c2da00068480380340d81005803a081d0303a02c4000185100e29801d0071060005c04d100c42042d15880100400e000b2240c500c518400e04c85d4020027800700309a15511544e0781c4000c16024100d079000c01c414020665005145d0140f4403c0c0f0ba00146200c01e2500104040600ca030080500c100c0001d007502c207007030103000072145625101682031001842c07020401181022030010008800c40300d1130040c0b441c00c0b1314281d0a54441090050721400b00e14100096880342c030980441e10035071154400e0300d0b01c1c0005850b0103400e000240c00340501c079016a00e000d4001e800c1c0040c00c0c9045600c914010100103150071500c3e44880c1144509 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 338645458 1250 338644208 338644211
    0xb030708060f040c17031e2703070506211308190206180d11120705010e0f010506010813081e1801090605070303051e040b012c0f0a 58
    0xe101805010640c800c03181c80001e814075241920745154803d540350043c2c400c44404043e030610444001054528000c419648426203000490099055014a0312109084600d0b2400c251035540b2405c0020b178410400d42c00c64841e16225000c00401c1d000302118116511504540102d1802c1c02220440d00b210041036603018400d503a80707516029074005000d103440324280f41520280507a0420035294458010340800140034511560680c641c004509000100800c1008890710303410140450044401864449607599020385000d9010300480b0146211038082c81200081490040c05214070032103050355489800d94034070898a1001951035402d03955030209010003a002c54ac0b103200411207280d060f6160b0380355100c0d0781c2190004004c00c0392090411003400810484603822034143c0d0001030f85030070013086954039100c8002601e6454032403010240c00c0c800900007802403140040b8141d030180c007800e0201054105481c0c3c48400100c0200c50242c54180003d07440350802c4203c29040400300a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 338646708 1250 338645458 338645473
    0x21011030a08130614040b0601030b06030115140406030e0f0a0b011502070e070305090f0705010801290f07051218041a0d030206010501120912050a11060114180603060403030b03 78
    0x10b5050403580319000319505c2d10080810302081c0040c44803c82e038080b01c2480d06104040308040460a00e00040c424002003148105214217030328081d40c03101d0310000300c5540b81902d85540e100002c2c05001040441c801d1401040411500c021001c42d8800c10250802c107188a01d0b4641002c0310711034207641c4003800440c010319401041c10046103860a00600c0b03540c0d030214080c2410304102e420040d030300c3c40d111615807090700104038a9030004280c0e811a50101d0382211186064a500b864188513160030740781a007030010b10940340108903000350030b55501540880d11101000c0454000c18880c00c441c007501840181c001c07118034074054020460300b1500c9000e508440b2403d00c04588203289060088015030050340042c40702c0c2d640243c207003051001d0071809004110780d0ba110050042c40e0103d008040000018611540d103004025a4506800340012160300c1c0d070303441c1840700221404000041c450304002020b104058580e0703000034083c480050203080692a180d8054000703041540e109a018058250f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 338647958 1250 338646708 338646713
    0x21f120b060f0715110310080307050d05090d05070306051f18050a0f020c0d140a090504051302090108010f180b13020f0607060e0d1704140a1e021011030a0813 70
    0x45011780c180903813409407241012400d9000b40074250300421403560007444003c0120b0400602074020700c17181e0a100765a00e208002250f401074051002030a0780c401c29074000204601503005500c2107150380c0000c00017200042c00b441e0701d0141c030321518a444000130840d292200441e4851034014948440008100c004109088103907040004d0106d030582010079400030068002d02e120380034281400c41d640c50f02c0451280504104024052940a0360707031400010070a01206841101e1141c00400d00d88456956400850180041c1c40e41c0d070700030b5402c040c00030544095070414060710f01d0340200714400641e00c2518441c11000040c07010b0380d20104808480c08c140d05c031a0020030742640a07000104000240e099424a00b001201d800302c10490880003440c0104401c9520030303000b551001c81c2c0240c0b6045100221701d4246d45170400343c0003c5000d0342e0624000001082105024030949900506c1522204180c4616004100414154104024551145100d000415400004000303508a140c1854 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 338649208 1250 338647958 338647961
    0x1020a0201020d30090201080105040204050a18090501050c0c0d18091a060a020c0a1d010302120a050303160f030c1b06150602070303121109010c0807021f120b060f0715 74
    0x10220206036103480301710541d42c0c032030720540c05814159819881c0515100105030030746071a2080d41c406d50a1503209803010710181c1c01070707519190000000d210750300382074046c43d65641c0140900b98152040c5448051442d02403c001d20040800c8210484060315003a00c0d10051701d00034000114041e42002140c6403940c418015291000481d0700520124880b441444000480d0303411140d00140c1104941403104950001e80d8152681500d95105004420041030b103059440342d0001c12600002c000c07c2030521881c00d28240135620b41c3e48400302c0315070001e030560031114a08110000140d022000c07260350083c4200c04040c0320f100700c0b8001803004000340d0415508099400960040e0000c0404001b8168040e0300e4422988803036230200142c0f02c0e1b000040c83c049c03182ca03c0840c180451031058138140021401691075103034024001607035003101c01c0500c130408803003402c1e800007007211414584100303c0c0c507108860200a000d8100c92800c903880e0f1032135046070007003c0b0455802d1460590410000c856 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 338650458 1250 338649208 338649287
    0x50a08030703090c090e0d090f03020f060d060b09040b0907020a03030507110f03121e0105010c03030f09061d010902011413031b0504061a03190204080312100501020a0201020d 77
    0x300170000f4540f1740a81c01904110040b1489030400a042e43e00344543e000040407441160f604440800030720399660003103041401181000c4000602d80700c000200643e0100c001c00c400300b000c481c10445034200350b04011050300182c80c03200060780030400c10030019000b41c2c0031940191460030001610200700a4030303807410451980000c05904003049040301249010f440d030b500b041500400798000e040c86442d82d040c6010500c609410031042c4000342c410f0601035484102801c00d0114107121240480c24080050481032080c2207814030207245901c550070040c45000c030301c0ca5050f514003140b145100090f10301500441000301c0712071854003002000581d9004440d001c640381ea5500111755103400200412030780903502040585c4150f20700c0c00c543d11b65102c122640705d9402440303442c000c0105080b03000203004130b4011050910001071074191800a207200356100710313403202981d21400d456400498554541000c02800f5a1090300590310b514001c81c601342040c003401e40144841c513410703201c80d080c0c00e14 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 338651708 1250 338650458 338650469
    0xc160b0a110f09090603061605090402190c110f0f04020d0b03060702070f08061005040c020703080c100e030c0705100e1804020126131505010609051c050a08030703090c 74
    0x2000030b405003d4108a010361340d00003003c601030001031900c5040b420341c00c0c4040954034104400024035629655603541034071070081c0e25441094030300d90442e2000d07100e544100015502c040b401102542c0b1031400112070b0a2115001c0d024044030313444402444040c0d007049a401d00003d441e48142403175038804103d61341c0b10340000d60042c501c89180004008401d482e58001401c140c00c480c1c10030815211204081d42283d20560700025810a425800c03400c10071075030001030000e00001030054603240d000030308918250000404000070390041c0d10081c0c0e40d2280f100c46180c640c0107ea030401036440d0a4000117485c0b01e49041055150701c03000e0000700202131103480280124850000d000c155603001c0e14101c0c22040107506440c0c0151510503280c05d0b040700070044910203d200940d501000014210100c0e0a11030307110501055031140f0000d0016000c0b0b0143d00d0140e0411040d42640510403024034288641250141140c20b80a494546155100804a00c185074680c41c1800000d000188280010301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 338652958 1250 338651708 338651737
    0x9100203091206061c050c01080c0c01050108010c030b010216150c0b010603230609040b2a0702030c0a140d020612070e010f030b181b030109060305060c160b0a11 71
    0x50312608104100b00382d640d80141c083d0317082c0201e0740003d00020f07910321010001d092401c1d040c0d0300c2c1c0074070030540e10503034086002a500f00340002550301c2d0150401600c4000540b801d102e60043c202c01280d58610300030705a804400d81080401180c65020041c0f408001c440c580444031051645454400c01c0080e03000f040000c0d40c4a001402943c141c1c0c01d041401d0b0348c021000a20750902c04001200050040d0019044204c4840400c00c0001e2040030105d00032010301e403548100550005001c81c0d500504010380c002c0c02a000c0100d880c0ca840400c0100792240e0864039940000c0c1d80080c054120029842240c00000400c003200c0c0510040b60120b100e14141d07030b2200500034110b000108052900c0310218145402c19074031012560f00c401d28940c030b00d029411100015551040b88208140c52801035201c2804000008214800d05400c16070640303010740110360142d16507a54030031842c03007218030a10b1701c410882040380000e4646105e1a400964100000c0303031032417411515403480d60006403004a035030b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 338654208 1250 338652958 338652961
    0x30412030f0305070e030d0e1306081e07030308010605090103110c100605040218040b0402040e09060a060803030c040b0702032a04060506071a102417010b09100203091206 75
    0x102e525014003680301d9000e1802d10030100b00100171a0392500e41200c541b044c00450700b159101600d4025403080002c1d100042400101e5417201d030940c856030401184050007010b0002e004030101c00081010407290305590354900c0e40c0c40c04d10121240d400242c030b02410591070390340c24016070a0728000340c4490b181401c042c12515030782440007000c07100c56921282c00b4031300500c0190801034100c90f00d1b8101d80030550340401d4420141c00000c00900c00c2d60094100007520b02c06010032844005542c61064803840c1e82000415100d40d966540c078003040f10184e540702001c0000340421511140900b48485c070180880e4298140342c83e00c0340c6071314244441f2400d8001d6804501540749014012403000340800e4403654a485025142e0290107014400c41c400205002008640300d00541d00c0780c8002030060718001120808084000114103900004410004800103e15100304103408203060403603180c5480145040c102401b800700310034804c0b1a42080d0b010078800b440481d118451002c40ba07403008006010203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 338655458 1250 338654208 338654237
    0xf03010303120e010c08060d060f0c0c0b09030412030f03150e06041a0d0605090a15052d0a110f0408030d060e040305070209130203160806070f0207140303041203 71
    0x2c031070031103803c0201e82c0c0c1031800303980d12550000f4000d504076009488810941c142d41c28140d002c1c04486488842091074a0505d208a0340d01c0702010310214412421150340791038204a15035203004501440344d052411203e040000b038090254401c510565040c0400d202a500407019040c085035800680c00d00410f004125040c50280720304084200700166100c0c5011400d4042142ca00402c140140607580c2d0340e021400d5800d080180112066204014180c040740150356180600816681c0c5c159801512000d002030070382588140725512000850149995517880141000e444400310090b0900410050070504c490345100a00107005400b00071540c40608104400c1260215440002101407040034400004e6001017182d803019011140204151612a100054071580300802945849915207081d141d81203a002441211000c505542c044d070f442c88001d6500c08111240d400058000070740c2031006402648a039080e00001a04807800c0070b0321344807031484800c0f5800050f0f02240c66a030700302d0305 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 338656708 1250 338655458 338655461
    0x1214011802010e12030418090c0308040e0f010303050306012007121209080d0302070c0504140f07090501120e0703020d0803010326090904030e0a271515050f0301030312 74
    0x81510079a032075005039a40413200d54990107980103080400c02995003d4000905941040400c0c1c1e80102c562218a9544d103020700072544241f2464404121440020b04000c0480310701c0c1d81207030b82640ba040e1640d82c03805d0044440c3d00c1e0141c4880c0c1c40300f942e02500500343c0341c100803c41c0600900070341d804000341341e03050500c1c10541580c00c050801441030002c0c0311300c04c8042080a041c40729800c01584031400d52411030803600d003980040307411a241c40380c000c1c6a002d8500066000f0140b4400354521a155000100d5804919014003400300f480d4904100040c1c203c1e40c0250b4030064000107907280d442d1258001110410000d4003aa01454040014024041030b440a4585000204c01402e4100b428000e50041e5010741400c0b030340300e030a0000001e400d0602805a840c88000010310a01e07203682c403060040f100ca244100700841c00c244444424102d44407510884108000002180d54034a18007044480d505103420100c4013040014002c0841c3c8101c51400355010318407a8482c1d5070401115020b880 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 338657958 1250 338656708 338656727
    0xe0a0b0603010203011202060d0f050f0403031a150f1209030a0f030501050108010501030207051905070906121e02030708060f1b03070c1506030510050f0c03040b01121401180201 78
    0x1e200780d1040004026150260030490758490341591016180c800000d11000100b131303a04105004181000c00b001401900840300602c00c0d4440c5d1020405030540800c2c3c40100000c1c211699000704603441040d82ca50b0b0120050814103c0c500034061418040c0303c614010301e08243c4410f89550f2002c0354681805400002d000f45c011928a802c00041d031411000800d58101885428107150340003138410b0074450207004149440750650400d5591003500e280259440c0a284180c4040d00e02c1c0c540e000ca8000d0000f1300c00c881e41e64026a10010b2000c07140f0001c10140642c076022039143c419000c000824600502c502ca21610b03d002403015545071600c07840c80d00d90300843d5103403044c910400410800710f030001c0c00524060340008044200c00d0180c006e10300203040c290401b030100d200b4a1180702c0380d24241e8102074400c6500140d109a6620742d00c400c495540400d56004100c0c10040005100f018458404403101c3c6002e15250300d003800ba20000c0c0340c00c407182240401c440451000320740d420b5580002501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 338659208 1250 338657958 338657971
    0x180b0a0803070b0f0c030403050f040e0403020706030614010806101b0602070c090c0f0e01090b040308030405011407140c0c0607062013030f05100212101d0403030209130e0a0b 77
    0x5100c14940705c51200454030000300010113008012806d03180c29414a81954041c006641032040c481c10700d1b0401030354845041c0700c1c0b0000641450400304400c064120740f007074099410b8403440c9081c5c469100b009550509454004204580e55030b9004d4505070402071689401d0046500582e954200e003080b00351030032030381c014108440c101034040010a611400d003062151803807410112182c0d041c00102c1d520344ca0760b4000101c480c2c0c0450080188088070b00118091407080000f04442a411030000c86403520440700302d8041404510440e071044422001845001120b10980e6103203030809001582d0303508400c0040e40d4260b038861244541400f5001c3c00301d0903941d50720f042400d100e180056240380001c280001010b03034079000301e031034204881004810300ba100203040c107644a0307200c03504a84442c0d0044400b8098220700b03c6002410500d40e04d16010b030090090085881552a51419000b81d8406181c40750004440442200d01580c1c5126001c8800c5080e806400c0d081402c0c1132011002c1005000c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 338660458 1250 338659208 338659231
    0x9030b06460b090d0f0c090f060807150503040804150c03023007030c0f06022107090330020102030108010c18030215071509140313180b0a0803070b 65
    0xc2c80000300101c01d44455080449803801c810360f00d0f15103440d500d112507400a08040700c4031000305810310a50018280304002c21410024542d0764124544d407000b4500c519003203070b0707000d400c2d1000301c2e88502d000315030042c025850546855901c041f11030b000c104242011000910b609102403c140d41403059650b81640801401207160baa8404a4165282641b00540b84207000032440d003098054248c0008075500072092140c0d6481c24200000607500116003e07282807003040300c81c4844a81504001e016040d5070391030200448c11940c03402c1c8280c030009246860310500310346005080c0100c201c2400c4e00811580056102e5140941c1942511640441a410301c0001c0c043c036031417591342085000c1100c0d0110b9a01055540941540c0a14407503810094805a2500d00c2078080075510341061080f03600c84c001082e5800601d0070b170143c4a00410117005455035000c60204a11508513045104400705004009010302c1c40d40c001500480c4954003032501038101050200900a0103030340242e2003802c0080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 338661708 1250 338660458 338660599
    0xc240703060803281101050a050916030f0206030621010c0210020408030d0c09180e15190903181d01090e251502030909100609030b06 59
    0x5540b00f1121300345a42d50403020349400300c80141341c1705458021001e2680c100803c0300303042ca072210300017800048605c43c0030761241c075000c46a5071039540c09007821207401c2041040c0030512542004103d5002a05180d409000d0107006040c20350718403c0c80c0c07288000c84000080c1084150806828200c40210442500b031040c4020440458044221406a226500001112040d580080d0b420880710380260701c0c1c2072005040003940e411581d0200648419400480d040c0c0c8110010204410707004448041602d0b200300075064418846401025580d4824240b4841a611402c1060428482907104002c0c007149000c894002c0086420081d000d400b410409210f42e41c0500142d554420350803d240c11081000d4480e55131404a08403518050204510700100c65941010020b40d2504031400243c40b03441c01d00c000c00e1400d070044060301c0485a850303d8000390149142c64211105100808041e04000904005d8000805042a04401900c81c9520511582c8410314480c81010f1542c0303801c003440c04240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 338662958 1250 338661708 338661727
    0x20115080a0609060e060702151501140706111603031805060121080406050306090a0e1209010203121e0708041a06030c030a0b061905060306060c240703060803 70
    0x504203480e079400a00c041019211072400800600161401c0c4605010325014400c0300b980c04070b44071900c4d602c140c60b4130003182c95501540e91091419100b482c041070008201844500401c000740103464051000010b618988102c2078030340341c1c07040a149000341c038081c2c500d508140e01032044c0b24402d01c4003c401a000816a55000e9850206000e401c0282d081034040e540d01815030800307150940d512013203180d00c8565613000a0490741065908034400d01700240004e019500d148103882d034600c81c4100801805009012110256210918460460004200c0e2001c0d04180c3c0041d14014401d088035040311303c040b142c1d051004080644500108211582030002043d0b0039a107103103600c00e80710b02c2c1c46000c3d201c8100092034000719181c01c81c0c02d0b0080c0710b408010321010114040c82a4000e440714680324550019650806d4218025281e00020a0000c0783d180c3c14094051302503501c5000c206c8100e010f03c81c200303403c040d08010021040342c0300c6000704841184c2c1401448000c0c0460b00055080c0304451b03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 338664208 1250 338662958 338662963
    0x70605040b072616030e010201090f0219090920010215071b021206010e010902070521070203061014010309030206130206041509080d08090601120204060e0a0b0102011508 75
    0x102026264000021002100c802420042ca80f0b010040000c1030360307021203500c10100030a0030f0300c094010641c0d00c82c0c0d0715500d50040c003d040c1c040750f10a00d0b030a010301996003040300c4130607181c048050f868a4400089807a0b02c2c103100d0020014014103604030f64001410114641c07514070302005045400049805107401070301016150000c3c52800c203222060440120070081c071507a510702a500691104401a4411000c10424103aa480340100141b60782c0f01e240d5501603100d0301070020280d620030841030321610b46920310032400388645d8440710700d42078054000038600001030700c9046204110500c100f100c074809150607114079a080c01c041c0010480b0f520060349811000388070f00070035007078034070b04108540d5258219030140c80d84008004c852004054001c000f48024041c040c0076115110000c03000d1030298188a01c6620b10b2401021035a00300b940d4001d920300c414800703d070400c0d00c079000031440c460004d8060744914000e0b80002240404000028290f410040341200b440c151030b1000c1c0f0659401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 338665458 1250 338664208 338664217
    0x10801140f04020112020d020712110706030509160e15010c11060c0c121605030106151101090602040b0a1206080601150e270f010503030301090e01090b040c0503070605040b 76
    0x100050000700359103e000580e40d07910405030001c612407000800701214903007503002e420001d0180d00c1c10703154014100390954040c00b240d0007ca20590004200300a260700c00d0b0000b6034050040c005aa4000f00ca01c10008942c108a812031042d89030030f802081a0f9008040b4059140f440911701040d0346956030300c1c0d001d01c0c034105242141c041e0800160040d480c000400c0104e000311070151402c1c0c2501459149283c81c0e0404503664520208814800245450140507810903181900300b03500003841c00290941e0901078550540e00c042d500d840d03004011070098030141c0004c0c1003070741d01720780e49074000348000700185030021030900201d19040050080700740c00103c0a040d104055040040c07000f461905076a8000c0d55960503900c007000c6910344000d80c801080b214440c0c10008040a09a242d0510301400002d00b40601c0750076a006000401035651990424040039100c10300000c0c03442c1003070b141c489407000300321004c0d900e10ac8506410005408c0400080c00200707200c0c80c0c0780b81414100503035603c82c0d204 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 338666708 1250 338665458 338665471
    0x30f0a0510090f021b07080705040e100e0a1b0e0c21060612041101142106010c120f0210021c020702030309120a030906080708070c060b0d1a01080114 66
    0x143ca030368102c481e45540d41156040c02e401c0c50307081140c005808034143d40da200c900405480d405403540000f0b4a04050140c081c5850700c90b0090026003000503000300042c40b100c0c0c0b114900e0302c00c1d103102c036001c5050319011000e070080300c5095014a90030f1507688002c140000c1e0020312101401c1000030031402041164807400104011141c6954a60074005509401500180c00c8140c2076041400200981001650158542070721419801e0402c01d04070840b600480032100000d1060145900782c8050000301c3c40d41c41072f03050400a84518190b119181c2801068103800049130b000319040260340c4d01008164420021134105600c0d0040034401007004c0316102c503a0000050700428100c0440d541070054900228000e41309020740d00040c42038554a240300e25060340803640c240300124402c0c2c0308600c1244203051035202c0e007049407502142260004056542511136a40d50004c07404155503800045001d24000e01c100c00005000c15480d085d034a8043e0b000c0b440c941e240c0100328840421581d2803d1303001c43c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 338667958 1250 338666708 338666711
    0x70b030a1b0e011d03070b0f041e0305070308070213050702010b09010b0307050405130b040219030b06040608010605070606081606090b0a1407030c020301020f5703030c030f0a051009 80
    0x1022402007850301b012a0005004000041050751a8004040113001103400720b0103c42c8020551500045803200305000142164100c1a03051011644000c0105002c074405014440300e8019103d150045400a6688000503511140380c80031602d05100503502400d40754801c545141090807000d0603512032442902c4c080d140d40c0c10720000700c00b03140d88600140301002e03005656581c2030318460120900e40c51510004039160000c403018609090301078034141c5145e500d038954140d003000323001c2e940c0b0b4001c910100d800c00c4e11018041024141400040340c2d120019215003801c0742400c03806424541550403417200258207000c2540035907440004d182c11100c02070a469921039681c24100c0303003c070724040080e4066000003203407100000c0c21001045010035249941d40300021074280100c01c3c0f01000251030024032446c201c0c448419110580780b1001c181d5203180c0c50030b842c4000159007190402c5a400d215240040204041100c41c40902540010b041a003000245000100300080300d000b8040d000149 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 338669064 1106 338667958 338668007
    0x5070204061d090d080a0b120a03020303070e040e0717100c0f030e0a02010206061509090915100e0f0a0e06130c21020909070b030a1b0e01 61
    0x4070044c3c1da441790551110040c07000070f00ba49050a41e80a041748100c039954000402001902078400d40185440c2e140001000d00701e0022003018902440c10310050501c0d102d0041240c000340e951494200066852200005281c400543c4610b1001487c151111f090960002120007510425503818461003196007006901d0316503d0383d0090159201c1c1011034680d2034a5403841c40000b40340030302d5900b00b204c0340d0002404080f0036201c071405a00040c0300c8040b4254a4500701d030380000b1030445601400c2c40c0101240303a00a0080c18403426801440c0802c6200320260040d44010003440d08565440c14000403c49450f440400112260310704601e00003200c00b07098529107800b040031280c41c619540d80d5000e0082c80000145558640d010f0101c6c045020f6220101540c0a1461500c0005400d4480142120900b0600c001e420600180ca100a0103903a8044031101c4811004140d1107440c = true := by decide +kernel

theorem cover : BRFrame.Cov 338489208 338669064 := by
  have h0 := BRFrame.cov_init 338489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 338489208 ≤ n) (h2 : n < 338669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
