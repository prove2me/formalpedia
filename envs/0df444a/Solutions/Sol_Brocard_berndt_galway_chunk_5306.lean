-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5306
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:26:04.404976+00:00
-- url     : https://prove2.me/submissions/90578e0a-ede7-442e-863a-c3ba8b86269e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 954136690 ≤ n < 954316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 954137940 1250 954136690 954136697
    0x4060c112b11100504140303070e13110405100e09010f090f0501050d1b0f0b03011e1512140903030907090c0e0906060d1401030b0c120103060e100516 66
    0x102004400d000c1c04401e40b09040407005040001d11000010b00140340041003540c07046200400c0404100c0c050004522441c1c0d00e44514522018680600085e050017280000c1c43d41e283c424513403a400c0e80300f819602111401c43e24020801c0b40120704940e0000115a92604a454080007142c50031003031607403500303a910420003082880704054040042d24001e1040a0b0880d2510228001092902d290354002e000d52071080758001e41d44071007052583c0701e0b5903c0004c004d00044014420b040340c5407844030080054840c040b001a00740170110b1010242d4900700801c0c44201e07071118481c003daa4001d0300400b41c4070083c00324685030106030507459510464071805103014146c400300300c9550710321451a046030580d5814254491050a100d4a00d1000e45015480002485060b10442e014080c1301c1d802000c0b131100c0700f1954510301d0030100041d40039101d46101a030a200c6e00030010a4540e2a0b41104c4c1c100c1408182c1c007110002050900070a400c841401504020811070070610340b8541041c0d01c4259035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 954139190 1250 954137940 954138013
    0x203090d02150f04020f010c1203150f0506040608150618030f0a1101180807090b0a12020d110d0b07080106020c030601030203070311060f0d0b0405060603060904060c11 74
    0x5442e604000085542100b8901c00c18007180250521000703101e0001030605122014450a0712402c070640841501d00c0c002a4072840c0c8050b002c00702404201c002c0c90885411081c0300c7c20840003810f03501960181400308003100c00010406220142000d20045d00680311980e2002030031640e10b20207181c80c00e010700a11078115000b4002c1000251345880d80d030808140005246401e004491f080890810000014810f03900460141c20a0020800078001c900700040c50707200a2041c003140681a03408000070145115400d005070b01d4072175600c00c400e83d20895000030581000c1c0010340c80c580002c03028081203c440b04128240c2c0d04412813078145d40440d000c4440c901404400c055481100b400025095005014100b0000b510425001c2803040014222810214080413a1030b054000c244007444544c0c84031408482818180301b050b4110200b6608a03165252080c00701b141d80802500050407a640c680c0b146004030b1044000181c0141458151008029010030ba9450f800314205050070b0504040d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 954140440 1250 954139190 954139213
    0x61401062a06020307022806050709270204150e040e0723040603140601260a170906070809130203040b0103030c0f020603040605091029130203090d02 66
    0x740000035001001d907001c81407542659640069007004d04200103510541c0300780d450441801d00f480c080c420704455400b11200c10b5041c40800d480003e0146410300085032010b110200c0260300c0c000a1b1551400d40c10844448402130310000d200d2684280303912081d11000b240900e81c444628041900126002d0013a030500d84200c1e52601894450050700c170908064208074662080105164400000c00018600e40d982d118622000044940c80c40240c0007040140a00c03104424000051940c4c242c8000d509000b4460040e960801c84401071b042c20929404801408a004120303040004050855070310f410440c6040095600480500385c4203640040c8010500b130154030940e44a04d40140c40b4141a91868a042c0c60140340c3d0201a00c141d20b1a508540158a803000250b0089105030f500040c01d2800010003810040351406081000b070809088120380d191010082413501030030804440b0242d25a000225042001c9645514490001c0104404000c004c00d070a100c101181c1c0a80d6822241d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 954141690 1250 954140440 954140477
    0x10903141507020604020a1a040e0612121207021f2a03090b06030d051207020c040c0c05010b0a050a09020a110703050f1203011809083606030f15060706140106 70
    0x101f1401c140340d0b0380c8c180130070080309050804ca00d40020007c0c000028200c9040940f60420784100780d403c2d226500003074640c1d01350f0281e40c030045d440365562014085240c0040409a60301c450f900c02080b4181d00c0b2800d502d1a0f10301e8660148030b001d040e28907031021780e000c1d80e00500580070424064910f80c05400c00500fa600303011488032920075199451920f40303008995a604103180180c403000c2144a070700303844502e50310380f0311440d061080c440d11030700d15048441c9001070a507500aa803040c040e4a0300d890400203600c1d0240d4a409841e0445005030304e42456a0303048801079111440703040d251041c0381c00002440f1004c2040c40c1044c0c5007034180e4a191004a00190141c402031040c40401601e14040c03040e03c10752640501540d51169039421b180071811016029041100500e020603502c51a139402c0343d00907480340d518202c120aa401c40e09528142e400d0304080c1600420b0801c8190705110f80300290b030340764422078040d264010380802944007034510fa0b9113803481c2400340301702048045240005050b02d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 954142940 1250 954141690 954141719
    0xd0f090605031506070510021611180a051509010b0d0605010810050603040611130609080a030e040506120f010c0f0c0b070e04020c030408030715020702010903141507020604020a 78
    0x101e844072243e0910080041c00301c5980482401d4032036015190440b4105003090005014941c101c07010001c0f800b0207030030300041d40414154040d02c00c40000d0080c1c03041c0103000101c0e0b80d0103c004580061555100ca0480c03001408141d04568008050400410000c0442c0c000e0505000301450800c005601c072030064a0480054803503041d100142d203401c022500d030120055512910400c40450f030202d4a02e4818204c1c2c210141240c00c8011540c0144101d40d03000071290700400c03051004240c150201d4038041d11b982c00005455014685990019030662035002c440c3e44091420303030486620000008480b03000301030520141c0c000a80d100e070590f030520f2107441c076101a180c2011507244242c641c0d83c8140c40400b084200c0036005602070143c404130342000d1003c0e00c020840319001d96038581c1707503140c00a08e03070394201807a6036070520508c58280583d0740440b000c015298404003401810595505462074451881590116501c0070740c00c01c550749502251240c0901d00c2690101a0b142d1101e0b2584081070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 954144190 1250 954142940 954142951
    0x1b03020913230a05060c0f04031e052d0303060112020c1f02090102060a0e0a03050f0c030301030303060303170411061e031e150102030f070204020c0d0f09060503 71
    0x1580c0d408100340315000803280070070354881c0800003011950003105280c0c0141e40408001d503500101c40314014800e003403015a603c907959000b550719007010000c690041d4003c03404050150501c551281e100400c011429012460300542180c040c1201401036486080341807151054001e90100074201c0084004156406094141c41d81d0140200c11400d4400130f403c0001e90701103d1040341050140003d40e07102140c0b8034011603002582d148128400645010406004250020310b8646100e80c04130000c141d60440607811b1401360782c1c1354040c5100c3c004d41d002d0300c21602982e0100000000802d60540d1010b0122171203629139040301c030300f90924800f403c0c000710340103004117810001a0125203094002484600004c6690074841a04c2030701d008100e40042743c0c0e0054124401092400c640f05d20320f40d0070fa02c0820420b03a00031010b0303000c000030349074045c40361002150840804c200c0c0442d5680c0d010380d40e4410840c0f04640005565900042c15044090310f624041a0a09030205826102c0d0040341e00c142c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 954145440 1250 954144190 954144199
    0x504050f0607020d0809011407080115051e070804030b2d25020708150601080c070c030201080a0209040203040f111903020904020a1e030201020706050c06151f05071b0302 75
    0x200803a00c0e05990b010401001c00c1c015540c0c400c0d00c2340c0d075683c142110a000e0010b03999140c55940c1881c1c0e40b900c81d004019502e1051210510401c25001300da04140c0d030060700d4800d4a140c46482074684012580256000201001c0d081c008000c200300e104569400b5452048265540080000c070340d2101c40c0a0a48031300d000c0030f111510604680342403041c2c042840715603204a801c034603a00e00e0084d0420b0500e0820b00180d240680a000840da0702444594100e0074044440303180c06100d558000c00c01d002440020705102203c00003420100b6158180c85ca40030006c0c200f90760b030b403810341f90004001d66068000c868000601040e00d040f03043c0038035a054608883d440a414550a5808101c84120000d004a82c020400800822401940c540c14030030340382ca07800b000f8a0f007030851001900341409a00240c08004dc18040d410407040000740043e084481c0000000e0a44d482d6004a00d909113a103520b0400380d0300f01d126035105030341c0c410010500c850003070a40c4a40185490764001e0a00b400b4030019512 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 954146690 1250 954145440 954145453
    0x9031006030b150111010c0503060301060602030301051807020c1c0b010e0c0d020904090c03050703050c030105070e09070311030112140a021005030a1815050f190b0406030203030d0504050f060702 86
    0x2140f1482802803600c1d40141000c400201000c0790b094296130312900405d002902c040244960b5080034002c020141400f03002a60940d030621022458140241c07560103420f5282c3e40108000324003c1c000301c0d10044002c0d115a02000b44036071580d1010510090869101c4c1d20240009480e42c0c44209940c061001e90300100e1804441090b2400603400942200303620960707a18030b00c4005800f50348036900851080c4040c5c00c08a1a6080c550308044005484600990400307081006d103640c4804800c1c3c0c461421584550140c58542080f8014000c0c0da4045400c83c4000001046041555107800703040c0c1d00c500941e04407010141d40c09034651140351030094102d00001d200c04036086c0100003841c0d21040390140041c0347c01141c01404c010442c02e500c1074441c5c003c40714820180040038090140d02c514403000d04520b40c18200f100d2008094101c115601c02da640d402081080d40e201d4000c90003e6400404070b80d220980c0000700c4009000a0b502250107110380b0300d103850420301c0491480e20951103034014090 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 954147940 1250 954146690 954146701
    0x10311030625180306060608090a1e050f01060b0306150c030304060c12050705120f0912090a090f0203060406050d240f0219020610050d08070305040e010b09031006030b 74
    0x18440b200381c8400140184115081d0b0010101c2c0b84401c0114003406020a030366150200150108101a0002d181900941c1c90362000c155102d14a0780c41140c40c3c140b4440707032829070070701d20f05020380f21200d030f9155401e1200c001204144c0d000510f0154404846480c5040503481d4080ca2078401e003c1e800c010390f082840082c0105209034400c44030703042241400c18810300107404203000ca03082150840c001c81e00210351007140800c6240da1551220408110300e603141010200550740f1395880c03001c07a010b00000640000d0503194540d0080042503004824442c042e980d2105401a410071144240103a140c040009076038601143d042c10529040391a1800c032440f00102d0724841402d03a403c0c0724141d1303103039008144c1c80b00f00c43c4010031a0700211285102411392401c0003d0820802515a0f000e03e01640301c2840195222440d0000c0258040403d0b0b5031801c1c0fa01d0296000e0050380e1040107644001000002c110002d10000c00c0308cc01c0c100e003503400d41207902d080381342110500d0001402c0004004009403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 954149190 1250 954147940 954147991
    0x13050109152301051e03010807090506310f05040b0705071502090316060c03080f07020d0302070c030c03150606050f03160905030102031005030c060c0c09100b0a080103110306 77
    0x52681c0410304d0050b207450040c1d5241164058601102e4000709000001000791030001e00001000e007070750070814031140c140715000499800d64081c00003200c1e01552160b100101171844034035841d90000d902400141c1c2100384100007054115425a029462140040c40d03980c8241c0468201d181d110445241040388080a81c00940124484170781500c1428462094042e00da10310100804669135045244403403494001c0540c50701800c1c244c9000c4091052090040d000b180e0030396003154a19006865500d94244174496981c00e03480500070090b032220110500c0b4031500f00c42400003440106100859407030074102e69501c15068017400407130007413002c510521882610b014180d03c007464013403c0561500006422030340305803041c0300d00d00300c105010003441c00d00f4810042c900008541040c1001c51b120704840d11140c11020561240200c1c40006200d501510f071450b001d042c01e59409901c8844103500549817003002c4c0010350b804646415201154900080c21502c5070400340d4109441d100b0480340348 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 954150440 1250 954149190 954149249
    0x40c030b090c030304031416050a050402160b010305030c0d051303021309060c02010c1206050a03020d0f0b09010203060a0503010519050c04050306090d110d05090f040b1305010915 79
    0x5000500a1140380c0300b1583e070803c00380001e580249000c202c40445899814501441d080082c0038114003101c0c2000190356480641c81207441c143c40c00360350740c40114403c6080c544001c80040410810390000720138084000041c03c403000d200c008440f072000c43d01c030094901d4010504000e07071038005901e0500050800c0d100c0e070080d841c1200000b10746d05895980391030030f581001c0356410050b03660b50a441d0125500803c16082d9010031841000801d04040100d001c69051b4040a800b0b40080c583c01e00070041840780002e00550050a00307086403c0080c02ca41c003070345c0b0039204036100b00108200801e10780350600c51240101010314078412034601d60300d002c81c050a001440c0c40071a1405100010b4152001c0c0700c0d039440b07507122030050050f0604441000d00300500b05000d0310340e2544002c0071134800f80d40040c1242d0b03d400040750b0a0205801c82000103010304001c024850704a2070085803455510f10980106058861141040c0f24502100f02c462818070410b00c101a583c030740c05071903c082c0c0c24194106 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 954151690 1250 954150440 954150451
    0x90c0d082a0a020d2d0201023003070e090702060403140412020d060b0d0302070f06051c1505100c05060711030909060d230609071802132402070806040c030b 69
    0x105e06241240d040c03425610f00c0002c162080c00c40d14140034215a41445021109011a804250050f0012040c00c9068501907404c06c0d03503080010200325158011220540507a80041c482c80325480d0500700291111001d6604901080c16504681e000980c5001518244e0301600140104909541c003001606010b03c90180c6801d0740e40c00704113449448008030555140e002c0d4000340007880c5444020303040d0720321035803096080200512018210160000b0711540b04007000d4008904040007030303034403c803c00d030f9a808141d000820b441c0b00113403140c0024410301c50900540075115542e035031050944011540d28283d00d4985c0040007140c215240c00740d592504218040e102c2541900141d40e451740341c20076100000d200e0404200c000d80c04c1e440030452a03501102c1c980250105918041081001201001442c80d425401142c2d0941d04a0715000d514014080c06100c100c1403080b406501e0304c500e40d8420b074030005005d00c500104480d0030000d0520b001e2940168081440341c919182c0b5040d8a801404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 954152940 1250 954151690 954151703
    0x20907030f02040807170316030f12052418190b060c01150f08030f0304110904080409060e0c0d0b2806031a0315090c0d082a0a020d 58
    0x41d1480301e001d4600c0604003508401c002001401d0800504034500d403654011a0900e0340100039400c94629402d188074030107070381420003401803030b00240280c501e000300620550700c00e4501404c10501c060607817103c86a9080408040f818900c107002440902d50b10b501400c40c0c0f803c500c1012842c04990144d509403600706640f40013550022000c00220954410181c1000503074640d0f442429400a2092120040680041092540707240038121522405100c3e41c1840e0303044084009003d0028140d0310182c40e04004013424024a4545001c011070307089401032451031b40c40c10740040341e4040d00004140c040e5249200345030403c021052000c01a090302808540c00001d20f4030032180b0308156202112681e00c0e07071640d0000540c1403410003000c80d032589400c1c1c003030024a6040e54220340c401280d081d0340a400545a01407642e2003c08252411041d4030031103800c505542840c3c003c1c00442c0c0040d29a1402024510038212111600c21600401c0e201103825903400501c04407006140c100400101c503403250b071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 954154190 1250 954152940 954152951
    0x12050a020c010813050f01020a08060901030f060f021605062a16030201110325030908030f0907050315100501090605180f060d09060b0306070912051e0709060803040b0702090703 78
    0x15145414107244241b03c07045603401040c210401034104000a40c010000d84450381158915101c1c1142200f0714100640f0305035072484129000e201540480348019040300840041d0801483e00c1607480360125400303851100036039022000641a11210130758800580c03803035030078401c403846d045020b034000c200120207640d60303215540406000034010b07622403498100b0800d01c50070003100171107005544508a4040515244da000b00040b001c2050700e4022203260051845075031000040303480c001113904140e5040c81800c81d141c16600c810941c451160348260303440e480d955690401580e5081d00c0d805074070040b407801c0c4202000200c048001c80f40c3c0c103c0041c00e4001040c2a5004100282d20010a40f030ba159182c44044040c01a240121800080305500420103854080802010740301c0c00d000c0c0c0c00700030300c9101461041c800c0c1007008810000c03400d03100d150721008030350312555540780074810b00c43d0450030030030300080540000c401e5500310344501100300d1404c0c48907400c200c0350350300c0188091b09055466 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 954155440 1250 954154190 954154193
    0x306011403100f0b03040c0b0f04260303090a050f0f0a030c08090a03060c110a0b19091b0303091205030f0903032802010f0b0d0209090a08030a060312050a020c010813 73
    0x2030200368010b0540c040c0711170340c90415051419140d10150007501c1c0455040000d41450004002140d040f01c116020b42560155415007007940b403161344400d003000c1d10011041c01100b0601107a440d03074140c46001151603070705040a14540b070310035908201400703070081021440403c1c0251500700803948130b201143d01e08581d0300001000c4070703c0c580054412507520303a00000b00740e8020842541c0442c040c0c0091032003000c181d480034030100c0001c01c0c5209010020801040942c0c540e0011045143d1182020341d9540c07000000080600082c8000d0303001074503007030000418280345000c065000390444055460110f910001c888554480c410054140c13004012101201031401212594002e5100715404030701c1c4080303002421740c0c810403a0521184e03d07181c0358031042d598002045070078175410b6440308410fa41b0307011424100511800058090365000040000e100360078ac1c032034410340e0301ca0f050707502e4026004101107032076010740059140568001070401070550f004032503e80d40002c000d056400d00c8440c0707 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 954156690 1250 954155440 954155459
    0x15050a020312070801030605092b0c060935090409170a020d3903171905070e06180f040204080f010b10140901050f040623030601140310 60
    0x80b0f07540f00001c0c00040c018410482240900fa8000020340c001702101c40d40025580e040f406042402440611814a1304040d40d0090b0354048a15800c10000c000810807800c01e250b46807804265006038824482d05080054070011810a036116107000c02414030010000f440000c1400c008256810000c1141140320030f004880108007800c0d41f64003400242941c2c500c00380c1b001d09989444403844d05032149e608c527864005d01e00c441010b1415201c04038009890b003401e40e244804404500e11590102d000c00c200110b0440c6403c400d4070720658100850303940c1c514120760b900703008550a98480380420400410711300340b0344e18065000c1d0052a8021019100001134101d074842e521000e03241c1c004080400754100203204540b4407030300c281e98160580e20191002407070401120024149003e01040c8602940d1051082c0c8100324030701e81360a5640c3d40c0ba650040c2c0403070504450102c3c55820303000c0c0c0810702c0e40ea04055a00034501078441004e0b4404099038840d95401c01008221040c0340c98a0000d0b0321400b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 954157940 1250 954156690 954156727
    0x150602010b0415080c2103030c04031401090b0114040e030d0b0a1d18070911030a0f0e0c1c0f0b18010c0915030906050901051f15050a0203 61
    0x640002a96120420a10040d0b44aa0b00c26140c60503100c1e2003004060404101240c69500c03c4a00c18048a2071180c2c21408507084042041d2600c000310401ca50701d0303400c50052098034050b00f0040d40c00415004400e003680c211090044c541c0441c1c0c00104280c80c61b5034a96403000e500100080340b00c1c2c81780400b4a00d16000305100c641142c2d02c40d1309000c010b05180301c0c401c015140b4602081d00144172860740d224003150150920240010b8001c0100221005101d0340c800341c540d4580501482d140703100f421307019400c140c682e0b0708c0f03145c505105140004018441c1c41074184d00b00340900741050904013000a015404074102c203988402c004080c000601038546026014803601803c215428a803466540d04170701c107c6d090410380c0c5440c00000080e904a50060200d8440a500b5049001c4107407048014011842c8010301150800c3e061200b02441900402e200b0b08404819110240030504002034040480c13003401030b071a20f4940325240ca640f143c802004070012900460b07284c0a641d258a0520b42d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 954159190 1250 954157940 954157949
    0x9030c0306040629030325080a0302040f090c0c0326090f0c062d0c0a03211503020405150a030309142704150c030f0f05010b071515 58
    0x15070f20032000149032030000401c2844014132002c0c0450010701000720781e5074400c6040086180b00c4036000c50000c156484820702d11b05520142040e114485000d001e00079400c42d0180c02c180c40c08502d004100c0e070015201c1c040003040141d8501000d032855807000c0d21034011aa001c200b01440c1106111508417001c1006805030030010010f000141114900e00d0800e01c0020302e06104444c1009003041e1080e402c40550b200e201110070710180003d034924210a980b007811100b810302d0084e0481d44003855040188a102080c3c00d49016000380c0c51202e0b2303101100d0328442c10032002c1529074418009400c195225030740c4009440d0f604141d03020803000060742c50a065108400055800c001170015003146d6000c01115401524110803840d03488070000c10100b9801c05050044921030009010310908900da0345540c5400e40d020400200100001000340600c042900d416038246510030705216101e1052038101d50317a0140c11803c0107543c1c0c2d04e105601d010300c0b10324504151200c41c824404000f2405c417a0040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 954160440 1250 954159190 954159203
    0xc0d06060e1305060916020a020907050a0f08130b090a0602071b05040504080405040b0d0c1e1706010608100513020301030614160309020d060e0313140102030a0509030c030604 77
    0x292100000c0000500001034141d00c42c41c140303414030615031a0044440e811001d007512801000219000c102d140200c10748021303500c1105a002e100715250071000501ca8000750303581703d608800b9203090950700018181d4602d0341800f420825280850740c1e0100c41138110a4080640d01040750640700e8900baa04a664162942e040441c40700e03800e1009021054010903094905001602e40b58650034068091031040c1800345843e82c0b000840d681d108007040e039405602c040c0000c103a5846032940c500800164a0803a9525034011002c5040b04111202e584c00c101501e00501240e801e00c50112000440a05042001040078901081e15507941c0c40e0a090150340d10700040e100d41c03450801c241681c10354076100440d00c0241c0e041c460b004400e200721170100e840c1402c02160f0400d5074030100c0c090501c04907010f030040786042000f40c140309002c001032021075070042c079403007000792100e88a4101034100000c840c02b60303104000703905507980110083c001d510002020f43e840484040042070802030111001c5401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 954161690 1250 954160440 954160457
    0x309030209091e0118021c0b010803040609051f0e0a0314060601080106030911010e0a08060408120c030114090604143405040b091f0f03050f0f040b0c0d0606 69
    0x11000d468a1900400f401c1c18024441c03514003072030354007000c5072585004c3d025084003052040d003020314014100c20710780d20040060ba15070796000003d03200d80160003500c0000d600304074006244e1030a0000742404100101414401d9441701400307a07487d00c5204401e41c2c002003000c9000001c100d1030b000f100044103110010704070318941b0788001000c0d0348058008c1020b040c40c200d90078020451031454103804100a0030480010032940c00020075044ed1588400b90600c5050200020803400d2005403940950080070710100c0e455036861f4282d2400700340034030842200c0107041d02101e461b166150603007105000c2d00c006000100d00750b04801125040301c02c661183c00c2140040b1842200008078042c02100f20100303070b110204110010b000f0720440c032600790100000f04d400340242d070710134504410322034641088142281303010030302400f5250460301010100346043c0014650400c0340813503d10414491441260540e078503a505903000034040d180b85400c0380c040c00070982c01c0341c85100c0e0070068070b410b8488540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 954162940 1250 954161690 954161713
    0x91005030f0a050d0f0512072106030c1d0a05150a170601060306180504021c0b070e09060f010c230c03160b0405010f03020f07150c02010603150207030903020909 71
    0x64444e8150b414010405440c80c01c2d04590360090541d03280e43c11984945200351200c080460320b000e440c1450b076107843c90940440c088244039038441400c40b4410002c40104551310201e41040d0301e02401c1d140341000500300050100e03085980700d1603024892030f07111943c0c1080d840102d04041341d150010070240815408400d0240070810000780184101d00d018841d0508004081d15185034400300710178a0790b01c3c1c90200e421541d4040c0304d07624030709051013a00c03581406410286820a4142c1e4900701156030103144c10743d14103003a1420b41c400d40d000f8101d4140c60040c174004407a011580e54040d41e941c1e001c0f001d400e000a256422140407628000d00030800113884074100350a09011075241440ca80c2180320402089804a0030f843c11036501342090260350102c040150041d11444100204800340001d80e10100324500b4204c0d56260b95046082220b00d00098043c0d00321241804041c00c85200f84c0c005915455a5400402100e80310b46004150595240d0200d02241c40a8640944640006a1503039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 954164190 1250 954162940 954162943
    0x10c03093210230d050f0105120a0c050d14011505041401050306131a160908010504020307031103030702090c07031106160309080c0f01060906060518091005030f0a05 73
    0x384000403100300040106840c005407001c40020a04621181030360080200080020240c9403003084d4100140524a0060f0303003213094007802d005140c07180801d1200741c1071b00c0301d0007d04510855880614110352a05090130020440320b0410704452003408110200c040010078012500c1d042c502814200704582800100410741d8160802d080d420362070b4030010401c0c1d81d000103a041d0441060b2004120705802400c048801003001325284c581201654140540c4a914208400000c403603684d4600c18680c41d102210700343e80b425580654144e010100a0010541e100403140c160000141143d142c581d00d40e01048030a902111800c8a8800208040d1300b0300d83c2021071002c05a1140000c4c0107949000200702c5e001501c1201080d04040e56260614200100601194240d05071041140c401e000c01c2d03c0e20740c0c060800c5010302d00403141040c074000f5069004806480b0b054510003143c14201c15440140900d1031001400d804c0c100354200d50010f220348080c070001c00c002c120700c0060500c101d035605005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 954165440 1250 954164190 954164279
    0x1209050306071b060221040b010501081008030a1404090f020403140319080712060e07120519090f060c260c030f0402010e100f11030301060905010c0309 67
    0x307200348103c03508100314001c180c407070900515902800060700c490340440c1d80303040300300c880344070f031003241804070030b000c10b004030b141455040361400d91f02c03002550394007034151983d00318138840c041041d8030501034201424014a0903003034060031000f4072800c003503441031607005543c00c80451011081d80014148244030b1104003501e40003100701c000310700d0050000303400071181072083c0c4900c003004501000300340307014810803030301c005c1403801c072003e215460b100c152201c4440015100c0c14085100c9050400c0d2442c00ca000311b0b032103040c01c010703404500b0015502802c00741180c4442200d49010f18a0402c0010381548291a10445030343d41e9070350300c86020403440ca0607a94207019103414441740c01c100164040e601080f60362150044000242c66155880142c444420403140c840d80302541d01220081141d0000000c02c40041c150703582c00054100341010764a0384801c0c041c220000d41814024001c0754010008400301c14801d103005128030703542c1c0c58003602d034448680910304000490b00f200071034401041c101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 954166690 1250 954165440 954165451
    0x170a020405240a0302220905010903030b1002070e1803120f04030906020a110d02030109020a031101020c0d021c080f030103150c021f05180f0d02210a14071209050306 73
    0x1c0d101c00d1030854000071005074000c55135150350b00318205060654001b031740010414070b0f4418000d00c100340e0203182c090003805042c01b0107030290803488110700d070309440041e039002190311400c03c4098588500d4030480c2079034240071600104e4070041240b40841c28410240038400c3c00072030001540ca080a03c0c004140c03107240e51280e400c45d803042d010400443c560390004494940e04403109503603240c6c01c0c40464090070310307040c3c080c1d800240d51000006006070600d1010303c00340301f42c0c05d0f41c007920050302c1005450700b42e940c0065003202f0b40500442d280c0c40818050750b03a03980641c2d0024144105003540d1041c540c0240c004452800c05906030f800041c059009074074102429001800c2c9010300c8042506c03526401001100d04541c0340e40110300b0810340b041c01500410402d0b411b030344000c403200504a95480d0280640c41c0184102d22004d10400404009a00403090f801010340c58408034410450300b11030045005908004108000310001e00d1402e0f40640080481e100e800d0740354545020113040a000501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 954167940 1250 954166690 954166699
    0x1203041401260c0d062403111806071419031404240513030f11030307030f030f1805060412021b150426010c0315170a02040524 56
    0xe4000380e00c060000d00c1c0e40c4501c040f120a0386490381403440300c016114a81c004400300080c0c0390a0840740c032550320005c2e04601c640d01e052007426443d1200b90740e248211f820840b1107102300d041106013458200000e00802d401103080800200c0c0c41d8502c0c038104240040807900e0300c840c1c410003070201030b080300140d103041001c04407290406292205070301048507841c090042c03200c540b0403076039440d50143c01a240c1e541c0c0492150f00c5006c2d140c0ca0810a150502c2c00142c4241003401082c440d1403170000100ca1255600d561861214642a83c0640103403006032031034062180c540c0707400701c035284480031032694030780c000c4008082506007400e003500810180b105075000c54200300b42900d02c07042030804803003424500396030b040141c1013440b0030041c580c041c030f402c03010f03048a541401141e0496040040085844000000c0000440c0c12805404071010240c4007240075501d00b100300002c4840880d45041c660a04080e51504407003680090304440c411140c500e40002c003e6101d48400c50409004506058140d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 954169190 1250 954167940 954167987
    0x6020d03150e010302060703030603060c0e0a05120a0305032d0f0a110306010c1a010b1210050f04051801290f090c0a1e030504061107150203061203041401 68
    0x502e8603080c5405003c003030702032600041d4140030540310b03a01c000001d44d0400c0d4100041489404001c08082c803681c00240300f41c051000200d544e1520740380034101902541c5c01090414520b5405440e60341009048084220714441e00051000010440c07407407120600003682142e180010564854810140051441c00d2404040d024404000400c130b072b82100c02401c0404010341c0a181130300740708514410305503481a41c040001617855904000e000304040d0710404144954074000703840800d13070f40d03885404c2e4045c84105a44801d4203041c1c1c041074010488035a2042488518007061f429541100440c50380399850000b540701c8855614840d0010b04001c4030022880c610311700c0016500c034805480740000d64000201c180f0420b025840c2011000c8800040d03442c0c07000740500142c01454201c0f0242c990b1400c080c21030110703000031030460300900d601c008071070400540440075030003c1d000102410740105d05100740b152000c404001500c010070089841c2d03281c03801600001803424180201807288041060b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 954170440 1250 954169190 954169199
    0xa091113090c0c03030506040e0f0a020909061003110a05040c0e0a1d04120e0907020a0c0905040f200a12140f1b0f040e01151413110d0606020d0315 65
    0x45103c20105803d441d0100b09134586000140041c0800d10010846116162a25000e00000301d00c0f01e80b2540222038500c010341d60201059110003080b01c0040d4008485481800020443c0e02240041c180c003030584e80000340c42e1401300c1d080f108841d01d03900c04a245209564914580100d032039014140e8407034521601c410030090212502d40140000301140062195403060f0b80c4551211601101c0050040e03c05090100010351101c0300f0001c00d8540c40d115100204440300b260280034000c070307400100390b011012151a100380c0b0100440c0418410300721245101840e5403252800c00c09808082e1050381618414544661030400740d00130700c1180c6e00b022901d10343d900302c003285030303980c0780c15514010581030381c0305c0002030b40c6200c101942c5600510340700a082100e10158050b90380c0607502010380300082c1d16006070310507803080305692641c0076404040030074414a041e04880f03031403400f0501d810b050421040700a819150503400140051303000e02000740f02583d044c0180e1005003036107036058158038100b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 954171690 1250 954170440 954170447
    0xf15060903020d02040b0301020a11010c020705010c0803070e060301091a0306070503062205040c2c0c0d06090204060810170a08210405010606140c030405010309020a091113090c 78
    0x3521000c0e2140e142028450259112900941d0007120020700071551006a03040c064404c11420014200781e628042e00b2120560000038000207070394058507051811025a510100719510040c805020400eaa00c00c01c0200c0c0c0305e0101641c00390600150116a5844401105003a0a10300360f0035031080d030143c0248001181c1000480e40c00007401d48456512414504841811a50300f0101c0c00100303240ca000c00060041e00f00945040d00d88841954042442c0410603860760090000c20514414030300b00440c0c105121030b001022003074481100428000c0c0d0381c105117001c80e0040c2d4001c402094903001000b200642c20081c0f04058a40051141d0380201c481150755990203070340b0001404144001656001d01c0e2400f6400400150400305100c3c452038240b0307080d17018002511034280031854188031500c0351500f0000b035440c541071141c01542080c0c070f0b18004502414a194090f038109601c81c8010988007028020b60b0007900800404580d50300140402e41301c400c0c0d16078042000c883c580028003042c00c0c0d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 954172940 1250 954171690 954171707
    0x1710091128021507030618050f0f09120705031801020d0e010305060612090a1518330501050f04020702010f0e1908071d04050717070f08010f1506 64
    0x25464490305000050003649800c0304403e4203510b0804020402021990680000341600c401c8020f01c2d00116030b034081201680e001399403c005541c0901c0004e074a00d80c940b08000e52200b8080121103280c444042001240da2190500b5a46900002280d120f14514a1408110b40c40c0070720050215000400008288604000540381059107442c04a07400e50341d50406d90348a15103030303191050142003041c50141d80c2c100f01242100c0d1003035420382e07144d11041c0522036105900d40d028518000700b411590390481c2c10490720101c060700540080d0721f4003030700d9032010018040c646061000640d54100700400507001c00c0b00e05060f120f41d00401c81400140d0f40702c04413181282c1642801c0419555900c0080c4ea0502440a1518403900d190703000240040d0001e000b40c2160301903146071216680340c60140010800c11a00034001d54030038601003224203540e00700346628103807101c199a03040386c860000110b0015240d024160a0391a804c00a6250406102d610800c450078030074551341e41d1400c40c0c003908810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 954174190 1250 954172940 954172987
    0x20f0a0f06030e031c1b0914040e0316030c0b01050a0f06360302010e0402210903070203030d09030f02010504031202070602070209070305390a17100911 67
    0x50f1a10b5003006034140c1042900c0040074008661485200703407040b00001002982c403070140ba5500c011070303184520b004c0c03000441940c0b501810500148121014003000e0b00d40065903241c0352108014000241403141d101e4070109229036191f80348018035040c11800d03140103800c850303c11102d520b0104840c110344813a4030100c030110306042c2800c2120104034401080e54242e12400440d40d81012010000002603444c1564401d88403a45601c0e0704909000403800b646100441c08507200d1000d98050004420302d079402940401200d00d0504030340d0120341560814982e10700040e4840740f541c010076030040015406c07030321284001c000303d1034961401009005440c02010741c1650000f20781c004c0c400381d0340449101e5500034040e001c5500b8400d10080c01003804650307100456048003c5030002e025100315510b13056000303e5048400c1c002200c1c00b410644d204c0c424203000d01c5050741d256010803004d406110711032290b00502c2c13544245000300e12030a8030181c0c9140107060004105030006944d89116400c51038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 954175440 1250 954174190 954174197
    0x1b011e0917120a0815030703030201020c01110f0409091509081306020d17070c170307020106060f0e310509190209011701140c030601021002090f0f060d0603060504020f0a0f06 77
    0x142c80f1a0185c0114440c100300b6141c060280d50004802d16805400a10703c0700e00b0700d00201b1500e0342c100a1704070180035180e27103030400050400c801c02c8940c030140c0200c8d0030399016260400d01120010485000c444c900c40c0122601c40700400d034000404030f626a004001c00490028107446c1b0405400100b0b0402c00303000c4a0f2103100d1a50214106501c1036441048982d403029022200883d0815010556002154003000541c20b103040810003e2048001c0030700305100c2d8903805440215001008000040111030302c0d440303029000c85900c10008002242580302000400250600b080580c07903050010404a1204c039030f81c10140e20780182c0722803030010f0440e2108030001e80d07882d50b41304003d800340824801000d4501c1c1088140140401040002c1d80500c00c240c0072201004d4642c41320304283d0140480c0301f90300200801404149041c4010032428400009140f41c0c5803030b01032241c92049619942090350f92594502c104011805e26080d8005094011101000040e01d041c0c03165500714845c0c010031042 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 954176690 1250 954175440 954175457
    0x1517100b0f1e040c0203030f16080a05060d060603110a090209060f0c121902060112080f09010c060c020a0311010207020d14190b06091501021b011e0917120a 69
    0x795141c40a82c107400024414041c82980c40c00095591f081500e02c460118104400300c0c0e541c6100410140c0c5480f12915070020a40c0d4400c01c0c080205002804103030070000d00c0801000081b11031113540051403140300740c090440c1c81c1c5414031809200540242d2025441042441100d07a201d0098030442420380c1d251555900100c0c0940e4101000c2c10004000e444001c100d1000350709505031440000d80d0765500300c0b86c0603a41d42d11100000c99001201800c1ca900c01c214201251807205c00034580032106040600001009507103481c100d803461151000141c100e10b00b4842019401402c07016807040c003000a50074810281c00041d0052500280100940c099009a6003102c0003889401c03440e0110a982d10108042c608000b400c0502c1250140c2c81802560300040c1146803603412860101030680c020184107900b41040121182c1e1000700a040c011503c0d040b4113841c01e0401d944a06004c2036440592161428000701c1325140314407207060903030b0490480610700769220300c20b0700d000440301c0c680b641a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 954177940 1250 954176690 954176719
    0x5190206090f01020c09150913080702041d120309071403071509080613060513051b0109180b03070617070804240506030d0c030509060a02011517100b0f 67
    0xa0149810300d40d50f00600d40e06e003048282d641c400c005006c2e100c41a01c044c0d20942d2080e061180d61441041c0041ca00c140500800740075060a0740500700030851070200c6c064801820086520f082d0301140000c0d05130f02c00204010ba002000c0c4504401041146a40b425080c0050300080c1c80e80e10502604070140074508455003c6403045411900500c0340005550791303803d1454a08d4528000344c04e05540c124103000100300b41c030020340d0121000c5604403000d0420350101c11710003040d000c9030b208507074100810014040340c3c0030208400e006000350310041c00114034083d4001e060514845600030307001d0085c604034082158183c07921031507000c0c4240c03904014030b030f40d185080e0b22036141108800b8846c14881c4256401c4010390342c403442c0190001c804a501003840d040d02100c00281040d40100002c070700f40300118640c01c0400243c400c007041800007141d0311140030740a10840c0d5035944000d14000c1c4411007011408d4051003074007442c0840003001d0010404000200f9075840300620b0303550064060035044072 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 954179190 1250 954177940 954177943
    0x7140d110402041a0723061501111516030e0607050307020a0605040501050613020406020316051c081008070b160f0204020a0c1b03020906060d060e100305190206090f0102 75
    0x1005000e0201403895181e040010b407080c1d0b178001100444002d41d41b81604811032540803420707120704244600030010313a0b450494008002402d00244d071f041c80355a0b00f03c481242000d0110540542d40752036690068506400e40707502c00350355804140141403504034010018000425210740c4a645402d126940e038940d198200d15106412501504481c80d08051000704903042d00094082e0304100c480546945064070102c0480c0700d28801e10015034810014811840404009034880b1801841a01d96032022a010105a69400c242e4180092800c004104452851141c49000b521520b801041d20908003c0c031060544641c1200c0d45104a03444141c204201a4440250a2136400ba100703645400041801820126007400200e4101e410740c40110550f5210801030740c200c980050500b40192903180900030503505c440c427010032803600c42901194494004525600503028110100d02d440d15600b011420907030540c003c0b003485c40c4000030540140c3e40381c40c141d401503041182c0c84002e5244143c0141d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 954180440 1250 954179190 954179197
    0x9060f10140d0605010e010e011209060f0c02061e010303020705012f060601030e030306091807030c0b0901030608010504030f030510050d080403050c1525020d0b010807140d110402 79
    0x2038200600014401c01d02d006a0b8004204959081c0c9414460035480390065520800342c0c3c407180c1c00100c04100400e8407000316001a44414001c140004142080080c0d510560350410048400f40e4090400d0200040c038589141c0b20304c04041029030400d5045903402074580300301c0e04c42c0038100204405a030300030030f0f2080089a140b000000d204226011001c0c40d03540c03a1881124030034003091170262410f040f80c6000c42101d11540300202034184955640c410032000d44a034844120f560710074001c0100c0041d0f91008284003420840c05510344500313a04000406840c1c050700b00c6050399040c0014040061b8008230168503882c002d043c0486d941e42c88040c4c110a00c45150310456000304410603100070b1007008001802036a00480035584c081e451001442005162080d0ba903e070a0420045412050000003101c003030b21000c544c030f10310ba041003600041d10a86c1c41200c1900c203103d010300100400e5104111b030784010200d2900000102040c000040d00c0340300e5600020b0500f1005025802c0e49550781d6044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 954181690 1250 954180440 954180467
    0x90d081510020601060905240f04050306011409011d04021005130612050703020a0c031404090212090717121305060310030b092d1203131109060f10 65
    0x202200040551070007940c42400b803042e280418000c000119070740c02c21846401d400309099050b10400e02d50f07098100311980c001e40030078000e040d01740004078840c0d03018000e0078000c0500110014002811904100d01070b4010380c03000b0018840c0b0303018140a691100b030030303d030f1083d0119010005c00741e000764280e03418840d0101c9404003012030040411140e40000b24405002c400e1101005140d4504400b0f400301d00c0b920498a022a107604c217280c0000344581043c011400c5400c0c4443d003419654184c03501030741c1000d02601c101d661100304220344c0344001c010b81c50017401c0395055a07090328000380b44103484082018a40122800c0040e0900400c0d65400d85140145005000c05550b03103001070180080c0d070038a0004031f4a0f14001c0022404941c000503c1d03190000ca444102800d100641d1a040121809881c0744890341c0104000304020302903a101039841082244068100c014492070031941c900303c000d150611890481c010b0225a45079070403502a03100d020341e850b98900c141e00c0005c4c0c0e2844100e002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 954182940 1250 954181690 954181699
    0xc0b06040f14160324051c1707030f17150a150203070c1203090b0307021f021e16020d150207030e0f0d02131a03030c011a0108090d0815 60
    0x40c0207160b242ca04000c0d031884242c2d44d080061500f003040c4525083c144500300d10042c40404800e11151422040441521820340c4101e02506900da0b2032140402e29021440322060703010a108040c540c0002460310421605d14241100d121a905c510004240c050900e11502030041d030f260900391240356801015281150301c4100d410303500003009689501454007201c21450284000460752035001240c0400d65058613844d40d40703420203060f40c43c1600700505a4045200d1030f9550900f00000000103100350b90110005030356221401c00301d07060000001c400b000c9a110030402260141e104d90264020700340d040f04c0380c0509214909000c2d5011120b046a8442a44000b0780c0c44105038100a1002c0c1ca12000d0b29541e8030741c91040204868440c0418000c2d42010458038201d40c4540c050340505030364000d40d440c819941a108000c03901e10f07000040a055160340d1000c01201800400001c000341140918148039249484014103484440e241c10724824004e1000200319000d03c1c40c7c4101d00c00f84000790 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 954184190 1250 954182940 954182981
    0x240201291206040507240801030f060f05040309062304150201061503020c071401120c1b030503090c0f0d170d0218090a1503020d0c080d050c0606010c0b06040f 70
    0x40198540d815403062074810048070480264400108000e60780b41c2501d621f40e00c5c01a0710316164004400e10750142242c0340d0365580300b003042d003028900c180f0b070059002e6500c00a02d1814200c0282a41c1400755079020b118044480010758070164408031020b0714051100344c00180c00070f110a9001d055250010404048940542c0d80c41641c0750340030700071800402045603109651190a0300c405807a030f40c402400a4000ca02c5510035011940008607207100510304000002d0301d0740e4161540200c05402100064800001d005043c43d0411403d04644003c460f5500005103120000d10820080c0000620b88101c0110201c410f00345038081e90000d9128003010341d582d05501e40e0020b0b20601003415144110f540c14040380e58440c06100b140e010f54440b04100310440e0841d000c1120402d240c0e13104072500c541503800443c480b0000e20413081c0360811900e902c0d40f03441382c0038501c5060901c0100b0a50400010380d082001040d02c02d60a960081d40c143d4001500c0124140c1c40e0b0081c104809002c000b403410803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 954185440 1250 954184190 954184193
    0xc03061b09120613050c010806150c0c04060b090301050109050f1f050604090212150a14030109050d02071a12071209120207090c05090906151324020129120604 70
    0x4c00400403070030b20880554040401c5100113455001c810f079083d981209c00c0f40c1a02503040c1c0c140000f0f140e4110800c040b900440c02c3c51000806070303595078010b0104418082030220560034240245800f50018231070a1000c1e01d400c848046c002c0c04024603d90721900c0c01840e10000398601d84803030015003000342c42d8650740c80d00d8261182c043c2d801001c2c110f00c0e41c14550000713804404610948428554000c140f0701d21396152019200714810100d401651656070740d241c00000403c1003046038094681500503004c81840c28003541c01180318445400d00c504c100708454600941032181c8140d10407a942494024031140300289002484252802000405000744142ca281e400140c9201110030410083c002d0301c605403001c946030301804500070340050440000c603210b4500007040b0095022600c480d0b90070401c50400031032102d01c641d409030850940110000305200c02c00c4001039000e000a000a00141c481101942500341030500c803d00d402001c0b610101107903440c0c84501e007801c2c11a20444980782850b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 954186690 1250 954185440 954185461
    0x50a05070e070e09060118122a0311060a03110307170901090201200a0b0c0909010e070e04051f0306020d0c02010c020d0822030201050402030c03061b091206 69
    0x19001e000d080341092000a000c103480746034451102d03030014108000c4c03610703000300540e641c41c00b0008024442c500113201203001c1041c81c00c12a0401c1c01014451b0781c1c0d0070f100d03420310410716454019200c140320000c0c09001080020f040700b0004402660020742c1e03400403e10860040c41740489005011900005001d441544030031440901089070507030b41c10b2520340d4104182215040180240410070380b070300b907104c00060025110020030320803054a0a41034550355160003148121203405c4410400300d0b1303460403410032038641805081c445000421506140b0005003148481c20502072240b44c03104001079115800d9401f2240500a00280424071502c070b00e803a401a411603022131040303d142c524264101481406517158004080e00035150301c0b4131042c02140e1b0420000c02036021100d868082c0140040702c0450000e40d02c1c0203600008540c1005d02c10076091170401c0304c82600c41ea100e10144404026001c01d2410343e007416080403541d500d42e51011508036440e00300900058001c040402c0310981c00d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 954187940 1250 954186690 954186703
    0x1101060f140f191a04050d150c0201140103120c15020c0c030d0519020c0a0303030b19030c06050a120203010801050108060916090504021906051b0a050c060f07050a05 73
    0x41121000e50300d038855000e010100c00f60309001d41070526040410010004032203182c025071820540041e15164a8a021520455000c40b04482e0002c1170103590f07a8258161141d441030384d085200138080401c03194150707420140113004c0640112000d0308100d0107140218100c0060617807180040c0c118440e4801c204000390090028400c0034041c01c0c203600c0b00c5190100300302c4443c040c10b48603a07061504400c0101d07820f182201440056200301d4503480795070f9075070500c450011403080d500410f80c0c03504003080c80056400c03410315002c16110b041c2c091000420265400c01618158070f081606c0c1c5030b41c1c810403a00f020160303420100151001002180454041d04503038140d030b201404403150382e180c00d0300b082d17650a12100082d130740e1040d000c0d0a019181c2160007254001d800103000441090300c244490407044100c0c7c5c0410301281000408082850b240b41c40a1049100e032000307000103030041c2d140d080e11400d042d685503100b000001681002035100c9029614034541090854410034610718000d40d4411 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 954189190 1250 954187940 954187979
    0x52503230603160e040b0618010b1308030702012003070b041a060102030a0804030c1106130e01050a0302281a04091409150601120e011b030b03030a1101060f 69
    0x1800c5001121003c4a0000004842003000010380554480e122003005040c060401a4401400c102d00d016211101e00f055000c0c205400c0c1c0140d80c0c440c2200359044030202c2e079003c804690400d110081c0580c4e040202340e8610100e440003407102a50040065046101307000000b03011100202c01e10003440280d60440111144600c1505496228003005a0741d038012403181000044000c0c0015002034441d50540d090780c0d116464594804805200046003500154403108081940c200c040100383c10012000380141003e41d44640094116004a0300c088408144d000500306002164620f15111019034402400642c1000180303c0d6050041c900c41c1c0d10902c1580c0710349060450b018000c440101402c1c2c0128003c0000701100e40780c244881504507001408903042c01807811710000e603418180101c100030031550f400007905000d5074501c01c0500301c08a0035034081610b4409000421b413000000c03a1202e07660b60801c1d04a09940e204030b140581402c3d0040d86241c03080f00d000050a060f4465900583c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 954190440 1250 954189190 954189193
    0x2090a08060408041203020a0212210c030703050322081201140916020a1b031b0305030418090807031d180105011b0b07050306090901052503230603 65
    0x15a032449000d541d01015500609075002c00c102c01c101142940e410718540c14030a00617221403c01e00d40006034407000b010914401c2e601b19186e0f009000038041c0240c00603c001408180c107141c400007030306940e4010713100c1c01014001d002011407164503040c0c00d424400e014025a81a2035203182ca00562143c000136810f920034041c1c2400444c0c505069090000504000b84c021021590740c000840c81e02500c402e1000c1c190301800c1d2420000c600d00351052500c00070500b00c191141851441e001c541150146144080e8154042d000d0002602c00302c01c8030101c0e440452282e030014460010740c002040c0c003000c0200401c3d030000d8010300b09600300c540d040810101c00814041d12001d0014450400d204043c0c0c10005444a40140802c0d8011500000c805900c10064005102c142d03488080404090743c028011403408010003400d031901c2d0100e03540c004100c5000384064140a82540e10070400380c5070a01003502c42d4803521344064030946c090080131803104200154607045030b4406010300b0041c2d4002d03019 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 954191690 1250 954190440 954190459
    0x1212021002030424020904290f090a0c110307030e091e06041e050a0603120c1208061201020307030902010906230304021903050d081e180106180209 65
    0x10020140300ba80d01c01c035004461042651907440c806114108000288598a0707400e20100c0f5171611984181183d02d001580a41c0c0041103c2540000da28402c5007841e200311610080301899031510301c04da42c2c000c500000081036181c4a010b0a03030b015040424222018031001c110501415440b20030222103000565840d8035503200c0c0e402c68001095130188202c0c900c2c540f0000308840741082d030b200c102c1c010000c3c10b0268410303109180c0704040d501c0c280d80981003070ba1030703c0090042c09006140f000da034100034202004451390035a82c40d9264480015040248030042d00002c0c580c1d1598550742054400d1200215501d24140f200900180402e00d01a40020103040000c0f13856400751540706900b4403440b50b06140c2036024141d10083c1c0d80002d008a80115074012000306643c000012031014600c200042d000304002058018001d54000348950200b0301003020303014600404008144d0884d04807604ca2000b40c01840210340034008691003455400b5088040500c5801d0b590702903c0d9401084070340884 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 954192940 1250 954191690 954191713
    0x705060f0604140103200a08010c0201090209060105040e0a09030c0605070201051816050909070f082b050706090c0512031e0a0807050c010e06010f0801050a11180a121202 75
    0x400703024080100607400407001c81002002146d01410a21001000c1c12900f03521280802c0c2035580381828540981c0d1a00311480c01c618081c4c1515074860420300e80a030501c3e1a02c100d5200c2c1003c042d00f20022617980350482c1c014544100009040280c009000303001c4c42c00c00c44e10090003803500b1101e2801c0c06000d61615000d10801280c0c01030440007110070b1200490801c0104a140760300900400349907c2048400504440880e084400420500018040c0003000350400c1c0020740e922020068580010322000709140c0e00182910051034002c480050448880e2602c0030501c03002740c01159202103140348044c51400000011301c504002945900e40742d00032241456440c1c005c05c0380c0d200100d90508001a801031254000e00740070041c0c140041001a0300f0111642081c4007038000d200307000941d02d400d00c0040000d00455400204a0408020710404030812071694004d4449061042d44020049055a914003924030007901251901a40120142c0b41405000350311425003809030140d081c5950 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 954194190 1250 954192940 954192971
    0x160f1a0c04080f06040b01140a030203010c031407020102191d0409210801050f011b0c080618150406050c0c100207050706140706090822050f190b0a02030705060f0604 73
    0x2c5c0642c6d400708101280340d082103a100c03406a804160140c02c008402030000c0542d600b401250540d00c0252000540c604900703c030340c680508000e120200307682c0100003442c00c0c1c000d20543e101c07044005290170b079080c4240390b51203440d5a220104156005013002d0380602400b032584480d81c10284000c0b144131a101c0019420b61b80c0d0030091152030380c813640ea0710700f003c1194010603503102003588d040c04601d1031054554403511454090b800c5001d469000c241003105c2f8008002081d845d101210700200094616504081041d51004200801e1240c440020586607079200054078075000f1840107590481c000051104000d42120b4819140d61280500015410703000d60040c42e07008005002481c0f5040580d2100710240100d00c000701c440070000c01060180d51803250000306203074030500051030910f01d002d0400a5121100c0b00c0c03288101c0c00d9103868803228464000800440d484c1840040d220504450700740d00f14014a0000382c1180122410040811781e038400c414400c1c60101e608001c40000d1540c3c20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 954195440 1250 954194190 954194203
    0x21909050703060308033d410310020408100501140303070609081312030f0f0504060e0402040504110d1803140d2a0305010506160f1a0c04080f 63
    0x20f003200d0000c10101c0c6440c243c56120401c030a2103030340f4000c0720019481c1c65048040103047c1200302000f05020602200c800000d0040d004c0c025030700c1003140504200c400075015068041d00020b42205c4070103662582d107007804410508001e002c401c40d221903035111010345544d0184003c804070b5103001c0010034140c0c042c5081581d03c84000e40150308000281da2044e009101001041c0c404513410b1002031185094498040b000e0320000c00b690308088117a02c3c0c06860803001d02c0103d800e004100c400c41000c0e69200040d074084903058648591480011000f040c000d00c1a608000c2e002410a40141c405180f424000e1036040d140741300403c10f481c00e00b0088a1032003881c11b0000c00080c601100303018010000300c060070050320241400030300317640046090000760080c80000c0703040700100100c0d1042d9a801d4410540103002c1a0740345494507965182d010030103900c1c0e8200034052000009240305100041401c1000c0c03d00c411003526540c00c20804c00e10054015224001480c4038040d01c0345000d040c0480d08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 954196690 1250 954195440 954195443
    0x30606060f190507080d1b0c031b03030e1203100f06210b1806100c0503160309171509012d0b04140f060904200a030219090507030603 59
    0x9400d00c0b0202151a486400301d044060410606000c4480070400b100e0090290f065200400210400741f5003116032200407840a043c14043d21300010300100e500700f14400510012220258030100081c5000d030020405005075007010710034a840040e02c0c4000900031801680d40c2e54201d00b91035601e203c0d1002c8640c1d1809040d0004900100322840d412000345e40842e000504036001c10210288170215601c40300e5204080c04200c804011b000c03843c2800c000c00c113815001d506e0490010020b0b625180d5a07482001c01401702c2c241c5c4440c58205252064414170040c105650f0070380d44541d0304012075551403d01c0c4440b11030110300350012036101a4144900f800e445000e8040204e4900e0070800c480e94024801980c0c1411a1506200e40345590341d4410f0300303411030720746c640d0b030109040c0012388a014a8004140502960060f000e000c045810021644400444202d1000d441c086134804180490138550009400c2072001e19201054a0003000301d100f5518140384c100182d540d80071046060312140e100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 954197940 1250 954196690 954196717
    0x23001050901060219060902120109020f040212010312030b0312030a0f020408060402010e031c050712090e04060f060e3d03082a06010f091a011b0c08070503060606 72
    0xa40171241098200320740d00f480e0180c000000c1700c003100d4001c61030700f5103980000e01d03240c3d640b02c1c4034000318a0302c480040708408082d6421420800405c8545262410600029110380a06010184801d01c01d811005c1e11000180c02e98080f4481d01c21061003d410a0f203c0b58001c904006592000e1001031081d02c04481c0408000c0c00b003501c50350015030f00d0b03441c01910030b50940201c039808500c0c0b4402494003000305019544503503072841e040c10220140e440e01005c0c4400c0000c1c0c0d40c000c00580740c01d41d4004c0c0d0440d0700b0003030004070b600100b00d01e0b1008111607072164072020f5010041120854006000100e000640761420450003c03208040c01c812100840c04035161004c0c1030284003284120340600b0f48042030300d184c1400240381c0401c1403041e10601f40044100da1107a4010710a25092040450040111100610034030844008800b030081603c0f00c118100000412140907140203417508040782600000da1044460325440144e490b92814020b190203440340f10041902c90078000100d41e801481181c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 954199190 1250 954197940 954197953
    0xb09010b07020a0b0f040819080426010c0305071116150302040f0f0501020f070518070507021002060a0c17040b0606070c0e010e060f0f130230010509010602 69
    0x182003400c035410085080c0d811988021010034500343c40d00090200074048590507880c2c0d8a0000d00a20305401c0c102105050b211000390000010030798400d507003d0342c8480103000c49036892844054011790605406003202e40c2013102d51b101290709644100d008100a6440170f21403041e042c0c030706079103a0041510b2400a10390020030032444030241100307080c090040c41c4c0503250966401081d440c00034650444204c00000001c04c000540e010005001c0c0941803001411030545841c0000e0141000f00704002a1140304100040201e48a0001c4407100c071ba00500200408560810007951110211a403007407240c07a00b019401d000c1c0c0500304c0040880086000070081d9a160382e07a00300c01c542d0207002d29810031824840b4000080060044501030312580340d03000350a41c504140245a200040d180502807402c001054095440704480303a44101d805607600a0b50440a4224000a219005441c2882c05404000e0307180c80c240051309101d12520503104008590300d0f9010440910b00a2091001603070205 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 954200440 1250 954199190 954199199
    0xc0813030e040b120105090c1816030b1201020307110d03020405031f090c0b03090606060f160813030b06030d0216061b0803010e060901093804151403010b0901 70
    0xa0b0010583c44102819814540c0090180a42998400d4500c08140e400400d1202c2a81c200094001d502e140840707150403480c208145209105034041404004240d00c4030542c0100703490f60030510041011b008000c40d0760f4503101d18014101c6941181e0b002c7c4034040c200221940501c28004c0e00d0965a00401406240341841170394101428104142503225498607010307800301d10402a00802003161007031040d42c03840c0410038141041d83c0280914407614040c0b02c00701911003650300b80e40741c1d2805151149041442070900b01e0b914083c912140c40d900074801c030003200b0004c050b807007070b8050b240560403240c0040301c0c1070080e6100d02c01104107044103c0082c80800205208101c0c40c9104513002c0205115180c1c9a120010a94000d82025603400c07982d00030702010341031600c0641d005006828041020301d00c801d540f1000c0600c1c1205161200c00b407100c81604869a90103014120342e401001040440c0e076030308007a80300c1c802030300ca0308241c0034041401100ca410103008850303915400a1003001e01d41e007030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 954201690 1250 954200440 954200449
    0xe030315130b0a030f05010e1f0509011b02030a03050901050112202e090e0c22030b010302030d0c0236072003070506010b0f07080307030c0813030e 65
    0x4030718407a910140c031115079030401d0f2110711035000558052030b04c8980d081541e040250942e19290443c509940c06010051140d13203c801541c04139148440b8041000d40711401d1480c00f511610f50f0011204c0011030084420303540001c0285200d00b0300d6141408140e40c0d61401d039013220f5091023101c3d440804505030700c1c000750007100205c0c00c00090048544100d0100070104401103800381006100d4501020001040607a4440442d40840d813458500c189a0412140b454058009003103014550f00c081400c10b0b0680c1c0140018203a08d0500ca500c100069032810f0808818100784003d070f009014114a044605e8403805c4800071503500034108d00311055a801044480564003c52701c0407040c5c052000d01015091040300a001c0c1d01d550b80c170b000394020341c040030081a940300d90161001d076100f04905000a240416401e04403030413181021b4a90340a040b550600e40f060728001490480008100005581c0642c42960110101e2f07a0300c042d2680e0744049425803403080340d80030340440e96606595a46250 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 954202940 1250 954201690 954201709
    0x306081f0b060706060e10270b0135160e0d0c030f060c031127120a05150c0405060711040e0a05011e0203101518060509040e030315 58
    0x40142119180c44080c0c0c66003c101c1d425034103c1e81c800946e80c4140044021861b0804001e07002c4150392000b1380c0d041074003800750100c03101c0d4411602c5407600ba9481060307009208030511100000b0200c220040d10f441410b4200300450240081880c448002c500454024101508003c440e174070703a6600c158040d02004042d07103207081c007240d511021140100002c1c0d11440345a902ca8401d01002c0ae01315001c0c0f5024042d200188811821810f01740000016500d141c11007241c400444991a1a070340d2a0001092250048003014620780c0700b42d008440030400c00282c03030840944c580e88440b80c2d645604450784070320f1085110382a0b022005010200100b284d0000107808035400800024417904103410301c0f03003000007200094555075550f000e240d015000008900c021280c15900462440c03400c0006500b200b009030091801c1040124038401a00c0d0241b0041001309801c07602c40f4a20070350b943c01c000c1c071952250300c0703443c000c90070404130300e14035600042500c1c0502c180100c088200c002000900440c205d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 954204190 1250 954202940 954202961
    0x708030715110708070b010e060117040606120507290f131a0406080a0b0901060f030905150601021608030f160605100303111507050a020c150a0306081f 67
    0x2d82c2e581110203821546001403480034482d0300c0303194403085203040c200a0310700141c4c000c00d800e10040d41000f00e81d03a8485425055000b03081461411900c070360500c0401000c19410045010841d0380e091418010001179020485c1d1110240d4088a00304074001034204150300070028071b4460600050410000d02c1018041c01d80f40b061014503019a901188110049000340386103034044005024060b540c0c0c400c640c80d6101ca6040d00c148080010800880c5284205200d81c108019109a010070010b00c00d0b0411038089401c0300451b5030102d22010346011a8405558040c0584505402284501d805802880403540224041c1d407c0134800c01c0350389003641c42681c4079142c01c1030741c0d950303400082c0b050f1042e1030146000b440e58040f15410340c5800742c00d00c0000d0311040c40e00e521008082070201c0c510f07801d40d0b03072000c0c1a1401e91f88807001e05800364504001c0034000d59020700109100028201e4000113800c0c01021950144446595500c01c0c5840c0c5405001610f1943d00c08412280360340c001c1d400010448 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 954205440 1250 954204190 954204233
    0x40c1a030705030402030c18010611010612020d47270f010f0506030c0a2d05030a3212161203020301030521032a070b06040e07080307 59
    0x447c03070300000d066204030000d05001800084014442c4980c024070301e5807040f1200c0c000f00301c418144010028071f1181000024481c5004a1140b010030442040080d21707219100d8504a0003907904c0c000c1c40140007403201610120b00044607002940044200310340c051611601c1c80c40c4c0140c004c00c60810700e440005060541881034969220b4454024411821940e13074201e00040c031404d0030030406040c00203501c01c1c42d1184c00c19040a0044ca07042480c05c0240741d61080740c03030801c54200200143e50060b0b036489140d040c02003820f04000c3c030030802482c6a000992440d802a0070060902c40e00100000031086450f07540030041c00d2a050701183e008140b84550141070103240040c0395215481038459000d203500007500880100208503003007144a4034540540b0480d82d40b000f4102c00781e18640002400f04042c102c10340031210428290010031020360180910303e5a03030b00fa803420040c009810640711540258a0300742d54a231f45820100358003003540c1042025620740749150700d50f440c44020b41007940d20030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 954206690 1250 954205440 954205453
    0x21040606050303120a06060e1e040f091b0506162405070f0801050d030e190b0c011a0f0604060f021501120b0f0c0301150302040503070905040c1a03070503040203 71
    0x302d5800300041d01e00c60004202206007450500c0105003980c500e503000006201012440040543e00c1402d1044683d82c2001c09001c122000b00000e000761050111701400780741b1300041c0105000152459040c10128500320380740c519910300c14008244076440b0790402280d14909100d0000d500385219140c4202d00034144010345a0340c0180d202104c0007914854041001001c908500b2034000d01200e004107400c884210f9050810345014201b1b050600c0301c24450305111111921440c0005813090240920501da151990f8114414034001d044201e0280160704c0000c00c4489185021f80c00482940b1010f805182010302c4c180f400e07507212050f24402025401005110383c507043d400c801050090a2414181c40c000c42181048082c40300041c010052503c411030800805e0200c0c0012241110b1020f0300d030224006c070480d8210002d004507081583c0c5800344e000c0000f8003142c1ca80025024038003c0540048090f17960064207035821404014060800e401d0000910441c05080555803090014059894 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 954207940 1250 954206690 954206699
    0x50f0919050a060e032a03070618050a08090a08012007080c060a02043003271502010e06010602121c09050f0601150206010513060e0c04061421040606 66
    0x5842644d0352404441d0f002040c00420310b580e0512159465203205141400c6240e00a081a240e103da00c0b00a00610389070f10b801101d40422101a100c0a5040400da0310b01070740c2c516103900580d1001c684680700719207400001c036107104180b28412140b4142803074000c10114840211039550802041a0351807102030204030080c41d020300c401d5110f4600580300590b41c40c00c094206982d03440c0600800d000b443c076881e5942d10407603a503001644103034050a21b5420307034182403185070304040e5007a4004200f0318400030024020701072a0310a21581b42e40e0300240500048200c00941d124424071481005a001601312440210380310018409400300060140c210b100c003030b1a00082ea4002841140c56901c525022116000103204050140032078007001103142003015802992003206014072803040840c2180c441600d22350f07620100040030004103c885500c0e01003082807480d0400e11510000c1200504000c040101650840e04445210146401358010801c02d03a5100003004108588043d6149004078 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 954209190 1250 954207940 954207953
    0x3201090b120702060112080702010806031c0c0209090105040c29030708042109030201030f02161203050906061c0606050a0b04180c0215090721030201050f0919050a 72
    0x382400d081d000e20001030411000007850040305034041050581c81070b00070300002c0c25140403140c80c140c0910303041c0140c0c0c8030440000d0400c2d0f032071511003550100c84183c11443c242c02502034000380e070003125107004070750382c0060309401d079041260014800d2450b500c041c001d101001d00a11803610a800c0d111000381140c0da80e0580e10350050300c100e004103008104001c10401001c81c0101024004032544150644e05403010b41405118000281410b840f001d80400c4164158180d03400008200c60203000780c41d40341803000c03075000d00c0101071000074241000140d00c400002105406103e006d070850500c101c5414004140ca080080700b11034141e02d407040050950358094001d030250001c115220740c0c070351800400702055015400801a4076003002c1c1da00514540106003c0c00b202e28018450803107940d258441810009a034200ba41450858400b03c0420a5600807040344035200c1c2e0001c010325203c06000e42c0322404c0880d007a9040380d00a015610180b8421484480500c0c881c10848803070000664810 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 954210440 1250 954209190 954209197
    0xa0b0a1e050d151b09050103091b030b0105010215010303021b030a0501050901060510080609070e1807020a1e0b04060c090b160204060b07080412022110063201090b 72
    0x265074025030000f088811141030311540f281003c140c2e0307444030050071401c0050131303141e0148200b0f0306041c0c0d5508854184080c40004098002c10340c6011001142c481c0782100001c41c00380900750061098030b034000b504688503032005040c1da401d5001404400091104030b248110030030440d6805005980c03015001400c01d0084500030721040d4001f1414504182c24484d94801e820707403580c204580301c014001540c6170460926000250ba207801d0700c00f08150000704000e901002440030905844008000a2580c00316405130243d128035801d41c04500180c02e40303c4001055100582095808400b0800291280d402612040310074100500722a54900102c80300d504000005030f82600d031f60f200c003821450a03104400290004c115210301340801e54407200c900340203038024108a0215001c0402c25507a0f0a01d000784030300241c100c040301003119100d185856446400e01501d000c1e080100c00326900c5000200701411001d4803100d003a02c105680c20103050180c2ca03881c0b0034180040c060b000b080307402c03014005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 954211690 1250 954210440 954210443
    0x71401090b060f0d0b13060b0603011401080a14072a03180e010602030f0c07090204030f0218070f05130b040305031209010207020105041205070e1305060a0b0a1e050d 73
    0x1518142c40c100c01407101443e5404034140c031601c1000d80c51000540300340602c40d003214082808200c4100e2a2422100030590780500c41d900090210001a036054000e00030511a103003a40c03aa032060721000344242c00d5480345415051402748050004000d9440752000c000c2c44030310030fa0312210031490f542d514000315419843c10f030300190349500d0740c080d602c0e0120003640c01011421120b164540c50003500a449001c1d4240c80074100c1070010744100004000c10981c8040e0030311780021903407203549107040341c074140300d1003012030161a01e40040c40b079a00444802c2031103420030761980d0951030603518040750582c3c8202440000c1d0b4030220300200d110f24400303000c3c00c0614030540003590b503460004650429580c1c001c00719000c5a00400c080c90050364070106035003c813601098202d510550510302030b4101801d0b5040a02512210801c101e0881501104dc6c56a00d0190094901c141c49409030720f41a2040c0d0346440d500b05d40031803001c00c41c0491000c40c1c9440c40d29220040300943c2d894070001412100203050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 954212940 1250 954211690 954211703
    0x40f06051005120706021203180706030506010f021c050f0408061f1703040e091f0b01090b27030a06020a0503060a120f1202070b070f0506010e01030b010b07140109 72
    0xc091040d0300b00140b151440f0070395400241106842c1c0040256204050002c171030140c0404404145020800041c00d039100162606545185803070b030000031b004040842c3e40b14000740301d066010407941e0000c544040d4944c82015043d41040c00310310b00365a15440903500c1c40e01011300b00070026240340103000050141059034014090f004011881c1c400020b11a0005c1d90710070300b98400e2042199000040340d0448100c185040c02035500c801c5400c2c1001e0004030100420594000b0801030400d25a001042c41e0030f098032581142c079160800350712103005410034610620080440305001580a041c4400344080080464510001a03518501640c000c0c604c0d110103d070000c400e00030317986450483d40016140c0050f0b890298000703900d0b43c2d100c1024640380075102c40c8a41d440305c0700d0103209010f100b0141104442a603618000352900b03000d0420400d400383c80500400c0300102c1e081c20803070860307812039801c80f903020196400c00340c00025950185008940d2503450a00c0007074085800c1c011320385058084d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 954214190 1250 954212940 954212971
    0x503091222050303030c03010504090c05120d031a030303060d0f0f0b012c0a1505180a060f030804140105070b0a0218040b010f030b06071406070210021908040f0605 72
    0x100c8480c0740311000d07000a40300780c10a00402c06118510401e0300c0c11100704a03808515402c542c00c01d00c0c950f0060b604050b801801b000044001d050001441441e500b00e155020066404000b403100803c00c108400c07540c0c141c000300080381251400110221000313000c2e40312007800c51403550703070f4a190500a945c100c031052010001088040112b810f078903121800c0000681c0b08641405c070404403180c0c01040da02c01641c2e030b1205003140e00f911805402c00380a018015484540407102e0010751300204483c40c01840c0d003065400f00e5a80c0b08400e0351000c403031344000864140303814945011030400a8281d2981000420302c00b10010425410071107000300f00030781d4011f94600d1b41060084a01c0c0740f5071045030041b420002c0318211a45c1c02044030480c0082c61030300043c0d1280c0c0e1400911148542c3d100500fa1040f2088070045d9164045044c500800d410b0302200c0541010000c001d050f17000f9aa00c1e00300348080c2d0300304020420700905071b66500601c00c0c4202c1e01c00003078a030b46000c1140e20644041d20440c6458 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 954215440 1250 954214190 954214237
    0x200d080703060503010618021602090703022503021e011107030903032c100c0b0903030612070f030b06060702130501290a2706170c070b0705030912 65
    0x14440c2c4400350100303800902c21582410407100c50f00d46042c441030442a0b001499100c050040142d00c40c0403640203022110509001d14000e02a401c841d602203000c24804440104000c0781400c0e1740211a41a0060040c0301f280e0489000400d0110a601c445d55484030004022a987c40000703008062094481d5941142542401407250701d0346000c040c0440305004241801c03115504580340003910484034541c8031140e2520485421182c04801030004010f6401c0c850040030100c080d520400b41540c01c0a036410745880866600c104500c07a000b001610340c001800415042007804d40c0c09480030b02014a000825408600c408001002100c1c41960720b40c018002d07580c0301589402c0f040e1505071074050b100c81c0d030301e031805161141c40111801d03c001581c0b43c08800c500d408040f080140f07441035600c0e52540e00e11000c2e0003405551100108400d8150018038070800c1c8030140c80c0215002094020b1030f0b51000020f8403c0e50001c0c00c261304901c2600281024040c02800030100540050030180c00306100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 954216690 1250 954215440 954215447
    0x615150c01050709150305060919020c0307060906050702120a0c0c2d150504090b03071e1a030403050702010e03070b0c030409180302120a0c0204020f180a05010e01200d0807 76
    0x3200c5c210701c02c03d420641440001e030350707984144c0e0704210000050642c2e007000381130320381c02032140030aa54154040030038042c09119507039000c000c43e82d01603101403200d559031110480e26001012000c1080210503c19070390b129101d040c83e0054148540303140c914042d10f40c5412803404507401120350444d0103042c0d408607821030042103100140003645a40c2c40ca40d5080034060114000c0d8043c0e41b401d6543c032981904d07150f4040284800501030b401c148072005c004806101c105180078000c00320112548a40a01810b02c204200c2c1d10031905a0f0710f06042040d0b544c01100e06a00307052006a144c840e0030404100715140000400920341000c00560b075036071402803000c1c1925980c50036811801c1120070000d01103600030445103031642d0391001c210794401c00303071000707450707010000c2006074101c0c0c804961004491441c10061140c8240c100008000444131004c20002010500507140020b501c400b4420055004000344041c060501e8043c2002d552011516072914005d5403840340001e40400510440b941c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 954217940 1250 954216690 954216719
    0xd11130806060a0611120c0a0303060f0302011707090509070e15040f0b160501020f041e05031c02010f02070f0b011a0901050f0910051b0615150c01050709 68
    0x40024000c5460b282d0b0000b541050303d40721341400d00521100b4240c00d418148240030506000d0300300c1da83c0b00c51032892096502c0e0754a050072000f20386010340108490384050000001c69071305035130b10b100d007516901a01b0740343c040182c403902c1400440c80d000f049940d0791101d4144140c0c0c4981c0c0d1074500348030380f004211000d0882c0021480c43c000422041c00000c1c0001168000e5403114070240e50386d644c0d1f054001703000c1e001082c400f9040e0352001c12030300244154100180204c50a00380210065900d2051a4000d04018402c855055000c100000d904240d21103810014481d140000213404003400003080507644400000c07a9068001030016081081c81040180903021511440c5020401d01683c8111841600500c0b03060100202d002c00711038a1a8003115007101c4080c041c03c002100444020b810340d004a502c12850840410319030000f240002003840c4a2100c0c01480c507003030315080c02031185003402200f40d0702d03203078001b000140c13071544003405018080c080c02d996800301c051804204119109 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 954219190 1250 954217940 954217949
    0x6030709020702090403030b1c1211190308150405012402030a12180213150515030609070c0b010e0910050105180c040f0e090d0305010506030c030c0d1113 68
    0xd1050290601588540400f130307510641c9800c0020b41c20f000d02d400a11182c41441c40c1141b20281044d00c801000401141e00380160581d0301c401851507280301800380c6551501410b0301c40c03000051200c0d40401d119240d44c2c1e4100c40c8641100850034103c1c800f0900707584d0b098202c140c4170003022108101c00d60650f03038060b800c00e1041c40918240020450010301300100101c2240b5000d03200c04203105c980b0700c00d0107a0301181c0d60040001c04200b01c40642c00380904480c0226404061b079405e00000c041c00c002404100744141030151a1860369020104903060304060070400400c802c1d185c18a00181c0314070503c50180c81d6032a100030311841e2204880340b411548007078612407181000c0041045840300522118840d40d0048070055568600040748000d0041340d01480710005134203030000f014458441118011001e48007070780d8002500c002e0607020f503003080c132031250010010000200c01240c10b03c003441d040307121000458600807105c000282510011000003444200015401c401d010b2405071000080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 954220440 1250 954219190 954219209
    0x21b060601050715150513050402040c020705030a030513080a080c01050c190c06241a0f0f0d0917030711010509100207080d1107020a0f050307030f030e0904060203060307 75
    0x5401a03840c0b40713003105602d54003518151120b181c2d5129800041c1108060140600003800115680c1e519102800041c0c03000c0e4001d6141002803d1302a20104c3d1420580e20081d00a04000741a540c00b10340c035234030074080501203164440740030400d10014013020400c03034000c20f03105494081e824952803c450010748040941c280400103500b0641c4500110800f03403c250801b44441c003501d0820b040030380040c40800e001030f50b0702c1c4024405600c68030200415981c02c0756041c01406600121030b25240308540410030400010300c24800440c2c100d0000b800391103488180861020003e41c2e84e000c06443c0706106031401c1b0404020800920b0b800070002800c41140346c0203215a0901c0900713240c0f2030314284201510300390005485028000484211840c902c20518200f01003481c81542500c0d036004040102e1013030660b41c0d0001110805044100b09643c0b008016222803403460f50f416a1010301054100e0500803502007525040c0d940d00e880c0c0388128020080541c0c0e0b468440c0c201410101c1350340105604 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 954221690 1250 954220440 954220447
    0x8070528030c06230907060201110705070510140a082203140d1503140c01050a09150926120403030c060b04060807180507140901030903090504021b06060105 69
    0x1081d0b100740240c101c00d030003007000510800710300d401001030404801a0b50000700788070244107148100040d07000c201c40d42c0358000c0044110848800c81c2c240f24060026006d9480558203000910300120b140e51066810308108040f00003511a07810542c100c0500e01020035844010800601c01d54010f42c1a06150b00c0002d0001812907039000d00481c8140d522803460403404901d0210819259110101c540100b1903408010750f03803454000b0707507444a80700381307400d90003090280c0741e40c1e500030743c107842600c14951039100d14141002c9030743c103a80300b030820107100b0000203450018a01d02105c001d030405840d0492000d18410043c2c200928102d0506850701d03468508000400200360700044681103c1ea00402c00710b022818400010068240f6800146850064840020f68010302c0c040c1c41590705441402030040f40e443e500261204070003061000c610044c104480d0b00a584284d000140143c07180c14002c0c201a103d801150072600020310162109204a03151400b420003004043c0d4461807d203041440c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 954222940 1250 954221690 954221693
    0x1206190b010c0f0b0a0213080c0301180209010e0721140115020d18211403090109060e1813020a090e030421060f021803011a0d0f08070528 61
    0x80c0f00e50584070240400080d071000c84d01034040f640441c1c1030342c001ca00700f440e0501e49030b07021141c81c0c860a04220f446503280c5a04034a40c01c00000c03440d008150010140c01590b072900d64a41d40070301d4010103001c1004083c0003041804031790110100a0304100320800200c001c4100241c4841e8003040e042080e2008001c107180d1066640000ca0084543d00d80c84c1140f84000351241d42c00504001c6d4001c401502941450040e54503264000000304500602c0d000c030b03600c00034184160701ca2090840c031a000881e503420900c43e0703a0003502c9000c14003002070701021220740d0640780c0020b641001e0b11001d00300204900d84000f0352034521030304005480c403000304002d081c0058001d0780d600e03c40c0d032140d54002414084503200305400409101e102a82109092180a00c080c280c00029440002e110440c9541c1c001007c109050500c110041454940c1426403840c8080c0304101544900400460301e03111840e810600084011000d403240f40d120304018186201c84500020500038400d03400d501d0004150382000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 954224190 1250 954222940 954222953
    0x5190e0c0604050d03140309030a0f03090201050301030609031205072712020f0d06020a0f03060905130308151e032401260105041103010f021303020f1206190b010c 72
    0x102120001c41380d1416021480c5026102d060028a56001010300030041141010f000300040810603000da4803564800c8240009404a03903680c00040c2c0003a0040c4014000541640d020302c0009001e030804882000c0400010b20036650704075442c0340002c4410901c048801d040c054040185100d0b000d5421005080c40b51b41520840c04801c080c0c0310311050310031401a61030300426540f0158205405658800c244100038150301110202407000a241840001e6000007500c10940a2031061881da40030104030348040b07920007400391002401c1d205e110f40c005da1940c0e548404113907407440c80f004004640302d61020542440700003006a1913032000f03140c0708860170661000f4030703040d02ca0502c0b103d145424041e245505100000350141d2556280c4001d010522002500300031444504900034814007011401038010780c068080c0c0d4840240101d0300030b10051910078503071050104007501e422550720030350039028940001503580c0055a092500d4000d4020341e076000b01d0700900ca0070309004100841595444 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 954225440 1250 954224190 954224197
    0x236040e060f0a020705060f06030705012c04110403050c18040c03030507150c05091f230c010213241407050c09240a0b0906071505190e0c06 62
    0x2c8103040d168000240001c0380507416900440d07001401c44000703217064246084002c00c140ca0061080c801e9220004466208041d0984c0d04070610032040c00300d90240c5002064a042c072180c2030f1307006446000145080400ca0054002140180014102c10146805202140c1300340041030000703a841c1010000407801c1a01d180d0222645807900c99651007030740c10400c2024000d03440e49484a070804042c140704a91001c042c0180703d42c21141d15600d45032505281d11100810050f80c030100304d204040c00004d10b036004a13030756840c4c0e0301400c0b0303072804020107215422030b40710310034000529510f2501032094590340135803205000032030700c0d01032041c1130054409895082aa039004041d40c0000501c4810042e041c403070704601500261128045040031804007014000c20b0707501d07400401c010384601e4400d25000f1401700c221088080c801d0301c0d01c0628402d02034264000d042c16904140f0351094238211a0140c411540705007903034000781d40c0110141180c0820380e859200302d84890360240500c0c0c04140e8810b001c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 954226690 1250 954225440 954225451
    0x10b1602061806040e0f060d030e0d0302031902031e040311211005090f1513050712030314073b04050c0301060305280c030236040e06 59
    0x1d40b2520044020320007201d14150b01600541c01181c0081c00e000703005140da0090304003031070b210440c4e40e0350400e00c00200d001001c00b07070000f2080c0310005007a0404908011965002e441640d14004000c42144544880301107400e00581c8009000a580c0e0340300e0800c11300c104c101481d500e01c0d0034a036441c1c810082444030402c5d8450403002030607814510070f803603580c1c000c11a110140da0140309240585001450121500b0303919008042c9200111100451074840030840e00310714843c5900ca50400340da60501c80c107030459051045000c04a1409002182c26080611a030303404a02e2909020315540c0014024006005105003940a440d03800d451450012154440d6218031014060b104240241e486450480a812038078107800c0c40040242d131001541690100c2d20240907035210800c0e00c0a0070300c1d10305400d4894055894028111000e03035000762070807844514025013848403e071a041030750790740d10000a0307149035002000340c3c045030a21003601d2410402c950820100100c107051648400f001401c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 954227940 1250 954226690 954226699
    0x9060e04180f0506011a0403081b030918100f050f191d011e0b1909030b011701050108030408100e0111041502060105100903023312010b1602 62
    0x329035120050208840c1915000282100c0d00140c500380030f61110000c0c010345400c800c122031b40c103c0ca01503400481e030031a580410b1051400703c8000207054a030041c240340d000540020091030b14150744408200e0700192041c005032006080c144e1a05050401c554031007400c80c50041c10800c07482d90790740c80c3c0910100055444070100c0c040c90340c1507500799800341c212040280d9204400003600e084401b00c40c0c1a030380c1410f0702400e8000c1c2d0903148402c01c0010312441040300400c01c601c903107841c441d070504036042000b07041c80340b0800d482ea99200c410070350076001110400b0131407040c084031103824024540103080e010060340c545420b01025a859282c4144110f9615458080e090a442000d40c0006044e004d6145d1403a119921100c10310004804d1407181c2c8018429880082094a4918850503110304a1b0b2030b0350640d1851a424003c501c848103124001c0b241c50340c018070143c03407050b040512920012003402d55842c4e065556228842d46c0603040740e0a11035062000c090100c0301e1000b941e000c150100c5d07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 954229190 1250 954227940 954227951
    0x1821040e042307182a030f060602030a170103050304053a060507080606040504020f220e0a020a090e06031908220315020928060e04200c010b0409050a03090609060e04 73
    0x217405501034140a11050750b82071400c030001450580c044064200315000b03a07200c6400d00a80103858440800030701000d040ca23002000100080d1a00785d07072014403c00c2e0560410441d643c80000311207510f80c850b81814032a1008100c9004100c101c0c49602d0f40450325041040e6103040030ba005c034401e4004c41c083c00e401680e00154140c0d0411030a0150f4010113010156042031074841080c0c10702d2840d0a100307041c00100b010010401d404001d0090f030b0305080c1540c2e11048668503020350b49581d07001c041c1201b40c250107034803880d4420091000034810020300454007103a64000da8500e040c100040150740401541c601c140034000100e84010305100000180300150303c03001200300103449140d200f02410840a003c5445580e03407000f24010340c0c01c4a685448403509607a030036044c401a039049000403c56501c3da801c00c1060300c4048800f80070b080c055403000064043c0d842020030102d030340340d45054401d2382c4000c07010300805074400b0151000c8d202c645040b2811618250300941811a8001058413440e104e4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 954230440 1250 954229190 954229271
    0x5010509010201060f140102070b03011811090306040f11060405010e04050411090a0f060510210b040908040302132a020a0b1821040e04230718 63
    0x35040b040242c07403401c00b560f50079030b42d841545c806d541c0c0f1110500d0150042d800005540e407405800c1d01c1c100e86076054406405061003d0010045c050103045070b602e10030074419030415443c10418144601d01c02c60424240f10a42d08141107001400c0d0171240c80b81400f008113204c0c99902c469580402001900e001c221a2160704c1c11000030503241c1c2d40c1903000b103040380c1001001007264000070072682d00f170715040007519101c00500240c2020060b010300450b2080010100600c40f082078640252444080002c480c0d05940c00901a00c80f041401e4421160100741070056117000d0502814409550800300f1a0301204418a10705113100c01c2007483c5d20b41c103040798507503440c001d20031480741c194031040000b1039280c00c01190000381c03d4801c8840c01c0d403080d12104034120f1a1a40d00c08403100208100f0350401d880c5c6503a00a0741d10008100b105c1004080540d00c6005500d8040310f0b244005c04e002520f8000d040602c095145412000803903181d5040401800305a018107014502040301040443c0003a24070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 954231690 1250 954230440 954230443
    0x180c080609070b0f0702032a0108041101110f100c11010b010c08070c1a0a02010b15030a0b060c010f230c04030201050a05090306040507080f06090607030e0a0b0a060509090d0801050105090102 84
    0x4400005e90540074803551003108d01111a80d6410460b0543c000403243d449410044401ea4007c80e0000c0030038802a0302e614072176008210180d09500b1040488030341a09403848103051020441d5200d00454483c61000401c9810600702d900d616515402000300c1230007000003c1400140420141542e80300142d24010b0041318039160300500f48070301403140030912004081896030301c1241e0580055180c03c000041c54503285a440c008190411061130564817917007000d40090402c141e541e81d01a03020402107051810030b02070354902e203d02c41000607131301070a42030f8260f40c10078001800d10000c4250017040703507510140040d10103403502071801688541450b14140c480b80f00e00e0059650502c07801041000701300b03000414400b540e03c0c589c15100a1403040009660351a002d0307625680a820400001d1040f500c80c1d84041d50401c80c02e0300715584070145495415031040c1c2594000c00240c0c0b0340d18240054141741030383d5900503940c0d00c001c020a100d039410041c201c810600540341002030000c2c81c411581c0c030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 954232940 1250 954231690 954231697
    0x100c05040612150302280f05040f0209010f030b040618060611070b040e131a0108070b0a08010302040b0f0a030804080d0f1704031110050f071b11010c06180c080609070b0f 75
    0x400c12006c1756101e030f0681d0b0b0054018407405104078104030041c0e566010500a54102903010707107441401410308041640603141e8288160340081c0c0d2485d0019a000124041e04607045c5010000501c160811000821142d05449980607543c0041020030400903a54101c604072400500c0701681c60b00c44048110080c81c007204007074a9080440c1c10f8401040b014030f150b42c100c4410f0f10031900042d6913482a01c0050080101000c013140102c00100050700341504001d14003100144000b903880401000121038060b16001a948401d010074280801e940c02c0080c020310000d02e052440b8481c101c00300041801125100c3d01d2001d80d10719012808050041708500c3c1000c0d003080903502d0390305135142480b00410701200c24800003807445001c00c075030901400300804e109401b600103160f001081c1c4ca80f01d003a800c4403c070708c03410032800f0840d0a0101c2c4c2c491065005816a00f0b40740c00e60300d0030364144502c0c0b072070321500704ca04180c02c24018007225000000c0c00b5400c48200c2d461082e210017020a94002500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 954234190 1250 954232940 954232999
    0x3020703090f090c0e032409010b04150614090d03030e012d051e0c0c030c15010303300b01030e150f090105040312050405100c05040612150302 63
    0x11202c002152144842d0001010b90030699a9418510114003c15568100002d02514030503481d00704030105c5d1070106031040d4407480d050000b00d40284024081012908148610072102080032014003105500c00e0385800d04950940c60030742000a1070000441001007040000c003415030310004910500400e410a8508158507854005100c50800e00e005800c40d041040a480500d40000110121000384100030088188550400b90340d03200d01884086501c0601301038000d200900c00c44031089002c206003884902000c0d46039005526603c0e000d8010744594010075011400c0f203c00e007c0301000d500300350501400b4130f44007042d61003001c40141c0040081b010510818024009011304540c51401183d01503c0c488400850355540d0114180c222507099a00400140b4680c81c0011111243c0d080b10350028001c1060314a1401c100c0308440444261609020228001041c02c002081d040b641140c0100c0d0400c005000001c82a5035458801c40507000091241814808031950700760300385070480224 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 954235440 1250 954234190 954234209
    0xc10091e061a06040b0406051e070503120a05090a0303110c03031006083111031005071202040e011809051504150204141210110d0f0b100302070309 65
    0x609080c00c0407000b909a000c008180c2c1e0b21020104645420104100d60889650b00d422904080c18110211144c0e80b02c6808404c01d44010700d24804801d90f400010003545206000850356400c10350180c040201d401495030a042d031410081111403003002c21038401d855171502d000213290300300c84c88a05040c000c844c0c0208291002008000c03001411082e02000d4642d26250010f05a6604411403100104201c0d003aa180a01003810521400200c0c0c07108030b0240b080c1045a4541d0031080424a031207190350002903102d8460051201298100300e9400c803c000d680c2d0190f107411308043c0070046180c010310030b0b803000c805400c0c0c210f200100d40e90301c206aa90340c481c040c0d4645c02e030800507810b003085050b01c0595034043c640021b5003070300c0040e108840c1201c5089034440c1803048010300700980c900c4c6140f0740c40c10718003131440d0155080910b480b40614180c20106810b0f11565040c0c0624101d442c002909201c10385440c03031040031603841040d6140921950b10300907a81d00c110f460102c1e801c0712264007400c041d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 954236690 1250 954235440 954235493
    0x10605030d142b0f0605030111030720010612050d0f050f04180e03030117161505030402030c1c060f180210050c0601030305190315120f1208060a0b0c1009 68
    0x801342c4070b42182046910840c0203002c48070000e9403141542c802900c400740800c048580429400e40780600701d50242c140301c000042d186603034034101002c03041420000c407543d41000c41414a4a9040f1582e103000101030714040b410480c5012284911780300b0350180045a8465030058040300c0096080000c0201a210a5a80b0380d40c2d50180e80590a03030441c1242c0d1b15000c2c1c404081c8000c01d07090385240865561500c0551428800c0105890030f500c060030a13030309030242c0460a0036a4a86440192a0388440301084050752142d08058040f0740e03c143c07002c1c48042c1000c194080d000d00103a9045221a0100d41c0f06e0300d0303c22072030003d032030701d214104041000307004200001007895003146c050710526400044031251840c11072030880803100e954204107402c0b0300803101840394400c281c4030304031614407a040b00c01181a0617121140701c102002e00c108005000802040104e007407210042d402011081900c44c10500020b290f2a1108000404034822a82d110000b605000c1104000b103046042c80300365034170 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 954237940 1250 954236690 954236711
    0x15090809120a0b071806030e030702030601140a1d04080307180303090e09010506030a0b0c04180218030d080403030b131a03070503150105120705060c010605030d142b 73
    0x44505081a0544070060380c580040d01c060f0103101d00d101450003140391862017030b080900c01e40090081d000034900f00d1009106910040e18100445406070035440044803100a04404002015245412246603c0c0d060070414104c0400080000d0b00140d110f48843e8407070340e90502c11a24200c00c01e10021030034840d03100020501d0f420084e044260764020021115a17900d4250243c240e80054035140c0c3c05601c104048001b043d022181660000c1400707540c940f400340da4024407080d5440c40000c42c1c1d040c6500040c8407181c00040201350126400079409040000e100f8103024120706401000641810703168204074181d90f550102c0d41c9200003026504110702c40c0003103803c43c105034400392050700a105070b20010540345000500c03118a0481040c0c4401181e08110600c060111442400801485210804038165950340050100035000000001e2414600001c05280c0030908003c281800000c20014091000404c1240c81d900041e40b4070841c0025200c0c2e0702d04010380640ca00c400480c0c40d2071600303117 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 954239190 1250 954237940 954237943
    0x60602030405061b0f3412121b320303070c0305090414060406090203090a0201051602040e100507030209061b070e0c0c070803040617070c050a0804211509080912 71
    0x7054080e495940e554a94000d01d44001d01c14598001c2050a0190310450f100140c402c02300d0906400041c0b801e034180b04046036688003000350900b01201c003030800c40c1460290310b46041001c0250150140c90100342021005010b840e40300281c05001004030111208c400d0600070811100380390f6029004105e800300078240c2413941801907035010301c147c2c18600001480c05143c003c0d40e000f614240d028000c16283c0382c3c015520f0741e129800c96606010a280440d015076140e10030f0300640365240002d4050f413150742403140104e42c001440035050520501c01c0d8500e50711014150713a6582e6401000c10115030104c032101d454440c07241e00600c0c06000603030400003071000c0c0902074900003407a001210b022a4903181030a88900540c003030721001030b071080b60b86105011802002c40d00541c0700d040562001c03100d0f44900d8104220554251143c3c900010108208019683c1c60900b050503000311a00443d04c641d01c070813128131802180b4082c01d45804407001442a200101c030450b40c002001d65090782400b0b14000e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 954240440 1250 954239190 954239233
    0x7140f04080c01020d120c091d0711033f0916050d0209070302030c0f0301030506070f08060a0308030901060b180306101a0d020f0307030b04060602030405061b0f 71
    0x4006014801d440d520b80e5000144001c4c0308042e540361005d281c000345107254024186820345400f0040900c1c000100e1283d07449016014104840e0000020315025401802240d032404100c982540b0030486502330000c9034441801020b181d80305102d00306058007810251a0540502e001d9200b0701ca028800416000030711200850710000d0a440c2982d1b46a0030015251352084012350010240000540098401c0d40119800802011150305080c10096100782c650426041201d03036034080c0302407250042c0c00c0710584446002c0c80c0b6107102c2504d44103000c03c80c0200700d8880108070341c01c0072003c25441d900a401c8a005404000500703601c0d4100300d481196515a101d5029001e8000d01011406d00108074900c0c4050f0b42d280c10203207080988102910125a01600a01d8005035007440390051a00c2000000e50203413610ba41c0104800240000300811100994080c40540d842044200001c0c2c40d02c01c151b9000c0f010f01e1311580c00e000401101942000c03a141a2008203024140c0207100340c00240260 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 954241690 1250 954240440 954240449
    0x8031303090b21040303150f03110a23030f1f050a0e12090301060e010e06040e0f1e010b0a08060a27020f15161403091807140f04 57
    0xd040c0165030701c1500da0603074801c1003c05440002da03050506041c081c00034030142c02501c01c4c40d00103800c50401207400001c0007150443c0001c0500500100148889500c0c081864130007258007800b114038224a4403020420b020080c081e040ca00f641c640025902400002c80c2e01e01c4150544810991010142d080010055035081100e403412000c641c04080c1032280140044800d0000c0c0b0304603580e80e100000a03001310002c207506640b2101c0210b82c48088506103402050458030544803810400104016100c060031043c000b6031203501050340100c030024030041c140340030000790341e010400b051000c2e0140c0080640507411059000e00007170180c4001404502c1750002060802400c0e070f14071007a1030306481681e401c01c204101040000058a8041e00300480741c180248550340d5200031b102e10070400d400512003101e401040e00d07801d0041c0000d4040d0001500301c0c00b005140b80006450018400c1354000185e020030a2052000a040070300900c60b140b6200010464a42c91b0710f1240611141940306001c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 954242940 1250 954241690 954241697
    0xb040b271203041802070f03051b0d0c02010f030506062b1a0a060905060306040c050d1118030105040b0a0b130207050105071b050703080c0a0c0b130e09070e04080708031303 76
    0x150042110014401d07521b03071a0740100301e241440401c0c3c1b011034068009014130820054200344882d4404020040e46000003419150004041443c1c0005050303280b00d03226610034542404201700c9183d4900040b1000c95204051143c60354084580940f100540d01c0c004c04000391030f2407007929071880e03044c580c0040c42000b1520410780b10785400003291000d100b44201c9401072428004201d551516402c44101d41d0014640b2a080400d02a80c10042d2403441d0340c60b42d907013040042e0001d1154260070041c040d0700001d9000340a1804d096a54000d101401880403d405c0d940d544504060790300c103489100e1058004600759110781c41410058020481a911000800c01100d00307200b860380c82003031510301103411030702a00b102481c68031500c00030361002e980d00c0c149014181c02c400000c0c1d041d103240c0001d41810b004040c0c070740f541c003a0b000200d00210740000a8141c1c0c1070b410460304940000701c0304240c2e051800318506940340c0f440d0003000c0340070f0301100038010354000c01003140c01c0c2501c40401c00790354040e95 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 954244190 1250 954242940 954242969
    0x70c06020711040608030f0702040911030d0c0303050109020a02060109020a02160b0c01140103020108040605041e03080118090c03110103111602010206060f0a03030c0819020709060b040b27120304 86
    0x240301720760b0317445040c80b0510456801e00c100390142c038040d031103003009034060231614403038040d1a170000c1d081405c001c4208012900c6200281d05066151040754090544031108500d000400351019548400500c01c00f0702a41d0000740003101c6901c2403010803040c0145440041c0c07502c1d00ca050705516034004032440382c4650300c0c00425041e001c5624580b82e040f41c0d0103840c0c811050307c45803078410184c5030082c01510b40c0a0894261441a40e0141c091300c44213010b5980e1000d203506141044040c0c800b4841610102400c184000000c0f810f1308940c0f2040f41e510001e140e03115010ba000503000f4065030001c40f0a460303c04070301c1c0d540140030710391543c842900c01d90076140d84c0c1e42d9200410604000d00b07140b8036000903994005000103400f0307500c2050828042d28000341403c690320342015039000300c061890016000084200034010f86070003901c01134400385d000a410241412200d40c458050b80b601d54880410001c0728044003c400c1c60002078020b00640485120b42c005001c060352940700d4498500303100440c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 954245440 1250 954244190 954244199
    0x11a070f1e050d140301090e1c1107050306010b032d01031401140106080112060608030c0705100e1509010c020a090c180506070b1902070b010f051e0603070c060207110406 75
    0x41e0700c1313a002812040882815a420121020010083c202414503548911100380d03008260110000751595665510341c0b0105425640b201d052105a41c032590007584000c00501980b8002410340b50b2110000265050034400583ca004c0e0f03200121030140c0500ca2058004010b210300d00300c5a00c48000018000e2025044103c100d0710a8202440b8075000240c0c418014403030419450803040c2014051000421003076140c940d010f080d5800400201d10366808040b007003080c3c1c1010107003401d0801d000d0070401509590500030420200d100d200070400c2c4240014040950b0380500c0c00008095005050101410740340c40d8080000d0100895031404100840c0d003031030700320b6001c9481d2130564170050003030740c00c0481e2a95524840304024080300d008100d1210303001901e40e01c0344040e204280c06400c00c181d40303501d004510320040086400050007a164104400d0340c03440c042c038101c000f40809468032540c80d9200081201d0482c010480109598000100007041c80b4040441070403000f01204d007003040030b030354 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 954246690 1250 954245440 954245447
    0x804050a0e070e040f0f06090213081b060702040603050f06040b060d150b0105040e0f060a1505030601111c09090f021c0b0f0a080a110108011a070f1e050d 68
    0x212500c4000440b89100c920f01400d01ea00440c10000c110705010680840e0398a000301583c01d1500310b6500c880d4081a1342903c0075214000d5002056a00702600c1d08003110300d0010740442032110b0080c00f03428009941d400b1034807151301001c01540c000c02aa076487d8065041c107901c03003006540544288407107402042541ca40500031030503070f40e4401500240d86405100314805882d10002030303410b01505000000e981c030000d1841503c5200c01110801c0c4524194040254050242d0400351101003061180d801c0950800c0c21650014824200802c1d01ca5403488c0d901d2404011114040480300846071441406801c2201c000941d00803480a02c1b0f050203c100c140204c0c01500504415003000075071a02c6040d01c01c2d400800100c5002d40520800c444600c04a607501d5505e40c8800355680c031414240c0300740240c020b82029105003d103081400c0354500713800d90165045100c211108a80001000c0c0100404014408a40c581c05002c4494140e0001480a030924081806541070300078059610740941c40b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 954247940 1250 954246690 954246719
    0xb030715181e06140c070f090e0a080d0e010e011d070b13030b0c160309180b150906090901080c030f01060b0315240a11061005010509060d090804050a 66
    0x41103400d40303002d42e02d8a481294583c010079220484d42000b00001200071605100f441d006c3c008100500110030702c0e1521031b4040301c0d03005003001c001b9000740c041400000d4020040360741c1011921004500c0000060381c0c0d9006005079829914150710742a050010b012074098034403032424031103040e10002035950601407510b10803000b074a000102118801d1000410780c041054000c1c2c850341c88a41000802001603425000d200c2081d0040f8030442c00801c80c48001c4583d040c60f02c1d28011040c40302c0681080030512000011150000c100004100301202da01d4010076655800801484041c07203594855420381c44000303a1840324040c0c00303209410b02403041d050042c80f0407900640c680d80e1441d80c4480881d4981c080d003e80c5c003039000c14007206145050700d15000fa4829226440c662603a2500d6026028140b80540b48401c40c040d017100c010424140006233864045030303802c0c00c0c450f81d6000c03400c0009030240300340c4009140d102e1600702d00c882400002d030064001c0ea001900c080b140326450300a01c0442c0340 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 954249190 1250 954247940 954247979
    0x90510050a1203050c0a08161707030c030e010201090b0a09020f011e08151e041d060a02071704090e1218101103041403011508100b03071518 62
    0x80d5000a90340040d104200031700d0384004560944414081541c0c4201041c0c1c000700c801c03844c5981285200e4103000c1c41c00e50141c0444080c0310f04600d40b013941c3d60301521841c2c2c1300741e0107420b1280300241c1c40c096034002c1d0441404150310040c11003091411280e05002002d00e0b0320300382d003d4600c218104090703500071405000d000b00ca20400760a01c0d02d1504044031180802495002d140541c0e0ba0741071460340354502e250481030302c02c60710f503408240e415040c0310440300c0700c014241d1070b0302038031202c01545c00d004a012500440c04042c0036948406d10b0a150040d4054441c0384145030340000740004d103500807940141450300d12441510f61054080075940c41e40e0240071980040c0f40d851000064640c5000c580c082e12011031401c15400314040c1d080014107681180c1e0082d610b07252040305010703080c40e081c07240d070342890850301443c6012400d154486a40b103a41d0303000d0b440015544d00034103220755010420f810042403040b04034020410712020003003d40d800d48200b00b1100120300390100b40d6100d85498002600c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 954250440 1250 954249190 954249209
    0x30415090501091206090b07050c060f1003030e03070f060503070807050301050f09090a0b0702011d030301030302061303110a120315030201120f1407020f12250203010213090510050a 80
    0x500b840c0d41c115813208840012580255241c03d82d0002508064a00c0e1140c1c0840c2c448644400c1d1600c803003410450010000780748202c0b2901003214a40350300000c40d054030b13003503c0d0041002c000b0002082c58002c403074020160311041d010380010120340c84002184190425594007134151100c210a44d0280028010140d110304030220343c40c0c0c2410403034803165108805004480000301c698841c070580c0c10301901c40300c0040c0d4559951519a4404010b84100148180021031440d855618000c1d1140e1001c4d141400c24404d8000440606104801a50b000120038060380c00c0110300386080d12903400b8090248001c03a04040c10b90381d40c40244000042101e4068440d1170300c929100790b20340001c10300031440c1d0048565401c4071980d018210041c1d00e10038032842d002400d600380001151403409190381a00600c031a030402240010344848034981003200c040f455103100342c001900c0004c0c0a070180c0110001703900c2d201d0500146401c3c03940c10260150008107146c2400940310400d10124498a00a1400d42c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 954251690 1250 954250440 954250457
    0x10090809060f16051b0315010e07052206080108010903141e070609050f161a250312290d1a10060905031e1e030415090501 54
    0x8500301800144888202c40c0740191400300c40104900e40380748203150a035000e134814590701040403a0802d4410250008800030300a043e000d030507107401010140904500c1c4c1c1e84880118440c1c50041003600c010f00402c020a0000a0000d03900300103000451140302c00095a020001500c800c040c441c0720701c5c541c0c059440103020070034160052942e07405103104200c095850035024071604102d20242014600c552404070702c010840c1095842c050606420b082d06030061035075500100d41107040a01182e8401d43c4035180240440403401c444d01600c0d000c8500d03070a0700c445c40701886000515002c81c5501c01d465882c0d01d04072a501040031108190800340403015030304044005c0110281582200c2d4500410407440c0540f2941c44102c40000d0300643c15180e8400c8c4d00b48020400d174102060041c2110b8681541e02918007000250358000c0d040d941c0e682a4500c910004890740103126541040c081550703c403c106900c64483ca982c0c0e4000d01c51142800f040300a080e070b07a14400d00800d001c582050f52120031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 954252940 1250 954251690 954251707
    0xb060412110307051206040605060402040810110712031d010c050a030b0f120321060a0509060a1e0914010f031407031e0b06010e01022d0a0c08100908 66
    0x2454003074000065814410038800082c113a0b80d2010b03070070f4180c460001411403410185410400c0c0c440c0604128484c0d40140800d0096400002c2c45500201e0031b80400b05110705c417180c1c2c0700c0311481101c1001c1c0a150b54951100c1304035070140c1140b800320064074000074043c60ba03c03040361300700c51000d624200091020440684010300c2034200081030321004109500d40203a07140081c1c4801092a82030841c0d40001c140e2182c0d840030b0100040648540307680400c528908100010010140350149a01c43c544243c0420300d42e07240c402e010700240065260104d038500c06c003184220340d45054030511f03141909048084201580d290003650482c0d003903030b8108440300d00350350b03a51202c041d489a11121500c0340810001c08580c0d0820008040380d0000d2402d0414851810a820441001491581440414982140d869a0002ea00c9144001c00180d400099440004102c2c28042001c52000305225080c400c0c41807040c500c0b00c480444403600c00321900d0a800c06160801d458803510041d007160001e000303465 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 954254190 1250 954252940 954252953
    0x10c26071515141c030801081908030109051f030809040b0105040311121f0518010506010c14010608030f09010f0206130f0303020d0213170a111009030b09030702040b060412 76
    0x4420f000141024036182c18000c600f0003040c0224015000950300c13000401000d101408640303042050030005911410090729440c1c0284010b10440030615030340d000080e90744003840c0c0182031040d803083c120b0401643c0e83c2080d20068101c0714400384074500d085415040b139800381d03089404a80d031042d00501c1c440500c1c070800440080326580c0c40f030389005802c8240b80800071002c40c1400d400f42c94000092604100700c5203085081743c0c0700c000c91a80e16000030311110742e80000841f00c481c3da10049074682010110003441c094145c540c409201484040340882c00084400c02a100c4400d00307a03150f504e0f14a851344120303038a510540786241401c0001c0d284c1c0010a2010195020040c002d00b8003501e8004200c0a0104a81c488903100c14085050707602800039400e010b80010f94001d10100424042d5010f45a810445224101040c8220303040740310f088020340200f40c0c080003190442d20441580c600802185d49942c85110201d1145141c004840190710702841030342c043c1c64684041d68010807096540c403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 954255440 1250 954254190 954254219
    0x6180115030902030a031809111e0408030c0304171606030225050f01051b0a2d09031a0c0a1107081603031d0f010c26071515 55
    0x810140c542c2d8011001d070310100207903682c0500c85d5852002150305041c81542c002c0c0990070200da0716081000f203200280610f402c0c4c6240c0311100c40080720154a40e01620000c1c0316940c440009404041008202120044040c2049850b001c1d002c0742034a80003480d260311203001c0d101c090b8669281440501410b031003903025000b4007045401000c1d0981452404542c15949004202d80b0760f0b0000d07041c0b032100c40d03080c000d450308040140c00d2180c41440e03200003610305006407041d00301081200720300d12a24020303104101860914100000711100c50a950041c0f0141e1140000e40d5502e000c0c84000d042d880418201038425801000861b09042102c01c08491407030005450204a11071901d000c5880391090000c650a0340418041d01c001c0ba15500e400340c0541189180c3c40b00e8400c01c803100000360b0710360007420b00385000300f4a450054140c00e0b1034240203074076906100c1008000312500c027242e0414240c00524046010b00c1d42d60407540220101d20054859000c1c2082142c054400704020003441282c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 954256690 1250 954255440 954255479
    0x30609060f270b041404030f0c030f050d14010801150b0301080303012105060a020307171003230609030a08060d0f06020f040806040c06030b0603070203070b22050105010e061801 78
    0x803d1000b0346100180a540c109850400500440000c0c80205a08502c41070300ca02c3d8281007040c0b43c1d09260700c0241515400651003820310074001480030341c24080ba4480003100d41d009081200a5842e403072982e00800c0800140c1c255003540000104004071414144d84c103c0704840000c510b1070782411050705080000c0817941d10081c0c410400c003c0040d80c207200306071042c3d0f5071b40c1d40161a40b0744041c00070011b1509040d07c2034001e0341801403042020011144000750b9801041c401c0d181030380f180c0005090260454085e5190103024140104005c01000504e0b03030381140e981e1102e0035122901040400543c400d401405030400e203e08000080542c1c01030203220303400d117075070030b04160769141007070b042c82c000301e904541c503a140a8040c401c1c180c02d0302c20f0019441c401e465560443c905424065600e12441c01702a0440510f100010784003c0c200310550500c898441c11120314544130720345140605420f0084d1280900c0480000fa200d0a2a4003000c6a034031004000d20040c0e440c100e40250880903e890 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 954257940 1250 954256690 954256769
    0xc110303010e07210c020d08101d091603050a12090509131407060c020a1409070522090510081b090912071406010504020f070b1015030609060f 63
    0x445290100b074610805c2110011500a0000506075400090245030010542c0100646502080c001d010800c00390310f0003119080460a05030b1030303081400740760600c0c207047c500c4440c0e69204080200100814801c800c10b114100c1d50400d441c031484141c0d041c0500307015868010400c000080d5201c0052000414520702680d4242c4640c1c11071420a0b0801071150020030125205560300710850409001000003001c03882c5030401c40e41c00480004091080140c031050810002180c405402030b5000b8240c1442404540ca000e081559282004050f18003100c11314035048820000141415012401c500c801d520404d41d45102a82101002508400034203048070320300c42c031558002c03001c09403401002a20f000d030141c0f0074800303540c96455107010016089070380030b60300500c2400c03000c440303920a580d11140d0000454070f25aa9861100c400b2004560040949200c4120401602501a4010019940026001e1180e15142d201554074400c052054542c84800b10310100001c4032040c2e603c400b40720f40000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 954259190 1250 954257940 954257987
    0x70305011d060a0e16091202010507020d1b030b06120a0302070501050d0609020d02070b0705180d0203190804050f03071a0c03161523150118090c110303010e07 70
    0x2c00900c95104104c501d80e103e1050f00444030746282d00031b0300700740040042846045141140c1d6000070030a0003102002400b41701a50501c41c00c00540c01d022810820342560b41403c1c65640f4240300d016141f0680d00c0c18001c2e005c80308503800c8520b010901c140002d8254000781122440e150044810760300c00c50500c0215036513484003040900480c0000e0800320f820f0f80c4051307290501030a16107000c841c081c021509121023001200c04d02d503070740d00c1c0d42c184502c2c2c115100c00101000340046801c2040205184200d08829564102000f004030090000d4517010346901e0303030303c80d841c2c1d09050b0ba411150141410410801210a0380c070040355005200030000c400076242006800b007000f03088021036180c111800600f0350f103100140300075407040084030404401c2d0ba81102d0002d04001130b055401038401c4841480308000c2500c5640500c9051121400941c000b01a00c6d545a002c00c001b010130810b00800181007080181e01c0060000039203050320f0481d8011801500c1d90a400da030303012070820300700710001070b00b2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 954260440 1250 954259190 954259199
    0x30a0b0301110a030606020d1e090302041503050f010209030309060a0c051606030f1a0f0303040b040b1305010f090e040c03020409060c0f26130506070c0308070305011d060a 76
    0x780207503942d82e035403a00d0040c3c50341d0f42404050262441038004c2e904551064010481d072503488010f0300c0c0c0b0408840c18400104420b000200c94441d016080690424208840800200f0740030200c00200c9029909541c2031090700d0341127500343e209203420340f40d0503402070082ca01c1910f480002003080401c141415000c804440ea41c5504201d00da8801d030030700354807107002082003a03014022854440704600c02040280c03030900a42c2003400c09032605600032501e1007640860f0f47c40802c101e80c06003d1403040c1039111036a550b4243e0055100d01489030901d11403d41c001803a5004502c0490343c50080e4440ea03820703500300b600c0d15001c5000180f065820b102011000000768685200710301105000f0103021076140000c41001d400c082d84441624200004501c0c0c14964400c0850b4180600080c10107540082d294032201d00d0108409210180942c0994000e006034103400185440c0c01502c00d4071f48901e0f940c1c0d20711040c0e003100c4e024440c2c0000803d046c000f80304104801c12031558010001403241040c1501c0303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 954261690 1250 954260440 954260443
    0x5012d051305060115120c05030106030e1e160506090d080d0f1503030e010c030f1b0c090e070b0c0703110d06050a0b13020c07210605070c1a040201020c06030a0b03 72
    0x2a4001c044e1a41e14a0500e0b515650101000c1049031406c4818402004100001071140c407051181a040592b10100302140b4002800b034180042c1c0c11020145071601c5020303086445516030041d04030b10032074443e800155130900d80251600080010324501d04100683c640260542c4802d202e08000e90b9964000f405404080c85580c0060045101c1c03d00c91070304610740581440c490300510382c1030120118030680000d0740420952403250702482d0802d0082e070342002180148040d03101c000c2002500c41c10108072101154800c288560f140070032190001d41d24068250705202d00c41f071f201e07031507000780c2c8040c030216070140c4843c1c2d4507031805044050b1780c4002e034541070100c403015982d5048140c0c5908107410b10f460100700d54203402c01035550443c41d1030707225418650340c2c58180c840c240f18482c422845900d610403a034042c41610b500881d040c0002d2810907001420348480c0c050480e030501e51104181c0714113600c02240362003a40d06800500502601c5001c00000740c10040440903100e840e14018801610f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 954262940 1250 954261690 954261703
    0x1107080a030c0b0127150b07050d031103100302042315090603030a0203090f060c071d0c090108280218090c03100e060415060c05012d051305 62
    0x642d540c066554030341e00e0124910310040e4060241c0031440c210300581c0d10050302c12480358094000c4002074141d10728144001c3c0c905668030081f0100e00201d40340c82130007404260070b100e1201d2550108200105c3d1444a040307800199441c1903400703100f08007880142020361041e0080e44a101810a503485a00c00e1400110812640806500405000306070300d03080004140e904803504034040c5007000c10303280c0d00940d039000d0310035030038426420150080c1c1c1c0c6845031802c941e51820300e802500e410300e4464400d100d904032043d40520b504450007001402032182c0b907081d91000b2805a4440c0c0715611502c00c498425100c2d44100c40e15003034a11130000c944102d600c001c1c86c40800c40401c040020790000200700000800500d545c072825020000c0041601408524209982d403a0f000f10b00c0c40d441c0c1502240081c4540c0e0031802d03a05400540101d1080c0c0c104c0041016280314800901081d901e411001c501c81200d52038540f543d0b802c9a10724229542903400095000c05040d90071344034241180c69051821a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 954264190 1250 954262940 954262943
    0x80c0708130906080a1b060e060319050c0c070e190507090b1602031905060402150f070c0e090d0e01030207050c061201030b130c060c0305210709080c03030702011107080a 75
    0x5010320b28410070080030007219445544c506c0030f50000c441c580b440113808031002c203145511030308000000480659408a480d102c80a07400b904010a1403d0420300019170301c001c000c01282c0c0701e00308000031481000c441a81c811000307404c4e101c130701c0c4181e180ea80010b444050820b40c10f02148580205001b015a80034091107540b2021617801008203006041c140f0b440c0b030940d500d03400701990054000c250005102c0e50041da055414071030304414072942d600c260103241e503254220740000942e103007400f4110702404291029404014500c0d251010696561080b407002007010075080a451284c560003a400303040b4803801030041c1d4500c81081000500e09601c1090075842c4120084018414010f8084060b58020351705043e20b246039201b600c90700b1208016101c1c240c1006808000794003017603c1007095892006864242140200080720990b400c075204642c4200000c6550200044540f0000352001442002401451400c5a990011128480b0b42d402c011410310900d18002100c04c810482d00ba2003d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 954265440 1250 954264190 954264193
    0x3050f0c2109010912021b010801030804060c022206060e03061303141201030c080106060203070521071208010311030c1e0406150309060b180a0b0a0801022107080c070813090608 78
    0x640071a01d648005521f40002c14104004d0380c0040c030004004074105c07426a6a24184118086400d02c005608407946c0e0440300f115070306062410041082e81d400000039034039130b5150f4410b2880070009166454034100c5d0f80c091504a110b419070086406100c0d051190035201d0b26a80c60b040c000400301748109400e0b8022038600d001c030113007001101e500380300707100190051b44080e510b0164241c480301c0da68034404080b0388142990185a401d045e100d0003c4400c142c0e070241c4440e40309001c542020f41840c0c024882601c00c40390a03201050329103130110b00f04c0c21104008082c10a401d119801700c3d041c1f5150003c400380c1281d0740307071800310f84d0714a04250384040b20090354000c50139070001c1c075010b002c4e14140d48200d8054840003504840b1404118200c560110a00b040003c072032143c100001c41656066000c01c5136544009040240c0070403c41b42035121070b041300000b42042d100e0102c1210801c0040342c40071200b1205100203000605048000e020115410036541e0700c031601c485108084902607400500b1a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 954266690 1250 954265440 954265453
    0x3090503010501060504050907030b0301060302130b030d0302040b0f0d02122502010507051215090a140609010503070302090a2009041406010e0f0301090f0303050f0c210901091202 79
    0x520302402094007520442c50f1403402c0c2440d0a011820601000c1c1080003810344a0200303c210b914258044001190000c000e11003511000c0c03500380084c030400f001c0b28000e00503005807021440c080c0c0212000c44140c00f92181c40e02c8450020151950484025a96203036002c20050f0201600c4c0c800c214040d0a4808a28480c5104440990a5601c1c071050308002d590404042000c001e0b0400142c805044084099a005950351500b00028201c1d42c0c0c09207501c80038035414030100e0341040c0e20102c41c0d4000e11681104a4658800300030303000d00d0034450644d02d81d0207094184010300b0302d00042904012020404a461a142019800d00c0319882d070f0440a1a43d000c2246a80361402d8043c0340d1100ca000854880c0e58140328000030410038181c3c3c04180162410160012161004d61003518141c0e00000014584581460020080c0209560f0000500f505201007290351000404840340200005802e00fa4001120b2a8840700ca81c010540d0740305540c0c40f105000400d200581c0343c4005c5809078080c050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 954267940 1250 954266690 954266699
    0x1d030d0b011b1b060e010512041506030b071d2817060714210903120c0a020f030309060406051b1c0510050102070b07080f0d0207110904020904020405041e0309 70
    0xe00702d903550005040045840b0002142e0b60400d0490b82c940c5030408102303056a96904101592101c0b014070404018a000b60010070700c000410224018842555281106800003150250740300040b500c10764030114100c2c140b0703032001040c00310420a054201c0c550007500c6e40c62a0021541344001031440080e0801010800340aa0180b8030782780c40e1900707907401c41c00c0400001c001460090341440070021400c1c40400b158030f001003002030721682d10301c098030b58480745060300402c95940c1000440c08054815000c401c8204000401a01d20941c0001c00a0070a6587c0d0b485590241102500c1c000e0f40c8a208100c240561400714014007040d01e000d8010511a040001d000044420042914452504a12040c481b50381c0c0440c40c0ca0850780300d1540b41d911000b840c03c1c036810038801c07c02203800d031610015420740d0424558015165290284103c2c4074020190402d05c030f4105e104980080d840140040018014589640a2500300e8002d000e0314021007000103040005005041065001c550769003820030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 954269190 1250 954267940 954267983
    0x100c0806041803030902012a0210020303330a030f1112031b0c040c020f1011071e05011d1b06070b04030c170d1d030d0b011b 55
    0xd400200a8808000b0107060b41401d030780150441100030300705900d801102055a11560382c0802c0c80901a41150030b06203031094072402c1c8900c014040f4050403282401c11200c1d400030054038441c80f0450104500e10340310781000c869000e241b0248403e4080c01c954074032540d403240030840001d54420f80c0c42416610706801c2000784580302c82400c5d41300305041103488a2075071010058030003990180c130318000c03011054901c20b41012402040b00342c20900e0700602c030851a600060f4480102802d01c140d48050b2512118a01900c002c0c41d103070b03034130740c1c104222443c0011141c902c00d85e001c1502c00742c60001444581d940a0941d0003d5005503001c94900f042030b260110144900c0d466020240740003807c04134582c0104d10705001d44100600b210b03585d03000150505020b40378a00b1001d0340002480a4500d00d03d512200b19005100446901890000b0045040196881100700b22000c90300540c00c10791201d00800140000c080c0080c10007202040d000603004044031906000da204504008946a1a03085036 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 954270440 1250 954269190 954269207
    0xf040806100303210204080f061603200c0109051204061106190203041a040302100b090712051504050103081e03191d0f06010302010f051e0d0b03100c 66
    0x81c91089080410030010390048030704442000c1c0c0003414203a0082c0e0707003280c1c0001d001d0b81d0f1080519010f0340d0900b9a1610000c82c01300d10400e1180f40100c07140410080c21000c0b218841d440210607640504050241d2000002406503d00c8400010801c901c2659940d414013484514080c0105004a000c1c00010341080d45000450304000c0141568980040c1d403109000c0005088003d060f4000007003024080d0000c02d0b80c0c4012a40c0c98821000e0402c0c0c54001c8da98143d000000d110985410050a214074101c01124000d2075180c1c0c0310b019141e0090300b0305008181c06045038001c0391103600c0c09086c5442d24003d0074003e5000e906040d80b80e42121200c05040403c03014408029681001003001807600d405003103910036001040052000000c101d036200d03803181515403911034410466030300452900091848d040c0d0380b007a0381d1024034001c9030310256090700448191840b40311a80c0e044c40b221f89005006040c9000b007950001c6144400740c8042810320036000c1c0c0d00291103171140c21056070142c015003070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 954271690 1250 954270440 954270451
    0x1317210714151b0409021815030718140f01020f0d18080c06041208070b0a0207060e06070e0d0501150b070308070e10030903170c04170303160f0c080f040806 69
    0x30601204404061a0f105102d6401492003481e4003180102580c84e03243c80c0280e01d524041c3c04500714a0400c120b13414160811200080044d444a100088050603508004115805005182c0000c02c1a40c20030980b00320b072407400e0741140310b20310310349514540821aa001485080e1602486101c002d40010181c40d15500504150740c0400c0c41c91686440714801c64040b528188413640c031811861030280345070b01c504200584540403142c02c0c0182d148840d4011710000f44504010001c0c0b2000314500390f1104c10444100c0d000c104040a01c0c01d25051a600d0031500740d1190780000340d070200d20785800e4020019504030000d00c040108040d0201130b00010801d420481a05100c0364201c410800140441c4005114004068a81e140e0f0340406004022040c00e410301c28001c0d6280c1d140c40d0b400711b517568009204140b5000c14500607083d1800003c402c9a0154004c9818030040d41c1d0f8404041d03482582c882d40201c200060340320280c0100f141c640c090107028142c000103550780c074605080c0718540440a8031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 954272940 1250 954271690 954271711
    0xe220c02010e0f150a020705061008010b030a0804170f0a1202160f0b1b0604031e09030b0c07020d08030705040501030b102007090e03131721071415 65
    0x2004603c60020f6503040100190000b0042d90f694480948081e01505900a215114150910100b0303681c44200c3c000b81c0341c421008100d00d0081404050350362280075805400d001c41000240449038020071001c2c54140310604032003010600c102c04501d404140201911542d070300a514030b4045a0500c90521000e400c8075001500a04001005070559010f1103010050680000c5101001d01d07520100c0c0500c4400d0019140340b4a060f0a01900e40c0c2443d4a517513003419446464506000d0150920740240c03500002d429100b5950b5000641c1c2c03075482128203980c825016141800041c140707800441c80382156550b1183c440c0e09e040009400d07a52003805c0107224074442c2900403c0c581d40101340d10a9110818442001d42c070040c0042c505100c0c1c41d800008215003032406c2014252000801000c01b504105504510990b441803c0c100c0c2402c1c2d842489515081050014052441028100e00c864840750f203251511085940713103101c1c01044c0401d110b0503000a0040a0500c00042d480ca174020003d09 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 954274190 1250 954272940 954272953
    0x50c040303081302040e161a0c0304030609110607030c11062b1806150b09060409050a140f040c0501030209030a140307020901180c0f0f0e220c02010e 66
    0x15006040000010302080c3d0072407022000c80199611900300c904004440f4060301c209503401080030350031781e0980c000e42120740c01150048115010820850750031060701405582802d0842e0b59080141c214401c0030b60710035800d5491100d80f0b40d100401010303940d1107502c070381c0c01e07581061801540120354518024458101407007002005107134050240d011040d44584170f0349140070b1303c601c680240200401841310900c440c020101b046010350002d030903041001f60240c2c400d80d96200310703580b9204060565802610904c8100704460560300699002800144003141c0e2107201484801c800c42c1c201ea050840750030300000e220074450041c42c3c0d00c015201c00e1805600d0301031a0004603660303100141008210003500c24446c0f00014090095a00e45540285001e0155955105500a8459010300324000c0c61410051801c0302e0b010701c0c2083d040907100d89030703c101d260705e154040d0b6030603c40e1340c02c00d80c0005a0580024401e0b001c1103841d80d0815090500113211640340c14003d085955903d00c0880561069 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 954275440 1250 954274190 954274193
    0x3050103150518100b03010f151e15030204090f290a09050406090c060e09010b0d0b041401080106120506060904140304081c0320030a02070f15050c0403 67
    0x3020701c95807509030784804a100d44805000944211807002221a079008229050895034955080b001618001724024442e95050b400c02004a844150120780d010705203082c10090040b491844101c1c56443c0d01a91a8480c2d4600304c0703c004410004910002980c0052309015140240c070a4901d00146078504101d00c00c4681c40c1c51201b5040351421240808902910300c1c0e181ea141110031000d82201c1e90140041d0820786444400b0f450340c120115604103003010082a994031800c21030884403001403492180384d00e05000d072101540901c4115603401d4513043c424a945c2c580d401030300008a00e0180c108400c4d1325101240e030031079141e40c000c902004082d00c1414045000064107540101045130304680c15111498040001c000411401201e4000807030002009130340451038030f04010714203100040860050004404854880801210000c8104c01c2c0c2c02490040002560340020742041c010700d083c816485401580240400c05ca64001034880300c407032500c5580c084e25400075680303003540341880d056 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 954276690 1250 954275440 954275453
    0x501180606080613110c1b03010c110c040209010c050a1b050d0c09020f090d05010c02070902030f0f060109090905010203150118140612092104050f091f150f03050103 73
    0x403094000181902d45c1003900f00c401a00d0304507103d4484c0d00c400c48201001100c00c9040c0f040b03044104030f211394a001c0303401000c103000300180c400401103070f0702819880700c00e0710803c4001e401440300785040160420441e00011020080114060300903840c200c8000c511004951032190250031040c06404490083c0c4001040c55400c0301c20740e26202000f41e200c0070450040c1565006103030344a039103c0c405016000500c801035001010b141129030a83e2941a11000b50030143d220642d0900420444c240000da042000d1008558102c203051600b2141c55079589401015220840020b8070f10b13075030001c00e10002c9000609800c1039110282000c80e00d118500c810031115103181e10444000500415014039103540c0c100c01c41d402d041d41d4603600d0095040020b49240d54140e031404020720412048119030003010b02006031011a0f10003840403d9440d0608203201d0500e401801c81803558078080c0290100203401036143c400b8221507200c49201c55040d01005002c1081041c0d00b00038140f810b0010301c00f00f0103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 954277940 1250 954276690 954276709
    0x40e150a05030c120127060c0206040201120b01120e1005160504060f030b0310060e15060301090b131b020d0f1e05120a15050915011103070605011806060806 69
    0x40449450314614100241c132400b5140c00205541c00c0f1409065504d6040c00301c148248896004110400143d03511210699407007600ba1406804a1560302488966a42e01d800c1007400c4e0b45c041c58100050038803914000195015482c006c6030341e41105000199010542c415954460000e6903040d8201c0b01d5101c0280280c411802444100000f540708a07001d43e001e9040796640c0d0002a01301c07505e0001b01103401d0001c1c0524010500c900004c500416000110810401d9210000600d05440c50b4a40102c0e00300415400050303d0304441050b180c00040c11182c4601d03a0000040b052a40300e10354560002410540480180e00602881c00300300341c010365103d4410380c410034a0303c21400404029140a903280e004403240800c441001c2c1d03080201c0a40c40d600285c0c80c00705c0e00c2480b4105203445104020320350204950380d03c0710700071341b200c200450f42c8286149603100d811581034034a032600c0d41e1122000e40360260400707803108507200b003198200001489034400070485407900f49018100600041c44269 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 954279190 1250 954277940 954277963
    0x70312180f080a0b0f090c040c170109020304020f0603220f0501020307030b031209011b0f05030d020c0c06040503060f061201180c0e010f170a0602040e150a0503 71
    0x200a4248451840303068030311502038910718011002169840340d80c02d03551401e1038030445100f00120302007452001c080385d5040c068004400a0a006d010910500000304024981e1408001410b00c1e20132001000c803603590701802400e00096980c0c40c080c0144002120300800040c00750b441081085450301d2160612942245071400301c071851001420700d070000c03081c6020090882d51000082c4460250950304c42d000c0c03401c00742c05840d00560b0b092001722060169000300c6000c12540c4043120b001440c000c2d0280301651045180210202043e00d49038a160402501c1c1c07140503600061a000c050010040c2d4070701c92000b01c03411031609c1e0804020980740c0401400e401030040300140070400035035034040044c03021108c0178005c00012201c0031910302081c5200d91300340c2c4c5400c0321450100d9203207042e4400e981605d07040b41c9180340c40c41ca845551032054008115820642c040c0c0501c1c0ca0010f60640014070051001a1402d00e09080c8861040502c00005444070306c01ea000203401c01c0f00741c4011800709c4964 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 954280440 1250 954279190 954279197
    0x303060a09020307210914030c030a030203100816062c0d0201030b040f09020901090207030f0804050a050a1101030e010c2a0210091518090b04140a0509010e070312 72
    0x26280c42c4003c1e150044000411170718031182c0e0950310802050741e40969242806400095401e101c0c25804688910403414900c2c0c05070010045001c031580241c009603088460320413429503160381c030781c45181440c072860300d20b9008401201c0100110307a8003c5401007650501c40d0b0341c0c400c221090079505003003401d80c2072041c0a0203041e02c4c5c00e4190380c000e500070b003c1d0300e40161050020030b40000741c8000401c52068224810f814590002c100007070300c1d01c2503400ca82d60584442000000200f410307185054002c000300caaa01c0f8407a21140091000c2c000c03030f0301e01d920591590038a001e0160002d17050b00c411140d2101c80e0b031301d403007185201d40d60b200840d06079004d00c5404001c0c01000e1180780c140815401080650841c03003143d100c81c13039a54014080c40403900d40220340603480180e91011075000c0b4550070714449164000000f4445000d032584a0141144020000038070f03820081c4002c40480012100840d00ca0347d1042000241842809400c0c540c00000c070180c140e050842d51181d80605d841410300040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 954281690 1250 954280440 954280447
    0x60302130632130608060904061d0a060c0f051207030b0a0503030408030403030f020a0b0f07120e01050a0c0c170904020c1b0a0f08030712090b0a030605030c030303060a0902 76
    0x10074442035a241511901e845901491080b0480b4640380d620161407140c4144103a100012100e201d03803600b40c000c00c40100003840036110398a54201411140c0807840064031103500034101c0580c1000400340b0244509070114012100403030140842d138000418400780034040140c5048020f85013980f541c0100b041c240000c4d00d08000000c1051001c0c5604050f03003601c4005804a00d011b000030107401140e10a03134569003d400b007510120b884031314a0900070302c44801d17000402d900410042000360300c5142840e111901c903820030400702c19100382d20710718025659100d0030b03c5150149405140c8400720503043c05002c000e59030f507800c140b000c1d040d00c0c512032100e80821062819500d9030112650064446c1c1240d49130300c82400d402c044d4020840c1205d20440303d64070000b5407010340300c034440100c1d40414080c506118194039002d11400000d1000c00030030910050116800c9101c8003d0800c3c01481c1d50000342d40e60802c001c0c14070707084100303501c6032295209004007c0390f955510440d2054400507040540c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 954282940 1250 954281690 954281717
    0x71206090906151e03030509060d3914073306120206030703020d0e1e010501080c150715020a260c22030b0a090c0603021306 55
    0x600154200c059a9820940314034203002198001116031900850044080c035910050819510620700d400d40001d00845410404a80a240603100c0303035401034070705807030546030511040c21250130b007030506116440d0480d2900041254008000d440840054440c84a80e10300c001074038204022046103440038000821008200d802d1414620444142140501c5601c41c1c900006071661070000340c480c0c05241c08000142e002242c000d4100c101d4010344000e03d19111801c040303000c0d60104901040007034a81c1491141c000c000c0216112000311481d20400020480d0311f60b6003540c6060f8805107250748803c02d1120150388004a0051440302209019a07600c1145000d1800f084070803800a640c07880401d025a64940041e030054a204401c40700303094480390724034454030b126001c1e114410401000d00041c84804040d0040382280000c00c01030000c100e503207549a40741c811003228035000507521034024008001000ba441005800c0b182019420f04642c1020600d15003014410541040100b401c03409 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 954284190 1250 954282940 954282977
    0xc0617101a0415031b0219020603060121020c010b09010807120302100c0c020a052d15180a150e1509030102070f0201020d170a090302030909090105060f1002030307 72
    0x70010041d40f080d408598040703400c091300400070410f858507400c0032029803001c020302c08200c0daa2040d1008032090401e211580a00074982c2000340501e0500c00706401c105509214403071080c805201c820000b603a1804294410b80c01c3d51080b00565010708030070001480040c03404100042528102000340c20101d01e1400c0480c0f03011480440c10004520b0499180c00e07040d480301b0fa00721010b0090b14091445690740090001615070721401c01c0e807684140c6480070090703501a803403100c9614001d010900240701c3d2100c00e00c8a40c800c1d0f109840400c090241da040ba420401c1011001301450600d081c1405405903000c0e03d100101054244a06a0100001041d450f5501911400100035000319140c4240e0319184d0450009a60144d003d07101c0c1814000e060362003050042d580824201512001b51540e511031405010150811019408240511380362511640d850920400d42c0c40c00210356828840b00740418603043e0b07400c2034058003c090540710415000003c59821030414902a46106581181c14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 954285440 1250 954284190 954284197
    0x50c120a14070609031824140f030429180a0605010b030a05090105070207060507060902090f0411060403210e06030a0e0f061e090304120c0617101a 65
    0x40d41c20350340466081d0500c5590362041818910070b843c0c1e6010112003850000886100c1d11502a401c181035001c61680d002c090b030300281850f8282008000e804050345e0110315074101044d201014003020080000340400400f0401c0b081108045082c40003080705110b196205000b040d50100119103200117007c4102001145517464111b0010405540c691740700d075855900c1030310307d08400da091902184c4142030612541c1e00480054004118651078a1409d5802d50028101650b0f0700d503641d8074a40c00b42e03c41c10b488512444035654007103214502031402044113604116418090501840180000350040d43c5103503201d07017981c1240403104c2c44404200ca00e004800c0c1516041000482402010034040e002000a050b142003900c0903110700034403050741c0303040490301042c10100c48042450070400700d0340055000002001030361b140948130b4100c68030740e1640c24021680400303241010000740d41e0000f6200540c015610b0022403504005a0506c84070a4900404500080700400c1c2c24075054400300300c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 954286690 1250 954285440 954285467
    0xf110a0806150c150105090a0b0109050d080f0c031b030720030f070e10050301140403140c07063504150209090a020a08070c0309180e01021204060606050c120a 70
    0x480c4c01d0500c400f0801c02411000384074560003515104081900081c8500507040c0891042e51402180740c500420030000f010b20420540d03841c141001030034142c2107000020f15040d6281401103964011820201d0940c000c1d003070b0340d2002a00700b48401c20014000c90103802030510340050702c0d21148034641c00a0706000d00410513083c02d11070303020300203003007404529820301c0b030348820804440d6180d03500d05040c26240c01e0822100300b5a90100041c0000b07026076204002c4461807002141001c1244404602d0116140c103c0c402203640440e0a811041001880503440382d0401859000144181c200c80302100d4003600003454031a1400000b555908a42d06464410708000d2108049042c0080348400a5000c104440b00155120000441e60b071b0080f00c1c011505580760ba10100c03041e1074042081c100c0903012034403130912a1106c540295099090002e03000d41c00c2050842c0e0205e08051a0160840d039181d413101c0280300b01804004680e100101f082030006c10f06821040d40d802085e03c003128a60524941d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 954287940 1250 954286690 954286693
    0x114090a1b0c0c050f060301030b100806010321030e0316080f0a09090e0f0a060504020406050a0611060708010f0e090a020d080c062421030a030f110a0806150c 70
    0xc0c10480c2e80b01c40d0038160307036000d50300034400c5075100c000340840c1281c0117014507000074003000100700041d1011840d43d409040414160005501c844149050200a910983c2d21641042c02840e81d0307200c0508501d600c600c1c81c1801c002c428100300400c0d80381c0c00b038030155085088207408042c0500c80014200c0c1c40d100360003a8940e9681c0d0f0704200c0a0101c22003805082c01c4203181910750294600c00007915404102807100800d00002c0641e0f40c60060100204104d80103a01d5a00015070707030716407a00038406800245ca842d0504000000c0342440c14030010480c00820012000412828017008018810b45d96842c003000595030303600c0c004070325003c1040d100030340040c0300d41e5089091100e204041c1c0785505452050343c40c0780e1203440244901e0340303030700c9a1050380003d091000748a501e0280b007161191524015139180690a02044a007560040404040441e48541384685130380101e12480400d9910410810b0401414540041540b070005003540d00540f0101490340007424000700341d070f030104413080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 954289190 1250 954287940 954287981
    0x121b05070201020724110a052e02030403030203060324010501050c0114040302070503060a09230c0d0c1a03040807060e070902040602030d050f0915061519090e0114090a 74
    0x18003210710645d1401c46140014641004c0d10480a004141c1d50546500a4005d180c106100840303140803140c5d100040c0d240060035a040450f454040c0091072045010351001600c1e881d00d4400d050900b41504a14107a0083c10300b0384540e4a40c4030040281581d80030b03e0702d02d0301d907500300b0011801002d481c90000c4c5034590f01000c0204155000036540c00340c0b6020350944da01501c442c1c00daa0262885140000c1000e40038604c054494090342210301e040b415107904490040c001140411440c0002c5481500c900140343c0d42402071410824004113003146081d101c03461441c2c2902c603485030f0700850000074005515410f6110680c0c200300309140140c80d41c030104650766591007201030354a03800204030500c1c15003401c0004400ea451928424030034120340029003c0c164143c804608407c0000703240380d82c0801e4100d001c2c0d9404016a0161036204000d03c02d1000d11249030001901500181e840301844004038001403288800080744d2995251094520111703a44a003103032080505803140a80d01180e5400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 954290440 1250 954289190 954289229
    0x92601110403021924090e0f0f1b07020402091f02030304051902030d082a071a040302030d0c0e090c0315010513030b040c12050607121b050702010207 66
    0x3480103004903403003203600c800b804c6141d4030080100b281600c140d2500103d084984000f00300700b94000401407155291a10f405070300c80d04035014246054409298a0402c101004100100d00d10380c02d40040004407507482141d51300c0b15003c034601c110b003002802140c000c10040c074240c40352140c02ea14407140e602030300001059004000d550740c200721819201445403d6400102410703240711a461a42c006e00034282512400b00b080d109881c006e8152070384a4000c01c1c03400100c000b10300720700200d07038000224180e5480c018142000c04244840c0d40400705600d0000344000281c00000311048100c21a00c007103052003204a0556071854209003141d00010120100950102034000a511480c130034a0400b402078103003401165140124024070040f80b544840030f1001c1440085ea45900c603205000100041e03480d140d4003c3c20446902c0c040313519600c10000d100703040b82c000e8002002548030000403c542e661490040c400045945080707402d002d0009035035001c0d64400c2c08a20084c0c80e41806040421400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 954291690 1250 954290440 954290471
    0x120206040303270f0c090e010e0c030c011e141605061323070504140702190c0306091b081b030a1a130b0f0402011e092601 54
    0x403241200081e1900c6000d8200d4803c000040858614680344000c40604580d102002c1c2c000010068032064105880010a88080e01800d14a001243c00101c0d200080170340340ba203803030b00c0142d005102c1c2d000160440100d990107100c00c15041641012040e2203148a00c0941d407407022080c0601d80c1c164001500c001d810002190741c0c021500c2001294500d66440e04888002c4030030b808009d1221004a070321400070760f408641c01c0c2c80200c420050704c89042ea284002000c881c010b10350910f43d81c010004102144d901840803001741001584121412005943c50150b0302005000080c21240d94030540d2092203480010442c003a01f5481241e090f04e07407500c80309640d40d205c52010200325035500f8508003090a0125002210990000c10000329004c21400b030000c032100246482840c001c0f4601f02d41c04150181031450042d18658104017a50601e400010244480c05e071416000d00e00481c100800c255005040104a619040088100c0d440154003007981c803503411745200503503081c030440c030540c00031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 954292940 1250 954291690 954291703
    0x7060501030605100e040506040b0a0e060112060b12070308340203010b030f071511070e070201050c040303020d0f1407060614030606010f05070501060e09031801110c1306031202 78
    0xa1400c040d5130029502d5810100c500b200f01d800828503084680843c0004404000d1660000346400c800f040c1410f44c9003080c3c1c50400241d0002c0800041c000e440401d0000e04d20a1411284003522000e440f00c2005000d2951202540b2008040d0200042c014900c000e112840010803040c000c2000641d0702c0310304403581b0114450b6404c0c2d20079440c00000c44014a000a4210901c0f0440e0020701080340c0740c50959071a0b4440010501c0c14048002d100d440d11180c20b02c4542c000c0c0607019440d10090074078800003400c60b00b004010380080002044140f000c20740006078400541c404d46041c04281e141100100d41d600f10100780b80c00074103008035410042003415003191041d03802c0a074000d03403a00d0084003015596001a10341501040032040c240303520510400040054a00510002c9240c80c1d955000d200030900440d800905a04081084526000d010901c602516000d107407000398240004200d5446000200d0242e00c078500141002003141d689400850084d90000c81e010150000503002945404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 954294190 1250 954292940 954292951
    0x6020a110105011d0604090501180b060108010b0706150503011e05100302061b0102091305180f0d2a05070e010f1d0a0b0406060224090604021507060501030605 70
    0xa4092035040c040e6481441500d04032850404213000c20310804140002d1a2009005a60004e4686800002207402401204418071220041105105160612a8541c800075001c1410007104400400c841001d070030546a2050304140d00081c3e2941a140c401038410460380442e03019400c1104034100001c02c1542c44010507410142400180d4840030b084601a1580c04001d500107028089149160321038180e00c1c0d0b29011840005140840110010305003290f10b040141d00c550700c0b581080003010300709204d90380c0f680864004000c52010391034071a0301c41605260078810000d900d141040c801ca985058400c81c0703640039003213429040703540c10101d45419145c01070320100d0140000003d03a0100103007048003205d00c3c0b40f01e0445400318101c0b07510354002014140115003501c50094030910340d19446954000c00d2541c00520351003a40d05501d0481c00186d50440058032854010408458000703d00e01d0350003641201c9011813401d540b603c2d0780860186200160040c1d2030980048104404c5500c090b001d1b6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 954295440 1250 954294190 954294197
    0x20f031e010515030105160c020d0611030402041d100b0612090c03120a020a0f06140f040b0a0c0e13090c181503080901080612190b0106230d02120406020a 68
    0xc3c1501c4149030903070b1000c0c0c4005007140808144950214030031030040d000300748020882d0b03404103000d0300c81d5010b03103070700810440400d41e001091000f10324140c4030f20301c01404c840c103004075171000610041e900ca1406415aa8409444011444544c1d9481042321000d10321001240b400381460071605a030790070b00c810007501910401c0400900720320f07540180c5030391441c207030b006010b520603030765400e204543c6080046070035640300c00807000b10200c0078040b03a11585104403000174074070345400d040390603440240c0550030040c07178030194034403559000d80c0851400c001a501e11542501200e6401c0041420540180052200204c040341d02c10007c80d00d03456040802030184810104003100005980d45480000c0c449030080001c1001540038a1001c3c0e070101004118038055980d4400c0d00d410060207405801c00b01610003880030401154002e21405000c103890607486103454122fa840c030b1074001942102d41d60b4070104031802c0e101400d404075600000d080c1ca03164100e040034034201e00a500183d0012010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 954296690 1250 954295440 954295471
    0x21c0203040203070608131202071206231b07140d0818030406120b12010204060207050414060a050607050c1804151e0b010201060b030103110a09050103030507020f031e0105 76
    0x1403a1086d100c2c0340c000d0302d6607420030750015001e82e00c04d42007080c180700c107405500440704001000300a0701c1203200114002e42c0041964940201014074509000ea406603031984203406100c05004165100f12080f40044c41c1259540700c1070400407010317001c40024081c90710980140c1001d9550150045000f40c2c00111845400c00800d500951640118002c0200250b0400842c41c81d00706036070094895a02c01500028107450302c000f07240e0aa034451307008940540e00c110300c1000f407403c180c480ca01c030081c2d00c040c2018841c2840030000d010306a0600c2940d1040c40045003401c20701c0001d01101c2c001040040ca164a001c115185440c901e041c00c40e003d40c2c26a816410882c1106418001e103404058904580a1202c900e000c1600083c02d0031805241107668500780070039009200d100840c0a9401100b8074000181200308000c0646402c2e00003d1034141002d00401c0081d8224080c1d507102e6904480d8144450401c1012914140c00000503c641030042c0c2d0104000110640c0040d000c0c00d00c0c146803580 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 954297940 1250 954296690 954296699
    0x509040e0c0102190b06011b1704080c06040302060306010806120109030f0e100903030f0207031502031f18020f07150906150803030a02131a132c040204021c020304020307 75
    0x700d1149004c0a401d40c3ca01200203000c540c4030300320740d10040e042c00c001d241c080d00e0f2036201c0001c4d115280301c001010100c00a002c0c41092020045800220402c8a030545080c1c00c0d50302042c00b03400042c0003981070140240204626641e900a1908c41d5161a0000c02030545641001054120020034503408500c442c802640c90f81400b00078030440c0041130301c600ca0064034590b401ca58a4000c2401d1008501a14201100140c80d200700d200040203c3c070405078403420888071094003c4a03446d01121001d10111042141c28403500e0302000001d0702d0000143c40da01c001002d81c41511815500411380041c440b1140e400c60b0308c650010510600030b0358104101107440244102c2c0310041e003d054203640c02440000d04203005a0000d042e058032140e400001166030351806560280320243d14440e4203004100e80e016180074825130300040020748802070221601d50102541c050305582c05086a00103240010155103454040f14075906001710140c0005020301800002500141c0d4104e03c00d01a1110009 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 954299190 1250 954297940 954297973
    0x12030a0e330402091602031b010614030f1911090702030a120b0d0b04080c0a0c081c050d0b0d02031009111806010c110a060503070e030109030912030509040e0c0102 72
    0x1407240d41d004d40900c0c03003501c0710407600720451004890781c82180304c2040f07440000318410340201c0b0030f104064000b0440da0f05040c0c2c0f1000c4c10a1a2a4503400b03a4000d24082c8801d40002903031042c1c00c80390b900c138680c0ea031011b0f003040c4016407038803440182c0020307408082c080036035400001031201200e03603601d03c40820400301c902019642c02000d4035074008008101d03040803074451060103801030b20591005240c08000e48950341080c00d02c1406440c201110603040001035804c1c0030501700f040c00c44503406000150608050f01d10b00a40c1300c51454580d0310044400c40382c4a806501038000d400070210394640c030000035030f8005010b1740c00c030032070340214007104030030080c103003600380d0208800c180521429650b2203000445141100c0340c029500391500107107100c0b40d138031051021000380a16a440d59500c1c68150320240014840c0c811650213070307140c0008070010a40c05205041554422000c1b0000a00c9034101107c6074012468401e42c082d2800307485a0202c040000e0712092000203030240e8080c0c030745001f40f40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 954300440 1250 954299190 954299293
    0xe15031902060a030c03140708040506100303020604110303071401150e0c040b090d0b0f060a060e0a03120908031c0c18090203040c0b1201060305061212030a0e 70
    0xb50014400e00421242ca8000d400c60700c00c0c001246000030712801030441c0c3c5c81d031741c0e041500c503180411449002d200a07c41e0601c42d5550020050712487c044625580d0000d550384801070010303040c0d514081c14101e071903405004813000705410002c0740d4101480b41c80c0c10341c005c140f42040c40d5180c1c5c0d00054009060051056507510a150364003100f07040a180440104140e130180340e44c04e03407261380b0041000014400745402c502900000701ca408583c81c00a061000d1340314160001404d1040d15000092079130f42e103805103c01d03290311200728603108080140940d400b1481303130000f00607030101240d038043c8982e030200008000c46290710284145040700c00159005c2036a07540c286404041010180310118268000b150402d104408980d0b00a82c3c60f40303e4110354200e110084040c0c000c0b0001049030316817600800fa0040030071508620f45051002400d60b0ba03001985142d0500c0d2800b10015019083e664412000098070b04180c070304000c48203030302d600d007001c00000e8140c880003001d1000000d06c8030318021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 954301690 1250 954300440 954300443
    0x30306180c12092a0306060e042f0a0b0d060e1b1e040b0d0501050405012111100f03051f0302090604060302150c0708010b0604060807090e150319 64
    0x2d8126807100907040c50040d0000c2003042c2c50a004078a04101a803a280941e83d5140d061124104407150461800343c0c1540c4190b881541100510002d02006c80c641c07a10384994000b004481d085402e00300c801d072100200902c400541e006404000000750358000900910035076600900402055807602c018003030080d02030350340311099144541141c2c1c80b060f0000080000744c140032402070280022030100c0c0d0f4998015001102501008500d0f103e0000e44d078011a8058a0700315003e000660400140c141002491000543c881503400e441006002e100041a33448200c06020706004c0c402150015200030010700b80d581c00030b842c1100241e422122034000b445400b08072504030b00300520f103400f0000030803000707032080b81e006076a2100000107075107003c080c00100e0780007020f003502c030100ca070901410a50154450796090b41018003a501c030303030384402c111400d85880c0c2c186181c9548607040204c5503840070750000d00c00c4150320014010f02807504c4511510014040341181c110b41603140e810240280b08140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 954302940 1250 954301690 954301697
    0xa030e0f0c0d0602120a060303030c0e0102030a18090f0507080109060501021e031b0d09050301060f0b1c0f141f140d0503040905100e090a2607030306180c 68
    0xc81515151204818042c01d0241c0302c0941002e4210041a68050064810302291a9194420010590140103048a0300760740c2c01d11202581e02100081e4507171081400c010708028100290180b810750442c0b040000c1c00908204000c14000741c1c1c60318008100c16150745000c200c00c1400000d00000c4ca010710380940d00c040c1e0180c0382c2c1901c40240b0340c41c12803e40e10161860302041c42103800c0080d4100e0341080a0702814024542c2281105000e8503c0826401032070280e414080d050115074518074980048444803e8119500c0d0094403082ca060b02c03000300369081d03550600c8282c2080d071130381360400d4510f0349100c0360344c03801a194806120701216001c001503001410f103820400882010041e50b001c007403c00341142908040ca80d581ca030840d88540c2000c00440e40d01e10500509040800c0701d8000741402015118031814409070003659004d105a0040024600e820342ca0a84107542c1d5809582c203482031400b0307480391020301c2c000c1c02600060203900c2c110b03158076041515100c141e019000b010003032a107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 954304190 1250 954302940 954302953
    0x311030c070b0f0c0a0c170705060f0c010603050d030603060c030603020f0112060b0403030809010c09050109030f02040b21010507030b0a0306090f0206030f150105042d050402030106050a030e0f 85
    0x1400c0b41900024015000c500c42400328516003d0f0074411144e04520a101c220041e03400d021039100654009000344681c0c3e40004028001922507008903221102100707100d035203900100c40080d0140c040742e00001c01034000c4501552035203406401080036a807056100b44802a00c540307044044507580d21029500c5495094085215409403260103030042c82910041801c80e147e01e8540482d50082d4003c078009100d40081012903202882180c9010b4002c0c43d06d500014a004002881f02d929400007600340310a1120321000c6649a13070180d6000301020f0320f1501900b410951141c142070199000300e105500348000904942d10a00c9014060742000340b03591191411626100c0050615450460301000c41c2c5d558440581d40d00d001452040024117200070751441c1041e004022200313456460340c188032081c0414050101d04404040c80c110498203003d01c1c1103c840c040d40c2855106511464010b8400000030400c50303030060007401e1070b40315601d00f0b0100c041040510307595564405080c20742900000f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 954305440 1250 954304190 954304199
    0xf060723040501080405070503030a050a08011a09120115090e01050702060f1b09060c0307032715030f0c020319090b07030f021005010806010302010809210f0409020301120311030c07 80
    0x1c452585c0c00c0fa003c1d40441d01d60356107603800300c0d203154800c0f0f015801007036000c9240131445070300c440301a01602030100e49034030144061703801000350301401819901c5040c1c0c5c0e244e0860085401d501010706000d50040340040c00d03588414010081c00003801c401c40350750a10740060040b5000003012030040c1e0302c840c01c0c01e203542e403000136540e03036030034484110342100c42c0c00c00c891082d49c3d4a00f00540070300c040340c1c40556651807613803601a03e038a08041ca190b0800b0706500e42e006800854501c507030304882c0b6080040817564240c4000b20020940844c034640c01520b8014500c2250b50300001500c9001020303041c50b9100281c541060340e1030940c5104000b0800810852000080c1c41041c2444507420740c1d004030b4542c1107180d1190803d07144241c00808081c0e000700d00400540d80d000355001c0e004240e070b034040c0c030322000c1012000809000081c40104420380c0020814200c0e0328440c21207004040e8407004640320b50312045803500020364400154006494102201c000f07200110032140ca1005810007021313001e240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 954306690 1250 954305440 954305447
    0x51f06110c2b0b0109060f1508041a04050106031101030e210909160f080708040f030212210c120a05060f060d0b040507030b0102071403010e0f060723040501 69
    0x1d02040051807120b298560070050310400b01118024418011841e07958149084070007118441d5000300e40490044400300420421082c134607150b1156072620200a582e5420141e8460101d0801150700030102000c203c140641035000f0021707684150340f4900d880342024011001d031107070700c0300c4a10240c104041504104200b41c440c9000075440c168a1418484a500007c81d03140f0100d8a2ba05140f00068010b1960b0740c3c0040740d08000c8407641070040007410803c0300182000f00062005201005040320352060600810039445d0f58506020030fa55a81d40c0410001c00c500780d001094100400c54601186131104c82d002038400c21050340c02c0700c1060f640d56404500c06458050b01454002d1a800d14884403519204010404007c0400e008034080710820240001c541004083d007040500d40204000e45a9002c01c1c45c0c011654890381404603980481c00090060210b0101d0142c50302c1480c04508000d03c0210b000d0b803003602c698a592721455180c0022281721242c8240c1400f45260400081c04151b00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 954307940 1250 954306690 954306709
    0x90a270c08072007051207060906090b070803090106150504080c0d0201051903020c010606030209100c210509030a03180806010f30030e0406050a0e060d080d051f06110c 74
    0xb00d20848091300e6840c808031b08104401c64440c43c49801006043c0005500103600c1c0c0003c1043d854450116032500100540d00d020b0190020300160380080404c1c8080300940090300a0228400300303d4041c012094007030486d40c17082c82503803124040c072800c8034504d10300100c0e44000700790180c4405150a007000fa603e00c08541140c0110b0926600f840741c900441400d11429006e40b00c0340d01d00590f40c0c450003040000c003200c8015280104054000d09000007105040740046000444040791415202284d0980c0c0728011105031907014860a00050140742c0d104082ea0900707405000841c3c0925203070000c1d145c441809015143c2d010319440000c0049031048a1182190703000c004801c2d800c00740f948580859038942030000d1f00003070300c461044160340c90075110b05d400515080703881e40c8060f46000847c0d030400e2001048644a034032258089c00c140940c4070103da02a25141c942003180b85000804aa5000840300c00c000d4013415030040442c06030b005046032800c0348021030040c100744101c60104882500d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 954309190 1250 954307940 954307997
    0x30a06052502010507091401270302040219080105060c0d0c0804051011120405030703020603180303070c060b040b0d12110316111f0302090a270c0807 66
    0x800c00d041002080c40d41d0009081c40c000306600114460400c400c0080030f600480d04080082c00900100d4296a03800642c84403206400c00314103030602451140d100300301c2c0308079032020350018000540080c035101d1824800c2049541c0d910341c0504d81c0d80315000d0084500441c0ca1900b0350782d100da05400701315801181c100080c0c84c8209020303031416488901241c0e040d0315584000c230200380350802c20820214240a9401c040090390300441c102840e05002942e2041b032340c40003038000c25000011032124090921420090b005940417a03a50b0b00b89014000c0002540d0b1700c040c1d40041c5000c03415001c529041c00f501c040c2000c02400000100ea607510b444240342c2c01c0020710070500ca2007130404845100140081c2006003414044072080000700d05001c0e103020108000c0c01d20500480f54910421461100c0c0325084074800d140c01a201e42d012400714190301c0b41a0400d01800c14900e25240b040c0c0e00c4d407100c1e484141030503c01442090520704041c0c0794000151008004101c0350900703100704109c501081002c40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 954310440 1250 954309190 954309211
    0x11404020714010515030f070b030c0412030815010305060603241c0c240c06020906191107240c120806210613030201020702031b040e0c030a0605 64
    0x880d6607030701c4508000102d0400001a51075008200f2402090241d00340750b10010b401900d00711400000391902c9504a000e43c020581000c80415208a07000c1d05940c050400c1001c0400d204c400c0e400c01078036000c1c049840311100080c0080c040c0c1d455100c0c2c0100c1d401070b4405000c45055895003040180341c0165144801140a8540000d14203a5509421079041c0e40480c48241111411405c262000301c0702d85d04990b100158030407004074903082ca441c15104007101d5141c50b800d0000149003000103403165800480e070200b00840c2c0041c1c009190a4403007004d10050711250301c0400341c112681d403602c09078030031034440c141030031081180c40082c0f00380c0521810351841c1c0141c003080d0f00c1d603a2410282410501d400020030f0101000050b0614600c5071001407240e884000001e202c8000c0c0c1c541c4c40c80b0043c80c420704c1c0c40700541c0900405000b5010340d524a5401400e9940b41e591861b0204d40418801303d034284103c3c1080d80d0468841d1004c100103101c9a00540074007080700e07030760b2038000103880c01422048c0e80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 954311690 1250 954310440 954310447
    0x130501050a181403010c0201090507051c120206070306061803110117010f140a21020a0905131e0201140c3409050606092209060e01050907060801140402 67
    0x1006030b02c00400016000003850008020070781030030b160860318064410400c1da8500045000803942c00160b42045880c210b40d40710340000b4490103070b154540d03003050043c08034809100c1600e103240c0206841d407107032903150350070010380383d0b6101c040b0341034140e01401640c0c190018900344045000c0c0e00340e586105d40c060500304041c0c2d103442d03090710003880d00341d0082450b11102001440088072032070b03c43e0b80102040725800c62503030400c903039403120500e40f602041c03003c040e10203160110346900308144010803400c402000070303103000d0303020560800705d011048641c0c08003803107090034151014004401e0079406940c0e0211340d03220b0503010811030307100344c168001034401c004401c004064200080c0303401e00a0b5032810180141ea00c110307010400c80940060520a00b0002040000e803900800c0d50341110080b42d8602049081c0d441002d194820030883c203a20600f00201941807288a80241100e0301c540170080090380c0d1b64405942c1c807484180201c400258407000104520034902c0201101c652008000625 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 954312940 1250 954311690 954311717
    0x6031b0e07141c11072a1508130f260f090609030a0b07090e0a09020d030c151d15060906010c0501180b01080f1b01050a26100902130501050a 62
    0xc54100000440741b004814101c0c0d9564030340000c141d038103a08141c403044035203400c1484019252028019100400240c0710014810700c401c100799a0b90b0b42d81260313890040c03140c0390034105050190005074407021440c100ea0289c10740c4429007242d802024200300c0c076084c20340d944100074043d440040c2865141c0f08440290300401c442c0c0f03055034000c401e103407210b202c0503150030340801611300d00070420040507242c44003110150300c43d04c000790504d5a0502d003a040e104030318070342a01d05645c0505c95003072084c038007407007034061031144000582d10850742400c440c94104604c0d42d540035014103c55054000025a021070b01035405100d03a40d2413540704000215035208003444002000c4101d010589034403200e031004111600d010b015515000810001034a02c50b04a0444e822400c2e004281c0075041140000341ca908191080880d00002c11b51b1500075403518608080e500002d000a56240380700205016000403116001d00c01c0707602201c43c051a10911a2802d401910942c001042c1c2d40180411283c6152 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 954314190 1250 954312940 954312971
    0x309050f2403061f080402040f090c03060606110a170f04030b0705040311010224090f0a060902040e0607020705131b18051c0f050106031b0e07141c 65
    0xc078019490340201d450340b41c09030800c540c0c484810b03507886085452290740000380d544490416841038041c1d4020404c0d0103040580340003844410006041c1440031100801005040d402c00c000b10303411903881d0704001e501203141030345400101c98010480740709541c009503204d1840000d09120b111700304602d410b1075075984482c1c9112804a61041c00110001014420403800741c2680481d81028401410381a03606030030100000080024550034201b60030000e038a5840403c1b030445000c040c0016a1075441c0c903498600083c110301e4204134030481c18006172420790440016820302c640c1840e40284152071900080c8220185503c0180b074405460303010704c1580c00c282c03c04a8420380043da49100c00315030f908101034070040040c0c020510801c010344074641d20f2400e130001e004065400000da45002c508030310b00035004194030b500050800c2d604c6030045011400d0700c450901244d00780c02c81000c940d41c42c80c0085414180b4200b03907011501042c0f05c1503040c806000015180489018030025084040000c6403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 954315440 1250 954314190 954314239
    0x12010504110f0d050717041a09070f03260c030d052d09060a06050a0b0c030408060705030910050415050a0e03030a0608100507020d0c0f0204060306050609130309050f 73
    0x501d00782c0c40310700f81701700a68044031902009004210f8541241080c2c1e94a158044161032000d8280c0003c0010603807640c002e1019400800304221000c00a0b40d8038079020000140700305d9200c020182c90702800b0141c0502e041111404000b50019524000d807041030100144001707045c4103000d80396414003e040300c0404000c2001030405030354800036854508901d03072030140001c2481c1c003268105002081aa1075012a14054980c800c00041d00d0b440c1e032502e010310754056640704240e2032141506114000f500800154084c207068000e46012030040c00b5400b00b512415140140f05c014940403020101009501c9590050880b43e00400c50a40d0704001d90714503081031790708a48c06596040d040011110810841130140a0040223014600e04504040e464010004005003440b00180c1c05c6010442c1801d00e81007126401807080007803d46a061007001030104a032214022100c900215445040800c0034001c1e035070b456514200c03200e04000a10101c240105840d903040010b403580c83d140c0701041400c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 954316546 1106 954315440 954315457
    0x18091a33090105070c14011101060b07030c05011503061a030c0901030605041707081803011a040b0102010b030f100606111c050d1b021212010504110f 66
    0x1a5400c4c402d20900812092031102c0100c0c40c2509041c6003064001c00380c1e90481088407000040d4200c030007602a42655403810701086d40064890f03c41032041c24440c03030004c2a0803420001c0e0003000400e81d04102d58503910b81504207209a4180c5441c0349040c405c40040100b004402d0209050b42c0041c040a401107454034002070502210707500c5501c0c03012400b203919689012030704002400c1d81003009100d01c150084001807043e46014040c81152091211850780c294681c0810270005101680015066540f5a0b039041c40c02d03034040c032402d115004803d003d420901030400c040d40451b2015000301c01401032555150601c00000a2100344241c0409002d020102401c00150340b20301440003500081401e00c0070815082e10000b90703080d04500d180d02161480daa4030b0300049820701681000b02e800081c040010001451b0681052030392044140850703203031a02d0144c43d50520350002c04c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 954136690 954316546 := by
  have h0 := BRFrame.cov_init 954136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 954136690 ≤ n) (h2 : n < 954316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
