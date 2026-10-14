-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2552
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:02:43.068565+00:00
-- url     : https://prove2.me/submissions/688e6f61-27b6-4972-afd7-8a149b6caf8f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 458812949 ≤ n < 458992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 458814199 1250 458812949 458812951
    0x703050a0c0e0619090e07120606021b1002120301230306131211030a0207240e060f0408070b0919050306040b0402031f06090b0303071a0901140408180a1d 68
    0x3042c4035a0ba0404286406c80440c104d1181089540b01200c90441803903c206485042d400002950440241da020307410411080350b030346c40c800713982181a5006040041f460603c01c103120120b906001b100103e00364602d024507240c084200b07400080001790b150101511040150760542d8000600c1300200c0006481020081d4028014105071262003c1500710a046600c58402500180c0085100307200d020b903400e4090380f03c80b03007440b240d03004140070000c00f4003c1d0800c00540c0e2703c42c035004911040c0203452481110080d2040c6420364900729511119000d035504005000e070b10520165007811344848000c00000100c1d8002802000d140c0c4030b5803101a40110060016038140c0180c0c4000c5982200b40707078100001c40e644c040b00003211131400d03070154101c801565019129030030810220001c81d10703c649280c140da02400501503d919030b040f559005007d400c5208000031319203010441808100405461182c1c00c0268044d8060611410800f801105d40030740c1c141c51082800130482c40351950521 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 458815449 1250 458814199 458814247
    0x11090d06051902070f060e030a140c030405030f07030510090804170a021e0a0e091c0c060f06060305091204121406130203121309230703050a0c0e06 65
    0x520b48100c2d03880e840c0002d90303001100c15508903426040110800001d44908800e6101d050059400d210110344010684001441414110200422001c00c1100d041c0121401007000400b00c1d0074a020321108662950340d98031060f0341601640043e4490b0102d2030140955256010904510780780c245810b640044c12500d149105c0d51140c542c1400068442e55207881307105002d11030110024810108001140d245600000c0c46d030503c0c1010b201e206080000c600341e1440480010000d01c40d400501201c50b0440200302a01c1d40b800c29400511304001544401c06803003d640d800d00c0a5078800b0b621943d00c00c405614001d0341e0b1400c01080143c0002400d14000092080303000d030480324090304e419413801c01c0940c0c820040030300da160100300314902007201c40c81c001a02c0101c07900380004032541c1e10b4002d15138400c03403022940341c481c0d05510340702d08509520721102e00b90b0310908078208048002c1c028003007107806000282ca0142108417090060200010780c502c0204094500b1005445030789101e81c102c510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 458816699 1250 458815449 458815471
    0x10080304150f180806090c0102010908030403030519060e06040f0b100e0411030c1b0714090a0e1c0909090b060607080f0c1605040912030522080c0111090d0605 70
    0x82c402d0003c01d690300e0a002441310360010031030350a103805550705250044d883d0b203040da1700d80000040011280025030b9802509410006005e650b1070f141024180e107401800c0b0000c900e0b00001048191000d061580110000e5608014118040c03e03d11304661030b071405142e10004d01e008815509108110309000210017510101d0a40000c01540095030419240d8002d5100c01081c080d0b1074030391040710003104688100c01401c0c61441d00d503124864915800400340a040c00e00c00180d05510703940c000b9444a00354004440c407005c003502000840202c140c0900d000982502d80003d0800218040c14141d203800c0000c0314007036142c010030003d0990099408a9604405209400c0213510113005004503c500c00301070420360401d412003c0003001c0680200f403082d4502020100400c40d507010702a0f1507042810006850703155003091448904c0342205184030141c1c0b444200081068480c0942500110703900244040354440c1460388550103038035090340e005a09d414058000c50710340d4009980045000d45 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 458817949 1250 458816699 458816717
    0x1409041407180209031506130b04110c0d0f08070e0d050a050f060a151409060415060e01030f06080c061815030105090907030206030c250b10080304150f 67
    0x860a02c0c00307200d5900030320031640c0071035091807074101407100d428580aa1070780116103142c128001406844c0040c6a07100c606e5540031440241c1c1c07103660224080300b1a81c1c05150301d4a4030840b41a0361085204420400191a025842c4429003e960294024002501c0d42c0d00f01c40c0d00001845500306400c04261514854030541401041c070038041d10000414402c0138000e1481e2114500702600c2203440303c804110820f58041001800c80c5d42c1010000104942003503694507100e00240240c0f40c102040190030008800005110b0b81041842c000001c082e03d003808500410764107402215894400c281d1650070000c4040d0720740c03500b00c004100c0042c00050a00d480040c003404207118554245880a01a00000050041e03240803001d06904c84881c10040001c01d0440d070114031075020107001c031200c4210216100e1418000b0b444030b400501c074070080c0111400b11a040c401c5030954103846490040542c0b0304003041d1000e0200031502a81d204041514482d8104e0408541410544c8403001c10480412 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 458819199 1250 458817949 458817959
    0x1208040b19080907140103020a0e0312030105040b031c05090a09021314040c2001020c1b040501050111150a0e03030723120411010509030604050105101409041407 71
    0x1010303201070321810056601858035040050161100940400b40b03a0340420004c04c1088001503030245000802e290240c0c0f00d0000850030382c3e08042003a4503d83c1405044590401080084007541c101c4901b16000c0c005030706003105040d00c502e074000c407020f820521203d80500550298008005a44014008948070b1382e0301c2d0344c40400ca030800c08610301c080104080400c5180603088004220310b40440d01081958001d10700903045c0e2501504014280c4200c1e40014038404083d0b0581c1d024529200c1620014011074807000d00e0303130084040e40d81c03140e0315110021a0a5104842400c0460561002001c04c005694104c03415240d00410b0003c680d0340b152122000d81d00280003950041465498061240d10440e00040880c1c0340d46590911140c03092106180074110800c0d450780003a00f110068006810000049038288552010150944240401e00c0200801507008a10450300c210344115255100c0080211000b910301c1001e40c010b00d81d001080c04074032000302c484551342a210454601964030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 458820449 1250 458819199 458819219
    0x506030c07080309060103030f090b190207081504021f08130c090627020306010903140106031a1905062209020a150215010b070f0303291003090507120804 68
    0x2c0b034030004c0e00c0c0c2040c0010420990000e1508192031101c0c142410303800c3c10716030141c0d0b96000c0c01450703801c40c0c50400f9410800034002d200460240050500755a10000100300385885c0e000161400c900031000100081e105159900e6940001141a9940b201907104d83c0780d62a40317480b910340207031100c051406001a0144852107400028200c810410014402040c0465001c54014000c284081e00400c1009190307a130024084041e41e60200341e081290f00d02d00f040c07900401043d04014071803034101c0010701f2248441c3e400700348103400f40100c412104d0790701c0c42d4076001e81d6802e444003504002c0011001c080d0211407908149030030203940c000215144140c0004440c810311b0360086840100c42c49032550515410f2081d03500d80e110b510550b01003035140100315401ca104003000642400c0d8020007400801d4803035001040034407603810781d054040143d150304902031107000302058070501c0600c50100100b40280602000c01d50000094400d807450280082c1c042601c07a0012102140208000f10f500b80407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 458821699 1250 458820449 458820451
    0x120a02031c0e2a120601050d0609051902031207030518060c101a010e0306011710020403080d050a090f0602030702030705120c0111030112030302250605091002090a0506030c070803 79
    0x1000242e02000440565003c400f160f5000581c0d01400c0b4003000c3c840d81910000700c0604548050344d41912070f12481c10000000c25040c1d100424601880e020071143e20400a089c0001e01c0c000c90650b40a00f400121104540c400d58100a01080701070102d6640100440d0300d00c2130900002e04014646090b1064241c142590044c4140400d6612008030480c1851040c50204509080c00e25640016000d00041ea48440511550950a18400c51a40300c0002132140141c50604003200395200c03a1240703407103401d03600515810300c7c85910703000020300090180e014106003c0e41005946c4030012281d102c5102960000300381105611040000e5000100b04000d81041c812148003820744502902c10000d081d10103814204c24140c1e801d000501c14005041c0340e4503200c5616040041e0350301c070221400483d02a8044140140494580302d80d8240549500800d108002c120300343d807201d0618403100d404a0048111941e00440342103402d02041c01c0c4003000310b40140d506080c050804030940ea40140681c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 458822949 1250 458821699 458821723
    0xb03100501061d0102060a0c0314040506060315070e010c08040b120f0105010e13020c0c06160b09011b03093906050702093d0602120a02031c0e 63
    0xaa640c00400000d070340468200c40522680a10124220883c3c000175503401000c0c082041c640c2d651106d6154182c0640e00050394455400c28400f0146001c1c00c03c103440c0e032011a440340c000d015103044140b0020052030603911810301d81d02c0c0d00619210040045034000c4140100301da20310340800c804501800b041c0e0260034607280c410341c0ca4141e442d02c8420010096010303881789040c0700714800c0104541da1100603420394107501c03840040c2c0300c1081b94091850a00d880e10190b8021800141080401d01070801080105005e00d5030030884c3c2e00c03000203040c00c035442c5090280b1a0003001940c4400c062003038101840341801740f0014103900480e1800d003080c4801a45403c054040440d0380054400702e84061035005144a080031070416880e900800c080d4035008142c041000004d05040c0d03610324484d000d28582440c51094452800b0102214072240c09190040c5005031041e6111550482102c1d0103c2d01d9140866026505080403518481100d074014004c1d84880b03511070b129050071450422104c00105 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 458824199 1250 458822949 458822951
    0xe0303041a330f12030915070606060503061927020d1503020a1e05150705010911031e030d0e0f030a090504050a0203100b0c01091e020307060513050d060b0310 70
    0x511030b48104030380948208406801030f0311410a41c06480350101c15550502000d444004868000030420181441041c03801807490385000004200d41d43d005000c0c611070941500c5055441c02215002e007001001c80c8181246500008540c100088080313a148046034110000542030401c180b42240a07295110002d15100c480803504005601d40244140000d00041415028024440300b01d2001142180a03080c01110080075610111400b48215a5000c0d003040003004800154600b41e500480c47e503664a00c02c2c0700740f0b42107452500d03030a4400c82c41c00031380c0f40c01540780c21300100282c000380200c0348440040e80204130034011025000d00c010201d14a44c2c0d0768110840c1d00303010402049841c058030203004103105004000350840c100c2892019a182c0440746a25010024900d81c05401050390060101c10141038480c120f00c0107030044d1488600c00c509442c007040e1903820854440c018590358040500300c0700720400c4503041c0f481034910384a000d01c1b4082003044145000c2881c0c500c8034582d04d0070741 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 458825449 1250 458824199 458824291
    0x1a030a0204020a110615101701120f020627041a120c0306010902030403021e1b0303090409050f070e0f16050d0e0303060901090c091a04030606060809010e0303041a 72
    0x1403800b180804051103103230801508580c1c04044108001e40c4c14001d0b410203011010250040c0300011140641e101c0e402008180e8a00c0000491804c1c030350f11500f03103100701c0a607441a4465161034090080000c8860307840e108a68070103404c12861100106500800e07000b044001c0c4580c0e1000e020080c0030b884c503104056520b007810310700280390500c5011034079000340020005411401001c00c4180114071010248580c82020800007800c5200f9071101c00d6000d40307003010100800502141c80782000d00b5201c244d0310740703590b0398211044a80d03048401c001484007020026400405003012182a00420310703105007000d503080d8030042102e0318094a00403590011040000511301500c2c07a80c00f42c0040d074020b000014801a001e0415200c17030052504008008088500c401e00030001e89004580101c002c3c448035942d880302410045080e50680d1855007010045020304400008807030045500c2500c030440000703801641038068401030720f4140300e841502c11581c80003050119010311608014100904 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 458826699 1250 458825449 458825491
    0xd0f061211032418010c1214060a05061e12010311030d12020a03110d05011508060a03020f0d060c08151e0103090f0803040305040303031a030a0204020a1106 69
    0x4503950807464684a41c0c01000802c5910030010003045001803840c0030b20000ba00c80d520b0303008484140c0e0401001e290318245000b02c8950380224001199451604e080003600f81041e03440d18007040c2202c845400c246480c00c104a2810280c0043c0320b80315128244480703440000444680039444aa52018000902d400510074800507540701303041c0c00030440040c80c0d400309281014015002a821820aaa60110b0300035002e41c0a07810080d140300034008c4850361143c0a0280300c00030f02c07085c018070280748110340194200710b000741040d902800000b0b0481c21990715507030030450540c2d1003112041d00308010078004000260b02c0e0040a02120160703c400c206480c081e510841c240308091900e034450420751000400e00c0403003055a130f4060702c0a180103c4c00e00c2440c2005100c41d9030380c0300000e0a0071400001c02051685c400c0240c01520b1003543c040c400c2c0e61001e0104c130007600d00e1494155041e00b00f132404600528055000b06032403131890070041e040d01050300c0c80a06181c03003290200fa0521246610703d003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 458827949 1250 458826699 458826713
    0x3050304020f0603040b1f03020d06020a020d020303070e190315091202010908120702161518032418080301080d05070c0627080d02100501060c02060d0f0612 69
    0xc402c4025511141580380070703103078140100c00140c40d600d003c042c00e1011038951040d0029010107190003810318601c92000c2c1c90008000d42c00203100760700500074503101920161000c03003201e004194990701c1a6070640007108004207904081180d515074420341c400080040c01d82d1260a26074203410340001360072211414141001d00a00d903224045900d8003540324000382c0480d065810340c40a0580b03440c0c1d20350700d04000360728107084021030543c58044491b000070821550504401d44100c80d030f4801c0442d00508602c90140d07003a601000b40088000c50200840c800c03d15000081e41603d0000480c41e5440c10503e10076a5445003801e40d20002d0000044c411120100700d200203507070040c80e003140791600c240c076890040e0079940503803410000d14504a1400e00c0750046070020b4640d4005401c0720b840d690f10541692400701c802c010f005400344816440000f102d520a05041314887e80b034400800409600f000301690064601c404110b90742c0ba000380c034141542c443c5501414440b031101a000c0b103e428006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 458829199 1250 458827949 458827969
    0x10050a080709050d08070501090209180f1906180206041205010b19060c03050d06060e010f0c120302091203030a09030908030405030c040b03030702091609081606180306090305030402 80
    0x740b05080c038080040c0c3d100c0e5829050810781100602c1d44030011450701c035014152002010b5888125002030002c08200e648259030f0565800d8120f440506841c42034030307100c0700007261000000c401c00741c540000c19460f4014001141241c002c001c141046035002540c6600b1070b400c00c51040d44007881420800809201d555420ba00c11100c2221041e85080c1034203040c021809110308018046200c0c00030103009905640d080c0c0a100c005102e25a21444020003040c2015504c50000703009101420407140600440b60119401200c08840c4682446e1300740c0296200c850002d420075004002844a0300c0d0a102843c0580e03120308011800000c503080007001c03000c07242c10204060b01300300420042c50350000381d00603000d803095a012a8070344040d0000703401c5010303d100c080d4001485008001c1210304007810a00000f82588460030f030b681d26030a001d69610410301e0256001120040d00740034a038000d6032040b0440c070012050102e03a649981d0b40314103442c15881b04501154003c42803008500d001030b40740e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 458830449 1250 458829199 458829211
    0xc01060611030a0509030a0c090504030f05070302061b090d2114090d0305071e1203060e040f050a051b1309032001060801140a0507080606030f090c10050a08 69
    0x25000e841d4400e00541c60344200d0a10400340000000c01525030703202401918411070b0040c2c059407032140d50740b00b1031001e44801c803802c038002940003008100e07043c060010790b0764694140c1d000b0140343d590b080003104100004288640c8020b014085045582d40d074031428814648512072080d9203660b8950b420464543d001401d60a02680303c5002044200c04c3d015206030034003c58042000c81307010304064985100301c9101130299080044210603401112442c003604911800b1400140714a8540841c03c44103940a5522861031820200c0c0c042207a1109420b1942d00880c160b9080246c0f03542e4407403410a030f0707603c0e130141448000c0c414242e03440e110040d14154080118180074040c4031780e40c02051501c1e0403c0c1860031801e800d5060341082c0382503101001034000309000300800c0d02030190400780c0c0b40c021269a80d1050805001403003041c400c000d02c170700030100a08420301b5622201e280d07154030340c0001c0509086205203d500f00381a603d200a0405400e081d40303d01340c0d61030481d4001030444000801e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 458831699 1250 458830449 458830457
    0x30c1501050d1502071205090108010504020c0a0b15040c170901050403050f0d0b0907120506120a14100c0806031509060a11070b01031a0708040809010e030114010303050c010606 78
    0x1006075481d103184000c0d2040c1e10540f40e4204600c001042002800b600c24040d0000041a40d0f000c4070703e41060042c151500245c8079080e5070381c0d94004000c180d04c00c181c049401600012030f603100207610b540c40c0700c0d007280c910a000c0ca410000300002c01d0850301520364490000d05d142c1080c03229144010051038221884000902151400307850142441c41382e501004444140018281c00d510a1035000c007010034401041041182410b002c001d110006001d4412241890700010075024580b101104c10070350320140c041c000c9e0380f00a0306c4030300c40a604030042840e607025440d07000300501a144980c5081c00c40d00c1d2580882c41c2000c6090600d8050141702010811910b0028007040001c006412030f44041c411002040503a4500c7c1c0c000b241e4000c820b0006c0455000100102c10412201006490103c1000d4104051b5603074840c103d41120301950040d000150822030520703594812032851101d110043c00104140070b0715440aa0200000d034019400540c02040c491039a05007070150303800805061038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 458832949 1250 458831699 458831701
    0x807020304030b06010203070210121104050306060103020918010303030c08060f01080c1608040f1a0f040b09040e1b03010e120d050703180302030706270f050c030d02030c15 76
    0x10065540d2046000c06000300c6581c200240306a803080080b00d00030360380640b9141e82c51514600141520020030580001182001d40c8002104810000e440c101c80004000701080e844135001980254845003520340c001c0305101c1f5200303c18000003020f500035442550001243c5144030001400c3e4240030b4507442c80341e0720300c1d00c07484101d0381e1040c4103a4000c0c0c142ca89107540e07080007030169007140300d540800401003000841d0005940d608004400210f80080c10a40140c0d08515216007141c45451041e119820b0144014807512102c48007400940801400000b55112a07449680c42d0000c0c21040440f0a681d80202c100241420b00654040440e4a0010200c0650306000e190b40703402410150b4160341d94500014203110b120342c0001d00304c0c00300740700d80c524420300b281402500c035440028142d41860500c5141a5003001452010420400800b02c81011250302d03610003440c2c254056050b40d180c89510b003800402d40d8184140c1c03401c14000e400030b65848070850106410300001c0071441580c294050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 458834199 1250 458832949 458832961
    0x80616081303030f020d0903030e120f040b0c010b090a0b040b06030925050d3005160309080303070c0c1508060d05070b0f031e160f050d050f07080708 66
    0x141801c5034803541402c020a15150314240300d07000b03014207440890708034100748882060541613400400002d007028180d584402c0c442e82d2100840c41b8007840a515018100000c00c104030b5450f0203080c92807c94000401c0324130852002070450001940e500c403516036600711040d286d103018401c100f0001c0b000d441c401d05500c0c0601c40349499000c00f107100d0380d0000d240d001350b0b0303a00783e22a2000409080300504840c1e052640f418160071403045441c141c407914100300e0b80402600c0380110540c6603240e5035581c240c41e201900e901890404c44002d001c3782805034454004c01c0041050010b14030501940c1d4512101c002c413418a80000107040d808108046071298050f40c620381d009401e50750080081d207030540300c00040e07e042e9281c4102c075400001c10f56008600c80310482e150707038015400380071208a403540721800707100041a601800e64130311000e070342080402031a01380600a9501d164a89040c43e50600102c05160025114101c6450240c007031110104100c440d00b101c49150840c8191609452500d003003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 458835449 1250 458834199 458834221
    0x70509100602240a0c110714090a060510050c1c03020d060506070503040306050612010c21330f081e031e09040f0906090b1605040b0310050a08061608 66
    0x503081c4d0728859110130001560300d00030100a600e052464003200c40d15a9900102d0f2619000040e0b40d034032942e012004a003427101c890098205844000348240b15041103400181c4566010712200c0011740203561b18030f0f04581c03042c001940e00100d0b41e02d01581c0e405030550580200c482035081603108900601418012440001c20358094076480900000d0545803000001c3c40300300d6a44603e0740a601344801c92204e070f035020302404c84180070201519000041401c1d00015900e5094032007004d201040f00428481c120503158844c1072203955003000074591607030172585d8600b6080d085525503070701480395007160211010700a11007424440c06141040003151444440c081070300c492041c0382c0c0002c1404007240d540ca03840b8584144030382c5420010052a07141c840e011b004c40640030703140c09100800003038100ca0300c2d014119001c0c0096032070a140c14142200d00c0c1954102038600c841c41407100a0208107511948a604003610041d07009081c185801c0e0041c030902603038040e400041200c610b06000d500880 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 458836699 1250 458835449 458835451
    0x110d05030d0b03030903030409060e0a1103040b0c0405040c02060f0703060e0a0c0504050a12020a05060405060d0510030f03110d0201110702060705012a09090b010c030c0507050910060224 82
    0x4a010105181403140b001918500990825a130b15000000700010303000d61030b902c9041210750500c800d004541d603140c544021100004a0108502c03410400a80003500c40b841855006600c0d00c0704c24142a00c84d00480d007280c07481030441026034000c900b8801c2240000882d80d41c060114902800a075040c500c50880d0580080e0801c61000e881d2120000d8403070049042e60040e0102421011035a55a1402c0c0c420500148509a02420b0724510120f00e40c00c00404840943d040603100703600d0850031402d01401007400501c64512801c010801100041003600d030503460034020b54445004240d210500c60408a000404100b96031406404040022101c000c0c1e500c96a01105c09589031600ea0600c1c0e405080603080c2081e412008107068a805080c2d89504440d0311060f40c4c903403a0b042d4483c2c49000448044104807070208020720092000a0300c50441c82121a1250095414159a40010400b9001e040d0b03510000070314040340c1885002d50400c1243d00002c958250461100003501004260f148 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 458837949 1250 458836699 458836717
    0x6170603150c070b190c11060705070c0512150a0b0907080a33050102012a120c021b010804030818070f030803060f090108120313051603110d0503 64
    0x20a041c00070302c5103103508095840c1d4a0304072aa0840302c0c030b8030f05595420500b01c0c00d04107150320314060030b20020611401a84601c03403c2e0700020a407545410b101a00c19400091048400b01c5244070003150716200ca4010030320545900d8002c06a04406510305080c0c020003d144181803442c0c080103220581d50042c1c3c940d0801b4450521201035140c03601400d000d07000e030a0003290804c040d00e000c85880d405039543c03004100f4064544d01d06030b03900d079070049007a2040c2e0070020b48080c000e01c2c080f0084440c410718054100a140c20126481000070b041e000c2a20510b04503200582c03c803050660704500c1980001a403801d09207009605460f00b86c1d0068800c140c00b400c0000b101c102e02c4c28202e010042001203e01600404440c010f415503a0b249c0700300281e0045800c2c600860960641a0060a06018042c1620b045038082c0c220081c0070756100c0e81c240c0005100001013100d02000c0000301c1c0c0d003403001000c84002140c0da60300c10303401c0d400c000c001c2d0b402000d030713503030140101d804210302003000402541c58000f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 458839199 1250 458837949 458837983
    0x60c0d0c032a0b010b0c060a020d0915050a060f0302060714011d07090f0606050a08042405040506160903020f0a0b0307020615100806091f0b0406170603 67
    0x4032241811100c0004480d42c049002c0501640ca0300d4124824040c0e00e8007501c40c03d10303981941c0c0c030f4844a1000740601d10092081c0e80c00000454041140b07a0064004c3c040300006c00a034501240d190b1440400200040c421000c0e0f80300305000e0034001da8091440680300301246081e46614540c0441c0300f43c410400003604071a2200419803080d4800c0d044088007051801100207090445129503440e0780b914490307001da036494809641101e95040c0234a4085803620740340c490410f10360082c00e481d138003c010401c407140d0094a0304041d44401c1d1a985502c1e800b01c030000020341d8940f910740303d8030b00b61010340417107440b03861038051804c00c03a88201c164041d41d0f8152100180c0350403d0340403610b120201e800003000c80a02104002c03140e03600044507441403410070070702c980015855042c06a914081620003001031000340c009aa5410907200c00c680100303040d001d41748039014506a07803081c5070b807540201603040c40000742004180c1c0d104000051030040c1d4081c544190034694002560340c2c0c0a0311580300c0320 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 458840449 1250 458839199 458839217
    0x405040f110a03170a080f010b0f210a090b0604111602061b0c100801030c090203060d060905071811070f080f2a01020c1e0a06020403080a0905060c0d 66
    0x9488080c040c0b0021544003075a1003401c01450306003840d980200440c0300000f0802c1d4001918102000c1004e8122052034a40d00d1420400b4413081041da032040caa03041c5e41002500c0c0d00c0302482e20707401000d8403070b0512800c005600e8045192030303002d40c940584100e1080d0300b09004c1303000703000c048411a0813026400340c5400c12884640b0125459000d400500400036480031031403101c2406c04161500240c008aa5015549a68200075145d0040a00020348103000e0340005000c0c1c400c00e0780c0110780044004104c40303107c110303d40d01ca000345c8884142c00c07903113334200e44010410b030050156500344205001005101d91041c50341e0313071800c80c080d100340506282442c103034400c140111070044403003185c95100c0040e1b41d503482021a5505090302070381c1c02e11a404130000c285500b035041c404c0c0c81c01000180c01801c2c041d04400744683d0155442c500158060040202c1320703001420a2000700000c510684000351582d4403000085c0907040f80b42e010901902081040705005900030544004540f941c0c1011590 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 458841699 1250 458840449 458840483
    0x10504020a022104030b010f0303020a020d0c0b0a2307050309040903092417061c0203100207140601081501090222080609101a011101111909050405040f 67
    0x140920101c0d0300c844101c0f402070840707012109040100152401051020709590740c40f40c0c10728014140340700250058102c50081340040c60708011424000e4080e0180300c0d081500c40d00d000605034001c245620106210b2106199181d10f11101000004a803840060070b1880c80c0e20380980341d10a124119101d6039032a12400b0425010300e240074045d016030554a100401e14060045400c0d0341219014042201340809004101d07446040b1446001d002e00305040303d444040700002f440300c041404a03414007810005d95000c3c030145c406801c0d49801540b030341d009503444a0001d4149030701a0460003c5401c86445000c0c10400b405803e41141c0c0100d10059035151580703400d16040c01003200a240c00b4590440028028400203891402648035800ba54800102d440d080001c441e000070342c00d100180c0703118020080398051010b810752100d5000010901c03908101c0340b40d0850b4410f132200785e44c040c0208034102c1e4050b071000300c2e140640003c1e42c0410850901c2d031a42007000314040384c0140000120500154 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 458842949 1250 458841699 458841703
    0x8061c05120406050a080f010b0906070312052a211302040c03090b33010e0d0302061807240e0a0f1d011208130f0807060323010504020a02 61
    0x2044031001c1c901252a40c1c1c0b03030540100554003130030311400081c0e80c0e6404282c12052a01d103143c101d984c4601c0b0103203400050300900540750421001601813040030140e041c40e2006501680d031140c52000100d91a0f110450a0140142c40c44200e8080950042c860041c400e1000760b5042084184a0305035080d641c1d0743c600b0030758040e11608000707401c982429400511140c068010405c014403401c040003d03540c0b6000541c80c916950402d00300e60b605200403044c2c11501000b103010b4140c0d0180360020a03915000c011a005c0128540120b006a000078100444200120b05150603010008003410040340740540c021003900c2440700380b26449200401190540d80510002260300001030990002a81c3d24512084d0380d801070300c1a096024081e4412100c0000884541416148200c40c1419040d08546408046030080c594600b05800f42c0100490800b5601c1c48e044001e00c0ba0100412145003800d4006043d1040e100c2c000c13242c80340140d150030240f00451031090545000b40d0300140c41d401c8818041b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 458844199 1250 458842949 458842963
    0x322050a051516030207030e0f0103020d05040b0411101e0e100206010609060314040b0604060302060f040302040c0801081b04021b0309120f06010b0d1b02010c090608061c05 76
    0x424912551010358024103042c1086803041d00f404050101100719604164140c0c800c2c601300030002100420301810034900000403a103054810702d001400d01e02112041ca084800694069800401c040e04020030040004011b0f010313064141e03110245042c040781c0113003110002030307100086031a4000100242c24883c01e1211001080142259541420b034180691605402e000f200300040305110003184a80c0240150f0300820340c0100d82008130366454440400c84a00600f086c0e52240d04c8210020159903580060b14860504400f0310350354618520400080b102d8900501c024003901c400100f220b600040341c105413100c1101e0701203035880707000d0380024024414005440250481030807181d81c111800405004207030310603100e80d600c04410340012941c40348541c030159910f5001d44014000d6070301d0342c00a05620450300703101003051a03038010070742c00c0b101101d0003040050395945180e6000c194810900001403c0505109909007132900100305015250b500c0403103103c0c21581180d08000c8100900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 458845449 1250 458844199 458844203
    0x204050a0b0c101103040507062f030408010e0d090e04020f04051503030301090b131b0c0510050115031b023a0c0201020d0302090d020f0402070b0a020415050322050a 73
    0x4100e8180c0c1300803c0711140c1c00507981540d080c0f044103008030f50396004e0048080c0d08801070481041d81200c03030446041c0d1851580001000740001c3c0000101d80c2d400740200311540e035441e40940101c03d2520700c0100002d00b258002141d4881000501c0050307240c0708104001154140c5003c50143d4032100886c6c12a4001040c02d5010310002000080c2900d199100c00c06c0150101c0b080c642e02c42c04080700c50140c81040c40c280d0b00e81141e40d405414450300480ca1145030a11030030646c0c804514040260044034402d034007040c851000c2411001d240f507410700c6003a000e8041d02454440b087c001002c000d40c0c3c0c41c15400d080c00041c0300c130800030200c00500813020b805c0910450452503075105a10b40100039400403681213001d0702c190b01241135414020300030359100040141c00390305040c4035a000c014508813200c000c2e94006a003001042c0208250300b030410f11400d199180580d03524a07003410702d80165180b100b0201000014024000c1c0301da038200301d0001a229401c042d41040042e401c0482c00c00c1940040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 458846699 1250 458845449 458845451
    0xc011401090e010c0206040b18150a060e01060333210611071e0204021b0106080f0d05030604020c0102040b0a030c021c022a1903020f040204050a0b0c10 67
    0x50121142d00701808a00b0030303034028810101000c10aa0707580c07105031802442403507104001001ea654804491f9441001d450403543c04645005900015117803d803921207100c1d4480c030080c0815804070711814014191031070100002105645980400e1405200c0c003900e183c140c0c0f84003101c4d82c0c8116412405006010707114183c907154480a0101c031b9140c20001c88640341400d0458107171000c21003e490503150403c0f8001d610030310158174034482480d41d040480c1c0c0917900b0700007204200e12130a01c40196203401c10001840d9814240420314007100c041c1890040d5008010014801313a019054940240303080c0c0c0c015031548401d40f1414064003440d0000f00145401003102d40d2950b5058014400040c07180e002d88089440440e140501100340c072083c140580e00c2050b52a59070780e0300c5020b10300d140080140c14074092150100207003004000034030b003847c183c0c070802052040d4900708003030324140309044600b1403900e0300d0000441c02a614502c6581510100807075030328000d80081c0400c0b03081c0c59075200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 458847949 1250 458846699 458846701
    0xa02062d06040b03010f050604060b2b021201030f030e0619030b03120708040306050f04120e010e09090a03090e010e0103021003061505030f090f06130204090c080a050f01200c0114 79
    0x41004010301040348c040740318500b4586e0004120f02684112030764010410b4040703e00c2c5a03e40540000c442050f81a00c0d1000d600f04819004001c4000200340a0f40c072803da0044803104e00d0500409201c1e0700343c1d0035403040f1400c205031108800107800c010945090740c103000c5052040303440024104001c81540014803400003481000300100b501c0100180e0303201c4c00081145856000d204d0341d2100013140d0040070140c1c03d00c10703010b1a90003465108110401458603050170259040031641410081d01e10264035072212960300101604401e16001030300d145282c0300511342c907140812404a606101c080d006408400800e400107201e034020101070542c64841100078034840600900c10351040342c42152003040344010418103000428080d00341740342c45d002812191143c0201c5004070044107000c0f23034031666a5022100041a450500c00240840380c003400c84038020382005070400c02120001252649044201c1c01d000c81c00365244c021502a1254144e1141040200c080c0184000a031041c2c00d010050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 458849199 1250 458847949 458847971
    0x3030801061206030201020615061e0301060e0f0a0b03070c140330010317040909150b01080c070b100b1305121b0d020a03170a02062d06040b0301 64
    0x8146604884590381c640d0700c0302098960510072102140802401600f01c003010030000759155590005a0100820440c40c103142507001c18000c0d06500b51705c00c0e0f02d05021004000841d0010f00c400300345907003540c510360401d42e0319000460460b180e00400c1e4404a011021914240c41504440f4045600c039a050115207030300441e0b20794a82220040b418a4010707850406001e00280035400140c50016142a61590861f40d9000c2c02d51814108121841824440002d00311070a0051920311070142400079040407800c2044020788001f461024181326038101403215510503541111820741d005640040300b91141481e000d024150740e1300844448030302140da04414580d190030070f01100e0007121001d042400350328880791140e80080100c00340d282440203004c654100b40c0c03240c4210901c014259044207440f950713000d14201110000f070855803c08291801c8454041081365040400076001c0f1050545441050f80a107064a9a03010201003180c01701e0042d07100c40d00400c8130351100a009100c0e0103046 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 458850449 1250 458849199 458849207
    0x7020a20091b0d0b010e221a01050a08101a03071e20030c06010323071202120109150c0201051506041a22030b0901110d110d060303 58
    0x52600d01c28441c80000c191500d40d1032441c04540e4800080007401c00a4010440c0004c2144210301810b1001e0040700c800c86548207039131b4181c00341d580355031484c820761403000d88411144402c41404505c002c041c507441031603030403a064641e9114149080590f942c0c81d41c001c00d1001c0d410f03038030401e400c1c0e03414400a135545c1054400344d0f2046003585d844441107089003200c1d1400f40c0c981700b001c034046034070740c1c0080c0c05201c0c40b00d42589149400700b00703c0f4988034250801f81c2c0f50440036481950241c0e034040c014034680c5e2940307486d54002c0f8004001030151a041004507217280c009060000d100d00ca01503e40800d4000c29045140d000741c03c060901207580b02c00c9003460113000c00400303040055281c1000254508600c42d218150408054805410142050026444101c8641c11024464000e02043d08110718a1040041420082c00741c40040b42ca0f41c50001c0da07100c000381865031180d040ca083e503866108407806403041d81d1401c1001041d0908815480580f80c403507502845915418450301000380351700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 458851699 1250 458850449 458850503
    0x1306050607030f08060301150b070215130302100203030103050d0c300e0103060b090d081213170922020d05090319080c0307030b0a05060a08060405180a080307020a 72
    0x694480c28013035558881050700304d403c80200b401045052981c1803041e0301c1e24101402c8801e1002c2e02d400303403000202c030001c44160004042c00000c420500024400c42c20028072113104049140025403d550660351407030f454011300e221403400c0000941e065400d00610403020340c2038038071040d82407030400c000480411100401c2d031062400700f94151b9002c03403107501c40e11919088550884015041c040b4540400c0515200b8502c240c420440a000d111200c00c007500314507024407241004e25801c919185040d4582040c10000c150040c0014070180302c4c83e446144c4140c0c070f00c8a02a410b44e0083d202c0c010102d0080c001c89441047c642d1070041003010380c00d0008004e0009060030300c089540c0031550030080340d0801086075400b8881c0f034180003150301d190081c2c110341040640203051040254880011031410f404c92640d2a002540000c1800080c3c00c241c0305040c1c01c1035510440c485003500d844083c07a0349251000d00181003810001c0001c082c00e2080c824400c0c29035202c500c00c11025007103240140c407808 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 458852949 1250 458851699 458851727
    0x2d02060d14090f030301120203030702090907291602041e050103050709020a0c03050901170406090b090d050403030c020a0506070c0f05011d041802030f012009010e130605060703 78
    0x20140d000b00e031600304000b030440c80103001ea01c011032540c0e0814042c030122003054001240c0600c414084a001a0303190070300349100700d091400800484c2d2422001203c0f01c20000b0700e24420b41071642e81c070040148400d0443e085203211401c403117040c4810703102140061585034825024490741203510440f00155400c0f080c122030061085030300c590745a9024808a102d0380005030042550303c2280000a4015000b4142d002e005052024482c80715004941d58450701311411a000c9558403420380820403444841a080300d01c000040c610b050844d07601034580d00c01d500001d801d024203144d2070001c5556542002d800780c1409021140c075000a807030808580c0c90742d8000c0300c0c408c7e18054808501544182c851410f8000c041c0f0410494440707840500c80100715051802c02600c038038292100140c0c078104400e1448802900001071001c4041111180250807812030400040041207189800d80e448500040305020440c1e00074449025234140b1401072100e540410740000001c01c0310b034103240c0c006205682e00c02c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 458854199 1250 458852949 458852981
    0x8030c07060e040501050612040804030501050a0e0609060705040605130512010e0f060c040b0d1814011d0a060b0102101e0b0108041a060d05010204030516050d2d02060d 74
    0x8140800f00401d60b4424050180c2140040c000d00056448503002160414081d43c84689080c1d240e4480030f0030342e8070440e0003401c981e03211700d95002c44650401140d0ba214501502a18450074041d00007451441548212400c120010910400110848902600800300140240d6425920f1600300d0f010b4049001e24030107078000c071250394000110200e82e05209001450006140c60305010102207260000040e07065444c1d96154260502000f0504010415006000740244003102182060a5a20a9044803039a07c442400c0c018408400141404a5640030101044071a0842d0040b0b240c0403000d100c0d2aa940c1c20413088a4800f50140c00d480495000e40c442031142d01e4011b0010760b9550810f8030000d000200c030050100c2244198070746650050b03401090400c01c080f0039202c160076078100b40c10030740725030f040101d03030350091251020302c10020081500c04240c44801ca807610071090071035140b10070f2a01c00c1044c3c600610040d10460600c102d0f4011701d119155500700b80300c0300003051419a148490 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 458855449 1250 458854199 458854217
    0x31103060c0a092922080d12181a04060c05090609130b1216270c0c0c080606040e19031d0301020309030304050d090f0509090708030c0706 61
    0x14041c004484440141c0e442d51a00343c0e02c0c1000305158100f20f0015001c904c840040d031a00c10380700e6070340104401d030710544e070818800202c071012540c80101135110030890b42c072840341082601d8114202546c400d60b1020001940005500240640c3e012079400034803030012420300342011804514001d0007a40615005c011242c0320f5071040ea2503200310248586c2c8120240070301c15291a10b0908d401c928201c5102c0454a2454100440d0b006202019021401c2d00059402418070080261201c001c00c80c201c8080d10701c0c50f2200c3da0032204110a0070a8441381c0c0c031100000070450040920207151031f80404a0021295941e0b21251940410f5a03400c0c411420b0500d64495410002507504580004400816580c00695015252444155404291881c0c00e44003441d0aa80030701c080c40c416205c0740040d5960b4681407800b24100312403513680381c0070b10a0b042c10902103440410002d00a81300c1c25502407146464021185292a51a6004031001d200004182030030410218420301181c5080d102c08486d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 458856699 1250 458855449 458855461
    0x1206010e07021b060301090c11030f0a020f030a0c020d0311060a06030506090610090e010f1b020706031109090606070b04200d120819020a03090c09021804020903010209030703110306 80
    0xd000e8010001c3c55024005100600482000794000501603c3d18203040803a03101c810109400d5800a01c9944030525010442c080650340600c4040e8119242c10051407400f41c1e01800540410f07540030020740640016542d00c0704150180b07918003051040310342103450501d40700122602420359070008842602428012558080700090304601a00b2643d02c805401401d011750342d00100050b6180c041c0075900c806220b95404464882c0c078038018825030360313001d2103844075002a14208481c2e0145007014544064407100e0382042042d40c0c030b001d0781213840442e80c0d110000024040c0c02440405040e84050409020400c40300700044101c1c80000180742520b08451010442c0e180313501ca0f005040f44c0204031110341902d01c02c184a60303102203012083c04211980051000407078006040520100396100f070a0b40601409689640080141c0e0a0641c600342c0c4616502004180802c00c0c1800745070081042c0489075800e405070303281000007500700c81560703940b0300304046020f40c50000c4600038051b075004208 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 458857949 1250 458856699 458856733
    0x908041d150108090a02011b02120a1106040f03020108130b0907050906060f031b040b0c0705090109020f12060109080d030209040e010603030903080a03021201090f110a0f0e1206010e0702 82
    0x22003220744c0400303001d003012541c0040d540020055a0803c8401c0b14018400050b501c1808001d4035880040050003400e410340b602e940e0240d810031403c1e20980c410300040103d821154007140589a0a28080d9802e0722200c038032501c1c0d413001080c0106003141a4040102c004000240c503401c0b14001ca0710002c083e1940d030b0038030019214900c04200d8451040000440000f01c05a24991b0a01d42207841c501e02581c2d05160703a080c0d000306208000700d422141041100c0d2425110311400750601030b800318a4042201800d01c1d280c4200785800701c80c665180e0004200340c1c05003a80d0002041c120090762420000241e0080c003c1d8050780801e8451498018201ca011905124000c00d403649619041d500c54190f172101a00c80c2c0001004a041580800900d00341e9045680028000c02d44d02c60007068800c6001800350607900c040c40701c144041c2040c440107000c01d902c50710718030300500c4a081c0020b0f202da151020411008000c0390004d403912400d03000080001d00002c0003482491960300b03454550840903a060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 458859199 1250 458857949 458857951
    0xf03010602011b08071b05030717030708340c02060d0c03061403120708090409030306061e0203040501050706060312021f02040501020a120201090501090b01061101060b0d0908041d150108 82
    0xc5c00064a0f0000c15108a02d200e030809030031030044041341c1c2424070715560b02d402075a660002d0142e00303201105120110340c1150455400c410700d4041c03207440303092140701e2407076100701c2c1100d0801d58031394110070b250114095140700b00c5042e00a08419940c0d004401c050307010b0000b402e00080001d01d80840011903c40d10120b0b0505110b00401400c21080b001252004e02c0c2c11080043d1b44510080007030101c00c2c0d1721481145015803082c2c501142161822001400b400c0d80302d10740e0f904031000c5094840281d40d012040702c003a284242081c42e200e0401c0d007050001442150001490102d200003440c2c0322030740000f2000c41504132000c40000c6440701d4400b050070381c011881080e016138468024403001505680355401185554400000d0039644c588466082d642c0710302080e1410707900d00f001440060790040c2801c0d881e40644d8000c0c0403051030304000355103512804c51441c0d81103030341c0c5400c0c00400c40b40300c00b00c0300100401c1a01005030709000c5621305012906441a02545d400401028030329401160f0311 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 458860449 1250 458859199 458859211
    0x9220e1902030c09040812010806071e09061413140306010602030705030d0209120d080411030102120c03060a151e0e0904030e030709091a10080307030c06020f03010602011b08 77
    0x9006141500d07004d0080841d800341040f10a000c1c1485640c400640c0460824020000303600280150305126001a1003c80d002e08400c22021030721070003055454000103c4000c0f500c0514260841d0300e005124030030240603404400100a04580c800144240d42421143c41c1c0c16040782030b2034490340d80340d6059940c0e10591790020400e8105010003040408254040c060101c4040c00038417240088000035070400c844400e9640206003124140824880c0301d001c5154010402d1b4003c51900e5040070140703440c03600040000c0c1b98821300000103a80f070780310b1404200081c1250f62060359000281840544140c4484800070b1a50b003511040e80307042841801810b0300010081c0075024a9112070318112287c04650050076050306c21082c000a076151584903000509014540944205040ca4100708240c070001c0c02004000d6400752003030010071030110442e0310705985400c00b00303445140d502e00030001c2e00800c041d880740c249000c0700014060b6019000207050350000c800b503000081100c8419500c881703040d581 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 458861699 1250 458860449 458860453
    0x501020d0b010e030d11070302060f0d0605010509061606020c1501030302060906100b030934090204050901150c02100c0510140a02090f1512010803071101030209220e190203 76
    0x10045646d00445500070801c099600343c07407070365842ea00810400d5205c5081100d5103900001e403001d40390503030b214080152101340390003450003190100051481c0900615104500351946440c010000c85a04030360601e40090142c61102d81103085c41c2c2c03400c007024401039000d4010709000543d4072101044844c0b28921154050f0b10306401c007014100240c000802c00f1034944030344c2a406025034214252034a41210200745c039030740d0203585241f03402064000ea110980c0d45005000031300055072090740b450f041d540c0416042c600a41c030000102d4a00f16071a00c0a90045200c2c5800e0340495445403100c11042d00440031102008608000f0f4021200d481240303800a0303017040e01003400c0030900c1d0000c1403403510081a2442c81c043c60f900003000c0400c003e00c0c1c0d03884682c00040d00c00310341101d10304960041003414060740c1045c2081c0c40f0080140180f0409504141e8001407100495540d491000c2014035030055508500540d42060f50080a40b00500002442510500550b144100c5940706000b030b13000e00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 458862949 1250 458861699 458861713
    0x60f031101110c0a06080712050a0608010b010908150c041a040501170f010b0a09091109040b06070c03080913050702060402210c04050703180c030618020622080a0501020d0b010e03 79
    0x3201b202e400c807018114802300311310b40300b4500000800340659030040e8000a0001180c501d0424030300e00712008001e140c2c0c18014202c90412180d000841c42c2040204601c3c0c03142000c2d0b40780308520b80c441c4600c0e04031880381e01d4012400c2c1000b402e01e9000c1c000f0340703800b070303c883c00424401c01070003010440031146400c04040100041c08001310840c01382480220506220800e9600c82c6041c0040d079403c41045903c071140071480b0041c0f0728041c081c3d0368007010241c502920f8040240c07140800492180800b50524030001000720494075601c104a844200b000701c104075a05120034025150201034074140d1188065521401c0d230107031358018030305000103e0f60007864654003c80500028190080091045c907a0324001d010652030f81c003182200440c0705000d0340b1219815032412104880b10032403510101510210075500503107441c5c0480d800349186146060900004a00142a60546400c1086503000d4412400200b00d4150060400000d21003001d1028000aa0045820702d603c1c0d006940d1560042c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 458864199 1250 458862949 458862959
    0x2010510081b010318060e0712031d010203070c080a1119050d08160803100b0f0406050c1015260a0f0f0b042102070f0612060f031101110c0a 62
    0x3100c00304100b541814085130307942d03002021108508400400365400340e101c84008690200074002d0320060110710031030721000a503a1b00c0044c0004180c211079103001c1c4801c10b0300416680204280d80c480b50b03124215801150302e42140b5629852400c0b0100c0c0d5503080d185858441c3d182c08020324440306904640d640c40249014100098002e42c04001d90300b6a0041146070102804001300c94401406121810707500c1c2020f0015940000190380300c5010b80710180030005a10301d00004403011218186041519010030f501c6881c10102e0103e92840380c249000062001500803042c40d00889100d440b209181c0c1b004524185005100c6c120000075541040030799000141000e05030302d03802e030b009a501404a10781c0d6520090140020789040e00e02c0b4203c5500302248000c007d03003c031080003052028140702440d00307600200c2401d0b00c2c00f91340107107d11020400c403080c030547c0c0210000d003540700040044503130724104400c400c0441a24140001c10407081c004600300c0c001040d0071001d074003500e0a56030501d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 458865449 1250 458864199 458864233
    0x9080c120c060901030f02040b09090f010f17030d0e06090d080f072a060f0e0a170f1c0204050a08190809040e0a2010090e0a09020a060f0201051008 65
    0x1c00f4116062543d12104080c00c0b1082c0d201074405080504034a941e12440c00c000c000020074010000b0b0a543c40c3c9600510100034041c5000301100d080b00e0720600355020510940d03045015020204040f1441d2425072128a840011510b0003110346506490207030a81c80d10843c2c04413422100a44800b003424041500c4903c03844031510b4002d9002d40040e80c0c801e0301d21038103d902000e20700c142c55a50720b62001a000c040076100304c0203900c6180f8010109175440341d690803001107a980d20014030b148040381e00a02c40b00503a0884010250300c03c4210380c40c81103000b841000390014059640a036045400c0850844800560008262400c081d20982e040740d655030040030703a1200c150700d500b20340c90741042001c503642000011b0100b4032400c000c80c8925005402d591030003030400c21040c8203100400b0240c5100d90045207020903100071403204d1600d0759803100004040c02954a000703400c580c0218000910350b90020306005204c0d1958000d0000391140030700c1055076521401076113400e4000081c041c1c01c140c2d074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 458866699 1250 458865449 458865457
    0x303160309080403080909010f21030201060f2d06090b090409020402040311040507050307050a050711030a0308150f01050904050415020f0c1c0f1107090c09080c120c06 74
    0x1a00d4046549100c6503540102e50b0490f900c11508440046074482840c5070040146015000015000c88800c1c80c15503a1008a040a280d149104100145200625100b034200e0009041c251042c07074007995a5010700e0114a041031288650018100c5054450101070054981141e0321603540724441c0d820304010541a0340310307c01641d48107560b08102c00c01600c850020700011030080c8135407508a9004010300c000d445000b408102081000c000300102d1a80002c00d072050b10780a45412912220329103006207080d002c4460700b540c0f5100e00c0306600c04241e40159a0352060030500000e40144542d4024803040005068869007c141c05210040042c202503120551050181100880d2803401d8245241281e2009040701075441c400184210404020000c2d0b40048500405003101d520380e01e40b0003000b030085014420100074070b81c004040450800c00c00b400160001c808104081e440c0e40001910b1855103220300f00241c020a044020b40d03186c105011490707400e60704090042c9254410400100d60303c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 458867949 1250 458866699 458866741
    0x40f14040218060c0708060c030601020d020a0215220b0903071508010b0f09040903110c09040b0a0b060c01110d050f090601150c1a070201050f04330c09050108060a03050303 76
    0x201e90071001606c1242040050300038030050390080c0c0e4030b082c90000241446200e2170a1415035109030740d54001a11603403045a0354514803000c00d42c54060442c0300545403460050040ba25608000300070411513010b1009290510045044840c401c2c0d840c04880e00803001410b008000c90030600c01040b074030a028005000f802c03000c41d1690701e4201000c000504a8041c104140e00280081c000c6180e41401008801d040240132103210005107817503a1880030304140103000c01c1d517081d2224103815460729410150741d240b4103000001e201c00c0030b4080042090342c00c1a450410300700d051070702182d031480f88201c000b40109500c2e400f0740030303d84c00c0441e0b5000411044400c2010880a0000e40300890f14126070b596003018a610950110705243c140242034460181c03a613100401a4014040000c540c6080d840008492030f000314007110342c881c0103001c031042030f45182040c5400d1034040310300c25501401d0041942c400744c8501e00243c0f00c010504c000c4c1522808010b0450303008001190429420030482c0d44d03491 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 458869199 1250 458867949 458867953
    0xd0e031b04110403021806090106051606200f1305040519092405040c09020405030703060b040b130506010809030f090103050c0f0a050a0206070f0516030311040f14040218060c 77
    0x560384ea0201b5110110701400002450a11040c07150750310b032241c44c150040c05039260032401d0004010814a205061540040c46c16503509404807801d542020b405104000c440c510548071540c000c013421072540034004000d05981ca0320b00c00324880c6018820740c2e00402400c030f10745100c4003010210400a00b82624192421000c0c00400c0319034601080787c0410b0903c040310b0228081c2032900e0460b0808403e508a03020441c010300042c041a100091a10100e941084c3d005c501c42d00240003080061030001340c910b401c912401ea000440b00f8007030b00a2401680d00f23a071083c1855407040e90160310780c02904c1c8a4680c0c11001c009035615503202c0d41002c0d40081500700014500002039031090700d80d501c40300001d17004c1040031603080b844c2c54061154079880219800c00720030076801e0504c01441403081804960102008c00d65030028148a680a2403403002c16084051f5255110b100031610b140c0c1520848040740e410340303c5100d9604042c001d44a2841b441241c031490541e00e00704100d41600202101c2d0320354 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 458870449 1250 458869199 458869207
    0x1060927020a02030904062102132702030c0d0803010b09011202070b01030c1205070e07050d090b010f0902090a0e0403171501081828060e0d0e031b0411 67
    0x855007403008141c0031501c0d40065940d111010280015191075900544500e400f441107040c001c110003240e603800716411104001d6410092614070018408288a103580400507010a502c034500c2c402000740241c001c400301c0300500792080402c6881c0c49041710050484c0310a000400c02d043c81e403000b621903614141003105507926110b041d40100d130041441a00c2034455480101b080c004940184030107480f5645401648085a0712082d036124104d20540000083c81c41c0026603840c0310f481980c0003035482010074000f02d01c0c0d40c00d090700d81daa000c1c040d02400c2103601340c0014034042c1e14401c0b40c0103a4009482000744615081c6980c060325001041541400384200c8855aaa084441c0403441580000d2009000204280c00100001c2c4024410340320100814884c0381d01c0d503000250b5501b0b070b014481a210446500425140d4044e060343d00044c0f5080c1030242407100c6100104446030815160b070354102400306a0020565030303c040f450612640e00d1a10002d62442c01d180d089420340008584034140f40c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 458871699 1250 458870449 458870519
    0x20a02121f0b040b0607060501170d050f030631110a1b060b13050121021f110a030302120a090f1b050a0e0603060609150d0f0c080a051203010609 64
    0x56031b4004541124081c0d1f54800500903980000c050300c1003508800003c20324002030140140c43c601c181c1c1040b8010490200010b0f425681d01c210007211a1542600c418000b20305405011410078904a010340d00d6050905280c07001f401d450590300140034580e6804009a54000c00c840641c291210541d0303040c1e1031315120350301d540302d01c2e440810401d41410002410340c504290001401100071804042c100e1000c0c645000d0b942d0740c6d07607280300dc000b54425030301052416079083d0703a1007400217000807a070f0050820440170316415601034000100c05101030101d9681d210034200031609411001843c0c003194010850100f5410b50040307509114080765844000d459900240c60041180d202d0402c401a1a040123002e0030103011258114100380ea0f00903850802481942c1c09010358813000d4021840c0c0c103522010310902000035031a00e81c1010001481c25101c080164807203950f00c4003660b0502c9a90081b1001d0070410003100d04982959a0302141d080c101001907042e030b4812440c00007070001c06031909070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 458872949 1250 458871699 458871709
    0xf04050c04051906030606090b0d020309070905070e03060108070b03041202030903030708030420060f070321060602070e0705030a0f020d050a0f0e010608030406030b0a080706020a02121f0b040b 85
    0x88042c0c14a01108015203004001015680746c0c1d0820003c1003007a0100b00085c07089038090f22810300b00114056201d0b0b40b161466460315010342d112088250400c4240808070382c0046030503004c0c020580980b860382e8bc0766030703c255035490b6500c60301000e00c2c0c0400010380413449c200420760440b8242d2058900c2e1000b43c100092450308040c40650f12690008180002c02003907001d0500164024150f58580074003c10004065010340c01191404003400034103039042500c0341c0d29404003203000d4000d410301c0401c00110b400c0103007603602690300540f0070704001146c000a40c0441611422407940e403140345986a0100c42e018004d8144d034503104a4090000c04c0144200740280c034803070301900d0070010b0701c03281d0034980c1020740b490030030b1070412645824814410340c0d00120480e0181c6d00f00b402d0225085180300046140c01400c0c0c1e00c0344215005100300442c00c198003147c1382840500882d1000c0e4000c000109240d2140d051113129035168040130184220455990032400c44400020000510f00e0102c0000c18 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 458874199 1250 458872949 458872969
    0x6050a09184706010e030d03020319060305060a06331101020a0206071d0a09020a21020706050711064204060902070506181906050703050601020c0f04050c0405 70
    0x50107065159103004440b01a9040803a0711070701c2481c01501e00340300500880e840b4501070b5009402c2540000008034001e01c8120716026603071f180311003006060740d2410319545407078080d40c4d0340c0a4603007081400a104492041285d0240250159602c4d5020050070702000d4a01c4051510050043c40344800641140a101510005010360060145407901400003090f411400b60b1143c09242120030b019000d03210b440c09101920428400181e03100107a410661340b52544020842241c00314034090040800c45401400f480c520800050000c0d0b00c4e03440d41aa040d000601d00c4d0380640c0c2c03100c00010010364589490441030f070000d04a100c1141005c40718030101e061840342643c02003101402405517403d04d071140d140100782d0f20800310b0811407280d8800b134030b8031070203000e85000000c42161521340201c01e0064503070560f1104400d00440c100b0b483c0400150004642c10700102e45000000f03441540003244100c0c00000081c100320214180c03100b04001030001811008038004180400300b00d540315400f00b8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 458875449 1250 458874199 458874293
    0xa0b07030203070308013206161b060c0213020304030e060d0911040905070b0d060e070306240807110a0611031807060509060705010e1006050a0918 65
    0x2d9659510316082c041d19441042e80042e660000f030410740128144540324030031344000101c40c0004d400300c48030000341c014010b0f00e00750f00c045100c00466a081140352003a07402c010000941104d0215a1400c00b95000c46201d0401381d0000c92400404075211100d90065901c2486030a2a0303544000310408107000390805440107202ba41d40c0d20341749050100d13001c0c80402d519001c43c1c1c180280c800744c0d51030540741ca07058469030740a100c010420581c0a401c60b04280e000e4843c83c161992a454010300040140803070b4401c02c001310094070080003182c440d140c49079284542e640c4a550841c2c035281c1c41103a40c203100c00e8111f9414010f400000300001ea050040c49082c042c1d10f02404c2d04c03403c000a00b03402401180c12490280d602038001002442d0b0008181d0b0a110700407a0055107440245c1012409011a0a241e0b0214000d52200c0c000569081e401101501d1080d80d42100182e128000301003100ca22034a01c00324050203003003600002e05482000007540584206103500d4018001c20311306a17500503111 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 458876699 1250 458875449 458875453
    0x30c0c03081e09031009030908010c0909180b16050906030c030619030b130201050403060e070f0b0a0e0d05011b051801080c0304020103050c090d03050903070807031a060a0b070302 79
    0x81411421001240800b00810000100c0c2c5410103550009035210302c4041e042103c0754807801c03241c0600d4021040c40000b0a9000028480103091500003007250806000b090041860522909405910000010b40b071542c0065046100d841c1e0840d2600d101c1d040c01841c0b001c00104104045d0030391140e40c003450180d2401d45180d40c0702d00b40f500410101c20013004802035800300028042000c95401005950041d10a00100b0801001350004941d0b502c604e8102034030407401c064219076042c01c001f80803004c940300b170304010110701d0310ba003070709c0d100c51050a20060015403119900209031600052018800388202d0000a1544c00c4890344800d90b0080030b508400720f44003242d403d5880f159600705500e440800d1034404180d00c0c059450001c1800080c01c06410140e850000850141d0000300300d030080c41c070080c20483c0e41c55407490010b00542c800c545140c00f0307009065000806030300005060342034035030080006207100400c0c00032a40e0354000411807940010200c00010b01e403618180184142402540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 458877949 1250 458876699 458876707
    0x22050406080609010c050c030d020a1b030c050f030a090b030907150801090b150d0203060406030b010b0a181415160c211205090d151b0206040c12030c0c0308 69
    0x83c145003155038007017052043c0903080101910b001c002000700c5540c0c18200c000140c0f602c40304031080301d40c0c190007801500100070b001026803e158001c030070780300414410301c00c540b05410240d440c40d440303014051884000c00d80d907000034805211040040c40c0c0c80000c05040305d044650f00e5a601c00703401c2c401d0704003501003081c000052019071841d002d1220f00d07100c19140892201c3c00101c504250b44039421000b81c003194040049400c0f0f0365a034005200458000850105550315102104100c0d4411802d11002c00d0700b00507220b052904c5074440c001104d9501d50751000025031300c0c0a00442030410400014400d404000300d02184e40449454482a40078078603c40025040c6100d0403c01c3c0c522070038036405c039242c03484c0d4140015683c12891200c18620300c3c080381c5502103040400c1503d00320070300003851040704c400200e004401d960b12000f0314800107400c80d041102d041800b070f6210101507501400c1d6000e00030741400904001c00342da544031072083c40c0251240043c0e0300c0702128031074260406c40703200704009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 458879199 1250 458877949 458877961
    0x3020f060406020a2c010f050903060109060501122a02070f0e01061d0d110d0c0b07050607090605090108190518060907060c120512040b01030201170606220504060806 73
    0x44041c1645c800c40508003212a06040302c1030160f0b01e0001c03040c6040001e1010407542061050043d500e20f40c00203000c0710745651315620500d01500040c0141400605c542d541c150007802a4011005514005006c1c0c040d101d6045510702d80d0149000319450951150190000b00c0d9921018400028120400801c11950601358014603c2c0e0001f5019a4080c0208104505540d100080d10401517130000040442020550102d806005514030141c01c2600740840010306d0f40b0300000504150344504180d865641d1108401e4500544601440001030f00622010441c2c0d40070713802240d00061200844000c01500800d2070702901d408550100300e8455111401984100401511f9081034003503010300b040c0b41c100b0320001c001a0070754070040e0040841d984020342c1107000d002100d40007180b041c410039492810b414000c201040a1008030700240d1034004100310505555151806428020f02251038210046280c598032101c0503041c0500720311945002a45903100d11482005040000150007145050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 458880449 1250 458879199 458879207
    0x80f010608090309130605100302210108060a02030c091c02030f0714040207080d1119081603020c07080f010903080108060103050a02011202040b1303051c081303020f060406020a 78
    0x1a804103090140320414070994440200588148010582e1345002100b1130510080207042103512546d04160052444003900398542c0080c41040281143c40c03444440300c03c070341000413009102d01034064001c140860b407400180e400440e0441c07240d1a070300d0306080f0004005401c00c03420008400c0141c020064107011414203024541d881d14004001e8100903250054003030341860740b40350b4244101d0780054000f007009440b40658000b80103986003045003540031203000c030060748006000e40240c3d903402c02c151a110710585804c1c0c440c00c43c4099540740300c10b9007882a0081c0d003010520084500507941c0110341d01d4400c128480300300c158000046110105070602500501d03042c0c1110019070488070040c00419400141561859070a181c240c5ca50181003c0304002801160400d00e14040000780306500c1c0c1030a9102c10086c1ca010768140c0d0b0811402034801c040e207100c807a40160210f243d60740010f080242e8401c981030803e0290041d40d91800d00040501e0030306138215403c0381c1255003c143c01c080c0f950302c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 458881699 1250 458880449 458880451
    0x5040b0a050a0b1b0111030421020309010503222a030203070506030907121505150117070203300115121527050c090f060a05130303080f 60
    0x2a00c1450100341001e01041c0340250b10302440d5003284001404141c2c44412540d4406a614442c008000d1030a40500c000034603441a6420780c3c01c2d5003041d0f0114101c44200c240c501607034420750011031038410740c4001510f050300010a02e01d038800d500e0306283e41440c22601040006480b840d1913070211341d0340b0700030000c6440e0fa071001030090f04030b14102400141c500040301710a480d01125461b440f981d540802d503280000319048240d00c50300c81e0304c03000100051407480c0c4000c400c50344818002e60345d60410f141d510000d13052a00c0d0000c0c6400550001b0302c100e404400b50401602d10549103000350030f001c06054050a4089800da91f4001203084005204140109000d040c4e40c410380d002c40140a0b1004168810350300ca010241695241c180c42e149203079000f954010640d00644c1c240444828000a408814500d024141142040e00140201441d0b1088440c000e030014140070520341407809016041e001840e0b040c0900000f0859607484041b0310704d00700f0045101e80d88148003490000f82844481e10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 458882949 1250 458881699 458881721
    0x6150c060e0f0a0b04060605031c0338060f0406050c010506120307030e0409020904030305040c050609060406050d060323010e0a0f0f0510060f090501120c0b07060f0c08010504 77
    0x3002c074454010329000b10b82c011150b81c10501018040d100c41c14428020100c84e0b2080d949881000161300342c120b160f101d440c2400358140ca00b001090064071152442c0d0403a10440031580180400c0c01c0c405544181084000903130150020b400e01d525070458080c82e40c016000b40d8003088000c40d00009510090282d02c0d40440c0540c0c0c0d0481c00204610155a80c0c0180d841c000c06004921000c203040351500c1d44905c131640d40051070300c1810300313040c100940200320a0b81c0655840058003804201030070a43c0c1251581100034040720328003440e01c002210b083d00b00d409106d2601d500c0f0000007022480e4003060034500e40c0a0100c4000c00d0740106003d608442050700011010f812100711080460014814900442c6d006090840c0e20b01491400d2400d00b0106540009002d14014000c26801820100380040c3c1c0d210f02000c20069072611541003900e07840900003040345500c80402e000011205015041c0c0c13920072600131800b46200f420500c06d941d0310003064400034035500d004002504d4540650031042c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 458884199 1250 458882949 458882953
    0xe0102390a0312111804150605220801061707060c170a0e0904060e070512030a18030c0b1e160204050c0904021612020303150d0606150c060e 62
    0x144000c42644840e030404001e01070000521444682143c0c1ea008015240404007070340da5503003c115402a4620703440c02400f40510b1425807088a05181a51210142d54160705d0325400d06024095510020310310741c0004c0030000001c1c8000801d41000d00807900a0002d020402112080c0124a107181c80300ca03500070010440c0d13462101e4080b8201032000c202c82b10002154907502c4501d4181035aa642d11400c1d6942c12586081c02c110910045602c500d490541c4127041c4c1c0c2d1503594407010007400b0801841240040e4104125141c45240100864281c0e4040c9402160f4500c1d940d80381c640003150103034040307810032500054820301c1d80c80d01c807240603030842c41d1481d8505022001c450706184400c9000000d0003269a10040741c0080c030310b04140d80c031443c80104195503070b00d4400034030810307403884900455034482d09009001480b4000301c140e9125203050340003031880d1003202080165820041c9402c1d503500340e49a1002c181d1248050b08230401041ca91601c0d1041459803070b11808458200101c2820740d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 458885449 1250 458884199 458884297
    0x3060f041a180106081506070f03081014090606130807030803070801050402030106120b03030d06030602040905090c0d1e020a030b072304060e120613030f1806050a030e0102 76
    0x21504101e5090b041881c03080351b080021b101b0030101390309124150700a401214040c0191040507070010202c3c4c801ca1198080c0c2c00b0480d40e40c0e4128400a030a03071411580801e07440300155080c2040c0300940020f5101c04034180070030369650b6155007040b005800507244268008100000160000d10850041a0a460440c81c40d032510400400c0c07100441088149a500d0703c003016240c0e901001590051030100c07a0030000075a592a0802c000d5000c1c3c41440d0440d410000081ca001001040029903104090a2190001100d13940c603003010818204010941404501880268444030744039406107210740300aa8031400e003400c0c040c1410241d1010303900c8185a400701080c00014400a46084131081d007042c4070071a542e10f0000382000858001036009116110810542d08100701220003828002d03140e84150b905407030011602c1c0b0403440c1488110f100d83d02010002c2622603001840952840c0c5000a122511b41441c1401da07800b0145a149007580744109071500c40d88400359000700039162030403120b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 458886699 1250 458885449 458885459
    0x906070f080c0d0903030f06170c0901031a041e0303020301170606130f020408010e0a170301050a14010e0a0f060f050712050a09090504061a040b130203060f041a1801 73
    0xd144030f00465000403030380301d8450a08043c003c0c0c0200d00520210441881101d890303850070b020102c400303449201140b0ad08006c5041700e041241c1600d0617070b6004010503a503420010b10014460034081e004880c61010341c02c001283c15412004929010b00c66580982d9951400c00175034001c91001200204030307080311007400b1850b51400c0e405d682c07031044030740e0105d40070913058408002800f455100d02c05c030394202a408564031001041240925100c1d4130407a00d550f5000c0392940e4680824001c1075004200001e01b482051007211050f0115101454031041405602e00400d0f1071100c41e0f840402c0000320103609010a81d000203010103c15200d1506904108813603d80c400c0142c003440c812814024002240c0403c103200b01c80500c05070225030000e0195080c1b6213061002040290249100c2c40894040045a403400303016594092030010b00300d10304002d0130782e1500000d51003d404654880b1900d142e40080742c446000d270014041d14070402c010407400768002c1c84580d84c10700500840c42c05001c401845 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 458887949 1250 458886699 458886721
    0x5101106071101060315330302060d020702060d140106020c01200705030318130903020615060c070b07020f0d05060f10030b1618050f12010b06030906070f08 69
    0x150008092400d03602180c1e40d0b00034030f03005280a0f000904541c0740c10180992102068004903000700032000c941320f115031840c900441c6821045410114030300c00300030030030152401c00d0140c0540c410b440d50052510040da800105c50354400c00055a1244c0c403002c810201200c10211035004210324005046501c02c5039000900c01c00c0b10140700c0440c498800d10312121580c0801c48000500700260440799140310b02484e03100b01110545103184200d0100800000803155030040180b03007541500140500e84400002c81c0521400d4030139507400c2403040c041804080d1082000900600b14500003550311074050050140060010160501072090b4000380c6000450003c0c80c02d40c8224003002a00046e1186015010302c03018550002e03040d9000c0310148450108035284155107400700e41c481c103100b054400e859040c2030449109003076200102007030801840c1081100c400482c3c001500006466100400080140d0000e40b03030480254030150412902d039030440d80e000f641c030010f42494401c0340b40c8020142 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 458889199 1250 458887949 458887951
    0xf030207060e06091915090e06010203041802030a0b040227040b06040b0c0a060213051305010303080105210d0309140f0714041415040c03060b19140d020405101106 72
    0x3d03000365445400f800c0c80301400c80d500c170302404514520314004604650005c184801a010302110141c407000441c08540c0000101d80844241034a4030b60511001c0c1d146034000d400040005a07041e03192141124155540d2006209941004003c0040400e034034056118451001003500e005501c2d11580040035a030354000d8074101e401c40742c18543d44d606106c08150800c0c40d02100103107034a0021031480700c0f1860043e40707941039420030354106010f50f03201c0724101d0585a0a101c00b074040b403084001404182800100380e01d03c0c601405800c043c1702c0b10007500c2c51410000e030344030714001b030781d05c0340c4a8040080954104104860540c000c042070a5000e0038103450b10f0940c031401406008410280e00748c3d840e103400c0300c4550359108149402131702d0305916400c020310110808900c29840d048408044a0180c1b240a0a0b6444034920b2410302203005000365001c02c0c0b00360b0f0320303040c0414000025490445400285084100c035400561180c2c40e16003400344007500140c0e4101404081d00c1c6641c3c020500003981 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 458890449 1250 458889199 458889217
    0xc1e140d020624060f0c01020702042a0f0203040302060c07090c050c0705040f09060e0a05010b010c05060402060d060b0309070305150702150a06080f06090d0e010f080403031104030f030207060e06 86
    0x280a55410341c00500640700c2d20241040178540070480005041041d800307090114001e440130701c80110900600b80f0403452502e1080c140c4449051304044082c80b80c001c0f40650701041c0103c82c906500c0703400140c4250020112000c0562101005101030305180c01445417a108905000f42032140c03151000d502c800701800303042d000f5035460780c050101c071743e103600003910068011804016200c5000035164990102d82c01c2510303d90308065441d01c195216601c2c07903007a26088000703084903880f15400c00c050340d401368480d0410a42ca40c9400704151032036100640c01410203400809440c1c1c51440c1850811741013260501540c1307010001c0200e2150045118003030403506980d440071a550b142140030080c445030b003200d0307003510862602480b415000143c031400780291004403447d4420b036200c21161109158241030001d5801c640e842c0d401070091031810f80062081c18080f134100880c010300c40c2650090751007981c0c0b07042c00142c20024503405003d61030241c0b56602d44813806401000104025110301021 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 458891699 1250 458890449 458890501
    0x209070503090a0f0b060f0906060412080d06270203011d07030f240803160201080405011803051c1103190608100b10031406010c1e140d0206 62
    0x5503001d02c18003250449560090824101c5038060402100c0502c04131032403030045c80380d00720010b080d207030940031030303104140060002d032500e810100031712100116a0000c0f41da10106000d215610301543c0221406450300700010b40c8201d98152141004814006101f44154810801405184028100454400f14600d040d4401e922006000c40c0146401e41c0d542d407141d483e01d5420b00b140c2c2202c0c01410041d110780e4410f12806619a01070716101c0c40360358041c070a0005d1030382403c00154003460034658130a01030000003586245d15107071140c802c116920b04800003800000d1200111052000841c0c079107000340801c011030030f80b01091005a10001e0703d01540d080c1c0e040038070b0540001c03d0300540d003e4a440300603101c03456100580c08010b411002a042e03c07404003440d841880138072a01c00c0d61f200011000320042261601001522540a050025501e04014601c0700d81c806035429402d0040a01c02c50315205130216000710316041220310b0075500c0440d04280140120824030448102071010b140d41 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 458892949 1250 458891699 458891701
    0x9070e0f0609040f06050c09030f16091d0d03090317090c0111120d200f04090209060d0c020a03030e15012309090109060b0409081e250c050d0209070503 67
    0x1403070340c02d03403a0502c1e0041c1211b042c0402c00c261981642c02600000c001507040711001301c2040754050326107104003030341000c21440c542d0401c5800b0107500482ea00003480c00000081d500c440510905016450782c402d80825107458404040582c4407001442004815400047d00d0411320903142c1c9865200c403c1c281040045096408001400d00c00045000c2a5039001580d4010700451007001d485107854842e002510a1615001c0021070030480c2c80c107125269140e07181608201a0b03400940000d0030407074101c4020f02440c0e20150300c074801c0d00c41402058005002c03140441c0740082c2602c0310742051411a0b0494050110340346203501c040c506540c1040542c0c2e048081c030610520951001c600c0c00c130380c400c070034000b4800c40c0801940008030040c080c0c0c00078030801d91001e040c4800d40f48060401800c038403007040380c207003c07094100d20448505004103002d490300800351200c480180141a5160061302039500c46410441488903102c028202981c00d0072a0000540014a00d030130000e01d504280301c2c2c000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 458894199 1250 458892949 458892953
    0x1006030923160f18020415030c020a0b01080102071704050102100e03070606291201030f03090305030f0904140c0f16050d0507060b0909030d02250b09070e0f060904 72
    0x2c803110680c0341810242004080d581d2001e21008400c9200d685008203d28010b00011202402103c0c242c80c44241c1c840c0120000c00c038218001e03d84501140b045000c0c0b0003200e00090b8808040a000380342000c00942c4074411420003240101c0c1000401802c4102040100000d0b60003284c085020302042c04005000c810010f00349013103104c0c26600400061a00201043c080d281410b401e040c0019050150728405c00800d030714641d881010040320000140c50010030008001a1451054500c649058005160340756601c510b1a004448414104540070461203664140703031080302448213401c1c090602c242001081262036104800740322070b0507400002c03000030303690440b240c99043d10b9001c805c407070045072480c10040c00c9400500084901c0b0b800c00e110000c03545054446035000c4c01140c40038502d0484c4506100e0002e5110409814070f2218400030321384103880750010a5003042c06000c240849144c035541050070500c858200c0307900503801c08248511a07001480701940004213492040c1c103920340d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 458895449 1250 458894199 458894203
    0x31505040b130f0212160c02090a140108030307180317031003051b040513020a060815130c030509060f040209060f0d03020c031207030c26040603051006030923 70
    0x12620200c1c900f42410190354001d60264000c000500d04c0b507280d02d003180c0311400590300c0041c4105113200091017065101015141c411100e42e044403290b02e0000e8030b01d0180400e034001102c240d0203c1c030650004070401000e280c0007105486104500030781e420f480c0313056940d01c21b020340382d0440c005203040c0080f0000c3e0f100e6080c6401e50001d1600030b0b08881032000c0004500703100f100c6840400d4003a038205400300b54007883c2504024143c075801008500c039142849412104031600500038031000f4441601c94a6a85482e0000e01014205540c042684110910064250392001d410450540c0c072000c10001004025036100e90050b43c1140e40c6461030f15491700065211015500d400d50080700d40111504060300044d113007101322010b5055503c0fa80000900c1c0307031a406041005404139004549100014541001d0415001000000b02d07480100c10040101d55412940282d00403a55407000d2004c0750501095290050405260500100d02c040e44c40034140e01c503a81e002c2c00342c00110070b0004407100d01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 458896699 1250 458895449 458895469
    0xa05040b03040c03021206061c030807030b01050d110408010c08060a06180b040909020405070206071713080c100501080705100807033305060a050a0804080d05070509030d031505040b 80
    0x600da1b182414500103440c1d02c030700094420302e21414240518880199120701e8100100743c158a0b46499551420710035405820341c0d41c02541003000800844254540300d10505150500d1340e41603d07212420490014211400c0b094404103100a26003000610782d18000190f00f942c00d10318010500c040c440c03583d085041000e802250140401044c0420041032aa03c103500c100c1c02190188080d46132a04103030703107540c0190b030b5150000d01d217401010414204040301c190080c0800d039400c03043d40075503200c005c2d868002d502d0b5a0f0890b0020100d08108a079180951409000c0c1e40000e413000625003c00100e108101d2003c1d00188440c83e0000b80c14039000b6405100d032048218200e1006210040c114103d12580c0c030900c840b060862803010445042c080e081d584000782e503490351450300e103a0301c50560710320308000c01c00c03100c0150401008464540e0790180e240948030780d480b00d548800c0084c0801d4100b40c40d0613600270070036140c5031104008010110b1f90104461040c1d40015501c0c801d14041000c05038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 458897949 1250 458896699 458896703
    0x4080f07081209010b09090601051c0609050607021b030616110f07180603152c03040e0903090904060b01030f0207081201051c030806040902090703091104020a05040b03040c03 77
    0x40c0420325495902610ba000380c441c8800320000c02848025804100ca0b013003054a1042c0c0e940d01202c0148020305001280c40c0c60782410140340020f0349410f41d14501603400d4400d0844107900100c05001510750100640c80b000c00721f10940404200507400030960703074000102240c00d5040705425440405009015203070f404d000c44025038852014003000c09070b4541d15031040041c1442d08811084080ca854480c05085d246e014242807504450300c02d840000e030100112403240c40d1200754001c8044a50303105516020310000001e152220702c0c042d4102c1400c80001d02c0701c18160410080c140396507032000ba005030710580c00b40c4001400c10703103100100c00424501e18134140c9035100213807104c2440b2220001c1c02180c0817031200d60043eaa259000d202074504c01c00744403021900350340809000240590080e603400a400781000a030b1440d80c1d000625201025103c00020130791342ca001405200c50186054400e20040c0d50075898400c000400500c21300c15849098850070307011000c038080004800401d00110703 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 458899199 1250 458897949 458897963
    0x3051204140a0b0f070e090103150b100815060f1b0f030f0c060106020703150e160306090209010509071b08040509010e090d0c03361205010506040209030604080f07 72
    0x45100d01d460740345101c0664481040307004e8180011541446200702100041000d00b0048160f440e5681d01c1c0408003400d4144002c03503440d1705c0740e5080345d180c078580c5c1d845140880d030f119203060614170550180360000007c100d0056808010300703c003029421044501d802d80074035030030b0160092136280f01e040c80354400380c502c035034040001e04e00d407044003e13000b42c07207240100415140d15980e039072000c1c0d035030322000e1000030840c40da54040c003800441c0d1607110f50380003441c100a40d21040d880f45034404000001ba002202c1059955520005500f450b182880c00f604041c0d450a140342882c0b00040c0c41f80400c2034000c3c0940e040d45070444104100942038400606018000103840d5850300003070382c03501c04100d6240d07999110b60f04146c800c0074424400d0361603c5816441d160301140c58080e41c1610b49200944041c020160220380e050a050044051001000710030180c1c0b412a00600d40a4251000982031a00c00d5005100c3d20141d035501007041500310390301c20642c40c0e4036820088034120034001e07418044c20034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 458900449 1250 458899199 458899213
    0x51e0f0307090b0a050906010c08071e150e2b0504030b0c0408120405060a0e030102090a0b180a051003020702031c0306030b0108210c070909060c09050303070305120414 74
    0x9441950003c5001c0403084070200070b1303103407190107000500b00101c41560005120844030b00c003082c21800200452801444108410709040c1240c1160140c00481260f0880c0c201c80361001d402c5261061000c90100c50700508407450781d82054210440045104100c10180221000e4a4900030b50403180210707400032094003c8d00d42507490400c00d81141c840e2062500580203c0950210444100c50030b454009040c01e0500150350b034100c5160100c20150b0390959401c1201d452956984604500103249500100f542d0344990980403c201c090b000c2528010004040c1c01e104035510100e00f00c0f1340c4000c1d0700e00143c032550140002440c5c00803200200d01030807000e40f80d6404245e4580c10032400e8a00480034541980d0742c5004040c2e440706c5440e41c208024480550340104120a4402841c5201e1090300320b602681e11007428504903114070600701e445503511110030728400d401201036801054200c000c1c2d42401900e032030180c82c032b01c601c0724040e840c200c44000003420040300880044800002200b06c40e15 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 458901699 1250 458900449 458900459
    0x32e03020f010c0203061306060e010b191106042d051c0c0b0103110108010509060904020d080c071412030903060103030c060f020a0324060c0308090304080f03031807051e0f0307 78
    0x194044207c1aa0002e00700368022501108829082d030486a0302c00703d20b4585504074420581403890307003444508000d0240100c0c100d40c0000c000d07442c000c501403544541e02850942200200c1003400030003800d14641c0c44210300100303101141113010034072070711801441d00f80c919804849000303203d9001044001820000b1051217414213110080103c20307200d031a407690321501005005101110750b15800f00b4076100240041c2006182c400f0007a22a01c0054140008281070a0510400c0c2e040746032881220000701600340341c00300400e041500c03200d026624050300200401d80701d40c0c050001500740b10003544030100f0480c0039881010903900c440411902c8811f0147c00030701a0169000a50304080300075421403248008442c80001c4420b01e0f00c030214841501c1e5016134491740010715114072400140000908020b050002690814241000c2d694a2402210304001340c0b01c0c3c03240e034600070b0340501418403c5450342001d1110b081a85c2c12059041c2080074001000b5407108591190103026500300025 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 458902949 1250 458901699 458901721
    0x105060a0302150f210604110301090b0307030605160201140702030a110709090804090f11091003090807140601060804080d0b1f0237030503060d0c0308032e03020f010c020306 77
    0x81700740c46819180109450b030a080200ba604803c4002102c0c1c881000100144240e5911130001500090280d0f0811b40e680d803120030468134101c407500304503c0e044910b520300c60303070a101c1d411680b80b003421865120f0414540003541ca024185025041c058440b20302000e5810401082d001881c600b0020f101181c0c40c0c1c0742204039034206102c1c108105041151080c103030b0040e409140003115000b51054203107240c100800072021425003d40081c5990340c650030001c620301c81c0061206500600c4401030262a82d405c440c41c203030059010008225074401800b0001d1a01000c40d02d6032311180c0008210042c2c40d0000480850302c2c94440d40701c0d00d0121200002c034076008a99020750958400c195440340c1881c9425804030301c4403a500001e80c241c503d0201c4d000902070303009540c0060cc01b526a0000385155a00c094411201e50005c0d103c1c0040401080302400f2400d200c51156003040e050790704000d0402d00080750492150100074410002c82d0050304099100b021244c0c28213030004c04031480d034100003080c44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 458904199 1250 458902949 458902987
    0x25210203040e0a05090c01050a03060e0412020f0f0706030c09240806010302130902070303110409020301150f02210c07090603060b0108040b040b0a0221060109080105060a0302150f 79
    0x2c40e280003480090540075052007201e2041c1d100384090402d9880c1c1100454040d84801030303080c24550b6510000c40d80b0000320024030f20442c8902000300d80e42c1c01c2000068504400e000c0c0f021807a502c00c0303049142001004c9603000882d041d90501244070722a0040a4030401c850390020081020076520342c640d0320400c010362410511071510340005035207650004405910501ea15022401d8410b1020841c0107100c0c0e00416845009190001c0ca1117124280d141c1c265200d54000c80910b600800140415150709000005c50b1065050440100d82c0e160340113500c0d24030703400d00c0d2113a00301c4c1a50300752201c0300401e0885494140c900291080ca68072120081e00400b1709001c02e0390304e50b2810f40d681c0001c1d4002c11100c0d02803078001420310001d5981d5690101d1504000f0004001c403502032081034021070061410f88034513001286940031600e09607000504440385030340075203456810003090110580344c8410140550f50103032040e1198a036014003440d000e1044140101c01c902001a03981c1e115407100542c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 458905449 1250 458904199 458904209
    0x2070c03081c1407050724020403080a080c091e2101061805040302150a02070204050103030e010e10080a0b011710030215130b1b0114100b2521020304 66
    0x1080581c404040f4242460822039003400800c0041040201041c140c0860129942c00d40c44101c0c4449640c009802c180e0704140e00440b801400800c00b2900140c015404a600107940f004450a000070400024044030541e04801000891445c0c03208140c3c46099440c18440602c107042e8141c070340004500e50081c4081d00c1146420b01101d10300c01810360080c090b150180e0f4055000b40103064a13022101e070b0b416006004110519420800100103880e03500505009600a03150550130120040000d0140c00802c0b2400d4403482144085542c40d580015046030004070381100000c00b0242280103a40044442d0740e1034102c1c0c1c1d042410407600860b441112401d50b4400e603170b240445c880c101d0721901207000c0d90980c0c54200510004c1848001c07513600c0034000c1425145c407080e0449601904141c00c580b0110300b0b4610300103c4a0070400143c10032051800207104c12001585000130504141d900b2141c030510308800014140c80381d0091103462079288000010580b0a4602380103107a4005e986c80c4c0c00b9101c0c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 458906699 1250 458905449 458905451
    0x1e0e0708010f0b060304140a060f06090f02071703062701080f0307112205100305010e0304060e12070f080a210804020d03020f120705070f05060d02070c03081c 70
    0x102c2c0c1e440303840c80e010340d08000b01d0180c20203081d901e071340c0d5031524203402e03211900c4001d104400511012822500650042e039032043d60002d6568204201c20003903400100f108104140104100070004840c6c00701586072a4911181c1c1d61a901c411002400010b0102c0204030241d40c00c48104ca42d070901c00080c0342c1260000400c030340d000381c20300300407507100c1c00b549101401a880710b001743d40d0b05041c0119071050f01c0b00c41030380c42c441c0c2c3d500d050307071010807104183c1d507501c0d8056130307183d040c010040d00f441550326401152000b14149458414001c20413203007108028081d03060046407207854801041004094141820f00040c203513117603175201d60350300a0060161840790540001c80c02d9040510003444840e02c15640b14411540c60b5006d1122002c230312107049085220306440c480303400300c051042d05000d43c02c0c07030300c030f0399403010300c0c1c189580703040800d40040406403914481000107988200c101c032940419410b01580340c0c032031030800c140d4403d090703070004d02002c9001454858004c00c4400007800401c040c04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 458907949 1250 458906699 458906711
    0x18050601140409050405150703090b070206240301020702030307030221030105010c060515030d0908010f0225030c0c0b07061407050a0c060612030801060206010b030603101e0e070801 80
    0x8011200c0c95481c2440900d503400800c020b01145003150411a48540035508480c0040100c4554245041c1d0845031100000e549410020412550580003500a0141d200500440c20030710030240325503016030030240e4403043c206802070745034034290140c443e01a0010280c0780c40c1c07242400c020f52030b00d040095200101d840c280d890800c0c0507048003034074140e50060790b0303a107a8081503503038003402410007412800792811401c02d0703c2d009680030810f0031580c0100e5940c44041514291125082d03031007165082806c07a0060020010b44100900030441b110408c00180845071030504043e500300c0304060015010105e40300d40803500440c0c42008190003445454100060300a60401c4d0040703480640c2c4a0b80014400c007c10110684200c492001c00780c041c0d2030000e88aa41c8058960500c41802000c03800304980358010045a60188000780c018015928160700c1d600e4482d00003501c1d00c041d00d0b4a60242c50307403094000c83c03841c03044150001c03100394604208180c0c1c040450447e6195014412288a90700f800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 458909199 1250 458907949 458907961
    0x60809071703090405131202011e06030b0708072a120e130b0a080a060507030b0904030e1509030a0c03020405151e0d02090f01030b1008060a0f020c01061805 69
    0x401c0140502900310080d50034a14030004102c0500b5000d00883c0d403000101032010049180f016400080d5500c940000418404c07003408404a4032802d01e5800c401c5141c00d00c1000491110030990303510440c075250801c140d40e40c10000355031040403030400c1002c99030703d90007004425445020450065008403120510440140c20031a00c2d02e00d254401504080108450f900300b01064104081292006104006544c0c40e00300c2c4924000b51000e050703420b26241c0e000d10403441e80610a00427036950580d030b0b030140c500c0c00b6200a849c1c40c1e0700c0d00351140200c0300c01c984100a141c0b42c400f034450a00340142902c8000b01039061040540f801c0b0b0000b68441c0d0b181c8000b1820b81240020038082002e8043c007880d407000020314150418030402d8a01540006404400e10016035610714558410302100c54000da541d4114140050f200d90000d09410610320703131075000d00929600043c1ca560003001c1e0403022511010700201c0700041d00038130406030a00d600b06440410204489195202132840c46601040656211 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 458910449 1250 458909199 458909219
    0x60c1204030605071403250e04020a0201050103061406010c03050a1b03021f0e070902160605040311121e160b01180b040218120a0b0a09050c0f0622090606080907 71
    0x80c0e90407400c0d0343d0340c44a5034503441c1c6052184c00c030911460a000103023904000c00304081e6400310500340011703591000180100002c0340320b00b8901101d071094010462809400180400412802c05001c1c45400f0803540700700d03841101401141c0130b0700740c00e006c089817851802a40d40c10844021403410081e0b400310a0809141d84549002c620030180102481071600a152000754400278511550040c040e00110109059005041c02548650b03600148112030000c0641081c041c00b0f10782008441c20408100c080303480e21580e006001c200481c5c940d9541103018074007902170702500000d02c0107807200c000081825541e2101d038029841c190051001134103c0e030030001207100d542c5800c2203050780e0680c41e00450400c04d01259a43c48801c0494040c81241d8441c14540641240c1c0f00c07440544413000507041090901440010813420390303110b160000040d0008800d40110400381c0c5034400118a0415440010403400c0000c0072050820000c05e51110f100800c002d0342101e0b04c04281c8240207000441e0440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 458911699 1250 458910449 458910451
    0x603021c0209070e091602030c06010b1b0a02130f0207050a051014091905100204090618021303140102041d01060908120304060b0109180605010f0e0609060c1204030605071403 77
    0x17030852482c0d40d1482507010280d01810042c4045102c02c1c080d10030808410031856000c2c0401040154460f0010b85640d0400701407040e4030b811075000303c0c443c0001a15124884405840401c0020031100540b1141300001e000f0440c02400d140f044011040902c040406d0409004101a20901541c21401074160107401c0c00d6074003402c01d5101c035455840b04180390140c020094440c4082c0c0704c0e240740c0c000d003800c160f80142d040740454542e00c1208000030341210f46802803149002d40190708143e00d41048460f8003079544005000c5c0c59002c0d41d20901c4080a46c1203030b01030048082010b03800e65418981c91210f0701c090040e40049403800790041540100002d03907000451080100d1803840e501c0d6a103d00207401022203950622403c0320020805c850307140c040ca08400b00c03064001034994071b0b20740010001c3d1032041180d000e20054000400b941c0e101c040446422079002e4840554502040401c1031820410075428940c0303400c08580842000304d40d801280c00f41003540e54a005c01040065100c6032444 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 458912949 1250 458911699 458911727
    0x30302060112110d0311010f0b06030a0903050409020406090807120803040809030106050907120c030b0604090510031403030a230a1806060b0d11040305060f0a0603021c020907 77
    0x400100100b02c0030300300440e4180e0b10361003440c0061002d0003c0740803800002400500f100401d05094901c040c050091064240c0e4816400c4140840e812903004620240301c0500003044041d1a005140d00f8503004801701d0b001005a28000c550b03441e600c840c0109111114080d420050017000400906202150b8030a6040742d00b1400352451500c039503482400c5907000000c2144c1554130b4080004055550045051240c015625140c290302200000c2d43c04a55400302510141403408000d03016a44400050f282615642900003a040e15170012601425540380d1000f820002000030203e0540f8000c000740d801605820310a2111803c4802c110311025440b8415401d114400c9000070780b40c403e00d0300401c0100343e9004000400080d540c071900305407281c2d41c000048000d00021000c4242d00303e4840d02d41c100c0c104c008014107060441d9640e51725010090003600300f440c000e0003c45c0010340240d22000c025980100011500040910358250340c10200f0b10583c82181002d0006450138040d00701032023441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 458914199 1250 458912949 458912953
    0xc17150c0a1d03032106030703030e1512010b0a17010b07021005091315061106010b0a1b061a1c08300103020a0f0305120f19081f030302 60
    0x101d4600e008542c840071540c521500d40212488052031501e05200404244d503561060f500307140001c01c0b10b070508000203000c0b01d0295001d40e07030402c04290301100f80d851441c0101c6240c2e2940300b10109150f4240980226200c048105800010704440c0e688018804100c05450f5110451300f500d02c0c140c1204030900c9009200d400400241c1c0040c68052002d0740c40014a040c098140b9070a0008640d460815036003103a03045940c0c00d0f03200100d48000941c00018600f40c6040c03803000f0b040306ca5568440c04184540420b02001140c0c0e021004e000c1e210748952203403c540082c0c92a0300c3c6007400c50242000d00c10105881112040920700c506003e200f50110450120464510300001e541d45041580101802c0c42d00410023201c058015078012030b01e07072031240101c0510581d54194010043d20011940c080301204156034030400c0050000301340783c04850398a00185468410000e0000362a100f44168400c1981501011180d5207404c9865030f4000e95501241586071007030300355500800d90440c0400340c003507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 458915449 1250 458914199 458914207
    0xb030703090c0b07151d0318031e060f060103020307050a230c0109050105220b060f060a020d0f09050117060a0506070507030b130f1e0c17150c 63
    0xd0194101148191149810000540d90b03a8250b01c525000320701d0407103a9142d81c3d5501803600c1c4d240d006041000c401c48610050b41c0605c0303034005030340b031081c010251100c84d041c3c0031403100b41e075060110026078460007541d000c0e540310041469850303030000c603800c0035600900d802049207540300b442640c2c81a0b20945030249000140a001d17120300000c1c0b42c038140800000010300c2c21800001015103070908200c0004501c03c2240c2c584a800e54100030315410080399004000300460000f00c548207101500a050200a07880b407002054600f4a0203800541020740011a05003550340003640e100304501d1903894203c0000c071020100c440600d1481f905000605040001c14544146603030306030080002800518000c2e5103602154180e00310700c4054540d0380150344100107000316200020b5001d526401c0000d4855515603940000c50305007203014184100c00400303141000340310552a100c1e550400601c2c1d8845568a15614900d23440c0345041a403402260085000080c0700000306001d04aa4100700f0700b8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 458916699 1250 458915449 458915461
    0x6050604032301020d0b1206040309184a120a11010603141203010806150f040518121305040207031701030b040c15140309010603060e150106090b03 65
    0x650100e5845115000c0b1200e400100070b8009100820f9034440a003070200310a11940200050017030f00c60f07070b100200d8102c2020440025403203c42c0405644440c881c2924650301c0c444a1402440d84003011648540100307d42c00b1880241c134500b0480000b03c2c040440042d040822410205840f550044020740c00100c4c40c4800c1c481c0c01014146118292510032a107425103140c4c20f0030341c1d20b19030060322990400080400100b4090002d98460140744c0d001c5440c5514042603070741e8908009214203624200725000c8a41c0b59186004920542001401030042d403e20418121a81c550714070030050512502410b0005030894105844c0e03021124015141000d02e05420302001c3e6100f910214104182e4035a5420100d80e41092113001c2d41c054400030400e803a1520345028005c03490b0f009000440150314408607180d0380082416254808134800603113035200e000c1894054042078000512007420040042d0030b14000080c02c0307841d41410303840510240d0340c540c402c2d42c040240d8051194004401c10003e15 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 458917949 1250 458916699 458916713
    0x24010f08090a0803010b0c07050604030f0f110409060501141801141203030f0603060a0b06070201030b131a0f0402031003110a03061e0f05091009020d240f0605060403 73
    0x10344810150140e031601a425955124144d03c01d030429a82d15002044000b1011800c000580103488250386161800b81992121901e6030a2020014030b0903502030b00d050100702401885044030400a482841040c903039180002c0a88024080c1585803c08070600d80814a00200001340451042d0b480e0003075a42400400c00c185004183c4403a0444260007000b4540601040103520640c19500808414140403081600301100505468225400c0c00c0c2c82480a650304001c070b4070403581c2400c00007208100b40020616018110b281028003070f140100c00d14a06415098000140b02d048503c03e41c40045403080000f28041564a1110070000d40c1003070001410840503110380800080407c45010f642e9906c0900781c0340c09191080884000400e10407070243c281c01208000d20841e18203021500c2d0400801359200b1050641c41507c603100d114500541d16001c056619054221804500300f028010784242c001c10010031032000700d86448400300180d51180324400689070003c161920301841e540301e4007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 458919199 1250 458917949 458917951
    0x207050c06211803070b011502060f0a05100317071509110d0302010b091e10140f04020904020307020102030426191e110f0705061909080a0b24010f08 66
    0x10a01020f4101c603410014200040c1503064451002c4403a150304090b0480c00401c2c1100780c4a040d0342c405001c0c00b0151015400f2035500600018000440c0c3e512220343d0340c0351500b507500152544d1070311290303c0e401e0102000101500e070b0082d161401d54011058420040f1058002d01030201c00c0b80d410003640c40e251501080d0001400b92001040e89621980000d158036410b481c0ca101d44445e500e40002031020501006074000e04040c100b4071500d181c05074401042a0128a540c4222078065a0b540c8a940303d5050312011500030700115142c0c940088081d0003940180e506a8809800c1c03c2540b112040c0d1500004142c10020354440c1400048003001c000c41420000140602a50f540b001024a40e2071460350803d02081da00d800041180c0500e10b4106000403a442c005508175a0042c040c50302c40c0300850301481050201b81c40540001d050484882025030810310300f6002e024103400030b009903840468003400c07980c0e842c100700d60200b40244103000000c00c0c0003800f00c2d8031006000c0065000303100807 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 458920449 1250 458919199 458919211
    0x1c050c011d250f14100c02090402010f051b010605242a0f0a11100905120a050d030f06141e0307050a030303151508130606050d0302010207050c0621 65
    0x20010083e15203480104008a50700440310f20780b80c0125003581441c0503901c4520401c02c506200e140515203802040214400030030180c1488245032551010b18031030021192280e41c022a40d507103002298401c2c034040c001d288074a03803040c80460360100203002109a44280d0001c011302a03843c0c0b2070740d0305d5209455403c2c1d04e11202d42c1001c100000f0000d80c01400880c0381f05200714060551006146800d282401c015400503010701c68401c07010400a81103402d58042d0382080f0b031000c021449007082d0310316122103508004d0150150b066840c0c4101c0d05a0888109590f015205004040c0c58080100e1040100c6481990000400c00c03440c0102d40040b0781080342040103010b54203001c1e107420226041c107a031030b0700880000c4e940e41c06c503140142090002c907020b00b00301c40710f000d0000201100103061403000742c1400c1c00c0c441e03410011130030401503034000c2008204c0a048000341d14524203010b4001d40011506541d10301400742880f1051038900120b80205108130f214480c00060000450300c901002814 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 458921699 1250 458920449 458920513
    0x108061305071b03020a031218030503060f19030c0605032509092c0303070905060a0e0316240f0320120402150a0f050c1c050c011d 58
    0x14007090064020381c0f030b01c1c07036901a07002080c1d030405615005007015114003c1e001182d00c0c00542040d610385000810005540502c1c1054070b075118440001d23422008940d40d01c1c0d100c40c403040791035000203c200b28801102c0c00b803640e1407060356407114259640e2004845980c0c0c001303102035122550702c2c1800ba500309484032a142c2000711640300d6031800d0031030307114003c202006243c2c01d000a02404922021529001701d0501442c154104400050403054050180902c2100003080c1c4904907445030000c41030741c91000f400c881000d2003100d1905001c6440b4080c4140c600380d2001e607210f80c624003003541d0315031074440d070780d000560341c2c000c00d04400504140741ca00c92071a00d4441c11051083e8030340064014000407010054140c00c0074070401000d041180449528620140003403410750350801c801100b04000c0e803c00031345c1e80c8a01400c250400480c0c04000c40310b10304c1c114030002003582c800c001c0c1c111075101030002c10410304c80542003140c0348000f5100542c42d0b48210752460201541401d8060034000e0015 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 458922949 1250 458921699 458921717
    0x2060a052a031f35030f030f060108041a0619090b0a0501110c13090510091202010e1e030c0d0e090703021617040503032106010806130507 61
    0x18500d408911459407400241404024800340307602d0b510f06074402c0c511006010f9580d41c0741c441c00d100f96440d482200c003d00c0e41e222074629501d103490a90f42c0c1000601d0001e07aa581e0103901c00b41003040d00162000d1040c000b001001608950007924250f00a580028042072182400510690b074020010f1815812201c40c2c202040303001c110a070030102501c00135001040c081c030518244440d445480e1b00c10350400600c010040348407200071807543d503400e40c01d503640c11252a0340c550040140111801c000d01d288079200d070b10b07104c0c92501d45c0920140e0384201465a840b07440c948040b4240e5580750841c0c0304540007484659903240224074042c5030001903c09680c241708540312501d003000007125134240401c0c1088a8038a00b894a51100359010b82d907820110f0a001c3e44505082e81c107007030b6050040c400c1c5402c85070780c884407040b45e0035140288401411039596103031096440c01c0b00e8030720400840b481d0220784081a055801102030718446c0c3c0c0050f10a000303031240300c0601c0010703040240c03d1205000040b9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 458924199 1250 458922949 458922991
    0x40c050c070e040209090d05040e040f0218040204050603160905100312050307080919021207030510150e07020303061908030a0306080f16060c020f04180c06030c02060a05 75
    0x4003034000144080b2484050901d464014040e141c100184007040030317008202203400b104d4200341070750203a954039100c1042c0c903a680c0c42e00b070401680010010358030800c400d212500070155a11010b1086100765800c1c8240d440b21010705684d45640030b6503403859410a601840340c102c40358421548082140581e41a03c0c0d41e03a120b4001541c005980f090004000108001c0e00e541c01610807034002d50366030000c100395070040410f0b440c000f65240d0002e00c6482007481111081c84208030000246820900703880246032003600d0320000301600c014115a042e01100005041e10740d80ca03800744100800d03000b551840d5a1042000301c00030304014581c40200c5840d1020401400400140a14840320b46001401906040819203403001d400c4216946500010500a080300c00c044154100c915031306011015507910702c0041e07081c0f200c650416030007a283c00b038881464044000400c06413802030903501c02085e02c0e110102c00342c445600303200e00503a0040c000315000102d582d00c0f41c3e60080101d0940e402202900c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 458925449 1250 458924199 458924203
    0xc030c0f01090e040c03021509010804031b0b01080c0301060501030509070e060d080a0503070314070207060302030702010b27060604061b150e06040302010510122d211103030402040c050c 82
    0x4d560540d80000110014402c6040c001c540145164400c4174440c180840e40000820000c00100b0083c108910185440300d003010b4680d9001d100d40e804050b00400d580c407030f40e111380c4d40d80413080c1541c425030800c00000b0306540203104d50340c0a0603803400034100d001c0c1001000310003180080c01c0300c0c2e00841800040360104408402405001c0f11310f58038960303603040c000d600800b80c0f00d2100e0000c000070405000d2100480d00001e0200403070381903040c0907849503150401a4014500401280e801200100d5184400c034540b080501c0310b144910780d10071694a401050140038040e500038100410b15103442c440c04400c400d50003c46683c403035000000c0c0c02c0c46520800003906c104440304052640240e00340010550213002ea1075002004840000086240080ca5004009007010141c034990002040060309282e42c0c4003508000d001d13980c160b4424029240000401e510000c5030b10398007201040484002d0f200d07409090144124000550554035203800300002440e01c50058411b118080002c908501c800f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 458926699 1250 458925449 458925451
    0x60c031008030c030304060b0901050d2a03110a060207060207181b080f0a0e0309061b0313090506030601050105040510020a0b01090f2007030f0c0b16020f0c030c0f01090e 75
    0x3c000d03586908051a21400f84d6640b49480c0703204600310f1005100a8a076001c041c06540e03000100150618005140d0218100002e0105010b41140241c0841488121849002c7c81c0d9801e4890030740070359403034404989600b802d000300401038220000030003103c0000c20b040d42d034000c0ba482c800202d000324041b01c0c0c1031042c0d1100091000c2060081003101c40008e01c00c00c1c50b03005c1440c032018011780c40a0b03a801c50b00c901c200d0241c240300d8171000c21801c0818840400c0394110025401c2160f5a03011003580500720031101d4410b5082881c00c046c0024003030304001c64060b040381d80603110982894106001c03c080d2800c07d0105000b103101e070b10510404180c50766041030003032840c2c20000401c0d5090074411410f17140710312411040c80005145019007003601c54100c4000c030b601440c000400d2584aa82111900a01032016200010300d000b80120310360351250943c0d140e801d07a021a403000414416080d1200c55aa10041d4075421480c00e84101d424410441c07818288149006141191105149218404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 458927949 1250 458926699 458926717
    0xb04060f060f090e16091a150304150b010e04020c1501091a180402090c04030b091507020616031d010212010e07050304080301051011030a17010f08060c03100803 71
    0x160910040000f03400900c1001c03002c5280d40040c217581125910310990070310320351041002d071342d6550a00701c0a51108401a0400e008000c107800540d5018400150154000b55029280303980c0d5042c18005144451041c2105114181c43d05c8801181c2c042c00c000003500840101c8150340141185d0f4800390203540c0e5858003a20381c002c00040c1c201c89080442251103030840045001da600343c0ea0451100b80c440542e190b100e81c2c12240c0d101240d80d00091049140603543c4001e20520121040c00354085010607001c000e11305010001c045075552042c00c0360ba51400f40c554070705011541b40d12002d42c0340b0075000369003554424041c0e80c0446659208131400ca90142c54200790003990480188110f0201e4920366400680301c0c6480d0f4214181034880d8040b40c841031040a2040040c804d030160028050200c24010441d2042a01c2d00e41d00d82542c090016904030380296043c1220000100d20a01c50495440c1a5034444bc01010303655a038401c8610340d54009403040300703aa82d250710b0000390042e040004201800d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 458929199 1250 458927949 458927969
    0x150120150a0f060b041404020412031e0f08042315040b06030d05120403090914040b1b09040b0a0503062502032701030b062b180b04060f06 61
    0x218240710044222150601060362950a0800400c0030007010b40a890076540d580740140f06540070040018003e00c40c6522840d000782400703044106142d0000c1ea059020801440c00c950101910002120003040c00804900440c01d001d0210b408150f1401d83c0c2040d49510f1844203020840c8000801d24003c0c9c4600608040c0720380c0010401002040005550412810350061001003a948400750141c0905641b2042500007030b03000405051203551640004c260300c080c108204520340c040c00c8142481150300b076032510f4240d80030904082c0540c00d4114a55010201642001c0c200410031005d0320400030340c01d62280c7c01003004038196505104050150b2080d800002103004a203000e020200a00c02501096400c00c0c4400a4140c11030002ca14134007085c003101c24651050040141c000b0300d0000c5140750007820100780e125200c20120342c00450350000070035041c81c10b401e408460b415154010241190700103039030000000a0ba01e401d40a030054031071200420070321114042541112400e5001147c0a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 458930449 1250 458929199 458929201
    0x140f07060b0909031b01060e040807030e040204032a2301030b030303075007050d080106170c0d020a021524040c020705061308011803080f15012015 65
    0xc1113401440400b03804117034000d000e141d04d8502d0806d4400b10040014122503c00180c900415100700c0a90f401048000c0c411519580c403810216141c60480d034412103000702800c0400c450b00c030b1940c0444102c90300c403688001c80e240c54000320304898815460f8281070680b10f00109446603424006544105407650b50b03e502c40c420382035244148070042e4504c514062070009100c0074084143d40c1000440200ca41c04c1c1044032603001c40f60791912620304060410701a250901c103505a200318118100c41035607840440040070380d0b1800c5812901075451695055041100b603941e0341140e00603042c0f0702203d0040da01010329181503c034101d442141c9a640c1c2001c1401070504d02d9103109008041e001c81034900b000942e00525019580300550b003d40c1d0320919001c0707001001d018003414414058103c0a00a000840102c032508010000405003180402c0c2a4000030340c29100303445213144109010f0305020789441404d00151140c99140402100b0700c50324000101c5103c004020000ca6a42080482182 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 458931699 1250 458930449 458930467
    0xb0103080c01270b04030917060f0903040b180d02090114030105070305040f06052707050a0504181514090d0e0307080d181e08010c140f07060b090903 66
    0x85035001040740c41c010205201a03656800c0c07241c40c0c83c29456028010030740603241d41c02c0a07101c84410303038001740d0b03840c00140e0b400c8011600803036002e0146002d114140d006441c0c484680b5240e01540c0141005901c080c06101070740e115101011b2020036003c0c012800c2e40d41d036500840c0b50725a09803c1000080344405001c00d0505003480b540d1fa01200300e00e02080360b41442d80d2040d0a8600d50b4402800d280d4462020130700385c08104221406405440352100400e519156580b6201e100d14800e140c0300e049850320000b054202806584540303444403004145150107030355110000074071640c40606650303031103940381c002180195800d4000c0c00d00200618802611036401085001c54114540c066004904100201207001480b540c400500d4107007540700310244d10341c0314840344c6d01c0d030f0100c003034840d141445440040803107040c3c00c19101042c0080c8030000310003d00303513131143c4480041e0303601580c10058000c2c0d5940f40c5000c4d22000e481001c020505032081c0b000180d07008800e03184180c03550800601021 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 458932949 1250 458931699 458931701
    0x60203180307060e10031b0c020103051308030f070c02031b03010b2209022209050706020f100504030e1e180408070201080408161110021c030b06070b0103080c01 71
    0x104400441c020b080490821800500d1141c4407507101d400b80c04103081c2d0002c158003981040b00804151854032010f0000c00700c00074036116000344281e0200f4604008901e6078180d40001000041c1c100002e14a07540742c442e000031400c14000c0c1030404214054103030400682c0c06020142160b101c1c1d0204c400e41017099400c041c00c40786414280e51141460f10b42c07044681c001c26410941c0821106000500740d036003400441c41e800c421000e540e444105c03107120780303a1001c10765200c140e001d802501150101ca403514400d0741e891828070039540d0030764003030800e100400c101030300700c41e600510074903280070403034041d0001c54408580880380d841600c42e0210300c55207070b090940541d01c0d41d0b541080d00c95441d04254031618003621407110007904102c0007400050500040c001200c800e070f4a20706140c4625107542c2050391302ca00184826911032849407140403030817840010700c0d68207281c4003e600340c40e143c10014140c0003801203002c1c954210b603052244801240110640f03600a41c0680ba01c590759909212000e4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 458934199 1250 458932949 458932987
    0x7180f0f0905150f03010906090501062903040b060d0501090b1f050625050709020702040b06030115110f010c080105031204060c06150e0115030c03060501020316110a060203 76
    0x21145140c02c04009840005020806141c102581c242d01c804a0300c0c000f20b4050101001d010b801c181c10501c42c1c0341048015400401203503205840c281ea83d078002600024444400314248100407824030100d0b02080c8500300c20350b000000107107c900e06182e55642e40b400d4420071501076545403034840c00c110b14040f240b907011034841c02d0218460641400c041c00078013240240c078065040c6d00c12440c4600420759041d0304011312950482d00720b4032500d685042e618065484450201c0c055403d00b00c45440c030703081c103c0a41e41a91072004d14045d20640c42c403011a0524a00010352071a071081c401040d03c01c00c0b081c41080d01c2281203548080043d0b040009241ca003100401c1c500c1c066980c10001000031580c00b0384281d0205901020204203050354204008038083c56030004800401c401000181207140d00c0b41103803884c0510b0701c2c1030101e064440c400303504440346481000e015820801400c200f40400558828070f580c1305031030004840c0245d602141c0304007902d0300014050303030002481c0164101c4d8a0301700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 458935449 1250 458934199 458934209
    0x170d11070201020c09161101090611040833040609082706130b031e010f0501110a0809010e0307090e0307230a020f3d0c050c0907180f0f 60
    0x40c48141c00c1c843c01c06c0125046c4a800c401c2001510585846a0042900a05076190300548140880600341085941541c0281701d0300030343c1d00c038110303280c030790569416800b844415044a0300c1a100a8249e001c4d0824000280300b26927844e03582e50300a00086030b060103064046070891920682e28032030315510900c140b41c2c1d5006032240b001445a428100241c8412170191020929103507102d441e010700c039072001440c0e41004185064004004203d00500003095411524266a8442c0c40c050203503419071154003030a03001d010b440003006101da04c0c0d40900c0e16a2450792000d000c075480c1c1c6076070324584011034054010080882c2c10000c3c86100f8090060080c5805441c0020151482a446072900f9500d100380b1a0003401541a040500c0303255460040011643c04540c140d0f0072100d0f030040c0c03400c682032070040001d0804907200700300c1e40c030310b51141122381c1090f030b806801032405510003800c1040b000c2004000100b041601c2080b00c00c04d803940c1824800810ba030b01c40e42c0010a0a007042050344000c541c00c0307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 458936699 1250 458935449 458935459
    0x60207020d06060f0b030408030109230118050604020901230c060c0712021c0c0c183e0c03090a090b0306070c030816030609060b1e0a0903170d11070201020c 69
    0x203007c04a10380c60300b202c0c1100c1c410f0900060f0b0842001510036030204c4015182070058284000060b07900415414000c03c00001004105036903802d001c02040740a0000141c0c0003995071074100b2144009600381c1d41c1a8090114654141641d00009070301c0d1400450301c000d122900130030500b0803c901d054181250145031b00103000495a19080c6030800400c801405041100158941c400d102008160708080d015041c1704009190b08100000003400440c1c41c1d408041c945c044500c80f070400d000081d43e0b400c104503030107107501e8030240c01c002c1d1342d54210a0b604031890004100740c04441c0d4403000a84024100c0d1301e00443ca800d20700381003505000307000701490300b0f01401c0380700c4600096000615a41c042d562458581940100520403401085990030900d0440d24205010401c911004090140492804400140620302c1030400581d8051400c07180c0225242032000d03c002030480e69222003c602034880182461404500801030310000711404003e500001403200640d641400b1107001400181c1e4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 458937949 1250 458936699 458936701
    0x3051209120a09030b0f06060f160209040f171e03060f0306070216080d0503011203020c2116060806060a03020f032503060602031c060803070c0806010f120f060207020d06060f0b03 79
    0x2002c64007032700c50303000d0300c800c01d00300000c180c4a1b45040d204201007aa40144c110300c803502d00343c0340c01444d00550000c1a81c401c441d000381003003100004422544054403210300402400c52100048072a03403c0580810382c41181104c08524640307081120358802c4a095009105500303400d99a0380c1c2c54981c41e0445802608581c4440900542240072641100c0310340c10000045d1110b030904a060141c68403099a01c2045d40440c40c151205104e40315400c4078455094845c981c813000090010310702c070b03445007801045101001a80340c3c0f8041d005082d40c0c54041c14054900384590442101c26801159800c9002614480f10200042200081403104540707040401040f4140b81001c1e699005107030220301594520802c408070784d541908420300928149080701d40380c0d03e0628001e00c200007a8022105d1f01d2245e603000140b09020040c0d48001c841e58071003500c804c8409070300e03a1384014540d80f4059561640800c4604010307103500174528182405214005001030034241069241e100a901024201d274040c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 458939199 1250 458937949 458937961
    0x12060c08010b0901091518091d0a021f021c0504030309120c0302090a1112040b0609010b030705030c1b0a05010c0c0c05091308030708060a0f0303051209120a09030b0f 73
    0x882c0d03002c20389100c44855500412075010460f9038101f41240203000071400940051171441c1c5402c1b0b6100f04000140a15040752103803000d0381c2e40d0007038000203580011086400b01440d080059103000c01c400c02e10540380c19002030030580384c40302c5007a01c114002a0001404105040e8403412050103001e00840c400c1c81c807501c41d2100051440765000c007902c0303128400e01017040910b280e80b15070508003d00b08065200d242d6000340300e425150032201590812403400000b65280b4002103190f041c0c800f82200c0c4c0d03096844012040350150001059a00c05403400c000c0324403030400c450b80e42030310001404000d00030700b00c0f186006402c0d52815402c0b0300c20700103031040b0240020142000740b4280c0300300303550107000384d40c50800502840f60354140243c0540f40c0007080c130030400e5215644920461090382d280f001e2a80d10050390800700031510005c2c0000300f06100448184490102c1030b0340146154003160710b00c20303405100c403006038440b048040100d561004108204002c65003180e51040e0b20041918036880c1c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 458940449 1250 458939199 458939207
    0x1d01080606100306170a06050117060c0d02042414043b040818030c0f1018080d0e0301020307051207052203020f0405040c050f0a12060c08010b0901 65
    0xd41030511690041032082c140500c00d600410041200300d806800107400e01a0071a282c44011328240c071620304100021070411480d0b0905c0300c2c040c80034001810190f540c4611141d10760004401400720680030040058121400000b401c41001105101c0c040103404201c0036140406402c500d5402505c00e03c002c101d0b884840b603840a41d105910700082c21404001c000807906003c1481c5884140e001e0000d00c02480b5106024101600b80072800101494003001059a5042000c402c65403010340103003251901c0c100f6464041840c00c0e2405e040c01041c600030480c0003081c03a43e800801c916031103800c94a540c540d00c01c3c48203545860030b0b0000c614500f00010b0081c010312800d1124808958190085070a9903c28412500712403040c5c100e00c8074180504c00c40e0350040045110a0340b28000e000103202d1145442c0c0f013440d000f05e0780112012070003440c002c00d0003c810048468164030030030f80900068004c002c1d01d80da40340580b04a500144010f0840c3d0040c00519041c1c210610a00c02400310181d540d0b00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 458941699 1250 458940449 458940451
    0x6050d1508060c130b04060806100305060307051c06092109030c0608090f0706050a0f0206070c2d05012003190510030f030c0302010f140a1a0a0f1d010806 68
    0x400c40d08903a50b040282d00e484c0c0700291035440990380f2100080d0000341982d1101c00b040c003c210844c0d020703195064451046091720400d07120650f040c0c100810401c80d61411003e0083e041e403a2102502c000d182c51f482e00c004070f8096450a541440003d0183d649000b0070765031108401e40203042020040c0c0c116101e0f501403a0441c01401e0501c580390000c507045040c200003001c5d40c0d40d2000100c0304155203a590042203a08901c0e0403030082260351031003260250022440301c0c0b05102668410700454000c0c1c0781c240403400307110170200c09100300070303400e81c0c444082000c1d40340f203e070080001141402d4600e001269801c03000120301c0d0559428801d2080084041000d4503440300000c10126013622101481042d2001d207a0005140b034000312041400c1582250301c45003940d0186e0001c0219803020f10100d81130395550807510036100260b400003090165140d1251303082c0b00030b0380b25007403000302005c01160a000781b45d00520401980c0820410030054009950414040d41c3c1c095035031076524201c5526502c881c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 458942949 1250 458941699 458941711
    0x7030605240c03070f2f0d02010c0309090c0e03160e041401140702060f25231204260d0c0c0c290c070e1b030106050d150806 55
    0x180c0092840b02003541001581c204c0e039000702c904017481e84245040c81258141c03125000c00710300c480a80b461541401c15221800e008041c0c09051000603940c011505ca0401c7d04044061009160000c00c00c030800c5c0c4261885188103444061100d21101c04042c6440c0c0c042e0f40b50480d021200c101404a8034152074140c3c1c2243e845003811b802c45418000042c090026420001c001144100412000c01d0380000c28a002d6050300d141107000b40c44410742c0301140e40004481c03d1441000c840301148051007101090b170711031030f14600c112441400703a588200f40d900000c028070350480342506000521071804508440d2100d01d410103070500441c1c3c5040d01c164041c2220b0b0380c4200303527a403c4005103140281d1020114035440700710030311540d440f16881021101c107052074405d22000108000c001600a204880d04103c2541c0240122483c00030141c1003481c00401c1c0302000c141d1601101803100c02003029602801d0720b131b200d254a4001900c4500c04a908040032170b1800c801480003001009808a0b0150f0084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 458944199 1250 458942949 458943019
    0x2708070f03060b101b0807050303040f0308090c0306060d0519050115090204050108061c061b11060105130506030703080a031a0405190f0b060c0109020f10120c030e0f0607030605 78
    0xa846424406c40e540100e92024020f404000100810000300d800f00180c541d00c030f51035030020703911070800310380d52107120110464065000f04042419032070031044c42030145200d803007100ca50801c0d000358410b08001480e81221680c2d1940c4602240d02d4411501d80d0207010611001c600702813514000a115800203070132036003d980e4140c0031000c89440701c1107a10003141c0250050003e04424058070f1b102d0010b1454002c0000d080c03000e014500500031440e503049401c000c0007418201e02808610000300400b611459041c459224000001214036001d0141080340f0380700000d42140c0e05140d21812a10f1402d468072462a02e030800070749966081007045103c074141c03c00540d000041a5103802004d400b244140d01140c0810388505c07148054214a000a10a49007140707040291410711107540030060001020400c980c1e80074050407050b600c0890107020ba40343c04664085c00120007070904c05803000c1c4844a82107041002811034042c002c10006010943c0c9442400141d1f0f01e0f541d00007007000350611100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 458945449 1250 458944199 458944247
    0xf030a120f0b1801080105010b070503030f1f0e0103030e01260408040906030c1a09030d0c05070b0703030b0109150c03081506030f150901062708070f03060b10 70
    0x4074480d036000c03100701600904141070980c41400000e402142c03d1080345c0039903080a0000c41d000009905407600294464021810b5482d03071590200c40d954000c100c1c002c41c0040e03d1907401100d1250002000800002100d8046035065040040c45c501000d0982418010034042c80800800c1caaa8016600a8900f9030800303551518617140025200d40d0713018400460601c075022080c040c030f04c6d5a100031035800c0100309600b8880002c00d50f60074022800d03442e5058008603900803000e030241c4003d00c00300e44504161402d5a40390207a03008540c102c40300950000b591101d0245217560008441c07006013810300e981c20201da03803c000050115032074500090800c9505030100d07032204054100c06840c2c82e0000c0c0300c55200d16001c01d04100c8540c040302e1004803019011954030603030421a4150781681c44c0d0342da8207410007031103030300800c0c12110350701c801020303480c07400c0c070008544906204d0800600140305420f07004901e1820300c48190f0300c0d680c2120b40300b007038100441c0b80b205801600c1004480d080d25220814 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 458946699 1250 458945449 458945471
    0x80601031e09170c010c081509040209153610170f030f130b030103120e010c0c1514032a0d0903020127111e1507050f030a12 55
    0x1856a1440544000310004030b604c908800064010340d0000400c0e0782c80c10429540c0b04000a20075003c040495049000f0902040c050b08040f00c4d0182e0008070801518440f01c02600801d41141426210b500700002c400b01e1a40c0030040040140b0700c2024000f40c0006a0415a1084032494110b00c40c10011a000e00080c03240c18030140010325100c1240001d581c0c803020030341d9054919a01c20244000c00514910380440d0310601c28058a0690b074003d40f41d507003680e949600650300f24121040c1030741804031074018500011a4090b544005c2d0091442d150301e002203008025180c500050030002c4104002e100704019003070044005141482c00502000031003800903040025441509000c4050f41e0400c00d2000c140360b01500728070401c800c8641020035450600c2c4000103404500346004102a0f008407400310f6600d455507481800781c3c61440184500c0001e84d0018403003803207041601554503804a030309002d101d070608c16138903440c0c00038028516007903851100622080d080c1d001880007654034801c03010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 458947949 1250 458946699 458946713
    0x30c0c080a051c0c0b13061b09060305071b050a0203061315090201050c070308120106090e27100f05070504050901030b0a1b02100605060903030f0c0c031c080601031e09 74
    0x41343c160803000b15606801c3c000380b0b4840381e8014100035640d07070b03007007909980d01c1c0b4038052030301b08040d0040d6a030000994142703002103020780000b03003080042209601e032007842d010104010380704a44c4140005c241031955481072500300000209440a4060200c6180020071030300800d40c1d0a0341c412100002d2014203601c016620b0303000790340045403d8840c5030b00100800c58060001d002125260004003e10381c2d8a680444003600f450140100500c03100001c41c80c1f030403086621441f200407004020204030404207800707241c0205404000a440d444a26181c03052406104171394110342645401c40c42d1078240004100803000611000381110310900005011202075440708010441980c031050f44000b20141c02940c0d10480910f140c8098580b090010741c62918004540c61100d014015608020009400340a181c0022031014007a0050300001c0c585543d0074030200080c801c101000c01c081a00d0600c0c02403103002c0c0181642d062529110031500140405c2c0c2c14154038250703041010400004520f401c00e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 458949199 1250 458947949 458947967
    0x3051009050603030c060405070602010b0307062c060c010c090902070218180a0f02101106010603090305090a060c0c15051813050f010923070c03110703030c0c080a051c 74
    0x90000e000b5602440100708c1e0120f24101141daa5a000340a201d01d408205038540c0d800c1c1c0300e1170f00404c0d80070801410020758140b1503800070080c400b003004d03944040c00201e00780e0f40c4084c081001c16556006400c010a030001411006000314240c21420010980e0116940e038401c411442401c40154001940281440310790100001000c0152501c450007484d100850f83d8440004901c281803c0c40c8902e80184110340c8000000103460041000e81d290030400d4004055030b80c0160f08000701005810b0740c603164000301000900055442c50746010260410603103525081e0407803542843c158609003401c5601c8003d903148003103100701c0c0d51604248640010a42c21908200e216017508000402000e0b03034050195074101e41c2407050034001d0315034043c403c044451404e42040044c2d071070700c1c011640c0d5a11401408042c18800c0c101b8841144c01319283c81e01e07040003907204400003000074008904200b01c1880d0761004009050003803070204003a0f03a0341c0b500d03410b41940001c103c0130f03160710003003403030380300f1a0f0f07070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 458950449 1250 458949199 458949217
    0x207080f0c03070606091b111e070f1a09040203060607022112040f0e0a11030a0c02070e01080604030e1906050306030c09010e0115031d010f0b010305100905060303 72
    0xe80e9499440918a0351a50401907080d03800134504800090380a02a00034440350300a441c000d40003c0401800981e0502030440300005580700318400b14000c9100c410072016100b1200300200501132925404906400e040d40101400ca4860303050f84602c0781d0302009580001d4003c540c056101d03510700b404241140031305c1300040e40c0148050081407161442c1759034140401c031101d0646522580d10754000c2050300c140c4c0310740780d41c1c0500c5060030481070002001c141c1e0411407d003c04078660640c01280310898009584c0441c880340d803000602009601008100007c206001e81c00c0740351f600d004c121945030031005101406008002100d0011561640c551b402540f41401400d00280c0d1036a10003000350300100c51150207440f411042e014503141c00d40704c0c03504945201540d020541e00380010148100c20040c1c0860525407164031140c034600c480350210840e50f19070000001c0209010188030140e452030038103517040c1850075082c00014101c0c40f001c002661440c81d000700e40c40c1ca4010101c1c0c071714410802d40c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 458951699 1250 458950449 458950477
    0x90f030305060901050901120609140f07060207090504110d150501060203071a010e040f26120a060806070c0f050303010905040506340e030d120e1906020708 69
    0x41410190550310050040409032503003000c0340c2e203503024003011030400c0c0507a44903105c445000200180c860b4100300c501600ca842811190410700101620b01486045001c0d1103400091060003002d40c100594401051140c0c4d09010506058442c0a44003982c00c014a003d400f141c0401414030560340702d102170250300c540c3d01304480c2da510711000303449420480d4200c070611182e1002c03212092002031111b0503503c4103440c40c111030301c8903552503030b014172929401c0f5260500c00c1c40c280f501100019071140e140b072040c0c8280c0c0d681c0039a411a0380c01c90000904424141385480e005109407071001075030940c01585030422101410300b50901400d6940c201000a01d60312002001041c0510390760080750003940b10304120b440940b01c100410740345a0002d44585142c10500f8100e284084d04804140d08488150900c01c001407074071004039007070004403016400480e0a841d100349100c0c900340b2821414111070009003181d02501411003005031600c110103405d464001c1042c0d02071280c44402c8641c00c000d040b40b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 458952949 1250 458951699 458951723
    0x141206040507050c0a033b06131e060f03021306080c1213061b021b040212040501050411010e030a06020a05040b0705070504060605090112050a020c0313080d02160e060409 75
    0x10b8000d00d1400a180d40400f4542007503421105c035100b003024101d902030056042007c1c032203005d041c4205900040349618840240020000d40405904058100d4110b040840440941854405841c506042100404240c0b0402ca221070500700c503800c103c01e13500146400c04903603d03414810311184c095046074102c046500400d00c90340c40030000000170028821a401d0000400c02038020b1488500c038806000580c01c01c11010907601d1400c00000b940710b0000740018201900002c0b050341e0040c3c00c0360304948a81d035460a000c00d00c0002c1221801d20102407808240740d403014408645c440100310402081a500441c1e41c0e05007502910a54001d04610b00700745031140890b051940e510507203449000c2c040d61606001141c15446103040300c242c1001038556441c41e440e00f1030000028800108400c03c010740c04d100c131001540301071000f4030031a801a01c900f22094100864581003400051500c0150350024640700d580708002c001c83ca040f9510b1114510090343d0380c1c00410060407031f4907c014a9031480340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 458954199 1250 458952949 458952953
    0x904020126090606010201230901111908092a0402041706010303080c03150d0507030206030c040906050a060f081b0d0501031b08070b0904021315141206040507050c0a 73
    0xc001900c1101c1500443c0e03402e45800b001079088441c04011351030300b180c803c202c180003241448440c50304000c1c4000005400801201a074005800004400b001101c0180000c60300a90015030039030000d8556010f08021440c1456003d50702031100f9084030030034041c1c070041d00f540d5a242d0580c1d0080c0f0004142240b41042d0b00d11740c541b03d4200340001ca02140a030380c041080c0801c21b00660388030304c41c5510341030898640041040310000051310103d41501c42c1030b0703002c030041c1ca4000256026615a212240c3c0b40c43c24000400305480c4a600003a000310800398040001660004001c014240c040c00d242036903460b5071240c0000d042545001e0029600009400100300d40143c0c4801e0480340105545150300443c041001180b510602c41c560306640710358002d02c511481070005090098004000528181070141c00950700c488644c031030310184121045000a854006a00c501034500f0011010300e4202e9400c400008048040c101c64000d0b652030001071001e81c082e0040780c0c10710324010200c40c00d0b401c0c03038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 458955449 1250 458954199 458954267
    0xb0f09040c05030d03020901080c07060f06080c01030b010e030601051c0b04110103060e0f07030c05040f12020405091f020702040905010216060e0c0d080d02041a0d110c06040209040201 81
    0x1d441400c3c081d1244102d10000c02d84a40300361152140140c0d40d03002152940c1501d60720a42200e1001c0e521159070312406008680c680c850240100f522001914000507020009000c0303c4a04c500c8a05014040b0404a000d54001c1842415184221903510026140030003403072101d80c20b80b2004102c0c5d0300041c14407040c841c0c0c40a441c143e4450036601480100c0d25900020140b80040d2080700c00100d0100104404034025008202141585d00d40f03035090540d2130441c12821217060380a48080d41c00c4441d66001e50809008550f4055400401030005811802c5800c07a244603214a1103200342d4041280d000719aa81c0d04007184068005000350f4071461402450590ba404400c012030303401c2d281111110b03402e4070210390701060a00040012010622545031401d182c2d0184c43d4500c1819401c000104101003020740300036500e0103040c9001e84803104d102c2032008a80006c442600070b55400c1c0090a901e090000301d199009a060b01c441215072103610069402652807850500624440c0450580d242d8007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 458956699 1250 458955449 458955473
    0x2190c02040b041b031a040c0e0301060e0f0106030b180103030e0f120d030b0a030b09100501080109152f12131a10090501030602091f0e01030b0f0904 66
    0x3120208009010041000100c5814542a8104802c40c2200f0071006009a004000200f142d1b030003495202c940c0d90001d4215030240c3e044a0114941240c0081d25080074454a80079100c03005041d4854102140c1d500e0034880148508405c041c1c07560048210ba440740c1940d028030f001c0a58151001c0c1d41c6170310340609440304442255004240b00c00c03280c09145000003080c1f01d080c441001502c01e006005c1001c90150813801e4803550001c0409200000141c83d042d0380512608004024185010103070342140e09480c0180e00c02085a8140400e03d004100283e259081c0b4405008000030600a03585400900030b100d80702c4900340700c2e180e65905c080f880d4400b005180c6920003040c2407040d640d54200108400303d1290002c1d043d611700810710312150211140340d982100324040c01c0501d85c3d5603420700e0f40a5510176041140c0c401d402080700141400c1500d2840000038542101c81001822084000d060782c60b10a10281050f841d10000c8050b600d41500f4144070000c0a045003886145ca420114080d00d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 458957949 1250 458956699 458956703
    0xb060337060f051f0308090d050304120b041a100504020a180803041503060b0301090e0f0f0a0209150d030516060212010303090501110a261801021c14030a02190c 71
    0x101c01c0010901c0104c80c000141601d0f4065070050070030801c0b00522240d0445160200c816100801002c542950303402c110f09503180c0704207920242c0d4035051818401444a02e403807007100002c0e20303051080c52801c0c40015815100152401a11122008400c5681c8a4101107070810215003500200c0c10709000320080007600d110700e00e50310b81420088070403011110644240130b1b806ea414030044c840030907150029040602c119088916903c0381c01000f0b4103048460002ca003440c0d0050032001c0440c20714804080d80f20312294406294000d2200115a500044090041c2000340c001030f00288003107509088000c030b41d003121045482d106c0141040c50046028041907020036505240090f50398410340e0001c1d000f881440243c20380200b1075640210b489061282e001464401c141251040c2c080403001d449c0700169410300303000410501c3c1c000390800150a0000c1101c0ca42c000c0c0105609400c5103c05504000e801929540d039605c540300d0100034060b0113444918902e9820038003050079803100c035480030742d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 458959199 1250 458957949 458957971
    0x30c0d150302090c040e061509090703050109050c0a0807120615030f0b03010204050307150504170615010f020c151b070f050414060f0a030c120b060337060f05 70
    0x13841c0e45500200d03d000c0d80c81b50710806c85244002928034140a031071600c0d0f031001c0d01d4400381082410000030b454494201c40e0000001c0c0e482004004a10a82c0600c40e041902080d005d0b10341461341e60010104000285070005003c018480021012160390120000b040801e2000b045c0702c204c098000c016000c03a08042103c6410800840c007540b8040c42110103c0782e0041c01048483e1424558485843c01d0354540004d012003403100007942252491030801224042c0c0203003c851a0400c82210000b01c03a000e00b5040101c10329001d584150002002601c4000499440702c000e10b04408030322170341c4203d840141c10116503006240500302c00041d000c0c103441400c034000304040d4950003813200b22404990540400309404010404506150911011000c00600700c030318000e4594440c0304400d602944040b04404841402c0d80500c411441410341080040b4083e12201d4294803a000700510a07031001d440300000b5907881c1000d07410038504001c00a5100394288031500800c0c140000601c0c00700c0e41c1c40425 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 458960449 1250 458959199 458959201
    0xc24020c01140112030f020c060f09180402130902130e0d080903030c07030509030f07080706180302061e070f030e090601020a031d2d24030408030c0d15030209 70
    0x255101003007440c113880940381d004140a00540f400c0300c0043d1107048807803e45c000c65102e050035889990060020710904200b00d6aa107901e081031009a40a000e1545180a03c020034440142d84415800049114045c07010401140c0c6000103800302c105240e080c1c00b81c6180044aa415600c0810000f10260041d2070340200da40d0b90500c055120b1000b01d48807844080100540310000c0d0240000e1b1480310780217402ca441c089541d840284c42d040e0f164000300b040c0e0b031107100200300d10741e44030100114900700254960300561442e80416081e00601080b44c0640076582c0e0302e078440300344207000e071500d99800ca003605080c1c0c0303c1e500300580101d401502c05400b500c00c804c0040c01c103500001d046115907074142e684d050030240040203041d42e2480c4e8812150f0200003040c40911100c0801102009034480e210a2184001188200800c40220300c401d0b0b0a00c05000f40442183d03042a810741ba07001350081d02c0203540780e0f108004112a4800d424294032020301e010640015030016003445004e6900c291a12401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 458961699 1250 458960449 458960471
    0x902030a051006090312031812030f0c0201022715031503060114060307080c040909080408060106390c0303080f0c031003020d0f0c0605070c0906030c060c24020c01 72
    0x1c2d12180005815454080c1a024001e4030a0b484107580b003008408e01c090500150707807003003144484841d40c00d0000341c403180403c08005851007110000300d82800214a4051400345002081000421140032102078581ea00810784540c0605160312102d203102c03d13600d161118503e0201c1d02140680c074003078414200040b81d03264805e0b5400041040040c101821980c03106403c480c0840028100302400609000000c0d8001541c082c000109214914643e1258100302246180410580c055020420003240700e446040c036000c0081d03403114014030903600c034001c400810362070700c86194001040b4841c2d00743d0020a05500140440c019201181c0e0031007151140380303007c05d20f400240d41480c0d600c0301d8540100014078001c1da070b11104901c5443e804280307050580b11040c446045a1202c170105100007000000c11036030607003030405044a14020003800c0d04640342c000c083c8542e03001d004107202c1046400b109111218107980d030502c4080000d8011490300308182e0002c2e404c818400400d035030800e0345d51300c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 458962949 1250 458961699 458961707
    0xa05121c0f27030213200405030606151210030812010501020d0e0f0f0301090602030403030b010f02030703020c0f13050901200c0c010305100f030b07121b0f02070902030a051006 78
    0xc05440001075a0945003107800300424800714903944000300d1703900c3c4102e9807070a071155501d407040b44400307501b5500c0b10700e042c0030300d070904000801c02031047c0009004c40d046041c0036400d6810410f440e101102617a07580c00440b0000000300e4001800e03041003c035541d03113002940b1100038180e44084c4d00751031407040b03041c00c15070f40d40d004090095806171298106403a2414250b4040100300300050003c20455655166035080340c5c400d0350141d0000e43c441407140110b580008408400103031300c0c8021071500320b40d601c000751103491040131103110703c1750003106403072582c0d0748142044020007441c420021802c00300222030090901900d04090030180c0b45d006c0c5051420001540d25108415020701200740300781d0300441c001d0400420711a40c00001c80701c04280c41c0e444040303001c050740c401d00211640b4100810040c3c9440c140d542100d00c0c243c00c11b0f0341f240810146414035001840c190900566046442d403080c1e00700204d542005101510120400c00c0f113040741e4101500401d0514144021961034400c215 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 458964199 1250 458962949 458962997
    0x15030c0503060d150b06130504050708040b13030e120c0a0803120606131205030d1401060c0f022407120801080607110319031b030b0a05121c0f 63
    0x40d80c40856080c400c004500540719840080d440781c0710006080e002500086c00c2504002014524a83c5a540a01c85030602e8465560008414104449540b80a41d40d81101c018024858043c2910a4039080c041501500501c07400340310040038440d80300e8250308202e60765280080664850303100580f002074604c1d00030040f544002d00e1000b40000700d0303680301c1c14000c05620540340340500c0c0301303030400002c1d0f0f4401d64103d910402c0e20550241d030f55180c05080350000e9409000d44c40440000c0000108081ba0300f01134070740002588070742c2c2410f0305803440c00010030541d1800e03484102d8000c0d0601c140c103012003180c01440498480d10004490080100d001c90f0484401d01800525602000109480074000c59642041d050510112440e02c40508800b069120203807c10501013511281a100e111070040e02156007050301307140812604442000040061582c1c1c4110380c052003403032001050404050040b2031010400d240110b0b280d800040c2c2c014003605072407001400143e84514100048284509c3c0d203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 458965449 1250 458964199 458964211
    0x2040b090613050603100e03120109020f030a2c1e011a130204181a030c1f0912030e010f0f0507060e03120a0e0106050301110d2415030c0503 62
    0x20410303100211a18000810300608003035810711620406d0740010100e40600340d40091224013031504d845141c1001c191010060300200c100c10b0062280e0202c1000a0050781e0307000301d8846000c12070041c00d00441c180072000d000a1f00d0f4500324146c580c4040200012170141c2c0200c0a00c1d90005541d10801d41d0382268007a1107071083d60214000c00350071914012003505449aa800307001464295503000d808005c250003011110b4443c1c43d401c500c1e04c00411001d401e4400c0340142e010f070184820101c0065541d101e0ba628039480e80810700b1100002d18895554400030301901c040681021b0303064203001d06144aa035807070368002200c000341680d20f40d10034610301310f140701d154039030b0b5040801c90754480c00908000c0070403000c1840144580301d000540401c0380340c024040107000240c48601071400c182920520380005019170304101501651840507012035400060840c00060b03100804031407d0701103405c01c0c480081c0032072142404079400c00045441441399805440421440141c03503c1656180011100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 458966699 1250 458965449 458965459
    0xe0d05090a030212120a0806090a0b151e0301030b06031204080c0f0d08280f0203250b160e0d0f060c03240f050a0b0319090b04030c02040b0906 63
    0x402c01820012040b00345803040d2002e030340c161451003541d441d05420449001c8001140341c401c0c4115070420028190300109000c0c0144000c155580102d800820038090006600f180040c2c14410500d50b00c44240c0c4010785844801e9aa59681c10000003e034002e8840f50300c01d000e00c40d5840250040a001c45007224031000160000c1e544031000c00202d60450784502d500015515880400200460f00511080140782e2100e070300034400c1002a41c2c4404058126003e2081946109000d80c0e0000240c07403865542c000c80507040c00000504002100720000010501001c91041c4081c2d0364102c0c04491402c032841d5207030840618003030100701f46050f0311000a0401414402d046010900503048440c0b003d0b194240070800e01e0a00103055003a40075280748000c0c0e1000d098082c0310400f1806000c00c0108021030303241070050f040c94000c008a200c042d10f14101888101442c031003080454008602c0782d50881e880b01c83c1440c1a0801030300805c8244030480c49280740903c0000f5601d00203d1290103000c001e01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 458967949 1250 458966699 458966719
    0x5010f0209090f070203070812100902041a13320d0201140304060b031b03060903180d0f0206040f211203180b0106050415050301050d020603150d060e0d0509 69
    0x400d2020030f0202030f040da01180002c200440200c0c7c5244028201e0042d44030400115181c81004140c0401d00754100c01800da0040004022141a1082a044540f0f01070304540d40e960841c90410140f81d855070050440402d440c41ca0488000074500a5100c403108407080102d40103450200072940e002248020702080c0400300c400c400c41c1500028540c0648a85000210001d012001a01d0041c40c500d40c1070388201d840e03421210b14201440525003290120717000b54100407404002c1565401b0610b005401101400c500384140f002e0b0750350618080d0b07000340200780d840d03840707103000007110b5510b01411515540c10103070100c500500080080802e50000040d00321542a89030880107044c0b4850880c00701c84c4156802c201141404450b28000c00064070340341c4e542c03403a2a904910f400d80c846041e2040c8402400104040d032210041000310590480d100340da0b030780c1c41ea41403110f0800b0000c41950000c1e0b4041d00c4000300701455000c000f030250402d081307501c4198400c0044902e0301c18030b01a207401204e204 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 458969199 1250 458967949 458967961
    0xa06030608030a05070609170307180317090a0306110d111911010221040605011205150c0d020c0a030306050402091528020a03080f1e2e0305010f020909 67
    0x30083c1070760606c07800740818040102e85400d5090403481c00b500316022030020521a500b41c0003444440c0c9103000300f1081c0701081c5152222100c5000304140c110503a080040e041800c0d98803d90040c001c1c0d98440b00c2080040011502e050458002900030040700786814240c00342c1c1e041c090b007a0b60301390b40c007203080402100040794103c42e8002151000c035030642d000d20034001640000e5500c801e10b0385403459150f205140c03508042c0b050314030680c44a0410b1551700510380101d00007040c0340c03951021104071b40c6210340300c48072151726a21403401032090180c404600028a03140220350050650b000e541d041c400a603c940030030049110325440a640084666004400307002e000c1e000d03102084207030742855141010040003a14420303440310090f005070054a881c0d01003680121120350088442c4586403c00e10705403081c2c0b50b400b42a079405201c0e000ca240006480500444e81000e036008008420020049003401800800900c40c0030881d0030394284010000700c08680d20a50306802002009030005440d20 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 458970449 1250 458969199 458969207
    0x60f180607120209060a020a0b060d121110091406070305060604051302090405131b030209041b05190e1b090d03090f0b1803010c020c040c0e100306050a06030608030a 73
    0x80c42c40e01041d0750248030284c1144d170307810080d181c500c66075000390100700201d241603a0840c1d0010f01e250311405078040d00d140480e242c80702c0f0340040701003810310036000a40000614980441400c5851074507050400310b00402102c0c03074003400304c2e40000084030178903124102c045c0d060b00c008440c00b5401020610007000f007072804400b418000403070303650014a00401c1401280585400300e030400c4440c2482d4100303070b00304804001a801d06540240f10707202c0341411540015600700014002500049420314482c1c07080640004810040c10001c01c08481d40b078125150710450481d80c07054011031001c1c0c20000307195980c0e0701044244100c070709521a15006981d4208840c014014109804000404a01041c4200000c924038040c0181c402c1440d00c0d02040b40e00b0808075441d55082d1030107a4100321056183d82c0e00003440c0001201e0480b0007050101d10320400300c60070040004d07813070362002c1604422202a501030340000140c030020b070751b5104107603228401079058800c1d510583e403603035100f0402540322502c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 458971699 1250 458970449 458970467
    0x6040c08160315080604031202070b0109050a0f0504140c030705060a0c17030106230702010e040e030c120301030c15531b0409020703020f070602060f180607 69
    0x225050002d1400c401090449812400d84c100b20001d60110041c48103041e00074095090064403480294544412541c901003080810300c500340b442611400451817002c0c254001002203808000100701034901814090141c0b00c00049025040c0039044500919040100b00101074410140000f860461180f1048a4046c07405c002038600304000704c440b004081c0d04000640c001e0049644600c0700608407030b010711100c40c103883c200010344410403040006076002584032800d01c808840c00111907003034015880c150300c00d54000c1c00e01e900407812030340a41c8542d0400355050302d010b0302d2a0ba046540702c02d18044402400c83e82e14001c500c41e000d031144170f001d030010209039591040100c5011100400021203000003100031487c040b040c2c0b56403004100c050388840c2540010111082052a00c22800c003171160306c101d000c3c6440c41c5400084010616000304102182a01d10800311048030741c1d600b81c02500c40c1c1003643e4138803c803000755001c0350940c5c00c4400b09500a680d20009400c0640310341c80141d0f10841 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 458972949 1250 458971699 458971741
    0xc070305071e050a05060a06090c0f110709090312050c03040206030f040302070f1805060303031b070521030901050f0c0d090c05090c0a081305190c031b06020606040c08 74
    0x4044030b07075000020400e0002603916441800102030504000c5c0e05441910203d81001c0851fa00c3c0c2401510000d50082c0859001c0381d40342003c19010425420351400e20b140368124685e1141003441c003204040d0301003d444c203209175a0b03804120b15104c80c1800030b4a07100668010f94482014404100503c41d0440c601c0e8000b44a4012142c079036655000b0005900e580340d2000e12008615100c9003c460001e00507258071080481c05541303945401880310384c141c0c1847c1c10705080454080355200c2004130812403c00c54075507040740035807a103000c0d5011103055401100c0d0403007035500303103804a400003454002c182d001d4042186042c1c10840751412401c02400c5101c01a0b8407044200d0001415441c0d1080660041c81003079071031030382c0e0480b40d50301401d115405041018200d10b07942d104000b081c0042809029040c00c1c04031030301c490680303080180760205d0940000c0d25901c902d10248907907211603004441140c1d019029140142c4e158001c110407030b5804416880440c80400021f80d1608949140000c1a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 458974199 1250 458972949 458972993
    0x60609090f020408060f0c132303010b060d1e15080d020c090f2806060f180e06030f01020a02072309180109061506140403050c210105040b07080c07030507 68
    0x410300e5210b403074195409070b00900c0c2c0c4030300000c552740f012031125510901d070400540c002d004d15040d580100303100b8403603040780f140b2280e596400c0002d568003d800220215012490a010009012085044200b500c0c0326072510752080c03100d030960715400802c4520460b20010101c410a5a8042c203c14500c000180003410306d505145040381086000342c1200701c0203086620000f4940d0038040083c06060722490030740203005c00145207011355840001c2140545140d03221034070064441c40013091034041c070841c1c0d9200039400400c0c085010b80c0d0016540d0100c0d4200102d581c2d11610340e90b9012400301000510a8100c9007180001d605001808500c0401034510000007800810a444482c212030641184c0d244030002d041c81041040d074014804810959081c84061425181d40c4d151079465070080403082c040d41e142c03294901414041c000610060840c2d40080c00035241601d0a6052031900700c5401022440d040d000c960500d5000c81641d00701681916014501101c1c0c0d118600309113403c00c1000108 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 458975449 1250 458974199 458974207
    0x17090402212206020c0f0d030f0506011e0e190b0405040606031515090e09010506010f051602010c02060f0c032523010609060609090f020408060f0c 65
    0x1615548014aa00c075040040301e884800c6559012101e02006040304181030111090641ca0100041040100c250301140050342c800003101100c1c01d0030039402c4680844d000701c4c81da00403001d4041d00309400d004140c0c6410043c9948240065480c1d03260000a100428500da41c04500c0310f005228454031000c000303240034001151001c2541c00405503800c0310b521200040740402150a060242030054400790a05020394207540c40d81144a81e03082c0b194102c01156400120401402042039070080c00d8050b44c10340d00341c40e04049890189c071059594600140c1051040300303505204105444070440440711a0703555652907001168005c00d950700c10b80e4009410002d1008440c0443c0044c407000318010055511031b0364640c41d45841e007411113920958a85081ea0220004001819441d000c180e010882c2d54512040c82c410f500600c1c4d5504000219440d0a0000c1444d60300480b020048845102c001d0201c890540c0b000b031709a019906c01c0356440d034480070106110780c0149101c154014800c00700c0c2d41c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 458976699 1250 458975449 458975467
    0x290a09080316030206060411250206030703020304050c09011a0f040503030a0903020901092307030b0406090617070b0d0b0d1502040e0c07120f020106080f0d030c090e0417 75
    0xa582c4072002c40803115205030518001c154061001c40d9029200301c40c01c00c00c03440800054040c034440c5014075920003081380e940c18000100f0031080030b0102d4000d450f143e00ca1405c1c2001400940c02507805803098451654080054030700002d02038181c03010540890005140310a251402e50495000680280c2c0103120210700fa03282000580704e1008995260400d0a00e14014481404010b03009118000d080140c00c1c80500310404040c0304042000d010500c0c40c0e611980304500a0948580e407591050600c1c400003a03180b0a50070010a9429640201e00d0900c402c4172810358804043c468888505420711103007420960710ba01010091801074003440800000307590303a82e951007103034400909071503011400707000942020700307000c0c8e2102e241c0c1c1703a0600d00f04842c2c0742d42084020055094041001484400c04032034401c1d0025401825840211080040d2900c6101e0f2076040c00c84002c000607180c00a1501e10900c140402c60894004a588641645840d19a1444222640114191040200f1280c40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 458977949 1250 458976699 458976703
    0x3062a080709031a160c080901050304020a0509040f060b010e090619030210050309100e030d0b0a08150402090a1506050d060f17070609210609051e0601290a0908 71
    0x842d044402c440740855145c0f0000440b182010014080d0030442190480350018610004495506a003400d04030340ba84c5d214400111042801d400154011011a003440300300018a0361906035140300306020700c00c4202031001190814580c84509620008501c04180c4606148a01d000003852800d48040745503140d4000c00c0782c1c62103540380c100000c2c200000300310841c4418042c0c15415120642d00380a2146042c240d141d4034055005610f8220750380c2d44840002c1c2e666650464001d01400d03040da0030194075600300e03826030030040790280d0140c07020305c0014907480e000d8425042800c04003142c81c26014100f007000c403a103402949070111800d0751900b02003180c03250900308030014021001d503c50401c8a190366982040c100d035000c071052005901c0144035501c25141203440c0228902c3c0000c1c400d102a04000e000b906a5040141c003501072070b03c1c11409201a042a0040900e01b001103a640340d030f9544480300c0c0d00d6103803c02c50110700c10181e00c2e2443e503122074009203660612890280f1409850341032041c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 458979199 1250 458977949 458977973
    0x50f01090309030302010b15070b13052a0609030604030507031110050402120115060f170f0106091403120708130f08011d07060e030a0804030c03062a08070903 70
    0x980070642c0c424003001010b909000b5100c042c0c8055611701d541d60310b0365a85c2601c6000d08000244213070140c01c0040c600718016a4414001a004012a051200c103064900704120f6000c4842d80c43d00108400d81c80c1c181001003c40751401c0014000705401e540b241c0b0b04071007540040804a08101d2481c8a805c00c91004100000309921800800545814584100140e500c003101c3c0e40c582d81d03410501c044124284400c104011100340f0309007840140510f02d802c4421244a002e0078601e402181c040c40411546140160b05070b8a040e11161401c5880b0349a080540ca81110724541c1a4400d43c0340c0c224507484030001c6c101440c414140b084c01d15412900100c00c4110542002071741c0002c142c010040140b0900446819080c801c0e140c081c3e01c0e00102c040c944515007030043c2c6090041c07035888210540c80c10085090550f0f0020b20081c1c07603076103c1c600010405417a1009441c3c0c241042080c0c0c41d40c0d0690344000c000507200030414a00c005200905940c020f10003801401882580713100000820b1400d4444 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 458980449 1250 458979199 458979203
    0x3040603020906130f170105061f170a050603061308070f02060702030f0c04290907021e0d09150219080c0a05010504020a0f03030507170f040602010e0f060c0d09050f0109 75
    0x85d40e20b00f884030555041c514241010b07401c3e0f04210501c021901d5040d003021100344005c0a80f141680d0848096070740c80c0d01d42d505c080e500d41011082110100550b84041c0c05807400710240c0c0c41c142c13601070f0070001c0b40e9148040a402458104020000101500f11200f200c0b480074081905080d040d4000908180c008c00030803260350050389458140e45020300c242002d000c40361112030018030010b41c5210300700d40c08400303c074012248200480d9003036008120180020b0024907818001c8000aa5030a0300c41c110150407401140d4080d4020980f04041c584841c151030140d401028403000a064111881081c00030079500070904001c003250a4906122110510f03004000100b640e0030503105100311078165501c08039151580c8003007400040d42c45411509059001520031400d83c00706200800d140c46800104071415a002a00160072a010340014200c2c030807440075078807400034513044030b91200c4084960842a000030426a50600b80b203030b0000703408601441c120b40c03800101070311603404c4910302001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 458981699 1250 458980449 458980469
    0xa021c0201090b0f012111120a030e062104020d0203161d06010f05031012030e041d0309060f0705070b220302030c09040201020a053c0304060302090613 67
    0x82c1c84180b1038105001500565040b074489015850000c45264107411500d900d00f80100c00341100003408072885183c0d042400040c20810f0102c01101559038642180404502048611a400401c2e01d448000c1e54494001c030a10075101c4208072210208401004100303d91007100c141d104009a2401c000401c80d1007d00c80c110100300f130034800401c209000c5d004a10803802090300c1000f43c00d90348508800301595a600b41070b912502e0304190070180104541100b60200c0881c940c0e202410f50007400100d01c0b00382a501000b01b05403c40d01c0851036184049008010340c42080008094200f140c000c051140752031925509045081d84e07210700f4100e044d03200100d19040440d1171380ca101e1980c4441c1e000c80c160203094000070f514560100c1d031030307240c00c10540b071141510300c00280c15a4001c1c0000703205503a000040d611000a41c460b00080d24222100e415001c004c2c10500da00005070100b0300c1944158024011410145403500032006035008514440d0805801c1c01070b44a50021110040d026000600e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 458982949 1250 458981699 458981711
    0xc03110610060e04060311010309030c050307030815011706132007021f080c03100b07051b030d050304021e0319020306060a06050d0c021207050a050d11070b0a021c0201 74
    0x2d8002c1660380700850181c480c03490804108000b074a203540c1044d1040e420700740410200e00c0ba0805503910010307244050700600000488108143e84100c102e40b0550600e59032851b907130f8208004440f07075100c15030110f59030011440070944074501402075501100d41c0d0103003c118075410780141c2c0f108000d01d840441007140082508411031070100414821502c06040c11907259084905c000c0c80b40c60054816440c1c00c4001003c00d00c94046c18846002500c000361006a84104901d001d030b96a40721804800012901c2d9110a0490301d004944c1e40d050f0101c40d542c0c0c2d4115201e5400300210702400c2c10350141c0b90a1401041d01e06520b0a1113041a210740310748600c801c902050050608184d0002d140307038030274040362600340032003074111040e514007103140ca40006408030880c80a0f071803c00032420604013414082064810088006a07280c2980d10480c02e48522000601080d285007440711a4848650001ca60900402400d0f0340940141c4030302d8412280401e410020030071042041c0c92401d030040c0d45a80b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 458984199 1250 458982949 458982959
    0xc01140c07090509151603050c12040503030a150501020d0806031608060403080a14010b180a12021305040201050f03040c05060313031704080d0b0a0306050a02070c120c060c03110610 80
    0x5c00500c29018007000c0083e042d01d0151003040d210160742c611507090569a40100f0071506000054480e980540f081d1030659042c0390800560725042222516411350500e006140001d090781c2d0707108102c42041c1c0007080b5a04001030190b03846a13004242d80e80601c91100180340111003840824002d011010250590341024280105604030040c040b015607800c00000c1c2007611440210541120103208580b40c40390b4041c548405000d10000b441c1d41d0041080202041984d00e86920000f9980700720390100e080030381001e0110030f843c011540a0f01050b428024039200744261030046901c6407041e1629060503442d900095155001541d8400d00b00c0041c05120003055044002d9041400100d401c000e0369240c1942d640030a80304480c4030005254440d01c0003d17140d15210840380c059a403080c0103000c54030305032610700c009400480c0d00340d40d03540120030000b414103050a09409116000030199010b6414030b4070598041e0160074044007000000c921564010506120341da0241c0010212145018500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 458985449 1250 458984199 458984203
    0xc02040f06090605010f02030408070e18060a0203070e0d020d020409051207030807080a091104110912030903060717010b090f06030f15180a110705030708031f080c01140c07090509 79
    0x203013a11b1425503004101c180300e1081c0004d0000c04031680c0240b6107800d65140c081511448510340070443c40d81c46004240703c00b040440c0c0140d807040401e40c0d194040d60f01d5036004c03c1105501c000d80070b074002903885884330140c207060300f14110704c60164007164003243c0d02181e444a203a020300d40c00c6d4002100c0d0740500095985c001901d5402038680003040c0415880b070744401d02030300c2c400c07142070348900d550799402c000070805801503c404220042050f600c00d130362000c140c6e4995000203c00c0c0d01c81c0c058140014101406000c90042d0b04d040210014080d80c00c144180354103038080310080d90320403040001c0015968031200218401c01c4401c6840303019060419030880030404159010340f00e0400a5051101e240090145a900030090301e8081a0395070303041d68090080c130407004040c0c0140400640e840c14005c04100860241d1a000b0160181c104007040c0049295081d000d0761030140c00000d03061890b50b208116101d25900205155460140840b10161034050306134000e000c055102e07010003c01042c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 458986699 1250 458985449 458985467
    0x50a08240916090509010b16031107080a0b0106020607050706150308031905010918150b03071e05031603081806032403030906091903060617060601020c100c02040f0609060501 77
    0x1003034039403017001d50405070354244600412051032607080240c8006014180315145151051070b0003420b4844207900c030050b9540728420598250303101c468401c0000f902070710000c1d07846e220740302c160b0340d4504004103030383c80101500301714a91020700150a2004000704060100450250740031000c044a11440c0051b02d20a54a0591003511100e16048041a951926600c9011003941c454241140d01c90714042d0140205502405960584108100498004801c8982c090b032600c0d45c40c5400c0f1610303610002c2554480d1000d80702160b0110701401040012003110281030118a9001084214480d441c0825060340044504024081080030180703e454100c140b00d22040d04254055480c01d034500c3c3c046403440c440d0401d0780380580881309003820501c40003031410014680c094001d000c41035440c80100314894021900800501442d8080740c201d600001e038049032910060850390b03074000050740a544a048000301640c010781c8070700e07140d1241c1c40e181c80b86102030520848005043c0b0304040c001040c42e00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 458987949 1250 458986699 458986709
    0x10e070f080403050301270603052b0e01080405010f1b03060803090a1502070312170106021627020d06091d06010509071202031015050a0824091609 65
    0xc0354a0a02c00401d9001e41180d0548070106441a00419600d140035820b80e0080318850100c0d14020001c410807102040051008140030600b05028920354003580d00f072814082040c0c0411155001c0407000d500401003280c0c0030340100e00010b542c01c2d84050000541c0c82c5080307402501400710010050b4590503215013809044240d0007107050480030004103071562618000c900d000d01c51110040050792003000300d90003a41e0700c403401006080030140c02410000074046d603031024008960020036110310024500700c0d080794688050200c18540388141c01408141e52000e1003521030b0001c0801a0703135440c0010000303460014030000c0c0007031408940204507290300c0756a400e50545250350001500c030025405042d198200d039403205e60740314210150351000c040c00d1034502e903a00100800c00102001e0b4070410440702800c00c04010040b42010458491080180403c007140d803060104002c092180f049000603c0708007078141c0d10081c03075000143e040004130b07111001d0b60701a211202d2181c0c0e11140c1c40005207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 458989199 1250 458987949 458987957
    0x1020607030e10090602160305070b0f040b041103010b060a05030114040c120f180602070b010905071b0809030a24060308090f041401152604230303010e070f 69
    0x10a150b24064a99410102d164000e80e1a03544010500500d43e0403540c4d079090920340ea001e141c41d94234014005800c284001c0da00e0080c03000008401e003221031029442160b1280100c0c4641e500c0756034284000070000005070b0550b41c1c400343c3e8001e41e264180100140e03c41e5440b90740d243d40c50840034846012068061500403801c000302004156044040034030000645100486c82058040404000300710300d081e0544081c038010503140503c0001c3d80103189044c01001494920380c1c9501c0c40000392441500c0c90f130000703014401d0340c014410705407403c5240d4a11a9034060716040c0d40c5400207160401c158010707504c044110200d40403a108403288480180700c8480217120312031a50701c0380d649501501c000540102ca80050150329136665a000300b007100c06404000c0e81650312010411015600101b514002c18213540c01883c4c10716660395011001d032004404210036950f00d9888a0b190302c000e0543c544c4402081e540081c80312410b00c0034501030002c214088103d45000400103100705034514541040c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 458990449 1250 458989199 458989211
    0x30708070608040305070503121e130804050d0804030206030a1b020c010f110118050105010501030b06090a050f0616050d09060f0206180f070f061106070507030e011b110102060703 79
    0x415040302c0e10a6000303401d4148151282040d0030840c3c1588664070134107503400620703010080c042d5900c011a0f080c4500780700c0784d04040c1d912021410a5040401c030041e141403001d210400692400d100080c075100d10070081503003010350781da02141a50b04169500803030300762103801d2100001540704a6550079910ad100070440130109100217014607030410302c40d000f00400c403001c03e51880e1007500090204070101302c810007521041c0c10b1540c002d10007801030314006410034a83c05a18034015082d541c1440000f00241000ca18107410414144421484990801024845081000c504101005109005601070000d1030601040104181501d030424003d016882414505550703002610940c031a0311010030041b004628500d062a190f5010b0500c940b501c00e070800418007074603045c18a0b040b0b0748640c848002149000e80000d0312103e084641400085e418005500400d121f41d0721003002d500c2c1030401d00c8410006a2244110b140d00c0c06042c0c9040214080c0300d0b1403540c0c10045980c1c052034600d020812 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 458991699 1250 458990449 458990459
    0x509060702032836090614090406060506030c04030c05060a12090804051203091207030b190902040f02070b0f100509043f080f0f0915010b0903070807 66
    0xc81010140800303806208070821190035005920500303200310300c01003c0001000380c0d03130701100402111103002c0070b01040d0900005da40700a0300078081914000704d0f40a000200d0002400940c90006105032502d40d103c003030015054448000031806a0041141c0c1a42c0e44d00f10304105403100700d03c5c0c3c0064001c6004118030305505900039a00700c51100007000114411440d801e1010b40350050390065680031006d11601c141c504c0c400030007070507510000e0707986003540c600034803450341c48960300d00c80540110400000680d202c103807460060900148900002045041900843d08176004605001c0c4001e03800203000742408031540c5803d502444d008104c0b0581c1c508000b0512a50f142440340740c1c01891480045410450000f0342059920800d03060828101c41c6480c0792401040c46c087e150f607003143c5641460728000d101d024041d10802000c000200144c40d81e8803044c01c0c4400081c001c11280c000c0410091441400907500c50003030410174080c03600c560290003014108600d40e488a51664441401048 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 458992805 1106 458991699 458991727
    0x204050a092004150302010212030702030d090305180f0312090d140a0312140c250302030a030b03030c060135061905070801030213060315050906070203 67
    0x4000318201001d001104c10a000190058106030810718159500030000c503000f12030351040781c1c980001101444102d501c03648088000620002d020595401100c0350b021421008a50105a20321180002a516060100c007ca1454008582c0764910707a50a0074800c3c2207a00002e000e84503510b929403250b12807490140803400b144007400309d138182c94114400d51490820f0400f0583c2c2503140c404a5100c1038000032100154107101c4640c8060102200300410212482a00110f0301c4414011001e41501d40c15014503001e50b1003845244000f48d400540d0a04680200760301c00c1e4802c801c444c88841340e844007022288003c9101124001011002074001c3c400c0d0003945c1541c14102d801c034049416100c0940e0f2074400900d034400140003600c0c24100820038600c0075403000a001d9500d0740ca905038032022848404403140d86400b00b00840d04d0070300686034000300f01c1c0701442c034004140c81d4142c = true := by decide +kernel

theorem cover : BRFrame.Cov 458812949 458992805 := by
  have h0 := BRFrame.cov_init 458812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 458812949 ≤ n) (h2 : n < 458992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
