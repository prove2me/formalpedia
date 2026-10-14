-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2623
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:15:43.880233+00:00
-- url     : https://prove2.me/submissions/afae5656-5aa7-4bc8-ac4a-67d98eaccd63

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 471582733 ≤ n < 471762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 471583983 1250 471582733 471582751
    0x6140a0c05160b0318060f0609190204031b1211151c0209030c011e031109030a11090612060c03131208070f0309080306040c02010e070602031210080d03050703060504090308 76
    0x60072074149000000c1c0031440744540c41c5070440d0308d0b1158002d22032800c3e0080d20030000490110724124104240740014001180710703107800300c0d040c8c031122080d9844c03400c19009038100c4101022260042200347c4c54025400d44122a0307004001051500150a4810100400ba01c1e1082c000d0310744020380700c1ea0241010340c109400b079440c030f80344807001160300c003071100c8039200b1910b11000c80305240361181c1d105103440d00040c80d00324078202d07a04001038a003841c071400031620600c2c00640e1114a040403040d107508488251000340c6a200c0300d205184c0c8a00700203040381403800c1c021000030080b40701c00d03064211042d008094100c132840e0140005225407400c0321282d0200e44440c0340c01c09c20740e00ca48112000c0c136030032a0762641980c417241c007000042c0000080315001c40d0749409100d0300e80102444903c00500700364000750707540c40d51060b004007a880014010800502032010800c42d412011803103000807000e40c60001810b94864100390b004110f25040260803600c2c0c62401c804058105d8011400394000c0c13 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 471585233 1250 471583983 471584011
    0xf110d0b0105040e0412020705060f1c0e0a200d1202070506070f11130203090708010e120f030705040e070c140105060307120201020f1b0a06140a0c05160b03 69
    0x401503520b84541d20890342804e05200c00140030903030700c58000385c80322120b10560f0545036072a800215203802404d08580c016400058100e581ca404a94240f070000405000344620b406c01c581117a22448009406048150741c01010024401c20446061506400800382c50601005051910402101e134030f03c0409440bd9000114040c0390100968141c3c59200c0d688410b034203400e9407000c0c111980e00c045c86400c0321840c04c03262607044503400510b106200e01030051003072514128040d1300392403143d045a4103030b0b0400190442e2582e090000c0320180d000041025503a03440b95a4101c40901c5640e2202c078600000308180f0a0303150348111407140d01400789450303450084240d81407a00702c402c2510703040c0e4164000401004909698400024554014019558240d095280803400c0c080aa203e140e4225107600c0c01d006d447c94004c51201c0500304510b132029000f19143d00540c1c2d584a058664800e102c82c0300100000c100c02000702400e95600722054291a5540700ca0241550300700740c0d140c2150b0000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 471586483 1250 471585233 471585251
    0x160908030304050703050f012c0c040c1d0a0b0307050a11010f0f141302130906050406090c0b0f0f13051009060909020c03041e0e01060806100305010e16030f110d 71
    0x14000c68994080f2020b11314000e03450129001546811042c80c400c480c002c9001100c0340c0e6078bd511681409200030384a10540421001c0210b8024041c003808520402d03019800740079200034401507a500c1200350400641c1c3d1a103440702079032040143d5078141407030340c2000368031110715a0a401010b1001ca0004007846030b01e104102c854800c01013103c2401e030014650009401501e01280c0e0721281805c520400940c034100c6407194070507604111015a44280c41d2884035081204c4265104010f10707210303015a04000c0080e202181c507100d03000ca10304858602081000c0c0c0f10220010130001454018800140f08085160141c0b11501070711500006c140c40e01c07000291030701507000701c5014180c03200295240c43e05100c66004008490802a010350380d07a110b0100e030355500902c919001c3c100303588402d0580c0c90900c080000d040500140e0394100340c00c0100410866114244258006c51200f5031003460031a4200708600401c903050720203a905003000c0210364400c98800c0100202c41d4071441c00c1c840009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 471587733 1250 471586483 471586513
    0x3110606010903021e0a0909060b0901050f01120e030d060303030f110f07031206050a230109030c140d0606060908010b032d01021611010305070f050316090803030405070305 76
    0x2d5070300c4080d40050001c111140380c00401d00d42010102002042e008420303817946100001c07a00c24010031103d80b56603240c00e00c0e0070314040604500500040302d5568880842c040020104600e0385a00e185580d10780007151000c0724240141c50b980208544c0c10400c0641c1c03801c006018000801092248038980180c40306a0b0500d0401c0300d01d07002783d401c90180b8264040c2c0d000c40c0d18074000304c0714568042c2d130b541021a003540c03600030920007071480b04405402c7c200c1b15a2404000103c034843c190500810003010000240340b0905102250100300e1102e10031490b20b80803030300c06170034008020485880c25001081403a00a28801c0540b41902c000b00035400c5600305150b99240c1e80104100300c01c4128844403180441201c0e41409035000000141c00c0080403114104501c800300d00c21514020103002d48400c07075034036116490340014103203409445070082000141903840058500e01c25030410360000803000c0e016158110050100000301c954070720300741c1403182c0c83d002c00740800c031b48c00c0c091014025042c070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 471588983 1250 471587733 471587747
    0x7020601061e020f0a06150e010302032d011b110610050405100803070c03031706090c09182505041a210f04050c030111090405040309120311060601 65
    0x2640c1c40d100d4100c440c0c909000d0280181d810200142144680741100b40e20700340620102c9100d510526021a0108076148800101482900540c03610b204c3d2500400141c1d80006101281c1620b4000140c68030104074030401c587e02c0700000c900c001d90b0030040c0102200540100e03034181241c1a54644000c2c444e6525800e460340400c0d914a04042aa82420311403440c0c26445a60080ea8620071410001d56650420741150400740f400c1e01c03018520641001410340156800350032450364901040b5a140001c0002d01c0c0300300107418401c1c003030702c081b9a80c04c59803240c105548003c0c1441d00f54032001d141c03803180702e901d0314000061090000c64103032440d04458018811707034083d540405c2d406103040d16101540284d503005400451480c4000d080404442140034100e503000f00e44800355a1820b140905045107002001a142406a85440101040030f0800303401c0c2e0304143c80c101c5000c01c403a1141d040841da9445240c00c80a4800071900c0045d0030103030403101e102d40003424032003950b41d165109801501c04d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 471590233 1250 471588983 471588989
    0x90607150c030e030702040e0313080102030f0105151804020d021803011119051c0203070201020c0d0503070e210304061805090403080606031015020d02071203090e040618080a030507020601 83
    0x3e0b60040c01220300500e0140c0013900020000e0f41281e0504048000099028040c3d9208002c6a50300005004400451a520700e01500081c0c9010900b01c82951044034248100360503410150000c400000495690382c044540d50501d483c0c0c1592110172143d400d26544106a003140d110750701c0c1c0088408001e818030192044160144000440b0030200032040c0c6059100c40c0c00442c0d4183c054513140c1410301c581c8081c0d400b41e8901ea0006880360350021040303182040c00203440c028080700344104014980d0207004490a841d09a420742034410540e98045c20610046a514103940004a000301d1784035031102680e00e0100d8000d019160f0142da600034010524000c2d240074001445280c0021141d0501c0340066800c084558000c100c002c3e980c098600082600309844001a0045542180280e604003e050b02a2241e407000c035090090559005d000501240302d522004d421420008080c880640d001040040500780556aa68a039262002c4158405c3d10188046450080420b406900c0061081d0503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 471591483 1250 471590233 471590261
    0x513050c0306120a0f031d01030603170a03020903030a050a18030c260111090109080c0904020d030c120905120f0c0108090f070305060f0906070c0602030a02090607150c03 75
    0xd1a2510300501030500f00740e03a103001c1144141c42c08040011381050000c03003101c1c041e030b030350900507a104586511030441c012241d038100b42c140501400030800c5c2c0c041200c1c002c602e6403841c596507400c81c1030583c064010303020041d5250001103441c503100364016009200100c0d19555070401208500804019402d440c08003402c040342c0760340140100300000ba88004406040c210b01c003101800c0b61500307421346041402c0b40c1c551400100752008076580241c6444003401c81d05025103115427000b008224403020040011f1720038110b00230820141405408200e40040d040112031011104200014100407006d20800e8040d03030001c0d0a58801c16004624240c805040d035004e8000e803020100111520b07000038113410400c0c004e81588028912041010400852180300904050b184c011504c45d075804000708103042c04c0d04440200b040740c40e84080300803c00c0741d1011340142c5a48403440e248009004940c401a00448001089418000b10400d0203500e0032000500f0b004680050f902107090f01e03091150300301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 471592733 1250 471591483 471591487
    0x308040f05240d0b061b0105090f1207140330010b22090e010510090e15072a02040507020118020d06020906070f11011b0813051201060513050c 63
    0x128900300702c001c29110080d11400300e610290703040018040e51011044c9203120701d800b51184180c500038054103600000301405010b00f00a42c903000c1e80c0742e0840c94881140c003a0002548d800300b1004130f00400118070103804a0b80c4400c5404030314410080c209881e440da40410640d680031001e09091b0b4541030b0b8002c2d030750281c14403c5c1c94030400b55111003c075002800c0c1184050101d176540b102c1c815800051018400401c10b41040d50f10034007414100d80000e081c140c14030310507094204000404500e4004801c40440b00da554641045925404008a1507001c4c01c8040c80000e40900742000810183c0c02190700700001d40303880100b0b03822914081420141d480b42da56011340540740808140c11038034050f5178003601d084961030002d40103520140089880407000045c200900107070a91503082d440c820b00741148130100e90b00581440c8241c2c020001d014801c001101072400e541d802c0c041005081c0588180c044601c0510320381c1c060f090354010f9a0107241c004110044144040c05490b00901821a20b24 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 471593983 1250 471592733 471592789
    0xc0304030f0c02031f02071502040807030b0a0f1404020907081605090103110301171002030108061602010e070906080d09050f090402010c0b01230d051b010909060308040f05 76
    0x24036414403520b400d981c5801140d201c800342c0d04031040c10b0b5400042c48040107a46400e685410400d4110b45c3c000344202c5071051005000004000401a06490304003001241542e1002e40d4400540b0301f00c01e020b002e4500344801100303a440b51040650256100311110441c640d42c8200845060104954083d1000c1c0000ba407108202e0140300181703e80c0c00103140c0072542c0c189072856854168002e902113052a01807008140100c132051182d16800c80310110301303500d5545065001030f921035026003101e020740b1a031750300d40300d00740d000750b0288299407007030400d0b80d00266580407441c3c0104181c0c401c104450281c0680c130b0101a02c01c0d400740c019603000400000c2001d118105008990340000c200300d0502501000c900003040c50b4410860081c9180480c4500c1640380c40342e81c044508028082c1d5004030018884440064804510100e890f102210f0182d9030b0044a401220700c0b0250381d20190400340303048004020b1040500042095410f003012040724640c0c1d070f105002401d0712015103000c01d10541c050300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 471595233 1250 471593983 471593987
    0x140109081804051e0a14180c010212030f15030d0309020307090903120e010204050a080706030b010f0c0b0a020d0207050105010509010e0103030504064e0e07032d12080c0304030f 78
    0x390400101040041c0c600c3e01b44101122103081070300c0744c14a449006c00307030040c1d0b54000c2000c044980420b2000d046e0b40b01041f01103042600001c0c040b490441d003403030300180c1c02c0909015181c1d1010070040480c0c0c1c20307407028080178008000c0388030180c1c0207010b04480411034030784038040c0400103581076888900d0b882d09940c120004141f010700380c68095408000001329640e030701c03d90001806110006c0d000051038480094116007501e0301c0c160501134460510040c1c65080040d00c0c1010740c101203109510390300c07451410001e105010402c2d00031803011035444240f05055008506070741040d01d00b1102d0784d8843c141d140441500340703c0140011802c000c240200c1d403180c134a050100d10070300d00c2c500700c40038042901121000c40b42e0340e500082d407040c0c00d0580340360120501c24022043e00d1404220303000022510030340341c80c0c5500001c0c0442003451480340c42c5040d0010f1030000450300b10080c0742a01e042d403514076681e2050851000002d80d000c008221401440700480380950360541b41c0c695800c11914003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 471596483 1250 471595233 471595291
    0x9090309010903020607060207060504080c0f0c0f011b052e0e120c01060f24030908040902070201090902040f030308091218030c19080111070b070c14010908180405 72
    0x81100c409802740070b00c00004000d0301981d03000e207114480c0c0c80d44035111146094038000400081d0903a41e48040d483c04095140c2c0340405c0c1d0340107420b1030300107c1141e001c42e020351000d1900310014000c1c442c04a10b460072050300450b6600a8941d00081007589009056120949401b182204030a8000140e64851960a2002026803100140000c94850341d52140280110b086601401990f90303030703445224010400c26000d5910b0003150808002503c07a94a48584a0140d03000b0b80c9186540000c0c0602036a001340380010081803410800d540e956200c4d1640d0800306054031040300400c103088081003202c0b00125a41403c010703000104d034200105110185920800000801e0b054003a0a0161820303469006400460740030b1240350614842c5059056400c556030314030000b000701814800100018510102140c11415038608040c20354414100b03100342060000c940f2010358030706074045d8200140c0202030b008110289481141c000381e00d40900c02554011103102025603030100c4001c3d075105405072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 471597733 1250 471596483 471596497
    0x90203010806010512190305300601180b190311160204020a05040902070c080f0a030914060c070e01050a050a030b161b230d020723060703080402090903090109030206 73
    0x44034850036225414070b00303641c6800c000390009400014503840038020030452001e4416400c40d035100d404589c054180030088050302140c100b144601ca01e060101126801c02e0240242e5403207144c1e40e1842e801901d4552514200703001c0460304051080d5032181c640310681c0c005880384190207d134000d43e0741c00c1000a500c04400c14043c4441072102040f8031601d8406040e010303124141810100c1d00b81550386180c070803205003002c4640e001c102aa00008c1d4000c1c10a01103808042c181c2c221032035041d000458602076a0110020b9102d600300c00500a003480794080d04840041d11403e45070343e2150140444910b25020184c90300c0740207404100c810284030140c0890810500d40b5522581903184540401c8108500035100d0021410102c3c540035400130a9120841c00a4000c0c0b90100c14600042c0d11540117120b0000c5918a81c40f004160040c1c0604010000600030413481d034518039851b028021340d00a030ba05a008880c410005040f0342000030840d50b83c01416150181020701c0c550030000d45600046c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 471598983 1250 471597733 471597769
    0xb03071809050c07020a08060601020d0804020d140717061b0702030a08031819020a0312020705030d09150905130b0f0301050106020a03080c0301060918091202160902030108060105 79
    0xe80007a40c6801c034850319002e58035002a00341c3d14900c40c01040119011600142c005801000502c192a0b8000407592280169030a11100d42d68403400010b181c0807052001a00070251001076060303a9001090140c16120100d40c3d600d00c1e02c14003003e4540e02d000c203c4440b002484080c3e0044030000c40e01d00a02180e61004040b1000c0160b035554030740c0305030000d40c0c800e8440d01391000650561041403042540f09102100c9034044824550000345040311544006091001b02c03050840c0001c0c42400f80c100502000340c03c4820b071080b0910020b0020410340302e04203002440f1540e041c0d142c0c0c03083e0202d0045480c010095514042108411802000c41c44c030050b070312485410202c100346d1800c0c02494001d00042e0060840d504d0281405000d8100041c04904081010401030101d030740c10440e035100780e4030541031001a14500b1002c800003080c94000203080a116040706025840c0c2c0054040c03051949c4a4501008a079039807080410f9020a01401c440341d04000010700040c105803520344500c090704 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 471600233 1250 471598983 471599027
    0x801050d061d010c0e03150c0f0d110306122407180f060f090b0a0302091206040501090212070602060a09030e060d0903090e01060503040b07110d090f0f0b0307 70
    0x19400b102070300034020207003401c1c50b512044442001600000c2c000080801034000e010041c0b00700750781288807980107101403811040450b860240c1c40c00041a00ca000c4252041000460a060804401034108032040381c45444424108441c002c00892240340c0c048044450011801000f48400041c610080101e410040c025680310045403541030800002c0c003030142c80c000417500340040203110000c1142480c041c007000310710030455903203441c1c200d03552500c6074500141c40711141c1c0009080340780f4040041c940d501c511000e0100b8001e06600000c8054402c13184000b00b070f52249010340d2154410320980b400358001c5000142e43c003209420600443d40309140c0b8001d1043c011000420325002000391010069403211705004154106040320040c04600304e800e07100b5031402e200107125200040c00188a2011140859020b50081c546260814a0441956044018643c00600c2c41080d44520713807820388001c1c0005010740d00188010117645041128030710f190b8451006441080a030f00c00394038042e840d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 471601483 1250 471600233 471600251
    0xa030308060405042a080c0603010810020a02070504290301181b15050418020403171303060c0c051009051903110d08061e010e010e06120a0506030610060801050d06 72
    0x110030884000c1d46a0f24a174044100e040c14074031131410705100d50140c0601c50400060014920000b00000001840203000d80d031a08105812410026a039110503045810001120b03012070000d00d00240e24641f00300c040907549482c00416007a540401e00000b6104e4850212a0205121610341110700d040b00c2840045a551140c8941d41800342e0b20700304e40000c1c4041010312000d80c2c85840c5400090080c0415410282035480b882404891452401d04010000a000c0d081c4000e1603241d000071504130500b04040b1001c3c1c08e010b000680101c00450310350044618510340305d02d00d4410400c045800c600100172011401c0142e00100403200d1040e0140101400344002c002010400750003108503d03541c1d1542828241e05110910380c90003070591032141c118600c2d00580e40c2c03003104072103154030918280b01c4c0b050092020440d94070490100c0314945d0b41c0b0504114100d529a04268010319094003208d44607505d00b41d0340c4008031958051000090007100040041e4940764482c002c80d94010b010009082035 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 471602733 1250 471601483 471601523
    0xf0c01050a111c0615020109171315120c02010209040c030e30040303030603030806040e06150402040308190e03070b09060d0b030604050d0207060e01021c020c13020304060b0a03030806040504 84
    0x3045e914042c0060391a86000010400e41c007101c6410010f000504074240305201d0750700700c5101d045000d00712500322003641c4101500e11586c0804079034242881c0800c907504940c0c100034041d50000a000340550f00309001c02d400d1603c80d07c02c240a40030580050700d41008404854038510400100041104d010018125820f5501200410046102c1e0724001a100c3c41c503d0041c01d403d40080c1020f00c903914104400088400c08541d4139801028405a8455079001c10005402400380740c00180c8255800b0640c0c0120b00302c00500a591104103448a0454000c0e1108043d070f40c00090280410740b4105108028031414182e010303200c0c06001c51000f0615124102c0800d18100c81220162071a9114104200000b90140202c1010b4002c504c2c080c420103100bd00040d5503820200d5692042c51609541498440d1080c02400c507d020000c10f0003e401c00409041e0001c2e40040d40c041c0e0f05945400c041d482ca515044000e40d040b00e42c192140f500c540c0c0c070002000000c0400800c1510106210172805101c80c0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 471603983 1250 471602733 471602759
    0x10c031b0302150114040c05030c0909071e02030310080a0206040e0a060b0a030f0c0915080a020c120315040902094b01090e1c03020f0f0c01050a111c06 67
    0x41003958280d22545e901d02004241c848101c4280b0030310404000f8000b900c402c03d02110302d01142603910841c641c443c454101c0741210001443c82100c04030f55908908140c2c0400154001c03113004000181954a80b000240c0b01c00403917800075800402080104003d1503801510b81d4025038030742d0b0009205a583d08240340e564490103110000036030303c1c90048a0140d01e4410301542d6445407a06145003400d180d414665490031a4000c4103100d10034000138008400341d0104c8614880b8142511840b00e0102c041440980090303942544030b024841000609040920501c04242e4000304a04003e03218580c401c5000c0003050400d4043c001201c0007444050101c104885184014040c108a0175629203903901c20048180c0103112400c0c00c100d408101c03003000041e0b545140d0f41442c0e8480c10142c140c18182c00a11030900510391004002c615405010404005069440f108100901042d078034010380301e040301c1031640c0c03000c1c41c40c2c420b020040c1401d160020454001892020004507a03403603041d0a4004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 471605233 1250 471603983 471603989
    0x9060703050c1009020907053006030f0d0f030221090c041a030604110303130b09090c0a0f1b061d0d17040308070e06210105010c031b03021501 63
    0x1058001400e98581507040046200f1001201400c12000ca07003907001074580b1001038940010040e02207603003881801005c291300c0e80c0e0502d4441c41840100d4092042d01300d90f030204d030014400e0142d94000b10000c80b0101d80031854400300e95413102c0d051070038101070700203420140c0c290248401c02ca0540203004905014940500d025400401141c8480c0040005841200072145202103070164882d92545001640c3c2c1e03040f41d4040707081e080c1d4481800c0405e1841c02481c07030005401c0d00c14000001c0104540c4020140300100791a40916035481c005034440c20b105680b100f800182a01f0380c6807144034400c41050301c0b01c0c001c003420310f45490583e4950b401640c1c14400f0302e01894601e0390a800400c0340c1042181004010b0b402c044820fa00d910183c0000f04d28014405000e000c00680002ca409103d00704c41c510208005144544840e910261446501243ea018440400104001050035802000200c2030f10750315544e8580b5040d08000030900c480c410140c21000c1d4895080c150102400c080380007400703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 471606483 1250 471605233 471605237
    0x702010c0c030515010f06030c0c0b0a14070309020102010b06190e03030c0304090f060501020c09040303020304020f090106030903020c1c0f151e050705030c0702040504020307152d080103150209060703 88
    0x81941407030046c8164404c164000018149071099101e0b2943d048400985223039003181548882e075075034113010701c003074a520350113600c1c0810500104400385400d5881052128000e900030004644d0300d0051114600c90004031810f0450325041c002121445492001d40c8414003030140c038246072030014800d1841d00203030080e9602c5030300c940c0d0544005580380b1074000108002d01c02040400c580001040680b6400340000e02010b40010010b401d64985400300804000e01518070306080d80c0d1080010020320802ca01100180144041c007051444d00070040350030700c44001c141c61540d011035680e5040c143c0c030314501142c01c2400c49414800c22500e520481e8030903000c54002004440142c0e1104040310b40003465102409000d009002041c403449050701c914541c159400102500c850000078a4100380768032510f611500f00c1c0242d240d680e84400240d00e080d4212403016400403022251350804180201820002450700c0c00400c040350903a80d001d0b032492100000140740c036040801280c0f15910484050700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 471607733 1250 471606483 471606523
    0x307020a0b0604090c12060603120f033b1006030318090e060c0f0c0607030b030d050408122808040b06041b0809010b1804140d050702010c0c0305 64
    0xc140300100c0e00459000748111010403104a543d0b985042001103805841e10600c2c0c505101c0d4100301c0258004d1000d550030103546000b41040c41002422144094580350010341008907242c039440441071040141e548031000303106115200d0342c2d8201c0022200c0b5038201c2c40d00c078002ca290308034000f40c8075203000307580030395a910546596890014104000303544501d124a10708844180004004103c00f50000f031404c80159035021021500c110b05d00a415124100f8000c10041c020072a4059001e08101310007903040d20000308014030103940d02c3c0110b02c00d0701c440e41c01c0101500f806140680007085c1d0364250b041a03180380160040d910050244401240c0041000078007808280141100030f554048400c8405100440c082c0c003000118030b50301d203484400e001c080400305030340d88800c3d003242e00d0204014141c04445007049610414111058130155814000d80342c00c40d00541c2c0200e2601080041d035100c1503d0050300f0340c0110303010b0050b00000d0307813a003000318004000600306020540410f0349a5806030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 471608983 1250 471607733 471607753
    0x9071b06140c03010602060403050a110d09170a02011d0a1703091815151c0b120303040c17010207021206060109080c0a09050c0403050d0f0206070e0a03021014030702 73
    0x20405030000707000c02d640d4000500c01000b90301ea00045241e8003950601c2c085468548902041d03c0b6001240403030120b81c0102d02e00c645c1129030004410007220440c081d48604001504a01c5844001c06c52010340001c0b04414403a00042c0755081d02401c21002a1188900984c1c44c009124405207002a80199400004850b0081c0c503042c0011401111000011255030410f0414001c40601c00a00e00e80241000140c0d51000c0082c0d1096075110b454042c00105074140d44003190000701000b400491088a0321a52801215800419640b2513540030b0100050301c1c0c100a0445018100202c4460043d0b408108042c0143c031400c00025036940c0180003401c2030b09110001401010b0160400d8059074080d0000322007030341e1102a1002143d00c00c0300b0018150304c4400100901c0c0c881c5030805012881005490001c00e0340c030113615280f01c03407558251585516440c00468006400000d481d5108620240510142c507021528805410403030400e001d069640100f605d0301a0000ca9040c00540c0060b0050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 471610233 1250 471608983 471609011
    0x6080615030313150210151d0c04051c02061b010f0e0c010c0303090f0f050607030b13391b020307031704030512040906150207030209071b06 62
    0x800c0d2910048002e5400c0122800042903011444d2080101803458160034190243c002d00c01311101e01e840c000e0901140c0c0548114500554551080042415418206034071808404413400d02541e01c0580d100c0c40c00f8980020042100071803414509001c5515081400682e141d40080090228045503500c03001100010a801c40d1646001703000110b08080003036081c0703103001c110340d1119202401c3c0121010900e050860003040000401000c03111003000d10414400178008611580c2d105404452613a43c1e400e400310180d4403c1c11080b900544220508460f15182da00424684030241c4c0c0034540c00d0141006c20003040039035003001c01d01c0e401034100d10408a940000b41d594411880c0d040714207044180d0740826514140c0e440064517441c0d9418002628000d0642114000c540240480e59090380b00090042c0a50061048d1020341d0324241c4000f4000400d060445514140c41d0050040ca6103184c0a1004000c00101000d0130812a000d1600e1450f1404061910840c010f55000400c0f030780381640 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 471611483 1250 471610233 471610261
    0x1807240201090309030201030e0a02040207111f05040506180d0c060201110f04030f0c0806091501050a23040b0a0e0604060911030c1e03130c0501050c0d0806060c01060806 75
    0x964011039040c0314036500803030b420421040c21264207107400202c946110803c0390424949c0c0e24000d50140c0001070103130a201261440d0034003a4001c0354410009207512191094500b0301d25140808100244400c20003403602c0809000d088a1a06001426a4004000525240c1d5000084540303101c0c0032024000207031309200703a00a4018498000f0301e420103070307100501180980d1000504028079540c500c2e041000440608000388010000c2b85c1c030508141e00c81c1c584442c074010f13416480c0ba448000000320391801c5604141195900d0351440f034290704004511000b0001e0025071a041503c903c55842d044d22481e000d2402400401c4c0c59101c5402c010040005952480c1d0040210500f03007081140740d03080d02022241c1061820398600c1e61407a024a074010740c0d01030700d0b80c5e403008240080300b001036148108407035100143c07040784807e20b159102c2c001034826001c4c4007000c0701942d1003480ba07a120300340214800c40d00b10800500e02401d02c060380d00300c5800d40d8419049250550401b0f01440200b290010b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 471612733 1250 471611483 471611549
    0x80906010b040f050d02120304030b010914040f020d02040b030f0a140a0809010c030201090609060605030105071d0f0111011109011b03050708210903090316030506010501081807 78
    0x110070302e06454030741025010445805000e03c03d0380400760290071951519017014501c900c0400340d031f440c0ca58908082001d46d0007441401100e500340262281039401c1006101d00c100d0f404050518034090039000c1c01905080c801e000c81e0420b59074481560b440c0d0b030070081058050780c3c45000703010b074286614003254480800c43e0080c14903801074450071b0000b440314003515107550b001c3c60903044c07010031800c089015249218010300054501188c400500c10180c01c40d406440003035000340810f446040303080f1041030403803200c810120740c1d085008400d0300c1c03d000440350042c0145001c0d440403c010719880d0841d805c8000760306004900140b650051358020008d0307001c0c3e500303d1410f406614120748020f88a80700e50700c0001c00031540010b241d40d880300c40051030030140c04001c40072500d0345820801282d4036808809054030910031b201d00800759220325200390003503030743c4a070207000a80d01e094019144200301800090120101b049031006c3c0d00820881c40c4024050380d0120300c040544684003008010400d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 471613983 1250 471612733 471612749
    0xa090f050303570301030609060b01180311040906180b010f06170a022208061008030912030708070302150c0421060605031b120102030601020d0e0a030204060608090601 74
    0x12054441c4030020f841020201d2000042003003690a1161045004411064600c0740da10000c000802806896030048140f203205000801c0702a6803400155100c0d80300c804c2c0c80080c509a08070501c00100e200ba60f00c10034640240000c1030340c1c04075584920a0301c40f20b41202c401942c588044000f07015080c103040e0300400034000c80c01c0705a4148907000703180405107200d0141032004107010801e1a0016411250b003d020400ca0f5514040c180d040410b83e61581e00c1a0300300340c46039401082444140703500035011100c024008500d015642001d00007280900751103c18070f80410b01200d00420366010040c450319100b58060b16803284a02da08003c03080300a40b00c0003c010041c032052220a400100700e0000000c003030408503100206180150141a41c1c0c1c2020b9054095107841c1000804104170f03191001908803103890798066a403110718203d000c115104c0b40160b0010300e00305003260084002c80359010021300661441ca03140d4010805071040d6a1028000900003c100b10020800f8824030303001d40800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 471615233 1250 471613983 471614041
    0x60504061d0a06150f0803070515010b0409090606092a140a111e01140a0c08010302060a1701060503041406070e062b051b040308120a090f050303 64
    0x9001601c1e520840440c0007002d596403620802e07a0b10184140313110080900320402420750f620f6a440c030340c81742c0000c0000c880d284034071820b0018601c910200c440c16540c91801850500e80f03015800d1001c0d250030700050b1802907480c4004500603a10740240c0042d41518100c00f03284000d5207200b20142d20009401900f000a84458004001d285a00303d074031450300380c40e28140d000300c404e440d5400d0240c40c01d1200c1c004040c1c80c1000310540c206402030786070303480006441600750395101304140aa84450007600001203166006200610b41035020301001c85842c034001740210841700d501e1040c11002e0b0440000701d0710200c104001c0001c43c1d441c080c1720300101d00240000303042c01d401c0506840d4540d031005115600100b55550b902983d00840244442007299a40005820705004802001c0503200e144408041070307400c02c29006540c0866044903400301940d4078040c1d0398038034001d07007510281201440c103848110010115012514002c012401400607507a6400c140840b094130841c008102c16280c684 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 471616483 1250 471615233 471615281
    0x1207030905040221040c0518090727020418060519090c020309091806010f060e10030f0f050601180608061c0506090307120815010c080f040306050406 66
    0x402030406080790400e5038096240c1c5500b03039541c0d503106200e4001c20b82c40310707503803081005001800b90080219041520b00100c00c0354000d0284d00c50203800c441041c800d40c80b0003420010b174403030039a03506100030f0794240f42c0d10110780309490303007090703030b005500030003408000d11244040e2a031781740f10b001c004010440d688900e0202d094580110502c10748611b10540da070f0380020668072802401103900407500140100c54514240d1421400c80845861b4010f0902c81c00d00003003041c0040700c80100c250b6500d9202c04019025500801c040c0d06107207460b0504140d00d54071141101522070241c0b4080004090000c03615260a03c001000803105128080083e66180001c04c00c41c0d800801054103c4000d507260305082220b5180d40d207401400420007401d43c0315240400c40610408409131a0852043e00c1044d6400303e40c690444921500b610551843c501140e90f8203400e41c014449103096520841401e418000440103c132544d0304941c3c0261021500c50702000100a00707441010b180a400c2c43c844000b9150b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 471617733 1250 471616483 471616487
    0x11b080901211509061401181e0f0603020708030a0905030f1c0f02092d300c09061011031305212503060507030b01030b0f0114071a0414120703 63
    0x251036059030502070400d2444030852307003611210002d0165481411601c41603900c08150100452040181c84842c0100203d0110311034021940650340020000741192550801d01c4002d10660340c08840a20040111a00400d28580a4000441c502c05525162901ca805e100c082d0307041c451141c900544100502d00300d65542d0407080f014400600e401a0902c00d220301a04070303201c12410541d6100702c425401030b4409a0300d003c42c1c0c940d0071182c1d582041d0700301203209003540c8900d0010110341c040b001c04005091030070f16807007a10802045150214407240420261821988a10700702d444100300c02e0403d01943c02c002c402c40005a1141d9000c841d80f0b81c1c0d1070203030390722800001140000c80f4004454140303544000c1d9080c1021703581040c0100301d5810443d0f8094000c0440c4802c05003c24145220b88403a8986074030445203550041e110500200810100b14038158084081110120200310b0004144402e11200c035204601ca0344800301d01158150b050b514003181030000742124801004000002a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 471618983 1250 471617733 471617759
    0x609070614130f030c060c0f2a1401091a0a080c0c010501180501050f010c03050309251d070f0c060908030a0f050105011b08090121150906 61
    0xc0d114900115020500c1d241c1041600c10908aa0b88090300580082600201c030b4000a049070312808918851707542c0e5201c00d0b9201c2d02403480140ca410a02401800800c020400c280c2004000d500b040000e14800031114106031044c2d004075034000005140d5101d40e503004808540a0940320040e001c400658a561444500c5121005401c000168010814900a080680d610040e120700203008641c1c42d5044a130140030500d0520451604242c000100c600308850000407240041c0e40d02e0b5928811780e1400d5906074170243c40500709118002c1071403c900e1191011138207041c198800d901c001d41c1b80c0544003000e2040d020803a181c1ca01000c041c02601074100d65081d5001d142424017820085690a00800510400d040501040000810007006072400c0d4010540008021802c000598807030004552200c119a00d0b180180281d80d0500081004038014004a010515040100e54042c5000790802c03411841407411a5445511201120310707240406406021040001c003c8145404901d41c0c02c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 471620233 1250 471618983 471618989
    0x2160c1a031302061201030b090615090610050405100503240d030e0a09021209280b0414030a050c071d0106120e0d0504031b0308071221020c0c03060907 67
    0xb295030906070115110401034845141c05020004610760392030803d215504401c5494080c640a80f4000503003040b04802e84070340105014100300d18981c0c800d02401306101c05200100700b0300c0000d1100154a80e6203a48001940600f0782d01c40d501c03402d21a10b0a03a00080d0888040a20224505010110340351002052507103600351900400c148074150101c1e4010035140c0200740154000940020f10240100f44c41d801202c0003400c643c1401c420b00340451610005c803e12030f00105000c11010082840d10b50400d030014000d00d00821800c4150341342c00d182d0b61281e0b01443c003141e0b010420b404a14000e00c034a00040117040d075590b07003020012038038410172a01402120184240060098006280395000e0f08145102030121480c524845102900c1d039041844100c0e100d58132140c1c110014480700340c0c19400c59510000482c00e0029958625011803c2c480d10741c800c0024000e10884262501104507104459072000182e5845507200f81505100403489014001c1d4880010b0103c01c250010b51300c070407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 471621483 1250 471620233 471620251
    0x2120d0c021009021c03120c110d02121903020c070e181f0218090f1902391f061d161b0506010e06010206090705150d02160c1a03 57
    0x1700d09550314050f210540c60301e4640304003910340051010340c103801c2020306d42d060400d6004c0391a0a11100c40c00c0340d4030402c1e22019a04070100b07201c500c040ca15107201c100300c096035500700542003a8110703990a1074541c1550020f85014403c00502c1381d13040c03c1706454845044c00d20007801081c41203030b03525204000c0e20790404101542c001000102c0b0405500c0c9001181402440002203041184514003000000c1e120410280c0e1028920007605c08280b00319503a02a0401c810303500006824201006020482c0035540108014056401d01d05814481c0150603030344d14485440c000204844c64003140c5c0b0f00d030486052203400120881c5140d1124051682c840074410031030701004104c080403600f40f0004411003503403420600312181000800721382103041e10013029210620343d442d8001207070f079040c0c2a14004595000010144447d003001e1484a12440c0340c28095031810341e080c12a0030480e8080201c010140e00c0310482c0c0010001080c410200501c0c0d13070300507110030150515507041d85200282c00018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 471622733 1250 471621483 471621529
    0xf06090605030f10031506150507200301140703050a0f06031a1f03050105090d020705060304080c0304050d0503070b010e0c09060d1812020f030a0c110102120d0c02100902 75
    0x180d16040e1040c0340c0040c0d980f01d441b111710303100c079440b18401515480c0500300f01c032412070718001d1803503200c3c0c2e0981d01c02c5600034131958161089a40c1d2013000d1a0700c201583d4243d520398803854660301040680c44c1c00340681d03540c00902e074505207180340107ca0520b42c2440c07203181001010004100c1c0701188200c3c001d2100f540708241e0303c85603500c1511140c94062912003c00804001042c031406610642c4202100c2c401d85810751201c00080340c50780b146010f10380c1e0292003030000c80e020801c900f0103801d100300101d080700d10702511080041c1c000703119800100d40a500000e41007040010811005004003000005030009003484004801130380a1043c0d0740307001d5140400d41c840c0c80780d1150481030860b40c50951400c0d000804e400d10300e4000407a18528005031007500952005210000101e99071103440f507640c264481c031295035404040c000d07112003504502c603504411282c158083c0003020700f10420107000610b84c4500e400607082c80100484101100e01c1c4c00300740000350b11082c1c500340303084a01604041d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 471623983 1250 471622733 471622741
    0x40e0106110703020406080c15040b07411b06030c07020402250203060c09010f0e03010b030607030501091401031505040812040b040c05030a020d0605060d080f040f06090605030f 78
    0x1d86003007050350001c2e600c07a09080c00000e03801c0001c60007030100d0301d05803501008100e80c81c0c006e884a20962145c4007268604100500200d109400d0316510240c5149118503202611256002c003a0510407020401901c401842d040e80207042244029100d9101c0103200c071000400f000501c0c0e800003d000c8400c0500000b950750841d506c0b03504481600341140e0528041640340803030042305041d440422400b0744036900201d034107a40709030705031090701405a454202d4070445078000c59146440701d03071072505992148a242c503556402c0c0042031046030599000102076140c15860019a031040c0007040034015032100501c003041084603480c10400c03c5450116540d10350f45840c03d0f81e403042c02c1d40d10340200c10b05000e2004105c00f90100d280214010040300c00255143c1c0105903e070100b000000354400300540d8200c000801c03a03000268005801400300c0301152132510348509583c8004001c0d40050800203050001500c2a0074120141c659031910b04105410584081d040d844040c01502c0c182800d00000703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 471625233 1250 471623983 471624017
    0x182403010f0e0c0a05030708191502030a0e0705100801090213051e09010b0a1b02030c060d02031e09100209061c020c0d050903070e09010b12070311010203040e0106 72
    0x4861000c20307081d410000a40752111050316219114460340c440d1884100002d00c5103000507451040c0c541c0f81d00580044070702154058054009074004603050f000b02c120703100160307040c2d10155120b00b0400b1320120b40c4001c629a0304e0b060961a800062060340545d20809190f036100c800503054400003580181c0e0344010b8030703414410084d40c1e84210361108612005007841101466100c011fa1800d9070b101d0711030790b01d480f00c0007114001c40480400061103645a60f2400305c5000542000314000780c2590038445940010490a9000b0440b44812070380000a0015100c4041800c00c05800c1a120b40340050504c881c0c0240c54001303021550500c9178001c00e03c3ca5865a0724400c90b02441d000c0310b40b45000203041010038020390408202c0e0342080c015a0b0380602280c1c000c0c0200c640d40e40c03000b4003404525051901502c2c9a010251181ca020365071a810a0013a071a1107070200c0b2030500000081215610303600e0444940485148464110741061004018090004240c075056178220704010041e03081961075 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 471626483 1250 471625233 471625241
    0xf1903140c0d0302070e07140a0e0f03010606171509040f05120424211104120f050706031b200607030e011a0d0201030c090b07080918240301 62
    0x441d5a0001182c410402010340000b1036800312002c0404014040c2d442d01411b44250b1412290204080c90400c0b07000011403184030400d040c0300004140c1d105541561001c203084917040d030000700100c0e2545494114140e8544591039010302030407194000c01d5411400314003964800303403004040d421080409400c009003800303c00f4001001c0c0010303a032220b0740e031001005031000e20b2600700e40d4441501e5941c40c4240c45510844004951f007065964401c0744005418000d00c140440304281c03d0080c00042400d110400840342c1413802000c144000d0720045c140203044c4040390b40020705043c41c000e42c5000920f900640300c80000030b507061080c40150360b11110003c20320707503ea2072069400340c2d10810482a0301755200b09803c02c88500200a014603c0d00c1003249400641c5001d50302c030b050360780e1320300040d882600000d28080036441c0080c2002e980c3d4059034040d4024a40c1101c41101c041541a40c0741440c56500d4014543d90781c40d1065414140341d45a1078480204545e04032105d02d050054290b203003500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 471627733 1250 471626483 471626503
    0x4090c0b03040503031014030d050f0f0d09050601150801090c110604050d08011710050901021309020a03050703020723030906040e0f132d0804060305060f190314 71
    0x2400d180e403440e0a140042c0ca80d40122091034035640d48090215502c138442c0a40400144040c00503c41040941701c01e903999045040c008078a076204120080c00440d11102810031a01c0174034010408404500e401c41c200b040503003140d41481c0e41c5180110440303901003805411a00d41000000342c00c984c1c01000ca0f9030142c0003211006500c580c0301808100140010003001081456039024035a0340c89031f00560304413859502d031440560001c1c0c0c1c0c545540400780e11143e0849821000103184c00011041d00301d690700c03590f00140b00e1681c0803071640c8005400d0300802d03a101007149001c628004e15941d07074000800f01e2040c440100c01581108103850300d81003040314030540000781340c1911181e540140c8205030f0011904181c100c610200454000740b20325885030029a801710390080d0f008440035191542d42004000c0201e8804428070a03c04290240001c00c05040300e40d801044c0c88c54840180086910440301581c0510324941e400704a050810000c08140ca42c030556115424820070b01c51894451003076 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 471628983 1250 471627733 471627749
    0xa0620040b130902160318030b07020307031107030c09020711040203011206360804050901060801090c1103090d06090618020108090304060e010f030e0607031508070f030204090c 78
    0x18007040e0310352000c0262164000201e1000c02850b1240c0040c401c1e401284e801c01055850100d5030000240550301180c840a40b4000c1141c03880c0d41c9840302c0c40c0d404010b440b500c0142c3c10018108052650006080d507803081008020045a440c0d0340d51900c07840854818420786650220300c01d010408002281200d201004000755282c0d40c542c52042076001400030110344d528608500c405840d102c00c2c405d44c518224104004907140c80092200d5100031805074212a418020000403845030380300786001d40070700126940e685066045ca805231088031180c0e00500c05020b6610503034402c417000002100c01c03420702522010307030022841c903000307020f0500c20000600725804d24409612a2040c1c42089085078000d90354003846450300c00d501c9480e4400e81c000d950025200f41443d0f481035000d91442c51642d1814900010040d80d44c41c0d07030908001040d156600000c0d1108001d8008101140141d0050140600904100c03407506650355818170315840028019515003601d501884081495100145510 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 471630233 1250 471628983 471628987
    0xc040504060e010e0a0206070b07020a14100e150c09030a0203010e0609010b1507020d1a2a18042c031c060503030d09060204090e0c13050601020a0620 66
    0xd4a0010042d003401c503411440ea44c03034840100360119002950300c0d08a81c000c1c00c00d42c0742098035102d664104a000b88442d06600c1642d403640001482d0a0b5282c4000210310301816a00d84040c0204007610101660278180c0d50200c81242d5541c02c3c54480185c01c01c0420a8240c0d071004c550010a061022006005c0d5065281002c003060b040d0b800314119118100140c02000100c46100411490500d03100c046212580180050360040c20658000004103010700c243c52400c0100000200382003a0442d034401c00e800e10146980a011107041e803c0d54106100b9260724140074103c100d4490780400895001e22494844080040000300910200514080c032111003103030703040380c0f440e02c4d42e06e40c880c0c002d540b0300f002d00c03602e0303c802d60095209640a51301c0050255281c1070005807a90301030280000141c6110341c0c2004002081d580512440a0300b0789038074003034240d591a5100b000441d0080c021071100c0b4078180410032185a03804206618001e0340f1200019802c030524100500c4038003064182a050000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 471631483 1250 471630233 471630241
    0xa0b0c030d0e01060b0d0513140a03350411030303010602030406090603060b19170a0b011101091110030609050c0309010f060b180f03011d06010e01060c12020c0405 72
    0x4001440180e444150074001e010911102c20f00f00c030101c1c403c403040d61005200043c0030500c603800c425080554080c00c0189010f007615081d1110340ca0080b00215503100000d00420075410080540c0c6403d00c4004401412203030303444640e40c040170b5900341e030215500000002d00308003603c12215030000000e42200d8480da10391070041d540c0c0c1d1046c000e00020030460310000a241e446401380342c05540207180f00c0c0d42090b50340301c0004044460070b084007042c408401105108020041419481444407000115403021880000b40c804c032080c4020500c40d9050004c0f100c0400c629044051038170038280c0c1d01c19051603858008500402690300700c0c4180d80e0808040c1b000c8403040c08055400b8044550003040121498000c040c225010385c40380380140117044c0045800025180c0704140801c0000d0b00ba1825507507054002800c48802040c0d02d400c0401100e09031001440811681d409400105049200d9505003e400b07444c0780c8401074024880440e28a0f07492f0628400d006400c0900d80140051105d410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 471632733 1250 471631483 471631507
    0xf030408070b0c04050102030f0c0f010e06012105070e04241b030c09090c0e0603010e070e0a0e060d0309030b0f0702100b0603180c030a06092f0f0a0b 66
    0x300a500c20b072100c11020b030109920764082c404a4085071416001103290140341ba44442c55030b0002035542c28503000d0200c0c2d41301815428000d09002d004200007820096041503020920620810b4141c4240307001e4550000c0061400181c0809940182d8000600e640d940e02d012100c0f8801c111320300010000712a0511801a8207401c007401c0d503010340e9000c001c1203000100460803110b0400c81a00000d41d4660700704109500d0b680102c0c0244d00c036107440b02e803000994001c5a2103602c20b900c100500750501c0c04000240354010315209100b4801c60700300c0711640c80d00c1098059104d014060903c1420505000c40c100341c003c20a0b00e0085920076000c0c1001e18200c3c0800c5034005d0101d40c41009409070442e00b46a0098921540310010002014581980c9130001500e140c81040551000f0a01c00c404601c00310b50381c00c10034401c020784940c00200e0849480d2400b070b26160070f40312020300c0d4040c85103c0900b458200350001c10140c4415202209054800d8000500c030200650142440c140f0000c0d21441d130340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 471633983 1250 471632733 471632737
    0x41d0102070b0112020d061a280504021c0b01120f0516180e04020a1d04060f140103060b030c150901110d0f050c030d0507030c11010b06030a0e030f030408 68
    0x140504040d5146a1360740c20103119201c0c81c418000e41c0a81c01080c554002507850307005900040e00080111820380580021034070b501d54000904140a005206044500040b201a0380150100f076509504201e4030180e214244810b003210716000940720004c4210720792041e0282c00041904000501c0b4038001450074500a00040d10500350092404421090203070140c00a003504402100e2581085464024096042c000190080b0780c0f08080078000120040c60180e241c90380aa171101ca44060b041502d040b0007120741c8241541500703030034103603034042e6980d842c0952030450b904000c0105001071000c0009050080c01c09200d81d00102030940c100c8030311100c401801c0381c05400e0300c401d801c0036807443c500d41d03690f6101300c060400074841d5888121494401c40241007540c0c1254101d03420b100c1f181c3d801d8000c2d610100c0d0403c001a54402500c420300b0b5000602e8140304a240c0c0c000c12001e00c5c044042211444018a00207019844d42d03100a095582001200c550210a400f00c030740364203107841c10702c80076 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 471635233 1250 471633983 471633997
    0x50108161b0b07260a0c0c02100f08070311031308120702100608010612030e0d0f050c13020307021b030a0206031005090627130f06050a0f06140609041d0102 69
    0x144d00e88400400d00a40c0d682c0050b070007402c45201800c0340c0d94100c502c001901b20f40100354100022090f002c0d0042c0c8480b0200364000310a80c54241d051803100200a004d904000c18480070507081c680e03c009541d040c0030131640c10407003114052440303903a2420140d07958071404282c2102c10307280b0000c01041580c0400d0354224111804803d0029680e900d40c07040c00d9500c903024280600301103624200000c1e024400200e031101e005130074a140b01a80f41c6501c40d14080194082c2d07060380040a075001140340900321428a403100e00c40071402c600380020003c0d6100e05401200c24a0f02c01900019603981c0c0412847c00c0196000340507944c1c034a0102071000300300b800d51041502801c40900418414680300160f0100b202e4880001d0308124a145c50768943c829014210000f4000e081d640c85010032400c7e0f1841d04140e0044501207014100005400d045030f07005c01d5007918140c5400000e01c8081c00c0e0480c0722000c40740461703100d40c0b20290040014001e007030300040d51202440740041c041012406402070540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 471636483 1250 471635233 471635237
    0x509010501020c0f0f04092405070f1e120e01020d0c02011b05030a091e0c21020d230d0f0518040f09050d0509040510050108161b0b07 59
    0x1499a85900599584034403100e003070f41c0902c5516003850702e4241540100050700c4001c201050320b01c0c554689803001055148034480d44002d00101c41040202d600585400403513614008964918260001300700440a40082006540c1c0d000419009445980d0040b128501c3e03140422031f0f0402e4401d10341c000d5104145521449080107030f501c107414018801e000303000c2500030f072142c0a00345881c421603d07070307000805c87d00e1800d65038150031011420a4503080c254031015001c0001c1c1282504000e01003252941c03140100c40101c1d2400c2003030000f0b4104002c0d034594140c0d1038001c007504501e403140f00c0c05010f002001c102c4440c0c2a0414041c6000030f41d0320411942034a0750140c000c1211001c842c80d00c20044120801d11311014100c40742c3c10180d00c0b049011003848400075828160380e4980e400d00031040b5071000081c2c07021070001c890b841e0510965801103ca9081c5500240c5070100207400100c0003812601382000400c3d00020f2940075454039456052010b01c1c60314419180c0c80d1200a4040a90301080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 471637733 1250 471636483 471636499
    0x1413060216080d051b0a0803070305060901261c08100b182206260303010e0403080618040804061d0307140a0512010209010e03030a05030411210705 65
    0x140e05031006030716070554058201410800c815100c00b503500d03600000c26011480038021180c00c03001810b00c8401851485250007a41d00d00301180c00070f09580d000381c8112320903503501004100020040607005056007a00469213195030207248114141015600c4665015010480d050740165010051a00c03c0c02c203040f5003400e90362a2200f4515502500070034840ca00d51500c859900f074904455528048c1c00b690005908000ba4120303480b040d1285540302d481d000c0210440c1d01c0b017410440d01c928400b6461600214115890040901105c082c042c1020f0240301c451400b103502d5440d60218070783c03424a484200c440a050904d0b085000d82e019204240001c4c203016400024225204007850700d01000400400d61107013407440348405155028035281d07020440181c0003442e525a20031204a40c542a0001a140c18a500001d404960b090b83e07120310a410801c4034801254000b41a00e40080c2c2103142c000f05000ca82002c42d1050203d904403082540c1d005c0301c10b1422002c00203205042e1070080c3c07410b0f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 471638983 1250 471637733 471637753
    0x60f09030c1517010e041106040810060603180f02150f0a0c030905011d10030b030a0302011e05240301090605090a05011a0102070b0c0106030f0f0c0e19020a14130602 73
    0x1040f800c1c0280190f0400f07480c0308000c28003082d42421400407295004024526095030707a0300d9a81703490710126034182c4043e1504001c201254042c407070910510380c0031180340c03050b42083d921103c05000d400c078002d11034041c0350303101074007640c0503020b440140714082452a5503802030f000180050f95038a60031000100c0100012480707500c0313a6070a0b901c0460b18101090311142c24003c01400741c1218400c4d00c101541d6406418281c0c2c7d08014806d030140c0240c00000b404c205140342c913500c00c119040d480f0302440c00d2000388600040d0200000000c20310b010703130401d0200c0d01e010009001d46190080074140d44d0504091001c4040e002c0380040b1650300c00c000801c00017000445c2880c5101b030000b401c0740560803499040100c050b1035001850000004070001480c1522580d0705180c502201c10261060110740b182002001180b4070b104010300940c084944281c50030200c2e10300e09401c01d800c3d4000c2c841d0081544004140502c4140714122504840c4a445290a03c0c0c00d042410f8a07100d03903401449455507071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 471640233 1250 471638983 471639017
    0xb250c0f081f02030a140c0a12140105130209030624010c02100c030c0b0f014119170c15160206070b090303190213060f09030c15 57
    0x280b8241c180d6211000d05064a5070703400e070300a410080a0300c508a440d03a00e00021400c1980150384a4074140d11000e440751104100204060801c5a618083d03510344080446107820f42e07105a81184d00071a5201007840081c00358030040d001c0c043c0b6080c1c02d4071596090105c0d10720404501d0107e034514901e104020b10504004640510700900040e4002603111240d0105520509240c0c01c150f0103410150b0358405560768141e02c10004440d4880d10301e0100c0010301040905450350f4011461401e026031400c440407030751611615003a003a8030b0f01701c400d00204103110348500c40e45410303d04102031038449880e654900e0101c0d483e4281800ca6050180c900f00802a240503159a0288104000100d080400d844240c0140c035469002c242c0e80601c00340700707050002d030104101911a000000146807a81491f134805420f203000307444040d0b2654010b01084001c00c40007803665048543c98901000300200c1e002c5c0c20303260b4407060340020b880d5592240b00401d410170b1044901c5c40c5c1907055511000d0a000602c00f13 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 471641483 1250 471640233 471640243
    0xe010512040206090406080303011706010e1b0d0b06370e130219090833100506070c0315020c030304143a180b250c0f08 53
    0x403402000c4108007050150a00304040d10b07903c580030b0030010341a5103038404140396400c00d91100000031500f0744050a40d1340144803450040c62091401c1c0e15034103191103007062401072041005801e03080800c41c0400c4120369041840041405090b540e96540204101c1c0900000c082810000141400c541400d5a5140b0400e0380308420651320a00c0c140780c000c0811880703040341030031303005200d8003400000d441c64400c00c010345a00c241c64440440e200d00e00003940f400e1007000396400940d03608001d52070406081c05401c455038544000c10540b041d644001d01c1038410507494100c160000c102066a40420019800030000d480c01203034011045030000c0e44040507441a160354100742d4000780b0201d0005000b0010104402e440f2105031094404140400440361450002c07480020100e10b030500d00c051010310f82074425a0b1285820040ca8009954000700384002d0305c145540d03040c0001380e41c0d00900307401c1c07090340c81c80042520300300714240c03c0d00b00807150703030014040c09401e44400314001401c0d00c40015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 471642733 1250 471641483 471641497
    0x140702030901090e190906061a0705060f010b070803100305070b13050604050619030207150f18030504060e031c03050108120c0705010311090306042a210f051c0e0105 73
    0x4c45c0c3c264500c1400444406051041401c640282d00c602c4086040c0140f1180300c0042c05140c4040e60301e4801c94200035140105c00b82c060130000a80764018804204444121801241c00800c00b6030340b1b84550703640c24850300507580058850300881901041c810500c40080031400750807031140c1c590903124410040075100d603200e103a512101c1007005442c4410501c2901c0d190010a00700142007030310070b40b04c1c0c4c2c65854440c03100c4020741da86c42070010b80c4110700c1d00c640c0d504000c4e100c8600100424960b4050242d11170f5001d0740b4203001200d8020116550304102c4ca800006034007460700020211040c01402a01003802a070440b0300034206003011000e0750b8402e4842d0381c0036480040812038a0170005500a044807114032150000411506a00c1c3c2c40c200821070081d88035400c0724200b4a8280101c5140c11541c411001c5d03031000c0c400b000c112141800b1402ca1408011581d01070050300c072440c0c2030580c039211240c010900d025002000818030f068601d05042502c05460300b4030190b104000454203031203005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 471643983 1250 471642733 471642751
    0x130e1b0304031706120105040809100e060a0311120408070c081b12010e0102071a0912070828120507050403020612060303160506060a0b04060f0f030b061602120a0803040803060103140702030901090e 87
    0x1300207943b140d4401d0704a80034034003c01d254945422248803412508844c100d806940e0083c00050010030030048070404001091120050400300c01060000401c88000c00f0041d4400c46410b008000022400c0d40419202c1e5040b00c021941c4010307074540202d101100b147d04000c1400001c0010345c881c00003140e0800100c1c83c452086140c980c41d03a6406c1e800e504101e405580a00d80305500700f401d4070403107001801c441400d8554092000009450b8030540340300505084c1004002d000405c0140c880c1c005880c4624140c00003080550785503c040307032850003009104076040c41d02e020000c042c018042000c1d0301801d0181c070815801912481c80010700d01c140d200d040b000500d8138424508003889459810700141440c40e0210f1842404800280c0e20f400000c00d01454500b40c03c076080451810b0070000380550101005020842d03021746400907a4000100041c1070104c0000000300c8681c484d5101c151610340c0c42541c400c441c2400a03000b9a04c0e00b0110b10107000c01c1a8510114203411061610b81c17080801e4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 471645233 1250 471643983 471643987
    0x170702010c120917070506090606030c0a0504020c01110f0316030b010f08060a081f0b120601360c020c0405100b0d02130e1b0304031706120105040809100e06 69
    0x4504002c002d246804060304d84a50256a0741500c0200030003d2100c01d0080b00201311500f00041c8150030424003400c00c600c0303070f8014043d0390300c00d4890308007140484908490040c5c07070b003030341143c000e01400411080c070105100c0082d50515800d95500075600076117584480c2003141901300b00650481d5038110f003181c0420140c8450340d020728402c000345544407902404a03040e6a82c0d81c03080c186418098102d400402e104400700030900c2c4c4040c8148407800358100c915005c2514095019616400d06006200c0c00c1504250516010f2401480204000a5184142c09140c400201c00c5000b8021040c10100500a0130803800207031515002d4140030780c440c0141c0024403442c10701108003552001400408117a000d003c210040581d50140500a1000d00540700302c61504081d544070360007481c0700000601e0003d00901022a61094940006642d400c405498036155607001948220035082c5c540115070811080104004603540078002c2e404080e00c1d0a4500140e1200c00c0d1030413031114003520f810441c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 471646483 1250 471645233 471645257
    0x50d0201061d0408091305160c02060a03050c070804060e01031815021b070f1a030114010c0c090c200106050603060f0d050610030210031415190303170702010c 70
    0xc0310414a0f0402d104820241ca03184072a40400c01d009420740140405907500e804002d141440c04820050011051818000c040107650000f1402c0c05001c05410406070f0b98000500e420010400700e0b150903800a0005407542c0d62644000d01c46244500f03050f0003e810040031000003030000c084100016440049040340e0341694004070000e40204008142c40030202c1601c0107805070612440000e001d01d501404940c1c1d0801004080f0301000c409000c112810800041040318180c4c071328541852001d02c0e11403e501001c0c185110b501d080d5070000e940141c03900042507041904460100c6040350f06c0b02010142d65001007520b42201c40034415182c0140e002c2000941c1850f203078041c2040140700600001030400651074442c94000101d0b0015001c0001c01c00c103200754508895200010745071803809000b0050207590ba21050701d0007800340460007148076040805580d485042c4412080c082d0711000c101c1e030390303801c0c02003480f215800c40c81c81002204010944061060054031869405a194640207400c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 471647733 1250 471646483 471646529
    0xc050703050717250b0601080c04030303150308030c09030c0a05061e070602131706071704170307050405130204080a0201050c0a080301090b01030c0314060105071a010909050d020106 80
    0x10303c004100d00003400070480150b0850704c0324140500030719680410034540040345401d994005004c0c00300382c1844042d40410140712205021a0141c907490b00d0007190411503c0d04080b036200440d040141542004801c02500d1421400540944c3ca0210101c0c1d0491902c03c0500480d203003140560740c0c106008001d0290000b00d9004100e084181402055103410364644443d41281c10003200030a500740070f294100320300d04540c00c406a80068940290515040100015110721a0710b100c1300c561508190000b41884040f0050480c2c0d461600b14090341c900c0c05a0f0001d0059015006240c403480700a90345030102e2503544203540c241c4000d4801016090f525800550f0640c00c082560200740c8602c1035010300299940c4061402000742880102c0c2c0b00c1c409070000b4041d0b54810700480c0030103280104041354440403070051900802c00382001607030341000c1d08104501c3c0d801c0894401c4400178102c000518101243d1182c0d03c00c6003d402511601d95200d14228280c80d003e00c544580c0c184000d102041c0c0003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 471648983 1250 471647733 471647753
    0x31a0619030c06050a091e03050d050f070b06030a0203070801150b1306210207030305010e0f190c0905040e10060e07020705310501050a050d030518010c05100e010c0507030507 77
    0x17a0503414888010343c0d456514804150700c1c15140a00070415060400c1049400c002180003032290b4200300f0300f040d40d294507041c060701440c00c020301a1414038000c00d80b951428460b00e842c1d070b5000750030341c1d4007162618402800f030000102c002d41c42c188130396000500401b884082e20303030b038905540400c004146410000c5030101900400d54038441449000300010300001d20040c80c050740719071008259503140c203050070300480c3e00030304a5201c2d190940800034400201422850511110007000800800041080b10004859003002c1d03005841c1c00d07000c241540d00000c160807040c01100c400c3c480d043d01e405850700300460580350580540d22622007803240e4a041000580040030510302030902c1101d0010809281c52601510782c0d40b00e40d5107005000c14207181c400b42016040036500c210340300b400b41c0c1c1d00420501c01d203a6240744a01502c0304540c82684600c2960603099001400c80d90410000d1503980000c0408007140da5240d13180c8101d01c042d990085e825103500c1d903090f4540b142042c1c40e9440b070360f950f4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 471650233 1250 471648983 471648997
    0xc011407080c1e030c0c19050915010305131109041103010903050301031b0510050a170114040c0f0f03090c05030a0515070e06032d07020d0909181209031a0619030c0605 74
    0x1200051021235941c03101001076100e0a046030f4061100d501080c009012a400039042d06000346000f444900420b003544040614140156000302003582c59041950403000071180303641c2d055080c0381d0840185035004003c4d5058078042c0500c0c0d50034421054030744c0003640042c0b090a40144880c41011482d6010340084c082c4d29105052a0a0038142c0180d10062800240c10402c025020f80c2d00c55491401c00303108264a509040c2401078500d1207401c0c0c050004403115012004150b00c3c1d043c104204a4294118002040090221420b03400a40f030050789900d1281414050b158402c0000740300303540700c3c2e2011a49040003404d40d40c40d540703a107550f00b8503020052100080400d500c00c00e004120b95400a1248250401e5002c1c0000c008003d200038404c0c1003503400303060805d00705181c02000c1d02808481c1c00c7c5156020004110710207002070151400d032603c0d40050000c0210b01154400404070004451082d10100c1c2c044000c1054400c040c510309010380405058086045000e00207030340100000c10780 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 471651483 1250 471650233 471650269
    0xb1008090a0c06210903021b010c0c030506250e04050901090b070207170708030f130b030c19020a03120203060307050901030f060606050c0c011407080c1e030c0c 71
    0x1150700036100c03940310100e140d00c6180001e0010a61144004401402484078880c660080c4800e80c1d6540300299121b040744891000d915100000c118143c0c01030581304030040c0e01021050700c10741c1c0c038104503845010499642c214041a60104151400c0c404a050f5031880c89458809507d40d1080074000100001807400701c00c1d40d61041e40c200481d006051031486192140c2c018200103090403c0362500c24056101e500140c0d100f52401d02642801000b5110700118030380d01d1903190826032010745942d14007680203140f89040041840020041c040003811034905254404200308000c00040f40c0d1503910f03e0001e0300080d03009000300d0701040160000c42c0c014200808940e040c6031180c0000e80c7e45c243c20f0b0300c100c5240c1e0340c92031050200055400b89000500c00d0382441070801207a420619114950141d030103042040c5401c3d100034072981003043d264290342101070340b5101d81c0d40d20041c1f5a14070b0030740c0c0f188a4082518420340b4180c94000201c4032800007071400b07000304c0e003050700a001c0010ba0703000d40f1100b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 471652733 1250 471651483 471651493
    0xf0e040305070b0a06050f0d050a12031e020a09170307030e0a0807090506040c0c030807050a05040902160203010b0f13051509070c1a010e010311152b0b100809 70
    0x45401c581c42c2c2d44c00780c403140100050305c3e4900b00401443c0030011416034043c03580e071080540401c20200c1c1c0c140e90180c101a0b8401102400034040b0000d01d100900d044660700c50400041e83d201d20395020300103004203a1500b0720015120001034080060303480d40b0601a0b0300c10415800024442c915080e25180040c006902142c0c64a0409017803a62720b4105a44d0181d0791000c12415144c180980140318055003421000d00e141d0703031001000d0502c01031101d000c0c82800581c013000300b48903104070340c000d0610740c40c03c6403a07100580f04040349074048401039110b907091240d0032203540f600c1c102e1000141001030610f0001046114080080c04009241c080403071185041c0d0700a41d00d40d800e4071440780149603200400c0180d08e01d003111110b042007004506030b40c9580c006020032a4841c4005041d00d41100ca44081c202c40c030000a00c24050302c2c86d20105519001c9a042c00030170280c02144403140841c0710311000b0421403002c03102204c0c00342c2c0349280e004d54040140c18a960092213215005840384080d15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 471653983 1250 471652733 471652747
    0x30b0d02030708031e0f070b0712050c09040c0809062a031315060503370506010602010b0409051506060d0e060109060501050901120b01050c060a0e060c040f0e040305 73
    0xa090102e294460300d0940c10010306540c071801c04254121458103205446814400301d4004e011080c002c1c070800814003161040804c60a41c080c5134800d200c0c071071404052101c0d1a01410328881a0044207202e4000d40c100001020000c3c05049210b200d010503a0050400b6600c48004901c01444000404c54034000d0345481541f00240a000b03601c104a1a0b54240d040c070b0303551400d40b02009110080210651410809000350b50b808150816030362451a1001800b04d440c42c1021103104c25484801c0100c10b089410004008011602c141201c1c0d40d50001c201341c0c4500c500348000c0c0c60441c40f000b80543c0140340c0440380c2903078000c519500300c00091308003410680348486620445455130030624082d40510010405070030b5034050040580380030720300b49081800e03d6001038400300d1841d02d0818500d85401b4440b0300d0380d00c00c60070f480120700680b044500d5070405044000090007a0605904503005800000310062070000c07c170f8045809111a000d0004d29101c007010407840082d00c11010003030704012071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 471655233 1250 471653983 471653989
    0x5090f0f040f0204080c1f2309031005040302070801060305060103201203041e050d30030f0608030a080106050c011b0816180b0d020c01062702040b0a030b0d02 70
    0x10b88094992540200540c1c43e410381000501300e80d108201e0143c18041e010602004e6009411411201c1144031048841600780300c4110300c9d0203500d4485401d0b101d00004060040e003c0d8214900450094017918030740c50300d40049030300781c0e421800068841e130302803801040000d010310049603140c4c0100051031407501c10180000c0c040b4441c2c20001403154004181800703030b070300f40c81d40c5c0d10765009840c800100c0c00c62030b05c0c0120b400461500e8015010500800d00280c1d51007040364840480784410603100d00c201c6c01c403032000c0e0040441d0306a60400d50300d011808102801c00000321180c12881d80c940d0031080e8a4690103c640d0f503c59400840745540ba5010b080f00a40c84440110641003562140f4130145840482c0300381c001046203a000800c140106c281d0620302542c0905019180092034403643c80c8106090080030340f0030391000d40142d618103880000c4840d403040a107031000001d1440d071054641000c103400300fa0300039400b80884100080100c42d04950280d032000804400182c00e9a8500101d5000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 471656483 1250 471655233 471655237
    0xb330a0e0907091b09030318090507120518120d0603050613120e01120c0512010e0403080a050c120613050f15030109080409050621030702010e0105090f0f040f02 71
    0x3000300c1c0d036000d05001d11048801d07028045200500070441242a105044000d040001a01c0003405201c030318002820868200b0007080c014110403507050066040415000300751540411500041d91f10b01004a1182e60150018400e405c01ea0030007480c0f054800e11460500e5440444108015680c1701e030300000040303003400220301c9091800b1907070000180e6801e2001040e6a0030380d01601f005007402400b407090780c000c0c0b1292041042c3e81000a030800e480d8005035514802d00c0003400314184410300010381800c201401e20311643c80b80d0b5034203001c0c1c0c0300c20300c0c00c2080d1402a83c1c20660340c10180700c0680a81c010040059004800501c020074911884404400702d070b0058411081010140e41007050645859001d0302c90080d013a4000c112099154403031940501460065240294651002c02c8155654000d00d0101c140c004506288202008010f6031f074a0740056000c0f80414000313407000030598020400c0c1c0c1c1124001402c80190b03068540308015004580c0006564030603500e00b28200ca5a4140c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 471657733 1250 471656483 471656491
    0xd050c040e100513060b1008070503071b1103011b091202040f090f050606190e18030c010c090b04350d170603010228090506070503070b330a0e 63
    0x603408000000905001068401d00080c2500481c687c5510b041e525520550340399201030f040c07514503141d4070b51310421540321041040000c05410300e0301c0c840b42404542d06140c5c17000c1030214003c00505c442030070b800a020f12480602004240401800c01048809420310504284014400218071690030042e07030480d800c000301030b100720800c800540c04210041103840d4003d602251342c40306601e01040809201d100034016100d1064409020942c1d00803000c01c12001c10000d101600e85a043c0b0400d81402007400130900e0340007882c451800240c00180e18102c0b000d40b11083c1d640c01034820f114502c84134111030008103240000d20704c030303044420503810322120540c5503140d030311a2000f5207040d81451041e000580388910903481001080c1d100040325503d50039240c00035100b0800c00134150800d4a50720803c0e408940c1014000608200b0030001200812410b4400c04020503141c4881000000c004c1c0050081d0500c4440048410900045004000d00342200102001c0d5920340315110400d20810580b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 471658983 1250 471657733 471657751
    0x4120615030f061a0d020d0521070b01050f060f071704090605041d03070f080403020915030f0c13021c02041d090a02010206040803060315010605180d050c040e1005 72
    0x41c100c2c1c4200003042c011040810104914280010f12800000b4203014400700300900c181c410240400400105020428040750f66407009410700390600e904440690081c4001c55641804000105062501c0c200310305c0d948001070400c40c108810070b0303411450b543c8080c1c1e041c1c495840900304245048440f40083c0040c010310400804e2141c501400c0c00b056601001c524400742845802c2c48a190100000b070f030b050650094a6524401e1a508214825109540020b90004086420010003821815000e6602e0405800b1079460100c102421a12040440300c2194049250f42009413000c950b600a04510640d0f040d007215080640e810800407030780940d10602c6040910150b2031042d002850707403280e100c0e2034000a441c2148032580001d44400c80100014500350b80071020600b01e40781000910101c2c00440703400d001c1941c6400c00640660800d0864000c002c00d4050848542c0c24410a40e0700300355444401020034038485800c200103041d1100705070b0f086101c0d000c2e1074851528140075580c0105189 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 471660233 1250 471658983 471659003
    0xc030f0f060f090b13180503030c0a09051f0305220f17190c0f02030f0f061b040e06030a081314060304023d12060f08030412061503 58
    0x1c04082c2403000c5295000e01d51440c039100083d40580c8955000704400918070100113a0300f8009540c00341c0f8641070440181c9984404001c00c4500c2c01c005d00100b0608030a5100c0810040c1d583d8100034000c1d0b501030300381c040e040e0b5100780002d0b014003a40100e5005662219511800510b040180d0910803003000140ca424408403240c400340700b21103101401d0f20f4824014249800c50030303a510b0102c0d1003502da034a01004140e8400c0424000c0387c03400740041603030050603101036803e90090306d980c58407a01c840c0000c2e8080d14020520001038032010300d070941c4080fa600741c00e06140c4245002e007518020700d06034045c020440b5075800144075500501080204141104203603003041c2c1c800880042011540b40200c02c10000d1101503a58000c4480c1d40403001d0640400b00702c1070a483e441e40c031640d907043c0030300c0c4092000d54500054200300c0b8030b041103c0042003040101d0741c501c1e8031744a2400c280301d4281190410072042c40005810826218110301a54000c00c21a60366403280e0029030035544141d45219407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 471661483 1250 471660233 471660239
    0x20f03010e0a0503120a150e060a0b040b031e0601090302040e0309150409050a090209131506171c1b03210509010b0307050310020705010f0203040b06100212030a0c030f0f06 76
    0x11009817203401c0200f50a00304680e031110718030b640b030180c21070040d02c0b000501000090000c0d603441d40000e005d4519099629142e1784c5d100400006034200740c848030250810701c041d07030034040c4880a50328801c1c0c005a4894551500d1502440300400c03680c110030f4500c1c002000700c0901c86d06d90650f03083c0ca1a0640d0b684680d01e40c6403038070b500200c80d03014000890003404c0c00800d00142c0c0d81c5041142e0001c100c4840b082c0604c6452030250148041803920305826402c1440c00681030007034034101c251b500035039000d03141070361070300103048111b20b601140c1c41d4041000d03003d0011032200707141800d19040b4840d04040d040d070215101c80307100294205054401c0d054981041041c661070030702541051440580040802d1750502000035202c00c2c622904080483e4042440018041c09410156484840040866480c10682403039001d601b8100d90a80c00b0307902c2e82d150307201301a2000a0410ba00300c0f00054003401d40c0c50305098031028011030803408080603211602c0000e052810300c21508940e1400701c000803210701e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 471662733 1250 471661483 471661507
    0x20f01110a170702031b012009030c01180324140613020315040c020102220e0f0903120c0712080406231902070b0a020d0b0a080a020f03010e0a0503 65
    0xd03500e54082d2510482c9001e0100154001099417484403241c14415600d012055076a801801d094107185101200c0c6184082c500000c403005080354072007901951011072900340199500079116052003031002c00030f101040811500f0000c1e0250b624254240100a00710340007850a031803842c01d0750707801c4d090b910044c4126481c0c044086401c4c0c6040e00025419483c01242950640c05c0300700009000d1078940209594240c030070760444003a0b080141803103400c010400f03580c2164481c0c1d070056075182c020b000c0204001d000340103482440345402100451800745803610342300a00d20041c1818260781400d00c4903c0000720009840c2e003201e04681d980300058a410f003040c3c8180d82c2c500d5044490301c18a0304400038905101c0f080d0342e9201545020300c0001d0420102c41d00300034818800080c00c40c08800092010111403034005142d5100083c82c140500c281440c10010780410364071500c0c0c030300d0344481042001400c007a00072021154000b00001913108000d03000904244120b0030488554000085200d4040c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 471663983 1250 471662733 471662747
    0x302060f03060102010b0f3a052a1012092102120a0c02010c0f330b0f12010e030301060f080108010606020601030308040503040506040303030606030b180115020f01110a 74
    0x1050885c2c01c800d00e41f91910100c3c1e06041440080c40308444031503104140c0c4400308002103c82446952040d0b044034190600940b1144410b500c0201d4060b620b2200075284000b00c6010095000245111004040410244c80484407141001c00b140d440303110f54808206906816201c0d001c80d2103500640b24200c10009040c40b1820260b2016841c060200c00d400d554040a40c902186c3c1c2800c08003081c0009003000b10000520140080c051010346107003154a401e840f40404040e15189000d400c61100009801c0c00c0d9401a050950485000d50050f005031a004050912406000000160350110111454210b91090b0040c0f0003160202b102040c02d10b603c40245c900504207a0700811100e0b0506100940703810341840007a04008440021a05001061045500801c4010241c80c2d03201d40e2803501801408151080d040440d28000c806481401d0604085062420390f005201c46a82000c08a06100d441040f000046111742194284400e400748107080d0741004110415071184c00c0313140014055 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 471665233 1250 471663983 471664001
    0x1510030f0f0201120905100b010c0606090e070f031728180504050f04030f05130e0601031a0d120314010b0903010606050f030c0a0c23010f020c1903090302060f0306010201 75
    0x30740d1802c090480855000b00d101d14007407101040c02304140c0341c0303040100d1f22004080d0f400b402041c0781030340014810410703500c003080c40404070080e03e501903070710302d204200420f0b0381c84090842004502d030350980d0150540180f41c03043c02c00622584882c1c044e801911496640c1d1203280c0480d4a26900721504045c00821034001c1404850520143c030b000d0f60782d0350080901400040500c5a249510403801d4095010b56600030210900c824000da50340e003608480781c9090304c480780070914280381d03100f102031200c040810f8403030007502c0f00401f201d0a680e11000d1031031182000080550750b15505100844410740d0f01e000304031032807009490b850300c1010142124141d42c000f000740130080111828140582050703079404071500c14150344407202c0341019244402290030083c04115a003a490798004400c40d110000100100002c00004017068440c034100c3c4180c0b0500c2410f94803104d000d030000c3c881c80d407500100a120f454902c101555a5010034040c1e08100b0441c502250302204100c41560309210312040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 471666483 1250 471665233 471665267
    0x3010605030f070e0a020c0d0905130c0e12011b0c1101020a0c170c090108030304060b1905090a020421030e09010e0a18053009031510030f0f0201 64
    0x104158190700b682d0f8031007142c400e2402d0070840d000020f0000d2003076130684898401c040c081d1080e59440d403500400c09210340c0103840c41100400905002e0814511404903a50207684800300d05042503401c205516180351b4258000e9920703411034030307441d803a103001d4600e8000a42c1c42d03617142c400b102d01e0100da0500e05866201d04640c4402c9608000c58441000c0404440030030804840441c000c080a50400100c1c4c900f05400400400000078a108000020351045028520400448824804000d0254001040e0340186c4030603100c2131140307180050429803c00c410000052401c2c0e40c580314440344000e01d480c40300105803940f452000b4550032002c200640c900c100d90000d8158184080c4030130f00384002d842546075559072103281d11200c44840c02e04071159003050403911040c0c801c01c0b44c40300c490311065000190200169224030260030f400c0a0780d8001c40000c026051042d85887c003080b0201000300810105c501109000011a442c010407114090050f00328000c20704807070001600c40c05011800b081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 471667733 1250 471666483 471666493
    0x1009020a080105040803010510030b0405100501080603010506131d06090c090a06050904030e01020309150d0f02030126070b0d0203010611031908100915060206011508070e0616050106050301060503 86
    0x40d2600c41100e0540303104271030191840500b024224002c1150900040d0802e180005109450301c0007040c1c038048900980c0c2e1b81c080399590070103260988006035841034002c01c034040420340145040d00300e081248440103d5055034000d403d03656161040c2a20b490700250004061005541044040c40d07038480c2006109005140c81c11001c50f0303154100410140400141e00e41024107a8070070f00c11110450380007081040700901844090b09a98882c240c220f018601c0e000031010440002d00a40303040312452481b000c0c4038951410034404980c840c5c40c07815424040c2c07020115101e01e005000e007045910000c001030320f942c10200050060b944240a0001550062040400a0b00034039041104c2e030b0000c2ca011650740d2100562454400c400341c100340d10081c105802c210911100841103c00c03591030340d08464603640d0311030202000d10143c030640c0000070507242c006400da03400740301c0c09042e100d0042c0c242850700034030701c20140d144507081000f107450383d441d600100820300d401d0203580080c00e41140904 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 471668983 1250 471667733 471667741
    0x1206040b06090a02070605070f0e01020c2b051e0714100f14160c09020307050409050402011e11160815181222030213051302031009020a080105 63
    0x3101040185500c0c841d00741140066108119501981e0300f950340001c09008900341142c0c081c1002da911406240091450b00030f0003402d43c40080c24500361400a04029021318404808214000b51050b455540154214061b8001401000b05852024407038403110000c04c003441d040c90902d07503683c4c885054541c1c200b04c031003a141c2c1ca2010000b400c1465050241d101507c40e001611103050f44040d0101c1c0b50700104101d00d0000c00c404000242a20030384191010545544002d01240002d640c2a0000741d030600007030080200a074407440e041030050403c0c004600c0070551261081601d0303e420000102c0c69842a1041d200030001a000307070740300c00002c58605090030103160359184a0106020101718120120708646000d241300101118070000395014551484406002c07940000d14121045120b03c0380c48104080281c03039141640c2c1e000340f01084000d1403481d07400140001404121406ca1504240c80041c1d80402c003090f58096401c001040443d040d004004800d0714691000e403160f41018100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 471670233 1250 471668983 471668993
    0x6120c0f0509160e12190201140a090b070302120d0914060c090d1b03031e02190f051504050c030c0d02090103021c1202030d050915010b090613090209120604 69
    0x26005444c1c508181119421307800175171844c81c626690969402003014082d90014081c00d003110117030007030302d07801c9495041081c440c0c50391040b455100005000c0302d00c207101083c009070040001e940244110340008004040e084160b9001c94080000c0769a40e020f01c0c82044410183c406440a0010150986241041d0403248910a441d4070600c40c1103841c41d000304022007211001c500100365402c04038515103e00d8042c194054444016054801501c10300b1f80481c4005a620305403080200400d10592607585c0b0100b004410312000c4510f070003003804649d01002094007040c0310710300640061030050741c02014142044e218450b080c1c000c005881051003da101c80101034112581540c0429280195601610001209140040c1482000480c00040580c00030241030090400701c000c1046403528a1110307618502c040050081d00920340c010410f80c03d10a002e001e01403c040d03e41450540039141d1580c2061294100400b825408290b502860030f016107403040142003c801842b031070400e80c80c0e07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 471671483 1250 471670233 471670261
    0x90325030c06110c0a05010e16030c12030e0607050d03050105010207140d0302011e090309141f0e0402040902181206040b0c0904180512040f120606120c0f0509 70
    0x40540752584580c0443d412201600c00c50314a80805401e40e22040d01c2890040d0181c0341c1c0c00d400365407501c00c0e1096288010340707007040002102e510500000c0544d107031081c501c0c0c07039241848098052210300c01c2c04c0b41440d100c680003020792074401c070040c0083e81180c40000d401c0f10b8040e00468115801b4010601c0b800d41700c1c0c244015160400c0701c0c0d80580e0500c9280803405040351002c5403540840ba003516000c10a070642007003004c10f100c0c1e29801002c075100d00303000d201040b86141d200d500c0390700031515000501d181c442e0303000c4100d51440e03d8181141144042002d80c0d107d0f80c441e04084da400250500411810716860311000303011a40001184510180580d82e004003410181441a03018085450319101c0c200312050084007410500120344140c0030302064942400059510b402000902c6480400d2032040300d0a0b1a0f03848040c3d440c4a09011580d120b000340158103c0d880342d640d505c00704541005610075501c0910a1003d02640d9040090f1000000c0151380900c5c052805a002e00103681b04c1140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 471672733 1250 471671483 471671507
    0xa06050a031d0a0f140106030320030316051305060310030507140f2209060606020d11102c16120201080606030406180303020d14060a0b1e0309032503 66
    0x1411800e840c031307509120100344d90017924200329610382000001019000b00590300301c1018032a45501c4440211030aa0b00c82c0b00440300700c80321202e81910851494091005403819500400c01084003503261800728085034007c0c0d501000355119010200708000c0100003090283c881c0580d90240c006111020800c04c41020311005e1141c2c100080c0c4462008107407032060200c806003107003481444280e08001c402401c49024020050151009400c200b42c010748840c209001d402c001040da10030071050120060507074003c8403c0346140c02070041c149401c07081d5120418204040a0034580501c0d2458042c8048250711810640568141c0d41c4003503070300b10329525800f00040d07804a60343c0d030f02c0f454443c2c0204031407880880c2c80c030001c05405040c91b80c558082d0660201a42080140c10185405031900040444002d40d00800f454820300c0318005a401500315100c2c039a09007103808200044155854000700d824413141c3d80085011384218170990548a130030b0581030004c3c0e400840c0d51710014103040480d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 471673983 1250 471672733 471672743
    0xb10020a02031903170103123c0c020d0506011508070503040605060103110d060f12110d03031d060402030606091e0903130612050f191a0a06050a031d0a 67
    0x4041042450701401410a45d40d441000e06001036841e86029036100422281c400e0001d002c000541c01040300d045440c000310640102024003240003071102080d2199103020b0303441003180e442c0d480401a181c100751010a18801e41c007619244d030410400c801081c00c1070030841e080141510a00c50102d402c58201ca400036003100c07020407680e44d0318005a003d00800011000e1b0b4078000601a12a4080e5038060303026910184a00c0095590342c01542c5400da10050010b445642d11800840e038070301d018010510954820b09012030311210119501c460091640e8103e06950821006c202c00c518017401010340c82101151035207041e0a01c0d120b005005c2c50003503040c000607c011808250b4a030020010348400302c040d2004540b03550f886100041194207170350740482c00c3d6070401000c1800240620030707071442513200c6010009908a89a00b00021300300c0c264024602001031489100c4507160000c200001d0b107230940358035944103100390b001001c850503c10511141014500018685580450000d10743c49d000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 471675233 1250 471673983 471674023
    0x703150c030209062d0c011d011104050d0606050d0b0a0605010302030408091908010e030c0106290d0b190e0a0501030507050111070b0a200c1305090a0f03030b10020a0203 75
    0xb41c5032036610305d00a00706045005c00041036814440d6070540104c40385103d0802651140007503881010b09031a01c07031403541403000003400140140d04114581ca800c250042d1404144159140081001d4082c5400240c81d4007401d02c0400c1100d20490003050020300c800c0c82c0031031840c0381c2900c2e44c5203607005209899205200481034442d103500d034504160068034805000708020020040100c1c2d4940c403500c8014215420325000007945040c00013000c0c6d00b0b20071170110f005244c1c1c0440c0200b0190744100703400d035250350361801801025101d200c4401e2030000b08607410000513003013440c846004040245511100c034200001440003943c0460a482194802c0c2010b021654034a182e65041c200c644e002000c0c44000817648006895100c1410b206140084a440140b6119515600c0d110301030ba10080340c2040c0c85804090000700d4541c805a404104141038450b02d02540c1e07122010a201e8100c01d4001944503281260700c0d18280200000401c110300052004011541c042030700c5d03541c0c10b80701c40c08100f0030b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 471676483 1250 471675233 471675277
    0xc01120b03030c010f05070201180c06051c110702012a060506031509010605010e0a0605180117070824010e0405041109010b07121403180f0703150c03020906 69
    0x410640d400c5105200080c031170729410259100040100300d444500541c20401910800500198140c0c0d03240c0c1c00c0031601081e02d04120b403d6a191713025002c8401e4001d0550b28006c4025864407514060070700d8100c03855604c15031030000410604400d403d4800c03240024132605651881103103a02200c690096010400341e88e460f0010307080404918003102e2420304803041102d040c0040d800001a104262110321002d841c02050120b60f05040c0151004113004200a004402c00340415031904001494001c81604400781010710844040d50307840b002c1802d5509105084100f03002c003220808401d0085e405020034600000c1c290151440518012946c85000c2014051380390300c01040000301500d081c0301940d585480c48007e84c81184150380444040c0001c02e582d0344120301003407407015a00c5100341551640d900300c4071900c00c01009213a0510580300c0c982c0c004242803003403d00035401822203064520340e03188c040c8141c860000007003082600c1041003842684d9200b0503594a4540c0003903180502c01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 471677733 1250 471676483 471676489
    0xf0305010f05060711030309220c02060c0a0c0f141006060e060a052101060f0e03030a0c0212100c0f02010f020340140d0c030f030c0210022a0c01120b 66
    0x448c40301c100790013001b04204d61384800001001e49422409000041208001046080380c03900001c4c0c1d1548500702040000640b11403250405409450060184507442c40196a54541010510b1200c100031b4012820701c1f402c09071a4460381c40100841d040c030791f18600c19800050141d104410a8806000c801b158030981c007910042c0601d050031891001000390f50310381e0000741c00314400071909400100640c1c024269400c011090f5000c5250689646401c0b69050f42000303424601d4000624861159485c801520840f03401548400109a181c0e807044039a561002429190100d0411385070500410a1010100803090f050340441e01140681d410061071580e00b4480790003038400306c600401c43c0302d102e0090003400b0713030f02071422241081215580f00e480003040d1a540e644240c040c0c00f00d002005040442030183e082002401413a106035040c1213110380441049800100d9000064501c40b516040d02c044849204480701030220001c01c0e5600856000174013595500446440301038441d80c084c032040d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 471678983 1250 471677733 471677737
    0xf080106030c0e03030a02160f050a03030509011701140f012d0c1202010c110f0601060f030b1e03280201140c060a050a051e13110a060f0305010f050607110303 70
    0x3e10000d0030750b544e5000042c4020b58404071191800350114801c0c90000d41006d00c1c0107840c0c12580003910749054585551015a225008540c3d19410300c800362450403c00401002c5c8280a00303007140c2c1c00320000030248107002103c112604000d042c0300f001581d51500c600344502e40c82400707003101003150400b0003001c02100c500114690052000c0524504014a55019000275203100366507905d0040d225070004941c4d0769a400c40400c18000d1f04040014080503101d480f50054103482400e0110b201c00010010921440104c0c01803082d00c510884810350030700e010320070441d07020030b56140e0381ca40c1d91241c000030120440381c85000741131060250f800b4808418660a807500b80c21014103842c1030780303010010070b8041c240480d0a02c1c602c621f41400580b882a28001c6603612a00b6030f80041c04c103503140b600f601c428011000d0b00350360105000c00081c04517a10070704c0f0350300644099615003d03141c40545010703003592011380068000f420030110612a607241d01d0281d4104a8110705500001c49030100424114 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 471680233 1250 471678983 471679007
    0x21b041d070303050408010f060e0601030504140703050705040f0624021515030d18180b0607050d021c0e130609020d06030308010909020a26010c03090605070f080106030c 75
    0x81d0060320400000d16800c100500111000384000b8805e05000190300400c075420b902071080c1084101000c0344155100358070480e80544078290a14140a40420483c41c08411303910480d03442c1d01509041c8614103280c0200011801d8400c2c00380441c6061012510310078090b5120841051803501000300020301c03c101c01c2c910b000345c42d601140c450600d8261501001020340600e4040c1c032408107004540c510030300c0030002c91210026074035481400c056030410036410071500c600515071990700641550f81c078036004000c4207114030003e140d081e1207640040e0070302d08444110b04410b250355905082a54008001000c441420ac40000c0d0b5100d01403055001015280c10452079184045041d8141580300e9004206590107038640c055140e0380d4240200a45002c800d0094009140c00805c01000040074000c103900d4801c0140c00360007003902c1e0100da0846415443c0500029110402882403168034825250010307035500c0e015810818a000103006030406200b000c00b090354642c180c5100600c50110750090b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 471681483 1250 471680233 471680291
    0x4060e0919060b060a090e06090106020619061d180a05031206010c0507030c05030111190e010521060406140d1b050303030f07031107050a0602091c0c030b07021b04 72
    0x46400e0140020b20840c05402110700804480300805c0849ca0001d811078102c0314603a0040245503940c403030036030b00b8419441c1503005040c0c54041c0440d2030710b0498200c102d00b20054001201c185040040c0360042030368500e030607240b0741000d500100454070100071103c6402030105d05030303256200c6500480340d01082c1003000c1d199000d03c16020041268041d09182210b508170000c3c44100c4914105001901c40d101c0c40251000d043c242c1090320301d0298011048a08050401c24103000c154002001071642242202c40b8814000003000703100d103014810750005d400ca03a480f0111508680002c114015164003000e4103040c0d011031801d00c4014203001110203008082c003a00d440b814a1068110785620503101a00400c1c10480c0a602c5081ca6005445400c1e402c0740052003c0c04145c0c035a403009510407100d041c0c01c1000b00303211511080048024180446c454282c03220082d05d182032010105001500c034008640140e00d911030b040a0350508400038a808807000103220701c1c02e180b2121824440d22200f94 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 471682733 1250 471681483 471681487
    0x6010905040c020a06230f04170310050a0b070305030f2503090b06030609031c020d02041415430c03030825120e0f0a0204060e0919060b06 61
    0x81d095002c44c0003103e152182c1710611100070240900550300002d0421280f070424910700249883c09450012a0030030300400001000120742c41201d2115030040351164910b02c40c1d50820072085c18070281d8070b0010080d05412509011752030f54001d0080c0301c003034051030824100c40c011a43c020005c80e400800980044030000d2241a0204040c0c041c0c240b803801504c1410300807000035158240400c09903c20a44000558075001d02d8500700300d150b10030403a00d5114a6800d0100034003600c01c5100910141a40c03141d1020140c15440c1005905a00300d18410a003003802d101c11810226181e81d02d44201e8101d0800c05e413130102c44040340700009502203040c081c5e0f100402112090100c001c003603000b96802643c0c0d0290039640c6007807100400380d000c1c40c0f040b020801100401c1c540d91083c420003040403200f031008030300250048002842e00507408030405154211000c410114a003601c1844014011480b903c4800d18103c415103840300b0015855131540001010000100000360f40580500203008060b6a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 471683983 1250 471682733 471682751
    0xe04110909160b0a02120d14010b121605030114010c050d030b031e19021809010c121505010c05160305071502010902030d1b050303160207050a030506010b030601090504 74
    0x3940d111a101c60310340b01c54a5141d404116007640d0400c841c074148040d00100843c0c0c810305094071850340466070b110103032940c4200060300c1014944555008041c11002142c03035540740c4d50100500300000d03005900e454203e03d024088150401c003540e04546030440b41a00c060807a0700180e42c40c0522401c0200980290869400001c0d0140d11401450009404440b8920508100d00e40c1225a00c0350042051780004106582001c0d2904c200801500c060200c15040180304422102910203503121000c40c0d465a0013840c0240d8445900c0310400ca981c44180301002030320031111414401c501030365040200303221074442489800c01040c06800300014060000350382d2030030710a40310f4100e4058025120201c0500d500c08520500031117141c20f4009004d0300c04103a407034400340d800703403800c541e0825031055500048002c10010700145106181d280c40140c400c07142940c009007461043c1c2c01c01071064100180501c045000040d0560565400c82c22080c0c1d603403541c0005a8002005a104d55805804e1207288 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 471685233 1250 471683983 471684001
    0x70602040b0301030309060906020604061802040f0c021b0a0302040c021f020c01061a030f060f060a02030c0606030f0a15020912010e06010905150424061107080601030305040e041109 80
    0x550407030380a0350314802c1d480d440300d0b4100d40723651442c42140010380c04280840c011441540c4400e0340020b0a200070300d008119540800d055611510190040319501c140c42c0040d40e4060202c0b13030001600060705c200c000302d900000f07601c1000e603001c042c3c040e0740d0700e10428058a00800c520211115100c158064941482ca1801c02075400008116203039401d010b000a0b00708c2d0551810070000c50340b0441e2608594032240340c407801c1600180b5150380020007201c80001500d5510040c40a02804d601460745ca819040d03006141c40000351407540240c0c032880042c2411140032611803030060f070100d9450141c600c42c1303d2600103401007410095204500d985d581015940550254041c8042403040d26460303070741c800f2800111380085500c2c920f111a074883c82c64262070543d20940701842d00142d2801454502e15204900d940d80e500440081003100405003802e00041084100420078040100702030340c15942c00411074091032140c821481d0210001c83c08020305140402c4007208081e15400851600810f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 471686483 1250 471685233 471685237
    0x100e0706020f07060906050a03091506050f150a11070305030a031d010603020307140d0b04060c110a020f150c010e1e0f030405010c0311012a0e090c0d02070602040b 72
    0x942800342c0300d503000300401100041404812078031244c4403032040d140350000c00c1da400c2d48100204800c03da42c4032141000030700e885101e242079032550000010083d0600d414040d07082002030030244510001009610030445207400c8959203400e519001a81d0303100000c0031458404260001090360002083c0c80f1844d80d41b550010003c2d40307105803154640307400f101d0024201d400500010f90581c2202c0020311030080c5600c8103242503140030b44054210821601c44241664003510101c80903910345114441c0c442d40f0112190301c8007001005022440e1161740002e00180b440151f4500030702c040c070014046485541d060301d07000d110b1780d0700a00081c82c1c61444241c9491040c10001d00c455000a14400140f4000941040c6a11f01c44011407416041000559007049800340072401c0044203481804090302c00c0c094140c401d402c0314604540004031480d0b48c4040c0b403000c003c01c42000a200200c2c1c002d60ba601c90b80c50740004044404079a00c81c581175040002e880f5458020703190038000540041c0c2d030b81c00100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 471687733 1250 471686483 471686489
    0x729091e07260d030507030c0f0c0204051f09020703090b0301061205060402160501090c0b13170a08070501060f0902030405060402040908161113020301030506010b031f06020d0305160507030e03100e07 88
    0x50100000e08c5022000c0d19043d000c0108100040c00d045201c0c0b0060815503c06504105003040c0780030103c8102200d1484500d0541107848401d8002c00c00780101a0000c9000c40035140e40c0c1c002c3d500b198107210004050f010491000c540450701e410118445443e9907040f104112440c040748445505903041c001e0103801d0a450840e00b45214980014181c6501c0055604105020300244075040c54090000080d5034542c00e25441402480103100c006401c1000400803184a10300118880d8038206100204096603842112010300420800000450101d00564495811030780001c803450141440d4010340550f08812100560146030042840b01c800e0010403101800c4482c1c610b12804050342c0400c3c0d010a100c000d101c2d512003001407185254050149d50320801c031462081714030741390003130b1510b01100707e50048015070031860400c901190b0502500740d020310703080c0022500444441d4001c2c0540710340c881c042c0421140d042c210515640c240302c0d040c40c103072410500340180a010000c50b616425984 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 471688983 1250 471687733 471687737
    0x61808090a0902031b0304020415120c0f03021f090b13030b061002061b120406020a0e190504022809180507140729091e07260d030507 59
    0x80c80016014a15000303d07031241c0030020a441000032545d0758071404d030700058012030b4003030380b51060100d80400000201000b00300072100c510007842d4a040c0200048031541001865045107101400583c50f61501e2002e2400309138041e40203010540b201301c401c140141c102415aa000160441c005130300001c1140c00d403405008414060b031280c500f0411180903400b084405070b0803003000140e5842070b100b01d80451a1100300300c50b281c0008650003d02c8580c08a40c12602c40b50701040015510b5880500a03011000603a1000e81c9074030801c0e41d091160100d80301d5a48a20780004d100c1d000308076541704031600d000c008a1407941b92100c241c00602405414010309404040c00307444182020b0140c0105401030040340c446645000035070360488c0d01030384040b0007034903411845d00c944e80e058610352542511001c0c0b000e1702030700d55041c4003010a0500c051040c18848100d079200c101e090f5480d000c03176401c0c1200d030115800d44070142814181702c80040f42c00c0c92001640680490448502c0c1c254018920a420356 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 471690233 1250 471688983 471688999
    0x312051c0c360302210a0606140306100308030603030d06030812061e06031b030a05010f06020d1b11120c0a0e130b060a21050d050c031606180809 64
    0x41e9030148000d0001112078250b10319000c0400150802446504d0114801d0f10100c00da603846452180c6000d00502088500ca0390301c410401002030301d40840030156a044002d0300740c1d824120181282c0103400d00028280b01340000c04201c2035a4104102d581c00310708000103018182d580d0400d00e410b504004043c2d9450b980410009001d80781410381e441491601c0c0184d1500c2404072014060f0a0704010401584400c100085071200c2c1c000c140514400c030f00c3c4d407001068644c14104102e10000c030951000040d580107034103620704241c020043d101ca42128161070740356203c1c28202596114100c3c240036800c9001e0384420035000c040804c0101440f641940e00040c01e51b910504c05002c03000c22200100c1d4880c014810340300007000304000c80d1700f006006084000d1f00b9154580c5483d01c41c500c00560001028240c082405c00000b8045c03003420f0401c0342045418201e0072175429460b4031400001440048c100d600000c104000b80d406407078684205c00c41100c2140051070100b0ba140e119011180c458004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 471691483 1250 471690233 471690287
    0x1a10080604320c09030a030c02030a020a03060e010b030609101e0615030e0c18070c0c080c040b03190314040f060c020102011803120e0309090903071406010312051c0c 73
    0x30843c121501a40090010b107442031711601c04581090f0329400481e49406000c0b003440140e510b02c04c8060140d40a2140001e05248103c8139900311129000d40394000d1f0810020000800404a10b0945640c40c10001198040405007004401604010b407003019503c0c200c0c0105e10580c01d2441104d0781005514200501c001c400380705a910021500e115a00c00b1190340e001030940040312105412100da170410050180c803503600c900c5149407a07045620b00340d0200c500c407001880c0074000d03400101010f802402500001d0094110410701c2400050f042c0308490002502e0210b244007150000c01d50b08404024a40e21050004d00540258400340e0056080c5604d600342022105080015a5032544494445c0c080340012000035003004200f24100c0e0109014419080d00c41040607403042c11080c0c041c41e82c401051906030fa01244000701c131000c41d40884014000182c1d00a9144c00000d0701c0d040c01d07512159030790314400d0040c581a1060340380c20b081900356011250420782c10b0404d644003041400c0e40c01c03c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 471692733 1250 471691483 471691501
    0x31803150105030709020a0e0a03080c011a13020913090501050403110f06150a1d071103030106270914161d040c020a02031902041a1008060432 63
    0x9000c0c016150f06401885007081307030801c2036000741740002c19070508810042c959400920203d03050780c020740d041e45001a580c00c29003001c0c0b1940c1c003068440d074405000c0e90892000315000c100c0c07410010ba4503640c001032940300f69441800b181c095000b9400f0a000480349454554041c101c15502200480c0f0b9034030710b0380e6100300003044082100b090500100499555072001d62100c982e45801d90350807103031010380440ca6002c1070401c4021850820007900071420309a8008240f8a0790b0185000260000d00040c08942d40c00803e4003040c0c040a00c2c501e10105d00d0030881580503c0c1a03000b000c090745407108041e40004d540c0185440780c05480c80070b0640c01007054040e40c030b10b0b4140074071018a2000341350142c800d1400794081c8240c1041031040300c0e03102003207601080c0b601c0c441150684444c02280380c590b003140342500a440705d6140f58480b00c18030401c000d010400c416004500030090002d550001419500c03550302c0017000d100c02002c040c122840b40348900e0300300c082100400310001704020000380b000c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 471693983 1250 471692733 471692773
    0xf050d03020c0c0118090f0204080601080c0102030403150204120609020f0306011413090519151a0105070203010905010606051c0c0504050618040c031406030a0b0a091103031803 78
    0x1014000150a800803000d004680195420700380b074811702040d480204005841e841010a52980200b0050b920343c00c14208500c0c00750143d02481e4075030722509844c84681d030301005a40031a5401494031900e80c8a043d01100a80555085041c2214003669400d05000d1a40c126101407070080d110407820140c203406040d1520403d01071080d40802c1007075011039600340040380004c9909903080004002819654081c1040d500c140748681301540c0d410010180a80001450003c0c030030103004100c544200b44514255184032240b540c10f01c1000f241c1340c0190340382900701c81d0a148d4040000c025054903580048c08540126600130301000b21441c0c03428403d9024403406c01e03840000e80700d003828103251404000d81680b2042c400105036018a1a191803503c1d035014580c00310400d52004034603000200301c803440b5000000c10051185d4030104a100101c1e241000c1c00ea0001c60440021030855401d0424400c444404c064a03500f42c44002800044801c0c1d5903180155050200c0c02d0b29807040040c20440b81c1c20b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 471695233 1250 471693983 471693997
    0x303031a101101020c0303040f02011710090c050c06010306200715020f0d1e05150d110d0b041a0c040b090d030c1a0f09030c07030822030f050d0302 65
    0x3200e48030300403140440c0a002030b886040c400c000050b10342800c07692201d0940d04103032412034070b1b441c1c0c04400d20210340c0c0200c03032000d0f054280d00c02c400c150b183c94520303811000ea80348210302400d9620120303d52240d11030340071182603850841c21100c240d41c1d285424401060328517050a14165070400c0c101e061032840c000ca070790302c0d50032656844030641c011046400a40c440803014181003402c1091008441c1f050040030080070001151004410f0300402060030303204001c00528504a40c40a861450b07035907119200c070a150000540540e050300e0b0001725003000726424010780b8002f501010041000b1840000b40144214280b09110f1902d078404491620b019a002d69180c4840600c40c107452070801d00325101c0014040e144c000010200c546643c40c4103070380c82985121042192003042001414030a8044c2c00c80030540085143c160030210482e1100c844e4000100540c00c00036501d107440710400907420800c0480030314120040da482c80c0c1540342c003580240071116030040184400c20386000348291201 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 471696483 1250 471695233 471695239
    0x70302060417040f03031d0607030816140c072408071b020909060a06081605010513080d120605010903030804020f0414070906020c06070203030a050d020702060d02040303031a 77
    0x2031601c1d50364440c2900c0144070301004044030144000240e048828001c02d00450280d20fa00c03111001640e2654185011221a031313010701c030100403010003c0e178070203c0c4a40c445103100f9040700c140000d210440b100c20308221460744236032010074098280900030401000b221404500c4060444101e0b0000610356101c016020104a43c00c00061265001c0c0010104c03000719406100c1c620001a800141540c0342a40c14200a602050030825000ca0f50302c20480a0315071900100448980c2050401d403d140d2401203d042180202e030425024103080c105a0140102400392068880102c10003448060880d504041c00c07400c006000420394010100d14041d02d4160352461159552134080c0202903040390000ba0700715030b54500c1035050b0000d982c0c81078026511a500c25030a145400710003858483c01c113030820f00c100304c1004000e0041c2e40000c1210400c0784103040007904c0e040d10044107070080c050f41501941081000541f6600101294020002c0c0ea00c2624200070341d810015640c80810030440407250 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 471697733 1250 471696483 471696493
    0x3010f1d1e031902150c0436090204060510050a090b09010804061805060c042c042d06061805160302090a050411040503010501080f1c140712090b070302 67
    0x30620007012503207802c00380e64012555401da404c2d0441417043d4088600341132001000c28207115200503040314100200200868000e0003000a03d1902e5080800d100c1280c284d9849140c401103481c1c81d00444000c200060040305404038003000074006a01032006080004c11140340070450001c01d034251041100180e4942c1c400c7da481c0e5540704000d0a4442a616030054070018141c0080c40400c2050f100d15203003802e040e200e40c0380a1011480c1c1c600070142242540017a40442c0d00d29102d100c010b41d000780c1240005050b0910006800d000c10550711010800f502030560360410f1003a581c00c040200e480b83c282d4880c5840c003800b1417004552090302c491003194545045a0030891098010f0000508001c120510841d61071000404072050145240c10f2010040f500700321a28007840355a0040405e10081c060b21034010900756141da107100b00000944a0502d042074180e4800c02411510250f14654159a008242030010700c40d0700c1042003400140783d02602180962000b81038070449030b07141e00244 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 471698983 1250 471697733 471697747
    0x50619050907090e070f0e0a0b16060e15070909050601020d2307030c0c0602060c1207021518060601050c1f020d0615080a110a0302030603010f1d1e03 66
    0x1040d050058a8078003003004003e808256140c1041c3c074a40030ba40e15485c2c2ca0200c10400001800d84810318400c1c52140c41c0302c050400c460300800c3c01b01d4080141c007850722020300040b45006001044561590a864880d104910700d404200319992406554146c031104d1800742c0d5100c520342a01d030102e80d16030042c1c01110341940076500406801940d0610020000c0d0507540f04141018550401441600060181d82d81d040920149148020107081188003802c07180c900390b40e500b10f0b103114861640524280740300010340c0c0d903482400790142505400c68058018240160480b4a50380e12456800580c095070002c5881d640c014030868245501c190058540101e8800951551110f04103000010700e80800960400b40614441c03032005c3c01401a040c9051078510000500c5040e00504440c2018036249010001101400940d900c8009518016036203542d0400440d0140c40c4006000c12040d00b01340700040039001d0784500010754140d144c112100321002141e905401c0503030501d0200c4036003042082e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 471700233 1250 471698983 471698989
    0x8100e0c1c02010309021005120a060506071511030a0603020f0f0f2e0c120201061d090307020a0e01051e0f2403010816050102030703020d0e0d051005010905061905 72
    0x1c00c25050050600045d10396207500800d8099242c03004210020328001403c1c9100510880c1c0160401842c5808200c042e041c0408101c0e10b104070b030710103440301d04080e070341190005581d0085800220354420301ea4403230820010f014023404090000724492003254031a40c4440c1000202c4808440340140304001c01c500d07400c1402100080400100714001d45041c103203045044040c504150718a043c1e440d009880000d003041076000032200000c800b1079050910030001d204115410840181070341c2d813044460349448019903c0c40c0f1a4000003034103c540c00c8800510b40d9402c6452078101c4409550f884a8500d1041d49910300c080c20f58400c0d5400060f01c98903024070300b0202c09240c043d078003000c0845940700c03004031001408d0704264821355403544544280341544910a4028004100030b00080d0b09102071541c002e500c07a5a806015020004a40144c43c040d5860051001400380c2110959000000d8250b202003e0942409600402e6040c04045403607030808511110000c55410803601d0414145410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 471701483 1250 471700233 471700279
    0x813121502270307050d080d050f040b0106030c171003170a080a02090a03081909050f010807030e070f0e040b060a0b071101021c030b0a0e1005060d11030108100e0c 72
    0x20700d60f018441d0803c00b281c10f4654104142002d40036003030340b640320b401d1594201d0903120001c0641c00c0240c202401d2000041c04c2c26042c5055403070b2418082151781041c0c10440360010021200c100400700c1e0380500070318100d4030351f22400b82d034096807400c1541d01c2d21000203070346441209000000201220000703500500154090310405600414461203da62511011485e4002400700410700072912a0b030340070700e0341016047c0000e10040e118010301c0400f400028019441c010400e80905841d03904503444403000744141d0029114640c8181051500c42044d049404400c550032204002da0a000ca041450b05503040000c9840b404e540c20304c0d002181c2d8030443d110401840c89410b600c80c607903641011518002c2c80400217011941c00242e030701d41b007008000032072880340d015650b003541e20824061580c1140400f40c00b40c8506030342c0c05644521640845008228100c0b030302003040c0300440040385951740458020103454100000340b100a02e4600301a84901d242c801d1154454001c48488440c2603040c21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 471702733 1250 471701483 471701557
    0x50f1612170f04090b03070e0604020705010603150204080c0402160807290a050a0e0706110c031e0d03020a0e010806060d0e0601061404030b06010c0813121502 70
    0x203141c81000c607149048103031540190415031800c2e80c01181c14440e90031148200c000c1501c040b002040a00d05e4185031801100e809040507008a800007500428441c007500018000c65000a00b02c0ca04807090301e8210081d0028025002d5a00802e880900c440c60f1500a454801d03050b40409440840310780d0340c040384d90384251021510014040486401907000c3d0311284505040c174081c13406d462070804044001c0b104000c0001c44200e20f003030000c006d200c2001030410700b82e5140e420a82a4240c1119100f46041003040c06203501d032090901c2c8038900c410164a81c41c014060f68201c4840b0000c0c004150240d0146400d81d40000c0c602c184150b80c00d48c0b046048076003082c1c0207860185458131520f021300c1a600e0403d66000e20ba071101e030042085070b5005620780c4031440203071030300c0f810305040d0b035510240c0450103003546041140c0070000c8000e01101340704444802d001d00b00c44100340303a96404105c851454805017610020a0f5a2488400030798a00846010030282104075000f0445242d40010340c250400b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 471703983 1250 471702733 471702743
    0xa02030405070909050c040609091703090705040f02090333180a0501060f06030218270702150106080906270703060621050703030302070303140c07050f1612 69
    0x10b00003018080342c49900750040c010000f90000c00303890301c02e01c070a4030780707079408030030060300d0925102c01280e084004046840e0042ca071503652601d450960901d0a4800d41081c0d82c05803420310f034081480b101e5401030154040950945500a465803003010003a0100841450382c0d544110402450040406c866a481705140300d5076041e80d882c0725045803070650000c1c421602a90b41702030602031103154041303100040c0803d107019417804001c980c804403404240d00a0900580003100055110300c1d081c002c01c80c490300e8071503004a04d8500204029a10306c04610f035605032443c00360000c1000342c400c5c18013910400c0100d009024135103a041d03000c002d126a1b007045154007003083e045a442030000340140390040d070151901107080e5003010801180d4100d900e080b0311160300700302c494000060002c9840c07001c0340d0f0103080058841045080c258090000a07100310485c51001c400c101002c049040680f017001e01800c01c0b24100910420b8056803004100b000b0300b060540c80c9401c01004100d000e01100c0b8510074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 471705233 1250 471703983 471703993
    0x60605011b063903060803093102071209060813030804050c0406090c08060604050d031b23010e0c090c09030f01020a050306030d0309020901140609090a1b0e090a02030405 75
    0x400d01c000803c641080b40200c0098514008400c29418003e90717019240031005145803007003030310015a423a10780c0081d02c010300d024891050307428800300c0d554682c1c00070001e0003550382d0059460200804000090703450301150f49100b0104076288107506940c46402d1208480e002e02045840588080c68000c004844c1c0c3c3c4608101460591114014200180594200070555128200c0e0282518400916040c000c0e801480100800c2e910050302c54005a018180b111040000480b26100403021607409451008001c01c43c074000580c1c802ca000c1411400c030020404404141c960544800d6081845a8810140c4010508540915000303100100004040310079010b600c2400c5426030f00161214404100c012003000011b0030700744856062500f11740345c100002c0f106a400074070540e03410300070307100d0040380030b200452203483c0e84003200e075501002001c001d203e00c0c094000340c01a00400d10003d03c8840d0141c8002901802928120000c0f030700100071061070390b590083c0300d0003500010300c2030710b40703200b8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 471706483 1250 471705233 471705281
    0x305070204020d24081231031e120e030a020f030c0915120d081603020c03030405060a0b0f090105090903120103030801030210090521010b0411030103060605011b06 72
    0xb400300001d002c13200d0800244009180007506410b004003100c00c010540820800c1c01409600d0088081c030240c8001500700100d600050000b410a03400d0300f006003205081210914808086001d10b118503200c0c0d0480c2c40b450303284140444080303c1d1200340c0c64042d400f03807240c88011b2901d03415030140050081c00303c440b41000d907130010704880c00596401e0660780c2c00078203441c96400c140140c1100c4440d5680289074000140000a1810b180140b84541550349601501a080d221750100c030600010328080b25180d0401c0d0900c2a254142540d9441c2c10718640000c50000b070030028076440d52064000c102c4041603181ca0103200c54130a004149090f00e004c10020f60310b4040781a180300e4060f60191740c94403c2581548180580c200d41440528242f0520090400c0541d0b078150840c032102440d00c910580394034080071000d024162083c00180e10900300031034070400381e08440284d4103e9010f5241440100e60360320065884050281c1141c64400c5449000b001050b03036508036062001030300040b2048102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 471707733 1250 471706483 471706511
    0x40b070c050303130c050a242f0c15030103030804031403090309010908011503022707020307050607030501030c050f04090606180f0b0108010608090705030307030e19080c040c020f01020d140a090305070204020d 92
    0x1440c05078211a024009c03180d10b2440c408104000b4441c0d801e0340c0b0061305080070080001d283c0814070000b0100240a030019040522510055164107841c500c5c058890400f03240c1c803510b9400c4a951a4005100c9620011302d450050068102e03a942d40480702e80c0f12421034091003038404c0b580e00c8541184401c0b02d0342c2441138004207101d42c4038820319030180d502e8a50b00d1601d2401c180028203018209030400307006101140c0340000840454408850a950800304000450003038440702e44058200b929001c40010b54412401600ba400c01085c2c004008120f0726094190450305e00354205070004000304010b0061030b0180300c155812104080484180540d2680080c0c0f95600c40d00080300054442e40101900f405d240c2550784440203040e0040703070f880d400c0068159aa4148000c0c0c94801d81c0c1340c68a0302d081500900c890012000c0c0313003000303540d01e0401d40d0401d0094428100e0144125000d0310000c0d0103400c0c01c0c4174141c1c0c3c965159442c42d1406645800300b1010b900140c13001180c0135600ca0340c4504590b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 471708983 1250 471707733 471707777
    0xa0201020918010e07050408071418160e0306100b0304140d0905090a021819090501080c120d1d13090311060a020909040b070c050303130c050a24 64
    0x4800402e5200007581401202c81e00480081d00744414040d09000a00002d1404a07502c0c0940b0070901c400f64070300c1c8a1074001031641111641625192040d2810312801000200c140301c0e4003040c58a4006040c410b04060507542c007005c4070001c4034459200c100b401628401d50085412a0261128104000031b1400e002e00b030180d07100074400891000a8104030908180c1400c0303a008202d08070445c101050507400c58403c00b12103e80f140f09001c628105100354011840752000341031800010000c85d1307111403a842c0d03a160803050b00d612031803003840204401400003c4000c504501940c0d01d80c010700f09002d81503400c4502040d46039120815040c40e1703001d100c0612840c4213980c001da41d40085154051403131403d0210280078080340d41e00410450400b0303200e8034100380d0802d6010103802100d94a00c901203612442c5602d0090a07404000180188070512a465000081c024010420450343e14010418001c40e203108006210384600041d04c01c0c41c03100c0c54458524811810050b0108170802034840c6a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 471710233 1250 471708983 471709009
    0xa030c0b040c0506180906010e060a0e01090801020417010e06061c05100f0504030f080903041202030309060c1b0a050a09020304170a0f020c06030f2a03040312140103170a02010209 79
    0x40303212404007485c0762420703405242d00440d00382894030b4200640b80c04190584100e20303010b0140b10802d510700400f41d100b40c0e00d81b0006c2110320021501e454a13017070608481303040f51010103600e6007401c00d015210360340803031345502440004091444140e800d18249a0306040360509542500070300d000c4142c213107501c0c011082808080c030700008880c0742c6442c000d071510041c1080d603000c00c2800410403900d00030000844080d80c405007007040036040e0b0351001a1540c030079820080c1d04140c010480008058000409480c0f941d03650284510040011007031080580d014480c10f60b002d0341e400c004110401203903004640180c041c0110111040070811100344941c006a82500001c1d50007421440c425414001815000070444820340395007402145c042210801504420b082c0b90081c80010500005410180d0036004e101d070300a84a10b0103050160100c9010320100312402d040018480d51200c0c1e40e0a1941a60780c416150441c210030b1000c1c03103010b904200c00d01c80941d9401c0010b00401d40d220710589007a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 471711483 1250 471710233 471710257
    0x20c0706030e061b0a0311070f0c0e0f160c06020c010501030c0906090612141903050d0b0301090b0c0a030905060a020a090f03031209030e0603090601030c080a030c0b040c0506 77
    0xc21022242c600d01d403940050031240790080c20341410319840018412184030190a2402180d0302810146003102e603c03030707107900a041103035409419040003055151001111003100000c1030f6655080703131150700e2220403941070b001c0348202803041c6c24040c05401e100c0c498038000c020041c10f0202c1461400d00b10788080c0c1007603485122079141000004064001c01c0054200741106124082c9442010f5401c0b503d881d030010980c0000011403d0381a5040101844082958080903144089401d01401c01d40c06909544511401c000c4c040103541414018144510f5204407440125507503081c080d01345800038040d0004242d141c2a0f00b4012a00c200800fa0148000100045e07a0300b5100c5000b82040c803295001c4c01c03028150600401c0031a4011001020113000703498042040d44c52464102e030000d042440d120761204011090008081002030138071f05036403050244d00c0b065500d6060b01d030380d03031681131000400241e900c03821100000e1000603041c1c0c005105200680c10b040d205c17000541540c02000c00504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 471712733 1250 471711483 471711491
    0x60606070c0b130911040302030a111f1112030106022a06070506180c01050a031512061509052406070212030733051005150c0c041a01080901020c070603 67
    0x750403105c1c407640e01c02642585210b4981881c5a02182c0c544411100c060085015a038004d070840e21005044d8201c0c600c2a403501c01d01098485002e84002c00d110301400e228032030600243e848841060480e0705030b80b55500105010101071203c0c0c0c840007550301201004c2145030544025075150003029200c024401ca0140400d40b50400351403210108025080c04298003801949038076036045800c40312099942e00c0d012a010301d20100140c022180347d40038101200c0062221400d00c09a540225000400c140013081150358524100007901c0080d600c0d8851131900da124640c0301c481d0381400fa054104050030441c106403460300005e403018680071f844e4416810003c1d11304208036513a0ba041086408070a40141d242c410310481c030142100392401d0051040da5000802c0d032096110a0301d42c000d050007402d42d00c03000e022041650054008010f262550b100d290010280d1b841c0c24090500c5400b0140d52020300419207100444260740050000f8450b03560803c5062800305040c003514002d004141c078042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 471713983 1250 471712733 471712739
    0x5090a060905070f030f020703080f04050114190c08010501020c060901021f06150206010b1902010e0d09080706090b160812272d0c13050a0506010c05060606070c0b13 73
    0xe015541b6414100038030500c1081440006500200c042d0380050707030403118031896990751600d540103000040341c103040c4501e00c000300700303c03c552150303181400408504c040c0403181207401d0540703c80500303020f0103016822000d00d1004078141080a403110f090144101c85984810386000080c280380c0c0286a014261a44410301c94000050310f00f100b900c0c4684018001c96142503245900c500901003d813003008149004c440942e8403d4101221107025031040e15081200194060015441c034401c02d500783c011f90000003102400380b00440d00321410244140c2c5000918a441500d814100c0d50440d6441001c1c041410714800010441341307e001404a0031008511201c151403884d4009002070449503c001403840080d0b100e14a40007400e501c800101c0c050030340d03c840f11401c0180aa441c99002451514001201d000e1900031034015400c0348020009600d0b044011641201100b9006e080384c1d008201081007130900000030040342c2d001e400400c2d40e003516007404e01c60b070350b001c1443c52414a42042c024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 471715233 1250 471713983 471713987
    0x409020d06030507080a0c03060b0d080a02011b1d09070201110a03060524120705040512010609060e0c070308070306030816020114161113060e1005011805090a060905070f 75
    0x51300262101000610051010344d448070a0a019408000c04141d21380c4440742e4140c42e100034400100b640701c0800c41e200c1e0f0b64034900030300030315089200c400742e4220300c05407408440c001e5488010359241c08014403041c0f54400c05001841034040d2600341159626480c017401001c0a0000d000c04030100c0d035001c1038440c94401007003140304404c44c0c0051080610603c1d4509030b1205402c03103034030f1901c2c2541744115503580041580c141c0200c2d80507503082a400c2614030880d0006500c010b05444a02004010540c0c0350200400c41c100200ca515215410401c43c2c1c0703010078000c80038158007240a18011401c40c2c1c0300c0d5501d421a0f04040c2080009034505002101150703004000542c0001c40400f0719424100d0b8030700150740398880c07610060103174208586036600755203030041d840e00d0700b48000c0d9041c000550394640c2103c8244088603288900c280c0c941000c61150300c2285800031000c0c140724100341d050b051504210f28500050581c884041d139809000900722051b00079203104081075111030381c002001c0c2c1c0700 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 471716483 1250 471715233 471715243
    0xa0b040c0614030601080a0b0a0e01060923010c020d1b0b0705010e0f1e011503080703091d01270c05090102010605011b060209270103020f0105071211030409020d060305 74
    0x1180100b8901030040000301d0741c4c0091210341c400802c1c04041040110788010132465801600840300d112000800803890503000301d01e071011582c01d05032820409125100340d40d40003040c0c040360341c00915003d8112003d03107403400611840718054902c9208044e1240d4110b882d81d005513105040040703000c0754800a0203000c0c0709110b2049a4200a031540c000302c070301280d03200c4401448800112504900c2d0a41d412000d41c00044c400c0951248000348030384a081882641d00f0000040b000690070400c0828418142580c0740b6506080740062101e9034202807003e0404c0072515079407046041d4103072001401600d02d0150001200c03007900c60540e11400f43e0002070035120079411850501028004070a04550008103007401c09070001c800580b580007850010b20b400340ea00b08100c221035554404102c5500c200080c4030b0499100300c3d0240200e200340401503503240034034030015000c0c1c0c00100710b03220f08500030016804031001792000d40c0e14294480301d200b400ca03000503004100309591000140100700741005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 471717733 1250 471716483 471716507
    0x30b06130c120612031202030a02090306091b01170c18090a27020901090c02010905120408010b0d02030a0f080d14010e0604021c020901020304050a03030e0a0905060102030a050c0a0b040c06 83
    0xa00d130b1900000c00d84001d40303d00c408000151803140d00200203840c514181d030655150329801000da884500305040129541d65030310684502c3c10b00c9130f42101603990b0180c903845400314030903408034415988490030365189400c070107000c000e803485280c9282603d559003a6924030441c9070007000078040d2802120107400c27039010086020506541da44810159540417611030442e40b00301008103003000f00080481c05804014001000c91103800d00b010b00e0000200040c0c001d558616000f00314804030002040490f00c03090b0000b07034060300031000350f030003091184c464000014002e06545141c60881c10414048800038a002d441e044411001805000e601c0480d55401c034a00711410360034201694010001406003400c401071103540001c2c200c0050f4024001d860040c40000d09000340550350342800b03407000c040405018820003200d0070102c2e80607036601c103950240406038000c600f0710b000001c043d901580042d820541c54031603001014000364515403558400d900c501d01e00490245010805820502100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 471718983 1250 471717733 471717749
    0xf050d060e1609210c0b03010f14040204030c031529090f06010215040f020402070b151005090f0112020409060810061428060f0e060304020307030b06130c1206 70
    0x35020404114821144050040e001c13007010071194a07880d0100c0c846103140e2041c8040710003c0000078a01c24245182c0c02254054800600342c804500c0400c4102c2c441c0b40401091910f0340c4105202140741c94501c64454010000c00150644001207282c404040c0541c42c01c141a0180410b24901e040410409030001480100c510b00f0341004c100203916054084d0072600b0010001c000a0244511681002c0300d254000d0300c215662860340c01d00d00c50901c0c0c11101e0403548064550340c0400340c00d068640e445030b90041c0e0788460404844c08100714014144015a03810804618200996000d0710320080004090542002071103070300e0a014542040c2c1480014184907181200c2004080004803596180600c1101c281244401c4034192280301404420284000c18032500c1c045070854005550b4000c4020540b2030494900c048810444648012103000b50990884a004c1001807078206009804c410000c2402010402c0c50019500303c030000352a0400140401081580b10720749486402c020780100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 471720233 1250 471718983 471718997
    0x31d0d2102123906060418051507050d0f0f051008070510051903050f010506040f050904030e06160b010911031305210c010e010204060f0f050d060e16 66
    0x6500c5a2240102010081d640249403032507640c0900000410b1141e0308002c9610307402c05503c0c1c0840361390b41d02c11101030b4069490490038001408074121007000c0b840c0c1c00401040310315240505d500d06202d002c0d10703850030b222044c00365054140c4030f80540401081d190000292420030103014100b03950000e004101c45001350102480a4003000c15180c06452040e18083e03c1c1c005096404c5481c0c3c4166240c0040002c10b42c26200390043d4960010350168895030015807203662038000700500c43c4907502c100320020348100c0c2e08000c1070521046c507580c454040d040001a00310240702040c4664444111342d100116106460703800c00030083c20080c003420001c141009500e03d6034604040d6031002800f5a404035024600b43d004109080141582c41034442031840d540c444003544c000542c3c0c01080a04040c3d5003000016000b80505100382e8080b1603440c5e5812841d42c00141068540e035801c0650f600400404000001409840e405018020518185281c801c2c0c98402d900d1000c0c03959004150b8204900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 471721483 1250 471720233 471720253
    0x7150b06042301120e061009020c0304050118030b1006080a09030e0d06090204062303030a020601061b051204210b1f0e090d110606030703031d0d2102 66
    0x4010342071242c0c0440380340c5440c1000541801610441d2066100105081c200a0058400000460702c07a01036044024040d01154440b080142680215040081541d00070300041040d5881046802c0201494401d10401c060310303500c40008031141112032141e814035051080107841d52050710203a000e4000c2004008503112580d0042401c1c140600c1544030f80c00c0040b4200502c48103521a09940303900500400c007081e507649200c00d42e0168884e02c008007220010080c295401c02000302e1300740030382e250b02802040e801d0207419a0001c4541da40607400e1007440c002d0500107142080f403a00b003152490343c950303100c80c500840001200c02c0304410003c0b014442401c2c3d000604c01c020210340000c2c016020f8902000c0703e6081e4914481680d0064a60452140600030340759130101d0b18159803030741aa10f00300030f19001e450307455071100240e400f140c240d4002a070810100b446101a0804400092070308500180503500061184442c0302c802d0780d01d81210790341c000c51045000000c4102e03643c10b001611a01c54 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 471722733 1250 471721483 471721499
    0x303130303020306060c1f0f2304050307120c0209090d0905011110063005100c050c0f06061f0e0d021f1115040b0601120e0307150b0604 60
    0x510260003824542c01201049980d0741d0345040d60501d4011400f15000440c0345400c40d44200c1c1ea00c55540782e41440d1603481e40307029466000740640341c581ca9203102440b001410800c0e0407044000c006681500050001000040c11321440c80e104c09a142c0c1c5d210000a454010440310b0701000e816031135154440c02010301c0054000096000f2604242041034009001702c28950030f0908a003868010729241c4000032480c1520900d01c905054201c840c0980c0c100411008003252140c481e1010f08658803070846030740125525081403070021201d19103c0d0401c1641040a841c050084594500c2a0062420844103081116440078428008030200d40380381e900a0307028140504c80340d102030240050783c01030b1081d5100e540401c0941d8140318841d840c02c607000c2200400300c001022101250b40a0501d01c04a0208000c160038029500b001a40780251200c00040d60300300000010b00075440e031207208080200d0014405415070701d02440303d80c029805070b00e05880032078148070101440303400140800d00c0780c12 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 471723983 1250 471722733 471722761
    0x402091e0604090206130b0c0f07050915061308010b01020127030e030708150106090f15031a060a02030c01060e100501080702100501090c030b04050609061302091009060906020303 79
    0x1503054900040002c43d40c00410020310071182c051803d15505400010404c031000d00410b107140380c3c60185e680a244440c0d041d5100d080701c2c421a40d010b24010045070006102441e5101c02c2c078002008a40f518907080714040441d0547e80c40400e03203035940e0104002c0ca503028010345804000c102891040454080c2151824800c07005005d03041007100d126842c400c3d10104099405025100121484c641108004110740c4000b40603c1001681241e8002010143e90138980c050304c902d04036078031003a440c0210481c01040102101e02e10724a4482101620740c40d10401030199404543c00345075504603203103150b42541d400c0da002007400c8201100300040310031141d08500946c0c80910b85008a9160750746c04a140c60b060740084220186008000036070500781da48090303010700d000c0c0c805116000356101048201c60007204c0c40c54000380a0300000d1110300d012941ca400a520400005090102d00d6000c500140c401204180100e804408140101900401e038040101600e200070b500d10310340308603985000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 471725233 1250 471723983 471723991
    0xb030303180114040f12020a05070515071709042904090c030b01060903020103050106030c140903070b070b01092a030c031b03091e020d0b10120501050402091e 70
    0x80d020208a00700182900164010201e840b042d94950405080c9949114046003003107684c945200c80504059002040c042d0020341c000e000340c5400b601d000240f0517009e1880705044881d06040003120002034006420380d80b4086991a01620f680e2018180030880f08808402042e03e00e01d0300c800b0b03d24043c0003c2400350380005a070041a54480d03860000c030384201d0b50304024291048140042845035200640004880c000d0303900740116640c4050580031240e440011400060082841d54414518000240006007018041b11400c0b55180c0040a164204001c104c541c100d03a140100000c0308180100c040001d801001d1071141401d5255a0340e06452000049080c191602003160740e85000780e0151802c00790320002e81c405050480402402031020000488042c10041000184055410241c41e1195409031402203030342c0883e140c410b00c01c0801030900ca4002d910f400045013514070054450359580c4150004506400c1030f104100803400001c01c0031009100c40400c0e0106170710039480f82904 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 471726483 1250 471725233 471725251
    0x902060706020f0f04031101030c0503040f02120322140402030c180301021308060619080a080309011104060507030f020604083702030d320a0f11090907030b030303 72
    0x503405a01c1001085405180130115840e900400c0c00014815603c0806600f982d0980e01085040044901a2110b010a40c1c4c003038107180e14503a203240181451150390240800003400c0b0382c24486207030800d6010cc110384100440541d40078904110311100e40032942c0b030b407140841b41903040d45001c0b540000f0a000381000019043c034594005407542d2000e40c111512006150801c6000c9034694003216035412040c1c6000f40251407595400c00b00501c0c02c1510001d0754800c0c1c01421f5000703000d13110b9018075080a45018040d5680d180504109246400240010601a00c41a442d060b41d42405000d81008103892000e64110a0812000404042c00c483e5000c2d4141190900ca6240d107400340c0c0401e103130940d6400c15015910444462940003c050f142010681700d0500a0501800e9811450000c101000d100c2062a41c030700203d4115040700280d00c00c08241000406c0e54074000c50101f80c58000da00190101700005d1040e049003031035403d4544c002c0d80b50405101801c80c007400300799270348030003895500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 471727733 1250 471726483 471726487
    0x160f080a09060524031506010c0201030b03010e0703050715080c0706090c0609090c0c0503091c0b01060513080a0f120302090a0f05030105090a11010e060f03090d02060604090206070602 81
    0x10300e000c800d41c00280e185800110410a031302c0c02c41c400c0c1000c50584034000f1108400e8045001c1507140024554000c081410780c42081a242c480041d101460710f90412410305499070094a19a07c0c00d00c907080068000300300412149245080c0203080c0201070704a07290380c115400402c52041d030000002c5810040d403084072503481e000780c01d0a00c0142642c04004245081c040c0001841c10380c02031030315003a82c04210b000c00c069a5020f1041c0e6408440c2d400062254009001c0c103d040d2909001c0c0c200410fa544003558401e15a40e41c13010311881090f04003002040b0041a0002d6a403d42448040034007242e000810440240d0344601c010380b0f07100b1500070f0584018500104070f851103501038030f16040700a4401c840722525000221082e01190203070901a41c40d290004941d180006120009240c02001401d00207074854011280421207440094010b941000464a840fa0080c0210300c140c00d0381014080c03103903a0400c02400c0c610090003042c825800d091300c1001603038980c0d04690300e080d400b010041e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 471728983 1250 471727733 471727741
    0x5100609030813380405030a081602030604030f090f082a04111b030307140d200703030e0f1b0f04180303050a090f020f031023160f08 59
    0x4025070445802c500341c84d12041801000d505a00c150404440b00c00410880d1035070811324148000780140c0c810325030325512012001010884030703002050b4201503a01c4c5083c4003807064001c030340f0b048000c1d18204d000416030341624481c264400c000e04064040191400ca030145001603082c3e40300c80b4540101c240e96217241c0f80540e04501003980501481c400b40047c090221b102003000399540103507025902180c1580171501d0328040c08800c071780c031070005500d821b086507101c990150712541044000c00070680d0345400b042040f02d45192149042016100c2c480c1d50b4030304c58640101517900240741110b0710380c0001c000c881e074824082450211520700b010360142182803e400200c2c04d10f040700d0002c4d001032824101692041c0c51000f503a0b2258080c4d00e050146840d508984011038031320307142c09401140c1d0148000c0040c540000b44e03084503000242103a21220160f034020003101d0141185005100908007017200101c1c2c2046880e0b03115051078420384603000c05200182c0011031140c950381c10810103100007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 471730233 1250 471728983 471729007
    0x6160312140f161e0e12010506101103070507121505160309020109050a060207211e060209090c030603100209030c10020a050a0809210a0209060406080a080d051006090308 75
    0x40e0013603c03068101d11600d0070041e14080d140040300307400d8a011700084007001164040500500340990340140c1140d2040800c0c10084500e50000324040c2100d000400182021034000c001180c007600b500c6250000d181c2c183d00e44005241903519203c81413a0801c8104450415402d00c02c0c0f04101680c01c0109901a60f071004840c14800d035000654045005140400d1641e8000b52050580e0710b07800c0058040d003074400211008100000008100903903051240007042042907500b0200c510440c40541003107010000644d84410850b400501d43c54084100700c410b25040001c4c1c0800203110004503d410181c4012a40702c003c4c003841c9030b0090280d1041405100d1003005240d02d047d41042c1503a540f2804c0382f41401c921341c08414624800d41a14540003140c12480c010541301d8501d8000801c2c10203415424089410002042294002d0740c440380062009810f110030310140c0c2c4070300b1219940351035222a440442c1c201900c003860b0310401400c09c0c4402c0303030011180f030305480d000038040f5210b12400c0a4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 471731483 1250 471730233 471730247
    0x2040503010501090207121b03030915020307020c0301051f0510020309030307060903090509010b2d04030c0e0c030609130203010f061d16140906160312140f16 70
    0x100a030036601c0c100000401c540e440d4083d0013098810300203580c079884800e000304c0e00314207030500c02e00d01841000110000640240c1c809001030303100b005082a44100009080d089030011184040542c00240460b42ca614081c0b24a07507003d12581c8410804044103601c4c221014a0b5008403401200e01356420b1000074001c10075115600d00040840395940d80d0307880c2043c050140100101c0100b000c0c002c01082e40e1130109100c1d4140c41d14100b80300c6c28031140c80e8041c41c18021000514182861315000050050480700003800a507000d44885401e00d45080e14600c501c0c4030080c42c003c07013400203005021850780e1350b2001541020103103501c2402000c0c10300000c2d004007055006840a24035200c80062440040780c5146541c0ca86803280c1ca809994840c2c1958014000d01030000c00911580d00c2212000e103200302601100d8405042c0b28100a070039401800a03042038a0280c01003141c0c0400340c0c0142c1c195004a407208400315140403c00c1c1004007014440010207803848001006030b11002144620580c0c13 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 471732733 1250 471731483 471731489
    0xa0b04061517071d22360209071b020310140c040311010c050106050d111039020607060e0f030406050406080403030b0d11010f020309090c03040c0e1611011517010204 73
    0x81040790764030b0204280d40d804d50f4200312001286c0401196501401e828801e0704105802900c02c403840c0d40e80c41001c495501c0742c5030540c0c03030950920b6040005070b103040266921f220015100011060310890040041c44001490000c21801c1044184001081c800620444020a00309010036503100d113003050143c600c0d030f08001d40006d840a00c0d9010710483d43c6001803842e00648581403d204615000c4482280004100340c0c100c4124071000740b15402007080031005001c0340202041c00c0c06c280d0004140d0b5105c21300a892690700d5074002c0d950000144400f82c49010b42c0d0004510301807400002a18a008520030300c0705200b98840010185402500174441401000307001c0520314841e407a050024102c0d444002d400960364031021b80307140f4000400c880032510f0043c8846070355941c0c0c141c0030030940c0c002041240c01c5401100001006006240103902441d002115200c0c80f801840004000c02c101b401503951301c1c0e0401c04401019401d044403102514010045489550302002d8200e0180c13040e94 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 471733983 1250 471732733 471732799
    0x170c041812051c0c031a09041410020708040905010e040c06030513080a021c0302040819030215160807140a0806031c0c290a0b04061517071d 62
    0x101e0380f4090f44070590003151203444c6618200f200307400502c8403201c4d101e010207070070b40c205400901150114041c01e45400c0307241c078010300f225520038020751024240d0300f0445003142d600c54007180901c0300c407505000e43c030b000d822185c40c1261580703007549880000441d20b01c0380109059698010603140303a080c4450120180e0001d104541d90010618025515507191101c010400307058070030749071900e209001301c0f0221540600145a4601001d03584022420b08000482c00c0d4803450440c1400305152501c0588903500c10140d0058034102c9100c058182540240307030703030200600e02d0400c1a02280c41400c0c0c1e90199180d1510341d055941d4040820b24003075080d884400008048076112441944c400084081a0f20940906210307169002e200c550081c07980c5c295601c00b00700d40000615040480e032084035550401400802e50595450040727021441c1d111402001135940071200041000900c0c5180d005103c510303217a6441c070541250001080d1324104903c0c4900340540c1c403212103560300103c1880d83d40000e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 471735233 1250 471733983 471734017
    0x628030c08160504020a0c02040b04020d182d061a13060504060b0f0301290f070203150138120910020c0c0f0613170c04181205 56
    0x6429481d030761000d00440740b01c1c14880100219490400b4001c0e9100e00c00e2075101c1006c044030940c20040502825210b443e00190309101d240d600c40e40e0b500480501b9816a1410041c85201d400c00c0d0118422612861084840007004514520821819001e9081d0842400665603020807064419a0182c0c2c4500b0341c00215046009081c8109500c40740448000f1141005919607411106040340034040d029040668240300412040402000d16004544410b62400031000d0201c90010590040b21032540d0310f17800403550b0710450504000c000644220400609103644c0341c59443d194802007103140060300c51544410645c0e00d860381104071340c0002018980e9890300d085868041c0c40040441c0e4140032803040c1400c4a00507401c0703100f180c9650326060050b01c4503165040130301c103601104810084d0080c2e03081042e020003413031030310800000d0441520070110601c681c09081c8d19054011801314491854007100080c1480d08580703881c401644600000f01101d03107010103480f035000703c1c12801d1501e021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 471736483 1250 471735233 471735239
    0xa0b0408030105030c150d110c07090504020f0111070603110904021b070e0c030609040212030705060a0e030901120c030207020a080c03010f1b110102090a06090f0b030628030c 77
    0x1031000785041c0c9000780d0458408004150811000049042c00d00c0d1650104001c00a00044c0c6504060140c00d13035140501e10340500c1c0c0c08a240390141943c80310303000d6680d0b6070500c4110714001c4c1c409503002009282010052117203158143c1c582409104102c14140d66001001c2040320030b405440078040010b100f1500c3c0c4801148000c211049880301a80c41c0c003501e000440c0c0418540b43c0360b402a45004002e0382141d60f900184444031074050000d0764403c2a5650030b1500f450104000c1050601c1070000d000ba0381085100507055620802c24512a41c106021580e0b0603680f241d20b44a40000c260030101e032111600b60150b0080c442c0c40c1c0302940182d00c01030040740c541b8000071400808541039008114086200c0b868400700d940b0b202d07010301c2d03141451030140c803094420024000c0d0400f80d80700051070aa0810300282e5102034650006010072294001040500c1030850701400901c69054001d103589400b00004e01e0340c0801403040380301d02d0707000c00008191020321a04d10340510b501130140faa4013a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 471737733 1250 471736483 471736493
    0x3032d0903030b06130801141014060f04180608031912090203060403050309060c07020906010c0302101a04060807060c1e060c11011a030d121e090308070e0a0e06030a0b04 75
    0x86000d000da242d808c100c90142904205d5403242d10500c1e0700e4984060690500b840c0744428003480c550141e0040091003111001c0066030000d2009141c00c0c40313542828200034003144140e84044d1701c8009960000e00481003040b124440f6600d507010759142ca451035601094070350004210794440030303405105a6007040304242c0c1100c015030140711007204642d9983e540800b030360414071030080c0081d00031607404041641540620801600284280141c074041180c41710400c003264944c100942810003080601c0e00c00c0c0c1000d1084a020342091405045030b00e0415501400c004406140180034614410708201000e0801804c6509560b100e00c050100c1c4008403c028007000c100c403666041940307081c44911580040d01495041c40074050098095207603c1c1c02d003559407038140e0900006030344d1520307600c03009003085c11041d48010940020000314203099080060240b00c5c002c142c3e00c00e001c004c0030000c41d02e039140c680350b000321840c0b00e2481d1159524040424280301d1210380c0109600f02440038001048 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 471738983 1250 471737733 471737767
    0x6030e031303030e01080f060312030703021c0b19030b0c070f05010203010617060306040b042405040b04060c05040b041202010c0818152704060f080a03032d0903030b06 74
    0x48003646d40261300e40f680390110070503080c00e032881c0350301d54069140c0800c85500c0d18040c0d0780c0320501d81001401c041900c0c170301902d0460700205403e0441ea8403000c40c0b08618184000c5071075130f4860000d1748110b40c00c5568039a90030134007402905280001140b050100403403408450002a840b00c029500c0356543d001c05010240b030b50201c803070300a40d0040090264140001c80300d100395002140b800c05e03602c0f152152680000b130b58000f0020302d01d90b81495400702c02d040c01254005c40c454150701c0742a140904241c1c003122500703551041004810401004402d5a640541c1d0a4500ba469501c0060241c0d10050300c5000122a00418000000c551303907911140c0c115145840c00400d40e40380311081040c0034501c03914030171101c1c25030501480b04501c80c9070b031300000009400307814050030000303030140c0350319821a06102c980d1003400c01d0340c0b20640110030564103028403c1d071070420001a100b0940c2d9544020070170041d07881c03a00340c2c03165070385000010b1500c25001034445c43c401400456441c940624050240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 471740233 1250 471738983 471739007
    0x305030306130b010e090a02271008010501170916081b010905030304090203043314010b090603100b042903040803011a0f0a0903060c0e01050406030e03130303 70
    0x1040c02c140b0035a45100203009000c1c0c0701005a507404040311070b42080026800303010b490300a00039420b002940c49000101c2e154882001440c0740d01c0391100b000d000b0003000f901580d01103810403034a400100101d0342c110b60034507008103210b035040d1440e9480500d081d14003001c0145900301e440c003010000618a402203403402541c40c2141101e104004800019103140301c0d00e124141e0954810403080000242c40e501440e006407282415040c110280c00042c07020b0303c10f80101c0c84520710b0b01101c038030154809204903444040d404645050310361401c081420540202200a801000004005844c11500000d828040c013154041c954846032503007485044014038014140c81c0000303a00c2080b80f0f00f8150816244a954880310326861603080484421107544c0d0309000c0074000c18144121415041034034043c015040190341c80d00ca90a04d9130a00e00159413040000b0710a11803034910080460364401c007190266031305402c000c00c04100d114040c074918401c1402c403000201f40c2c07200100400d54050718010324 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 471741483 1250 471740233 471740239
    0x220303121a10030608010207031701090e0309060c01200306031b0d0f02060c33060d060b010903080d060e07050a09141c050c040e2d160305030306 64
    0x85250203001101220700054407214110100200d1000500e090801c1d028101814078000c5441d5642e90000c0d03003640c120b118203d010900000000580e03481c0850074034018141210188440795003140e400f40c03a4403a19000034091180000c1d40a02c0d00401d4001503000e031078140c0c940c1d030b0117290501702d901541c1042da440ca00c40c0c0202031141c0c41c00f00c0781151841d01c070000144132420040045e500c08030003c0c55480308a070000028800d030011910280425283d010003040805124018403038241103010030555403c40400c00030043c020f03c0d0f00c4245a15480a50001d030020300e80960704010307260445e10b64802042818001a0425000207540004040f0394003010521195103403103406540d14029040f5000014880c1081040709618000c00c0c203240034130240580c000e1034501d0300d01200c1640e41440a445035030122000364140c0c1000d115095014540d00041c1c491002d442041a000000c09000700a0312112a60444510039043c00106408000a854400b1076079807403070466240e42040b2100e40c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 471742733 1250 471741483 471741497
    0x618140a151a0603090a0b07080603150903030f06030c062b060812070606050402030702031e0f120604022116140417070512030408070f0f030f0305220303 68
    0x2203401030350240490307039081c5198850001030094140f0103d80c02c002c2551050740310f40d02d264004141007424980c0910f03920350728400c0b24500102818a0880300c000d900742d0620b20f240421181d80302c017106036500a0442040301303080c6d4681d400040c0c6403101002505034008130000d1f40142000407010180c081c2d0194040c048129415000c0080c2100d21501c40ca0390160411416010380d0f507510340040140394400e00c0d00140f102d4031500410100c0c1c00840da01805a400014241c00c141029130021040141d580409881d00004200308500c42c02a1040c64559020701800b068185d5115010780e16942851101d040c132040c01d00329031440d02441a150036039002d145c0301980100601c1410544000e811410040345803c2c60405803c85040d0800b0851686001d02c40c4c0124803940d510f5104121030300302c036004503140c03403c3c6404181020803541c800300140c5000c8504021100ea442d8100b400c513a00004c0900c400180ea05060703c5c248941c111131000c83e50341d04544213003007500428801c280da009903071b007403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 471743983 1250 471742733 471742763
    0x9050a06051c090209040213060f120b090c0a05100521040c060e100c030c050601230103020403050d0507020a0b031e010806060102150714030411040b1009030618140a 73
    0x6007229003a43c0041d40042c1d01c4070000300075052611680c4075107402c03a940055020380c0c5802c0703900c506021b03810101a0520200214090000002009800c1440301e40603184c0101c143c00010000d2003144107040c068000d8100f5003442c1b50003031041e2401021030b584008103175120803608001c6854211003c8803000c00703070040410104e20444015040420140c10308500030b840c828292100e09046104404220381c07c034024000a00501040e8001d12080040d032aa407203004211201a494404616042510611040002c15400201d0b402116081c0c14a00d94480352800810b04014898005640c007030000070500210030150b44052040511350703220b15040b80d8070323a060140c880009a84d0980142e10284006040071000c0c10469000b02082c2001003510288058050b49034004444c245c030386000d1401000b0311401c09024005c0070041c03c5964020a03d0040c2000d00b0300f0704c13580406800d050f13890103031040070329034802e40750201c3d9042068061084141c900256989000b0802140d900240d903c0300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 471745233 1250 471743983 471744037
    0x1021603140f03040b0a2a0e180a09110a18061401170a0615050c010b0306010f0306050c1608130506040b09042406170702030717090109050a0605 64
    0x80d0b080595248040382c51a25161a00c148480e40609510350300c60340d801d92661115070070001c00c2c40d01c6440402d103a01c4d6912411000c1c14482d40030710071a02031070460030789202a2040041c05988912601000100d03031302c4030309051100c080001c000310b4000101910203c0e49204100c589444034061100600501d0b03100c2d00800481e400591100d4007140c3c40340314000000300181c0580b41d1055164000080c035983d10101c006107103501880c070401048000501d480081400e000c1e00580324000e0b001400254544903495414036450320015002c9569100413410030320340a81200c002007111854500341140904010041da07000f1508503140c66100b45c0c0008640c146581170b1030865580300000e070300b03044c811030511010b0606200c10146454406000964140211549030060111039450900e04030b1440503004e00030358080c0c00d107130a640c0184504400152040300305034910000c803555a803200523100042e540c580d03087d04440d078007098103407001c2030055000c800351401118014000304180015021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 471746483 1250 471745233 471745237
    0x90501080a2603150f060f07020f090c0910140406110105060904080a0e0d0813031712150607020301050906310b040f0503030f040201120b030a03110a050102160314 72
    0x94400b81418800100402c00c04083c0782d0000d2005002c0724a8000b01c200010810b0f4010b510070801d00d1404250721055050040103196824025110a81a070a000210421b20701038040100c2c406d802d17031107614000d503224411811120b90040d01064880f52076090284c5611488102c03011307190f107014009a06850400e0f104c50007150041001c82c5882c00180040384c81503c13068000c1c0e084401c503100b560004501c2402402d40c8110503004d00201411480c01d401c1c4032900120600d0700c1e2600340701e02400c129200b52101d402c10f040071002001e803041980810a680941c40e03003c0d50651804040190015000c118188203403109801c42560007154403d0642144500400000c0c2100000d01480010105105581c101d030103402c0c4a5040e92460343c2c0ca500d503600031511038030a44810b01c00e00046582050a4080070700c11b40c10184400e401200100c0d68444010710064100190b560035041c00384810b22170495106e403c0300080d50750382c000508624224600300390490004070140356404a810074070003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 471747733 1250 471746483 471746543
    0x6091406190911041703070512070314031504020a020a122f0313060504051819050402040b0d0501140a06060207062a062405060403030513090501080a 66
    0x105035030180d0814416000804601c0f8009111810804c40407551022441d8117010803a02070f8011990b604040c40c280741003140303104182050000c14001c000000e03801200c110300880b000000f007070301c2ea52440302d201000070101e5103c0c1d400610000b003410009501090040806000343c10401880303480b100c003281d00401d0402c6e42c10000954151710307498a0380e00f40c00403415190000c00c0303905110701210003008000343c650102d400700742c0c001030820040c10b05000f1015455601c0c03402c0d10b4030f450100001c1e002c42c0f80105c0642c080c595030b42c00050440d540d517800743d564220050030f64001541245401d0740203050024424041c040418005100e9000d9806a402a0f421950181110a150400654000c0e0f003844100481c0040c4500030300b01c0f08001e802011005028241c0464190030500785121003030603640c03583da1100d540f1130080c0400e40380d206c00c6900312985860b0144e40c1e24036400b4080d00742e4031103412504d001401c0000005002000091a90040e4040c411a8034141003480305d000c8484425a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 471748983 1250 471747733 471747769
    0x91d1605090d02060c0a140715030506180a11030a06031a09030703080c0405090412180302060418110d02210603211e03010801140c040b1c06091406 65
    0x103080040113080800281c4004803044c0d0803109045c03419503400345c0400001d5102c040c0c60340000b408106140448002c0000d19070b150030308100605090000c41c101000c4440507103a00d1003902c001c03521422869001c40344450700300c449140c0724141086035801800d0203102c2641c408141080c0003d8558001302203500905000780114070740003141d607017034070404070003884007070f800c00c0500c4000b455442d2085403e2040d88144032400c0c2c0b42500d403501800c960340080c40395069941035081400140c4407a4111019606403070251640c03101c4461219024041c000312000704128040307500302d0076480c0c2d500589040b0540401810788100c5502c101550040c048581c281c0c10740c000c0e001003c121100d1382d1241c0030a00c800700e030949019100d030480d5098070004002c4e0400d6200000041102e07900a108124690151950390b800c54208020401e00f00c0c051400b8502012200081038001c41c01059500441c427050214103002d92991001e080000700641d8842e00d00c0092940e0000c4d20758505406000e060301008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 471750233 1250 471748983 471748999
    0x1060f0b0412050a0609050313080c031f0605030a050a1a100501050d0902120a0b06010203040b0d0510030b0405030a1206050d0615050315040c090e1903091d160509 72
    0x294585882282c0c1260075035140c0a00c0e043c15000c07a5681c0610068140141c0082d030380e854462402c0c2000f40c040398040070705a000388182c400c0171b903400314820941c9500c03103100c2d1449440c0b0403101c0c0014030b80c41e401a54940b09444c070305810000701141d44440d41d40201030914001404240300c00c02543e0848a2040801035040c003403001d0760051004e02440c841b03c0f40e00003400922a030205443d02401d8500141a41c4440c5442c0c041000d284c5259a21010078400782d03040031318058402200340110b0140a01d031644030000074544032112910100119000000c0344000c0c03c250030f0050712030348a05002d10001e1000c12004040c0b00041c001c000440d1f201400c0a4081132082e1501c800802c0100100c0e0003900096800285568042010103a00003c6d8821311000b400c10f0716201c159902a9800006554208140203071184400314501c041d08490310a02e0490403418902255450001c0d0095403034a8081c0103d03801c0343c3d00b0481880e215660311f4030300500c008928030301a6694020300b410142e2108117 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 471751483 1250 471750233 471750239
    0xf0603020d170904090501090c05100f0305060f030706170a020a0f1209021003020406030b0a1203053006180103021012060b0a020f2109041a0901060e0301060f0b04 72
    0x3540e03000b0b003040c025544603600f8280510001030a94a1400064071280c1d11004024140642140c8180041c03100300e900100c40a032061303003d0407103600000d5070000d141e82d40000400340d407549001c0c490700c100c005080d10f103026100c24002d01080d403005580c0081c0700345d00300010301006452084584000d07094460300d04810800c0021190103085401d0900d0640e203c1c14600016150300340d01a2a0b01000e03200582c4031410704100804840e207502456110b050f240504101c404440030502403185d0b00b520700305590f900702c2403103a001043c0d4800825580c80e0f4007500750015500526590340074070421a82c030140d600c40c021400104d500c082c00082e52003850400b08048050281c0580c1c41c82c0c0302024000b0520695503a81200e1941100c1c4103d00960018452180140070601c0146912038041c9036541c0200070a20451116000f20040300780610381d290682040c1130030540d07140360b507020000c1c051051580c40e10801040150310312040d40c02503003044004030b4040340d070104420a0390242001035041c546 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 471752733 1250 471751483 471751493
    0x3071413090c020a021305011d1e07180f030b090d0801140a0f0f1a070309060302070f020d11040e0705010c020d06020418050103050c060a021e1c02100f0603020d 71
    0x1110741c4001c055120313007400400146c540314406040d80d0980d002c001541c0d0b15010001150b200080004400740405404125017550749404600755000180d010940d10756a2000c00e9400c0e44003a044c90782c0114040c500061a08000800503094900c2601c0d03005254850f068056078820304030001501240d844001489030501c400d400202c1c0c241c00800402d46179a480e840c0030441c0665401c130054065203004203005201044800340e5404400c0a052031400c030b02500c00803d4103146029103001c00d034002409600b0300170800740d44800360350003e140c4801006189080240362480c83c1c03444c1d0085042180b07005840e4070125a034007c071541a140c035010b0801c240c2c2040024920084201c840540c28440881c208803100826030518660302c1000403154110b0404034684003c0685840c403400003003042c00011a404a015800030201c00070a16003082498621070a181010680c07054500c12542640c800c2c46e800500d2454a50411380204070214070304400700305032800e13070001940000b80300e00c0e01400a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 471753983 1250 471752733 471752741
    0x1060b0306010c1119031a07050403020d030c020411030106050703020c060c070b030406090c0b040602010609020a0e0909011d10060e0c07021314010f09050702070f090c050705010c0201020307141309 87
    0x100300800400381d15105e03003d40088118550801d07941c503d01194141000202d411440c0d82128644c1403050825280d50300280607094000c1008041001511948045490b43d420848030700e031819500c29103d41e140e80000300250040c44064005104441e00c488040c1018002c07208455040e4003c1c044440c1004d80c2c0180b2948040c004072625540c0c2d0004901080c14114800c024180b03421895603a5880c01c14000e007550b13060f41180c2000d070320400840302c9003500460b1006c070000c1c09070703501403240d5164203070140103208034502405068038086030a0018080800c20807075100040c00300304042c980325002c0441c03040c0120303101ca4448100b0030030f8501601d13194441c908441d041120114026000b6907806c007002c1e20a84c03011020b50b284200a00202000380035996100b41c55100030030f5114504490341c1082c20070b0b44162040cae10b9403800c4181004d0301c910122030700540c000000303002400d50070781c2c000d0007540103ea10074001440000078550001d07102e000c0710a011210342c010740c84c2c20b041c8002c801c020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 471755233 1250 471753983 471754013
    0x31b1309050a050604030f081b030a0509030d1103011806180203090f07060f0f0816030e070b1c06081506040203061f0f0e0a030512070f140f01060b0306010c 69
    0x42c46440b0301503001440403c10a0b1145200f80d407002800c94041501030005070f00a801545420020190303a641040040103503940300e194000041819151401c00030708500c648248000346030f04100c07146036404414001103040719003a1050344202c002400d030b484212681400350f09035500050f0340c030204c400c03400c0d00a1034218451a040d81c034072a8581000e03d10f48040c961080010803200300039040126002038401915030058101040c480c54103000d030001140c141a509420300d50388204140005004200b1a0301400010340610b40e104004c520f44601d40d40e20180280495042c07010200307030343c680070070034414482e02400110780c180c58803000c20010303410051140d90400e828042d69840c60001d401007071244c00c2203407651751061000640040c103030200782c0009030140f10032440c20000188001864181c9552550034961940340519002d01c1e140c6031503d026000c11581c11072619108030122301600c903030f08410700070060720342c0d0f45803c1103150000b1a81640820b038182904000301d80c4540095040b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 471756483 1250 471755233 471755243
    0x1d0d06020f120108010c0806060a0804030c03140f0913020c070603050a0f09030c0507081609020c0f031c0c0e1c02010c0209190b031c050c070801020403030302030402031b1309 77
    0x24480b0841c5410000700e003d0b030040d07000303a4640b2848411140c2084800b50401c07010358185181540b0b140e0040d00c0490040d000404101c800180e12041c18425a00782036041c954800042e9200f15100358008140c0248400b00d104505540b6024141c0c0014802c4031b04010040d400750950b1807820205500400d03000b003241428544480700030703d00d40307042d01c0743c04c40140c401c1c0c0390301d2080c0605003840c51411030150045003050b40041070000d119000290880202c2d045074078096a142c40320344040d0b041405a1051146620012820a40e0150b120303842082030000700c0810800c8844180341141d20080c401e000540000004110744200079130440c2c3e0548160041c1403c02034140d09501085403808101ca030b80040070703000c03454500040d59034041c0a45804088005003082d01ca903035410413012003a03180d40b100340302000801c02c050b80c0d4284022001450400000c541315680c0e070801a01075801100e04a1207801104442c50002072210710764400300002915040100155508900c010621981c003522 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 471757733 1250 471756483 471756487
    0x60f0f0f10083a1d04020705060103080901110102040f03030e011110020d200f0901090f08030a090e091216021e0f030a210905030115061d0d06020f 65
    0x150484007040043c3d49103040c2c140c0e010500c00c5942d030040d0000e00c40c1c50f244019402c4000b48400040d88641105925a10003c1d00f094901180c00000d00902c0f9164008000340501d0000009110808014001154003a2620690b000e0030002da14200d00c1180100100c0c6107107240240301003031086240d1500c500e01070412a02803088181441d2401c080380d4089111140c00065690703801110303014080d0884034100c583c0700803c2280c03064204074003408110301c18255000c03c0c810340381d0307204110030760041100c0d9102441440e103502c540c076182d601c004180404034103c00760000e681808481640c3c0300701d1117800a04500d4414051580055003c01c0e50302c005c0c410880c1200b00984d45841c4c06142862001503803032107402200003480b000c00707203c3d80402d1080c2c001c4004031011a11a010040382e408540030000c0d424000f5110a035080b040e1030300002e4142d03280c01c00d601c206256a0000702d082e01c800d622400c00b4540d0000780700e189494010401508840390204540005009070044c0c40214600c4040034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 471758983 1250 471757733 471757739
    0x21507030e1005060114040e0604090f0c090f1802060910020f01020a090801050115140a09150c060506060c030a0e040b0d05070e011a0f030a0e030c0f060f0f0f10 71
    0x519004a1081d0401102c0ea07400c213001043da0090701d224241e100c900841c0b81020700e40284108a184020281c84c000e81d2251480c40c2001508500c40310300c0c65000001803c2075450700c0c6400002c050031000b0b140742600d000101040c3c080e038201c801072941e50060206240031071000c1401070000508070b10b48250b21a070389c40c54017540400c2c0081d00400c01241d44400c42c03685401600d44c255041039101c2040755001c001a002078940c00b030130b4681002a1101c0883da04c00340c0c175a00b01c542d080d2a80c800c0400b601d800908580321640421600c0301c2900400c0300303208548030340042002502c507402081c1256441000b001900c10b001d0f017141d0703600c180028400510009003401080810811340d074110707429002042c0512405450801d51409001c42c49100c601048541c0120040d505c18241074241c0e41e00301100094624482d50030003100c0546640640c0d40fa2540c1316003042d940c014041c0009080c1c01080700259142c031103854074510030140c4d4241d420309500e51110050340c488001e841800c2c00c0003868008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 471760233 1250 471758983 471759011
    0x1f1106010b0a080c0309070501261008061e130501091e0c141e040902331c0b03070b03070905090105030c0f0405060d051c081602150703 60
    0x1500810342035510540d92400b001005121140091640310368550910601c5400200040c0d240140d0b0028248174010144801c1c2c841aa0000b0075040909a10500100620411940200030840e5403c1e82140d015440d0314600030a1061341080f61540c142003900090100c034035450801d40402c1c041c500000385c90140b0744400e000700071050040c0e0751a00f8260315410801c8006440540103000c0c40c05140c1442000100048403440c0c02c40341e2000000c00f03080b000031170346d4271548000c15841d8002e0043d946411103102d01c031001c0d094007400d540c1c4140034039150001041b0600484118021641c4040e11441c1d02e81c2c5075a000f052004001a01442045404903006000b40011805543c2a0700c2e100909480c01041050141c41600968025000315180e1180c5440380c4141091205c0d0446000c19180d99040119490482e5054094100c1c450701c41c80324a0102000c10640321590541c1c0e40c1416680c8060440c024942d00e40e02d060016441488081448501d10103030301e420910b80c0c0380c0410120800e50316 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 471761483 1250 471760233 471760243
    0x1b01180905010b03040302070e0f01030b040c090e071806060c120512091005130f0b070e040204030b1f0f0e0a02070206280908031204080d1404110f1f11 67
    0x148080e8000017030200f0300d9010803228000340741610350b0074a0b519241c00d41121000e810302c0014410b80c20032000c102003000c84188031000d440680d504002100c12103c48503901e864501c00c280d56081c88c2d08600c500c900d02401414159021a200c440703805030b6555900400e0020720480404001061010030860701140d2149801254803800604140050082d214210740700580109050070941034004002880c03004400c03031842c3c000c2c9480101d0380d00c2e064161b507400022010550b1003840060b0100c100074009250b18007610403a00040c0403185084510500c0c80e9880c011040480e195481c1040100180c00500380d208d105420090308281e11607004c40d8003034000d401d04d503404060a0080c1c105040031070702d00410b0301d0f41a03d40803640520341030765a6200c0c0f0804640c0205150410006014000b0304021a07250000801e000c01600c11032034080030141c5010380782114403070001a410b00349850881c2500d40660401404500c02c901118040002d001002c3c10303000a0101104031602050301c2404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 471762589 1106 471761483 471761489
    0x181d040519170d0b1011070807060c080304050307060f0e06132607050d050301170d02100203060f100e100203040f06050913020a020d030e1b0118090501 67
    0x18990016050500d1490b4000c070302c012101d0035946e0702c1002d29451400071010b40c0d4865031554103403a2104030034821000000c00481c07485011545000085812520610450f450300005941d48401d486e10305414080c2d1b1079541c01c4881e65008140320580d4030020b0420f00598202c425550904140d40c1707071105e0b0004030754074070a11103110a80000c860301c0340e4004080b03800340102c0290080c541da01c01d0184c50300000136810300c62515030300003030709114030800303500540002a6950400030094200404203540030030840305845181e185e0f01e10b8401c1d02c0040d0b45d10010b1408031013040c0100d0114494a640440d4020001001f141108858602c1035a4031807a1036035543e824000010070101103552410300e46440050024541c0ba000580b11080100c1a102400954001d41c1301caa241d40c81e441e103600842c92203200b0012298030821a00d800c0180140c3c52000f00c584a45071201100c1c0300360 = true := by decide +kernel

theorem cover : BRFrame.Cov 471582733 471762589 := by
  have h0 := BRFrame.cov_init 471582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 471582733 ≤ n) (h2 : n < 471762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
