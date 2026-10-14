-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3288
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:13:14.035043+00:00
-- url     : https://prove2.me/submissions/abfcce7d-1cd2-48df-934d-6895ee5d2d0b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 591187050 ≤ n < 591366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 591188300 1250 591187050 591187063
    0x150109030b09010b030d020c0d11041401060309230307060f110c5d0c03070204060b04080a0b0a1104120308010b030f060f010201090b1602070806042102 67
    0xc0000c41d80c0c01d00d08148807032038002d1580c1455240280214183c01c0e160600208403141c0548010b440c58600e07000c03545d40c0301c164003400318250742c0c01517403180050454200e10a1541c080c0055031000140d80e601400d110307141604900d106074400700c400c0d14040f034a031404429120b42e540d1200c4040317082e4501c80c0c50b000c05849901001e00b03401c5004a40d800c031411000586124020000441560704d20000442144400110300350006403007000c04c0c000091003855664030741454031142107a80030400e407c40820240e21a060142d2135500104c0c00c0015481c092080e40024070900c00c0080c5081c1c9440350017034a41d004500d000d801e0241c4000004c0320407446e9009040c90850001000707a950b80c0b924076404068041d040e0580000341014000702d52401c0c4c00781102e02801d4824440342c1c003a0303240c000700122050343c02a254115526000c07078100065038a10203034080c07403540300141600484040000e14150180d402003980d907201341c0900020aa510240c0c42499000b182c2c1210301c5110580280d2a04a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 591189550 1250 591188300 591188303
    0x30715050a1b051308030415050d0e16050306070c030f0e0d0c1d0903040302031b040b0d1103012004030201080601090f0b04180c0206010605090f04020714121215010903 74
    0x70b600407012aa2a584a80207101e6081c142e00c40c124030f161034452856481c00b40b0300980225030341509001412038000c5000d42184140100c0205030b41c0c1000416600b0440d0004c1000f0003c01002e01c240480d1509000e840d0f4051745514042c24142880e03200180044800f4402100307018840310107100a840307030620380f00116040304680040c00e40d0b03000c014091040012082e14011701000100718082d10200c100c1f8201c0781c0042c010040c40d001401907a20001d0428145a44156142e07400c8001d034075030920700c4182a018070482c1d1900c080b05400d05003501d500c410b0b94120344400c2c0b803000b400040d210050b23130f060325020720b00800b4540c1c9840058461030100d030405941c110000c040000c08448060040090300d40c4580d035440c4800390804200291034003110310002682007140148280791041010303211801005081ca911b8601c0324000c102281d118000580c1c0c01e102441420018040420000420000b100c543d9498200401d5081c010600301900c50907a0200555608825030f128160b204045c0d07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 591190800 1250 591189550 591189581
    0x80c0f0304080609061008031c0204120606060201111303060e07050603090a030215010510080a0b0a06020a02040b091014031f0c182108041703120108030715050a 71
    0x1142c40c0e1140964440048800c070314140314030000a10341c00c0707189600008a4200b1401541000b00d032450070031200554420442200c3e60030302000624900d140f01c20066940200c00000c1d1050502200900795464180c0c9500608800c10000f40a481403181c0e020481b81c120301c000410000740e9410340d0426401d41d010543c000e03008810301c9840b500118003505020310079000c0b901100340d038460b14100307a4424440c40b984840341d02c40d4200918080c1d12955801140d00380d00041400710a4006401403200d41c01003001a03006030081c41c01c6090611401c0c40080b01203a1501c1b1a280c000d10400c4d2017100c134069010002d842c8000000151420484401030301050a0010318102c4000d03180c8005003031103800c03980080c1c030a29103000354502030341c0c183c0300341d52800d44820740c6200c4d41d000404000f50181c1045501c1c403400c02001610800270045601c812590202656039482c440050220040041c1c101181a030401c014880008490000c1c107019038001020104896449428140c0104140d01c1086544e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 591192050 1250 591190800 591190807
    0xc03031503080301061d040501031e060b030706030c12090507031e080301030b1608060102030409181505011a09180711120306040f0e06060f15040f15020a050a080c0f03 74
    0x105e50480c0035503000344548004000b188404004001c1542c00a01c0041c0051408800b0301110803090b10f44044440c7c0a088003203210b0030341001181c0b4000a07580028002036540309000540340c1c0c000302091081c0740c40c003000d100100050b164503444d043d071444014141d0381d80040004d42640c0d040c824500d103541001c007035a1250b0b9281043ca08603c001c8903403074941440380f41c101c03407102c0c0510b039000e02407003069001394186810484c84074014a04aa50942c003403020303040741e000050740c2404284104004081c0441d0b039506d0001c000a00c1200c2800c0d800122100f408010340d1a01d03050001d1900450041400740180c84d090400c0e00c020a080ea00307550720313004604490f07001200c3c9800850040000b03070ba04101703c0ca0724882200856100f804003500329003044000c92030601e889a00f003020018020410724103681a00601c59041c0d0150740100000c6100d10030400c040e02040315442480501030028100c2c0305241da503241d85541c9810f400034843d000100300440355000800c0400300241109003101d54 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 591193300 1250 591192050 591192059
    0x304031206140a0e1e130501150e010b0a08071416051b011803120e0d050f060a0540110f03030c0714040213060e120606010c03031503080301 62
    0x910000500195000b002d0f28400061a00c880089541c030501c00102003002280e501d40229064420180146240315441c02030903001c16001e00c155240101d085a210380c0b994030300448800040f03416403011090141c1403018121064101c0301c0d89074020940c0c034103c01a160962070001a50280c05034401c05080315461040402c040059030540307459912000a028140000044a006120032915021210911000c0000494800884514041318102014040c8002000c102c1d1258600c00656440d40801c114446050040c00110780203050787e241370001c0d2804090380c0d2805110440380c5a24205035441d00850703007580f005c0720302c001814800a418005010b05244c0012490810340038400c2e282c0000c2c0c90858a4004100e402407a805070141807c50f00e001d14200320307603803e560035a4000341c00304400640241c2d815140700c0500260b48613084040c81480900400d20050150f0ba9419408202032080c10323030704410107811055241c980898095100d01d080a1612801d5100800c41d480c040000309 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 591194550 1250 591193300 591193319
    0xb100b0d0b0d1509110603190209040209270c090d0b0403090803031f050a080d180302150c0c0f01081609080d0801060f020a170c032b0605030f0d050304031206 70
    0x30130f40b801503510202201c101070401c800c622003a02d031403641861a03035420140c0562600607200262005000505203030f001c801140c1e4071060b02200f0b6070307171030202c50541017040b16008401c1d8014201c001e299003040d8004020400310006142d02410b689403800c0010201886030030440043c2034282e058030385030b00740a0010080c2c1544042c0c1c028040c644034601182c3c034107109604d44200d800c480001c016002030983d06403495848800040e1002158900200140e102c41d01d0aa5025a4406206690301d02441c441820103072020201c07441606c1043c203c000c0c4c1c2c5ea2080b407091704840b02000072104800c140000740d0351110305510003420350040d51742d00c910058000c0001812541941c841d040603c207103540490701e0394204400208020714502c05040e2010300d0501074890b10803800308032407820603541c1d603071400d0004205280081c2031851907001c5d4603003058051540101802e40c01400310350301d9000c403952282c00c00c0c250001003080100019080c5031146113014204109007500b00300803507d551403031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 591195800 1250 591194550 591194561
    0x6020d180c06110a08031501120e100501091a040c0e120d110f0303012705090c01032706020d0204030f030e1f05032e0b0301030b100b0d0b0d15 63
    0x6004600141030750b0748030002c04201500019803005d9a5451956040d41142403074114a0b801030402024500e82144102d01d4842c60007000458401001100148030000d0151981600490740303036070034862015292a110f03401c002040c84200c40200703d25125020407108a0a1403013102d0f400850514024268040032070703000d01401c07142d03982c520420052a4510349e1043c107840898150f601c100700411074101405d911100a08000840d032140c450303a100f044040e01d8099600100542202c0c0c41c1c1000d42d03806d8030800201d95401480342942c0030385180e245d841c2e058031820103820a60001144840100d05604481c043e60788803a0050740c4140c1ca09000380b00c4066184401e000d038040c400d044036581c0041c2000c8014035100c0d82c0c2e10b0319550364030350081c001f03072000720028804e80c6c036900d02000800b103001c003103a025000c03c0e40460380f25851414880c20000d00030f0500d60510103810400d00ca0103000004860761400181c1000c200e078404100070a140c420b02600150042c001c00e511440c5034200b03504134 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 591197050 1250 591195800 591195809
    0xa1e180e0f01080f07120c05040e1c0e0a050411070b04080d0509011b0e030a050f0c0f0d08030c030408070f06050604140105010504050d05190317070311040306020d180c 74
    0x722505a0b03c43c5292661070000c1c4010b0344155002d040100700c020010700c000c5000d41d120342c60403504207613075201041c1a11800025043c00350006c2050104640d0b03078040c4e450214002e4a0300355410740c0544003088840703039a405800e0044d615216061410183c01084804495100e00a00c1c01d51406080510090700310407519a803050600021a030f8540050240903050404401548a42c07005858280c5031818100600d5030503004e002c00340000f0580901400c90740c03480c40005404802407180c1007000803a00c120b07003d4400c03442940164003066801c0c0c00e07254082c0f900384510755a40c5450800e802e1a01413110020683c004016544041254030382107180682c000380e800380164810002c0800c0c80c0c0200b405070a002031740c01d02c82004a490101e4090900c1030040050b00c4110307440f6100052000c0c4018000c1c1c1c003081e0004030380c50038810103840c0d007544080c1e40c0c6000c004810b90404611818456884042c040a402094189004030a40d22258100041381413000c5038000310300c0c0818a2407100c0c8034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 591198300 1250 591197050 591197071
    0x10305060c041a0a020c04060305011b090f090b120f2a010804110424050909160302060904020405040906060e01050111100203150303070b0415020a1e180e 68
    0x100701019885019641a01c103e248024041065106042580d070802d0b034480045200b81c51810015032142c2c450000034500440021545140c080002440b0311080d10000041102c400c00c00c0080d0060b030403c8006650b00d81d200030540e049a0400204070f40500c0125120a0080b500916003c0d1707000284155041c08d0b1481751201c02040d440c403220722102c600710030360205400100040008a4805540c126414003c0000480001c15000100d6160715180c02c11a64001100301340140d14015012590200c80075004001d4081500807480503203000303101c001d001e8080406d201300f280d529034050310080d000c094001c011040c01c03070070024003410b00c3d807081045014001001050340d5201d1b80d000040810303180003c00000f00800031840c02075100a1503d9118084a07103054283e0340e0038001811424018601e442c40340c2441d041030320f98184a1032884400900c10884241041d800095003441c0c0701280b801402d151682c02e03070958190a2060b00e40100a420b25404a403131840c28032058001c0c2540c80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 591199550 1250 591198300 591198313
    0x1050a06060f0e01120612030305011e21151a1003050c07020f040b060705060f0112120807021606030207060b0d1703100b070b07020c1917070b04030308010305 70
    0x545103841640e82d00000903e43c06a6203006500079485401130b80e000d050002400c90f540c00420b60605240d100880000b0344400040002c0401003c0d000c000428010607100401c0c40e1104840c1c02806035450307600c40c00070340404c0600380440d07601d03a00d06e20781c40f006040c882c4200f01c13131400407115041401035210304504a5840c0c5264820312900c2c3c81400d03e900c1083c130f03000c0f0039020130041c60f104031240c03588aa12000d01907050b440d03036800340c55050311030402040c150411080700c48513400d058000181d500c0c1ca200514021916080c404500c0f044103040c8943c940d00c1d07102089041c03204441c203150141d00c414200043c0e40d5071541c010810280614801c103c030407840300030071952641e80900030307289402c00c0d02e0356002861b040d00116000b441001e000c100c155520b1202c42c0c001e400011f016120341124004122004d84c05214071441d405080301c603110700300c18001c0165802c100034010014030407003018112880d6841045041d0107010038081e40c50310345a4a1500030507005090000b29080c1c007425 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 591200800 1250 591199550 591199559
    0xc1e0d03110301180e010609090201080c09060405060702030c090c0910051206100c06050a14060f100e03010b03030f03010f08030f3414010e150406090807020a0801050a06 75
    0xe118040304010041c0c0010300e141d2074080e0f4142800c1440944c840000e5541c040c4c003d082509104102c020503040b500400d46a031180000742c0220802400303400c408000b00840c2c080d55a9401c22103059607001c07030382030382c82d100240082403034150010416600704c5000424442051803240c090301c8101030032240201031018070394007160303180960341c42204094400d80200d0041d1a2084620216a100380380a42007003100340c4440e019540c1c03e07900400310554540d141c001c1002c0105c1c105500c00d40a6405c1000c45c0302175030118004003000c0b080f840030000441940705581d0380c2908241c0c80c0c0c0346c0060131a51542e18415131120340750300c00c1c42800442885030030b0000f0281300100c140c4404d2521000312605103a1000314031059106c070404c12103184805082060201070f451850240354500800320050712440810301d5500711081d84d00010701035802084840401c09542400540c0301c0e511400115111039185032a40b084e0103a40d4000f9401804c031000440d400c032056100314424aa841000d01c1030a617035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 591202050 1250 591200800 591200807
    0x23031912032007060905030f03041a01030302150901021308101b05031603020d0c03020d06062c03150403050309012004031e12020a1104020f0a0c080c1e0d 68
    0x5081030041c000c03860100141400c60035000d083c0c078134014000072a14202c01d03a600360031980008007049032010007109001c28042001d000350003c651504100703800b54150b48001c1e545440c0c02d60700c03151104030480000d80c401400c0d010b8400c89069002e400242640b115150354444100050002d401ca1411181450751418540080c00d00250354581358515142c05220700c09401180c54903000b859020009a01e07100010310801f60505408d550042c0c8a91809072030009a508552040e410405030700c58050780c1454242c416107503500300324116a510b08040700868205021100e920b000700d010f100401c400e150300800110722a0194400800200e0304400d0112048160300005401c000000e01c014400100c0c0c0e4501800100059841c401e000820b41e503918244a040c030a01900580192100e4010002c4404055030070400840d420740c2010b1242000141c54000e980d814801c01528140c00400e100e045002c680ca80d6403880140c1e04458410840c40203104290104804c0d1885206901e0164034071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 591203300 1250 591202050 591202061
    0x1110109020907050c03040e0c070312200c01060b030c091903120c1a010828050d0302031e0f070809010207020d0311070b030f100503162303191203 65
    0x500524a42143d00c2d808000c07551500b001c04005044e00c02084045621608000200d22644010540580e40c09051800900740400e803100021460b0030b094804851182a03042c0c41d01980800103c59101c801c802c034507902400251784110413080d000018021a80a40303401022018000d84210b01c450703010508403441c5031102d1001510000ca4805410314240c0700d176100b405120b0103038070741c0b41000c0030000d40307414045020383c0000385503880603000b1800781680d021102c84501d403022074118403810342d44545484400340c00401007010b500000041c00070562446010940c0d40842d01d03014586000c4541e5100360600b80d80f0b100c04101d030413001039803240050080b207411742d41c09444440a0515540c0c2560208268a01a202400303200004203c105485003c1c62103484180c40001341420f00864840d056001c5d03803c068060740210004294099000801c0d200b21000c4442d03003800d8500c440c1c10b1412410685000f01d40c90b0143c04a002c1c00501e40301c141c0d080c2c2502400054140c070182070310680c1201d9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 591204550 1250 591203300 591203303
    0x1a04060203030c033402101a040207030203190507020f042702030106081005060f010915141309140c0301150804050a02040c20070e0105120c090901090201110109 71
    0x81c000c1001855054401c8051600040a08001c42844001c1c01d00070180440300701c181c2034014003914141d200e61743d0410541c080540c1544080060030b070030351505031300c20030841c090360700894000030313044c0405208104446088000d81c44d1490f04c9454210300a18a510100f0140d2003140850034030b51084c500f5102302d0510000404009000d1440201d0901420b00114400daa06541c0d5450000d20760300144041c103031040c440345d0000b400d40342c0381040156640c91050302604010b004902804010750a03140106038404906008030305903a03d0b042d5000c1340c0310301c1d80c00c40c001e0b00f1288c034001200902034018100c410051415502d42e42c1da69940740206010901c620403050200300c05000040d80070700b2189401a0041045c2c82c020300e21134001c101500d000c1405000050303035444101e0000c64030104500214100300307000e000328a00d03100401c03101a006004091007500b07041c40c02e01c0010400c01a80f0a180006401c034103040c42c0c1040507034020144500103a011490040134803032441e4043c8121207406 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 591205800 1250 591204550 591204553
    0x30f09060507110a03050d0903050f010903021203090c06070c080609010504020f040903020a0b0114090f36150702071a030a2f030a0b040203060d0201140d02131a040602 74
    0x1c0310a0f00d07402d0314083e40d11201900042d00c188003002042091100c821900c0301c3d03459064a444c9140b80103807a1540460740784000da4035007501580004d03804182c0301e843d80d05501026031a91164401c05040984890010760f10020002d0350000300705400100d0421a1158016922141d5440380c2e082d090390001c0b98002d41c40310031041e621102c1c3c6016806503841601a104a031111402a41c5184110500703030015004c0610000c6024010b25051482070351141c485110780380e803800c0c9510b90540c1000b0241c0600d50f0807080307295503081e42c80c0b00c11000740341c0490700b02143c0101610703042d440000c42054074903900600a80b0400303d1007802c05540402179030110a81146950b5400c1c4113800180000c1264010740032055001c00466035000310305080091500322811b0b500d0614008000440c1c820b8403410b80214010300c204407190742d500c0c5102000d10340a00b400d4508140c109520360036485560b0f010031904d4404140703210241c08000b120f50940345180103d811b240d1a00c3c0c62030b402400b4038860720005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 591207050 1250 591205800 591205807
    0x106080606090a09030e06130f090204031b0303051206150706090605070c0305040b0904180627050309010806060c071715041502090a0e090102130e01060212090a09090807030f090605 80
    0x106e041440050615460f007023000a03040343c50740c90b6503407111a5a8000144241c020078103000b80580441c00103640741c00e0002c41c2c000ca03880c50350301900c1406001010316214100c480080c1044d116100142460341940c1c4100740c0d64011132418500034420700d007082d1a00d92810340003800c440d0142018000d080c0e01912950304003403404c25015140d074032222205400c40c3d16408e04d04584100e485032600100e20410f00461051041e5042c0f610180740408410510458800840301080f00882110300b071020030300e0030722500d82d1024041181440742e81c0e0f4030700c070314031642000250081a0401d0000074015410644140c030001c103910f9800b500c826100602400350101c0c866040212075402880103550203081d602c5000c1d038915241050002c02c07101e5645036500094541d00320301780360500344040c141d00b50305911254142000255a06032060910b2100d860000f0341c01c01c1a075400c0451002032038961018842c00d081e0385030000a82c2c02c10241240450800d154804006001b0b8500e0f00549101c0e41da00c074103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 591208300 1250 591207050 591207077
    0x150d0e01050601020c062208060702030705120f2217010e0708030703080106270b09010f110d0e060c070602071a0702030d20060702010c0e0f090a05180106080606090a0903 75
    0x2074480300d010701a0501f00340c031500011460000d210079807003007403a1f4001d16240d0849007051800d11240c0c8030481081e00e000c1000030403020446c0f007507a80c000f030f0b80c80020030f050240700c2e115407540709140c001101300f400d030129014002c02d054202c0f5120400b000e0640d10b40c1c0d55915412680c034015040001c1c0461801070050000354818007a20405000186604102c5c1c903403900001500d05103a00040000c42000075a0101560001c500031104005407070000d11000180c00303040d1b101c44002842c002002120300d4107105540d00d00041c5c0710000c448200341d408180c2e0b5000083e59030400c078842e56006400c1025410f00c0c6500c09401c1d01d640c540c000d4082d000c0c1c5070007000116080d071900395003180c3c0d07180b1b494949202c40b034040008902c00c0d102500001040b050040c0042d2038100f404a1380c40c400c00382c2411091843d16280c40c2d181d00911824004607a50b180e0030120a40c8841d6010345810961030b041c0006002840015000e001749001e0300c07064000e8076180c0e800030a9403518070380500480c00d003d100aa = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 591209550 1250 591208300 591208327
    0x3170903070b070506163f1406010e0d0b0f040f060216152007030e150334120b10090f08010605100c02150d0e01050601020c06 56
    0x4420000142620810342c2c541403149a030740c0028109071010380c402400c000007083c0310610481d54050f541003810001e418800019000e150742201e07802010006500b544080c4003410700300c4401d40251000780020350884171400c4541794229599030004540c00d40c81045400c280c25010b48264101c0e551515a0b80c0f84c0c244681c4800014004a400fa120a070244010441d58800351504241c002400d454100c050f041201c1c00620b81d044405449150000a45003c045000e0440441d009040300546502e0141010794107014109203242c0c105a814121011400c01440110710070142c0002e1451060401503070051860230300c1c20506034590303020600541c0c00b8003940c1d0803a10f4103008500415502d000201080d0b0360200040e544c0c001c45d641e000c0034052000c0307039125507025004030402000150300d0003001500450182e1101014130030a60101e4040d91036503280b85040741614207019a039003901889880042c9043d01c40c01c4032079440c0c0804507a0961000c40c0881002d0300c000d00048c1041c00007406503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 591210800 1250 591209550 591209557
    0x3081207050403150f05180703110d0f0b07120c0e090a0605060a050403030e0d121103070b0f090f120d02180d11130603080708030a0e1e0111040317 65
    0x9050020074000000001d07000c0750715040d0700c0b801007008180c8440c481d074008103551b800390052042c003420031104901c541e40000d50a0440742c00c0444103100a910340c0108280d40400c040240c8013001c1203407003005009100704101d002d1500caa40c0c0700650019030804400b181c54205245000400304010080c840c03800c0f0000d01c0d000a00c109002036601d0359040001d5641e80079958250124102140400a05401101d000140c1d1330035074802590b4082a9215825005031101030390a000040210000301507040007079800041d805050f91405050608840700c510304d00702c540800d1403040000490f07510302c0100c1ca07400000c001c214401d04000e0001e420070082e401881d00713400c80060310450411740740e41e580c0240100714024075441a27540001024002c22851410200c00c1c060308040741000050084002c1301c0b03405803c1101c5944a40303a91054102401c078030030702681148a04030340c00b4460b200d100501c0d0004032409000700004411003100c4240c6000764800909040b00c0030b08041b40c043c200c0c1009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 591212050 1250 591210800 591210811
    0x101e1b1101050903010c0305060307120210030504050a08070c1404020c1f23010626010302090403111c02010f0b1e030f0304090b04050105010915030e19080706060f030812 75
    0x10b01e0420020740007107400c5400040040c000241c07141c0034000c0c58141801000e003d050002a0001580700c180c001c034400000c400c0c440c808140c1e581001a0a2100038031198206903480f42032142e803910b0504001c10103049a000b10300100e20502d044520342e203003510031509130f1f40c941000f40ca14074240035906003401d0311340c0f1704080700a503d90844564219200b60320106010100c0320200c41941003a8004000360342600c3c4440f03191250f02048041e01d40c2d280040e60469604407080983c0c1c1e91785242c215089115180c03040382c3c0d8850b94000d0460707807031201c9050084820b6680204064201140100f007644d0b4000c20041e0003e5880c0d80c070040b0422801415405480301504443c40045500c00c00c3d455980710780d000c007a04656a400040300c0345824019607004003001d01e00b2030555030a005d46030702d01e020803035030010070b140d0380b289208110282844103144230000300d140c20b4181c42c210b08040c065603004150440300e60b86031000c04500d16000514130002d581d00104450b0520002034004103111501601 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 591213300 1250 591212050 591212057
    0x2060403030e0712030908010501150c110a05090906060316050f0d171b010c050307050a03090609020a0b09031e0604170d0203010b040e0603011119030605101e1b1101 73
    0xb408151840c0d1130000801c00f91007940e44099541c0340074641d600f15401a0402810403542ca80c0308600258004540d07400b150300b044c000a01c81516400190010150741e101d0341d0401c240c10100030813a000410b0f110f10422090741595141d060041503c000b40c1154040c99500c0301c0c0f00100009103052880c140c90440340703e12210b8001001d505084100ca4001195644586007200700c60f00f001d0b1008e0044144100361030506d18294140f03544082d140e13028140d9180201542c0b4400802880441d402100a894018004200551700d80101c0c600c84da10191425000e17228101100440f40c4c204a4a94810a61003000e06040c1d141d0f13556840b6211110880303014561400d00030318090401c0791000354000c114660400b90340d1031a041b620700c0502801000c86120703034948180d032076105400c9000c4403d1482040403140d02072158410950080450fa0002c0f0b410208649041c070f1000d8008984001080d032644c8000240014004100ca131044003e0407080c2d17503142d0000049c005044410300350f010420504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 591214550 1250 591213300 591213313
    0x414061509010c02130b011e080f06060706060e0723030106051b0f0309101b022413050a15141e13030c080a030512060102070f0306051e0702060403030e 67
    0x100001c05a19407028034140c81ca58440346c090156801c1114544003003c10b200c01012054170160150511000412540f0060003a1000070410750710070044801e210b81c81a01048000c0e2180386412400da000c031142d81c0454031649403041204022802000482d184012180c6142e0030003004032015000f41d1021710100032170490000c6482070510072a9040c104417001181c840354501304100f00c10750405664000e2003810300f44801160100195803121031740649403100708415250028440d400382800104040c500403400c0c815250905c00840300b01c0b5000c035950b00046480e03d100c802c080c800c5140940c0850f0211030342c2103208000801405103d0308800118050f60511010a0346961041620520a00c41c2600500412100d00e0028000e0301500c0001c000310015903402814910982210000c4683c1501c0000e1185e071080080c20041c044481900c1106640c91420074050502903509090010b03040f041c3e1000c038040c01c182a485503030355a00038452601d440d10182c0c020512807140704010700544 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 591215800 1250 591214550 591214553
    0x60309023003030a0c020c090717040201050d020a0c30120209100c0308070809070e420d1109090a0b07170907030305220812090414061509010c 63
    0x1d01c003451285201c4e0b0800314180c07084480090500f1010107004d84500e0300102800b0065a1180303c140c1039101290b04110140c0701e60005071414080c254521354160300000c0d01c0d240d0386500c44010b5060034800c501e459a074514442c440140798a024400038030420300000c8041c0b1103485918001e0a01c500031600510b801000404115504440d107070607000300750307404031140800d5403000c3c2d45076003c1007a01c0d004950b4200840405c0e140c505a210381c00b001e811001c081060003100400741600c888140003481c408103801000150101501c101645591800341041e507541d05046034420350843c0d00949840940c80b8041c200600380d00b01401c400e80d01c0c40790301030170000103142a050714020b0100d6101c00d00284071030200c5d500703100d600801502d025000010304100003070b040020b07511018181024000c1c08030201c05007002c0c1e401d40d544115010f100d800c000c0c011041c20040241b403090300c1a20248800362902c030703a064a0316000c0d103d881c0c2244000d2400d210840b9000050084103074141741001e080030741c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 591217050 1250 591215800 591215803
    0xf05040b12060f0a0311010c03090f03030905180601081306140106031b03020f090d030c0c09020712020a02010e04020a020a0b0f0603550b060a0603090230 68
    0x400c4460003200c1d01d8506102c1203240c810681c40a42600300c904e11038180c11940c2e1001140100b9024a06025034026a42c2c100340c05200c00304007800a072601200c0c203640c0c0e410020940e44080c8120f80c0540304003d080203842849444a81c4500d4040c0c4840744d5503198075607481d0951050010170740700c499807a403850003d0500600000d00078842c550f80070501210214030030f1520040c1c1e03040c0e0f0381414070411030450a86400d40641e01e1001c030451700700034400032a0030291100040c182000700460060200841d40000310380c042c01d4140d0041c60281d0440300c034a08240c2c4da40d0380c0c2502c01790204011820b0308006103000d800902c1d002c0d40314416a02080390035598003011141c145ca400c0856081141000b8880c01e0400804042038401c0b2481c0800d04030f140fa0340100c0807082d920407010311500504a2407800c0800d403005a08003010603900701c0a80c400e09013142d4200c010f6030f0582c0305450076500000c1092080c007030b08040b140c00409a4000200008200c080300b5a0340d45054041e600103000d10b001c0c0c520 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 591218300 1250 591217050 591217057
    0x1030e010c0206090c1e040f11030403020307052406041d010c030618020307090312021c0804140705031f091a0f010902040e01181103071d040e0d0f05040b 68
    0x8071900200402d08020075424100344080141070f001d525600c0007501c40e801800c02c5045551b1082d41c0c001805c04501e40300001030310501131101b02184001050004040d4000001c1001c03034050b00c20f640a1940c21011180f07840f1954501d4100c1800810200704a450305600104840a41010304410401180c2c1c200c1d0a482c145c030407040c04070340c1c2c466013001a44c101400c800c0f42004001d204502c2c40c03800380400381c01010b8070f000190042c00d510307105a41260007049041d48091880094144c4006180c0e0300900140044030b085451941d07422140b20289000240c03501900e03c02009072120300b40c444192102943c0420314640300740c1d00c511030796000c6208030b4518044940c000c9025007091800520b4002c80c00e00690000b02d88920401c000c002e00c0b500c00a40074103651024444400701040401d02a000d00a580c54001e1200c0001040c801c2c91034101c1e0500c0342200c0c1480000400c45003450810007142d13100a801e9489130882a04451842c3c800c604000140005003015414542c6412280c080b640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 591219550 1250 591218300 591218321
    0xc021c05060910110c060103030c060608031b0c01140a0c020a0e091c08060f0607030309020901081e0118030e030a050d021609150306020d09060527030a0903080901030e01 75
    0x104201d400c100f100800703008440b504000301e54040e1500d8000402d0340c0d40c4000500c00074040201c1e800c2d00d4002c010761500301100800000040340d884000081000f0013a6403400600e107032a2203510200b2100c0d501a50640c40070b002c0750000300d8140301c8000c1042d00c0300c5040c20070403644040f003804003082e0b030509003034640c2c06030725070000510f254003140c500d6254030b80d40040c4040601c46003404000c1c8a56800c4400b041c80c02d0240c4213191910418034068001d002d200304001c0d0300c524100e00104076514002546643c071420036201d1440001c0203c1994201d41d04400304020100c189041b000129014040c1000262405070460b60341182035143c46040001c0a440e0303100580080113095034003200c103824100904000b480030007c41c00c05907040e004040c29072100074901c40e0041040092524150700114101e5000041441640340005425007841c4024440c0b02002d26800d04102444400205492400c1c5141d201c1d10040381c05c5480c2d224041d040044041e042540350945018820402e000390800300c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 591220800 1250 591219550 591219553
    0x31b010209030c0108150411090d03020a0c0914183f04060f0e030c0a08060603161208030a0b04020a03051e1b031305070b0406030b0a03030c021c050609 67
    0x100091410581842c1520644030b0400c4619406c0c40303028052080050350700c650866000654030420418051580256100194021128010344041c5a00030401049262044d200c011641c4c0c0c848407490b040320400c001d01101c4440100000b1814480f10710b80740181c07180701e07080765a01c0d00f16802c5000060000240360800140c40c482e43c41c41c14030411640e800701410810021705050410b03100409500e4604801400c200070b809003c0e0980c3c90900070a04910005026070468336110803c0d10795410095403100d000b4031405901c01002e14100c030191059030782840c5448035517103113500c2e40303d40b540003e0003806400e0341d138200019041d625403000b407031420715546020a00746080c00214250443c890404105084180200f14280030a1640111640e010000107074803920b840b1081039401001a000424900c10300e1740200d40e0200640140084900c503503414002c4049010034400c40600b44d04c00107001c0391451f0944401417410a420508805255602000341c03400740c1c48440c0790040c29a01c05455 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 591222050 1250 591220800 591220807
    0x204031b0f09061802090a1a0403050712170d02130e22020109050d0503090d050c09010602070326120f15010e03150903070b07050a110c0901031103031b0102 69
    0x604441c4018a00400e51210104115440c1001414504452540340e82c501c9034002120500c595440da1450007074031203410716030b56031144084030401c0e41c0d01c180400d41c1d052150910000e949001584443c2041e50300000302c24500039a0100042550001400445465000d0207100c840001541e2900c000f41034044c0510044d08148001114510301c400f42d5821400e040c42c01c280150340c2006011045400c103480d504c001044c2030400c1820340c001d00e11210760104840c84a9030510500190f170b000610790403980a006a42c8c2d401301a65070703c400d440020301c103084080f801c04140090302500300c040205054142e1502d1102e4032484804003089031603900000c0c2c040c0c103012400407211b18885401d030007824110500d482d850006680c602030f00801a00100300d071000501541428420303641090781c800540391482c14400c00241282e0010b903003600c0041c80070760841110110000700c2c403146000241031001c0607400d40d00c60100322585c2038861901031104014201d118070f54031010b03030401307200b2200041c0c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 591223300 1250 591222050 591222059
    0x120715050a0305090102090f0609040b03240702070e0a0c09050621010b18120109050303090106031a0115030b01031805070e06150414010201061203110d1110020c010204031b 76
    0xf1142c0103800800345a04c18002111140c582e000529410081103a20030348035040000054040c04002c0c05a5805010324014065080320303800d01d0318500e410030400d810b50741da03031901c0c2265a00c01c14824550304003a280c0c0401e103010b20360350100e80310400910300740801c562034002040035544030440a4000d00481c829140041c0840c41a1074050305102d107245e813901c4d1340303c000315160f182c03922040f40c403a00000e01000d02c100c0307096220040e469880070a50340c030307494995000d40c020403140c40161880d1020800307090900341c40b00c1c200b605a801e24450056904240d850443c010a001e0b107001c0c1c141035a035602102c80700c2038402c40c3c241c1c452080c40140041802c00701c088401c00c101a1410340280080c190941032617031602c00b07035402e0310380c2c40c0511421801401c00407801760000340c3c00011142c0110090800b45603224100031a02131001c4c00701d070030a081400c01203070041402d0021345403581003215a580803c03181d40003804c80c5844100098103054480d1034042143c1130222081c070700011140020030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 591224550 1250 591223300 591223307
    0x5060117060f061209010e010204050109090f2003070912031706010e1203090f040902060406230403030905010f0207060912210513060206010315180c0603051014030309120715050a 79
    0x21fa581554100940c00d10f0b1030000003030100c11035030003407201207504c414002c5c8050286a005441d84048085c00c1d14040c0521120000300c0c2d401030b101000000c2e202800441c540380c814069640b060741c1a030394400007919001c006520100050541030420400c40c0e6032802c959100301d010000300c1c441601541c0c3c2c5603402c0702042468802d4089d030310b000d9800d101c50907001d03035036140684046036020300344400802c0412030725040258051503a440954070100b00441415849034081d400d554007a00d80203065100050181e03031700c0d1080d205020004a6826041c007510410498001e5014460100013402210a8141903100b0b4100d217848400648040b03032504900d1940700c0680003d01042c00134010702d504544810a030450f40c5205005140d840d1480b8451085c41300c10118504c1c2d4115600c01c2d16603480d40c10003000340105540b0315600300350b802d0022820302e100301c1c0c2400a80300300034021b5141141d0b810510600c054104401c00890103034100008030140c407210920700d08440c59403442d80e9064a0712019 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 591225800 1250 591224550 591224561
    0x300906020c0d050601030b09120a0503010e06060310050f040b0301020c010b100f020c041107081603090503030a050301030b040503072018010b0a0c020307080d0c02031005060117060f06120901 84
    0x1920559107004040b022820100300c43d0706403600481040345554502e641c0d1440c0c00b4502502c030090410000317861460641c0240a107048e280034803014055629540101f00c207501083d1411041c00704001d004200e0313490302180d09018500050004950702d56113900190072a00701c40083c0c86141d4540000e5403081ca000c0c040920051034030b08207640c03c02e1240c400250380302c0302d950042d809295034000401d1030200c25030a90b0507095201000595402c280c124005007204000c0044000c10080e1101060b103140110a503184d171581a41c0f028216803a540703503415079803000740c0140c07141c1c0000c004000100f1080e041c45d4200c41d422000b41800704400600340a0710402111580500034904801030045500e03203012680c03902c01a252444241456000090070030055501c400b01074401c000d49103250f0390701b00d014544a240202d0a0310ba46106070401002a1070088841f0390004480c0c1d603100044840d4024226049100075203070255290840d00411040d900c00104210000303901810000c10b1034090151 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 591227050 1250 591225800 591225823
    0x70f050405070f110304030b04080d0605030304080a020d1103121e032815080106080c0301060509040b1302130e061e0a110c0a03030903020f071230090602 68
    0x4005a19040400a0500c10b101243c01c0410250805041d03840f441041620051600f090850446041c103141202c520361006000303240759401c005001440b481d0201c207607401c8980c144054001100c1035070802c02501d503140411a503801002104204540b0100a03000031a140040030301c0e030780c2e002c406e958510380d10410414600d28904200f080801c8009620a0024a03602101d04808103940704031400586203c0040036084020301c000000c401c401500880200d0b00d04e02c064030220407462040c10309a4981c2d01940f600f1081504c0858000f841000b070459020304003261800c0100495400a01001d000204004809448042402c1220010320455401c500e04055000c5640010303980001b15034402458807201030b58680780307a0620240f000440f5541b40d28581514440c101501e40a0018484d0070310070760062041ca02130405060000401c0b8080d01d41d035024241b100b003000d07030301c072002030713035078076001c0196403228030007101440800f801201d080052900d80601c11030411400a00e405210f610 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 591228300 1250 591227050 591227059
    0x3130b0702010824062a06061014030601050318190b01080a030e0f06040302090c070b07080f040f0609080d050a050a06030b13050f060c120114031504060617070f05 72
    0x50002513107108002c05900752a00740c4889032100c009000c0e00c54010100c10308210242c9692900c0130380250082590344c4106021140030000c602d1618003118100d21594000300c0b0032408001103112580184042d50b070040c4d0000e9a0740c0d80f010360b55021801d140000d0700350101b040f449480002081441e514003409000c41c00010810382c1450b4500800600703c0341c3c20203005003464803012106869000860700a90f0300948214240d0420700c4006880b82e01c0100d098603100200d40200d401c0c140b04041d01030260808442d0200140c9650b10341c0c9022160804045551740d41d20604c0c0000540100b000e419040d161020009a602e00b010380c05068900044c004000349103024001c0c4002844112000e811003030780580a1215640e40c54260f1800010100c014500d00c20070042088250854000349841e25503980380f548240d13070b1400c1414444c243ca16401303a05402550705000e0000e4400039495000e4052080460441c7e80e4101d90032020100034040005a04841418800350a451220100805d4181c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 591229550 1250 591228300 591228331
    0x907120302031c110d0c18080f061303020736020d0b19030305070c050306040f030905030a030801030807051c0507060605090c19031e0e01150f090c0203130b07020108 73
    0x1a040304d011701c15800000c07601c90742c0740c8090007020301c19111044174400c601c602ca4038168075510fa06503543c90600c40c03887c1070306c280740005184c2000b920100250a074940c00800d411401c00f403e10300c3c20f4611429403401d000f1400c0c1c626a04607a84038401c002c02c1d0125034010b0f9640c41d5290424140d80110030b126003c3d00001058241c0040591000c0003100e405103030031a00d1b6102417421035118845644460f9061090b5130601c800d1202c41d040c01d002441c800c0d100c5200d620380da0028147c46103070500015020940301401000170650340c0000700b4400d0711a0054924002c0303042d10f5540e02c010700d017601200044001c60031600700f101714070501c8060001101c40012600d0b1003c24003919200704242c04c4440d001c070600020006000f500070002000c0002c05001c55104090444e0009150001c0904065802c1c1001c102e160300080742284140e58030b0002c1070188078201403108014190b40c0301c55204500c810054050440c0c448071100c4060301a42403450780d00c0f43c40f8000106524400390040f200000c3c2023 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 591230800 1250 591229550 591229571
    0x80603070b0f0702130e160801051b16060501080607110105010515070203070308030c03100e0423070503070f0306060605030c041512231806010e0907120302031c 71
    0x1070090352190304650003502e030780d43c0c41031001c110212012844240751a080c24104200440046010241d19000d4a039503404c4655031075009085c0c4006441080c0c501d040c000c0c00c2d006600200004041f20f1500d000048031728425540e56008454007603100c584c0359007024080c06080c983c042280c866004580000384a6541001d00094240c0000180d03111038200000e410411914140a031900031900203000036107078900304100c1e88150b4030441d4144590540b012011580e0703101d1601c0640030310341080b1583d42e840301100080340f00d40001c1c0000003142c030809100140e00d980411170135028090402440d85507920318603140c016100c4036004201031010034010042401006000d54044808420b0101c1c41d10040703080959601c0c055000d11041141410340b032402140c1c0c1010280d801c016944000c402e16a44c8060491041c0740070840040e103500103200400c26840f01c49011600805d5400035a070201d03684412405101f091840203c0c05a00b011441074806100061802c080411a00040c002d05825 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 591232050 1250 591230800 591230819
    0x1f12020406090b03060111160311011b0f0203070f0b0702090702120d1e0513020f041505090a02041509090b060906030a020a0c020406060923030307240c030c08060307 73
    0xc1d800b030010200c3d00440000d071541e125031a03203011801d0050a075402a402d410f060f40c0b06030068001500e0043c104034500d00b99510980780c0d0b00746500c0c681003400c60703c9203070303030f107848078807030701d003a040e82d05200f410801304410301211a0800103003500f01400b941c5040c113206102603800000c2007072003990000d20b20600883d01410850320800c0510000140c10001072106800a102d031640f902c2c0c00034901000c0001d0050010f400e40c159a000b1241d101640b0341000401040d42c1100800f80c8002d01015001c10a0381400030320107030010b852000250509848070310301113100d000901d60200285c2c40080803c050200c900c51260004801c2d1a80c0d4a003032400c40c003242e09031202a00000650750b0002d1403203061845410012a55a4000c000388011540c60000503c0e071520750044000510b000103011007500000b000308080040040c007d1410328081c0d48484038004010aa51501303460322051a00d914440e920545075034504a460020300000080c0c40101441c4008040390f00a500510052102418 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 591233300 1250 591232050 591232067
    0x61128020a05031f15050a050907020f06010609080f0625050403020613050a0b031b180d0803090d031b03090201050409020f03010303090b071a070e0d08031b040608150f1f12020406 79
    0x409e07030398081c2585903420200d2800140706c040d003903207000b02c90000c6004d40d8441c00850480d1444412140b010324000d48040e1078500c01d807441302d00e00105031040003904c004c3c0c2e801307595084010f0038402e041a5494012801030b9001180380d407500c540c5d14000307101524001030301b00041c12151817000c0c11441c00b294040480848440c103980c075844c0120f2141e50004403080174504c00709000d414100c8003011031404803903540082d504051180100c00785034000030300c6441105d10f441c05024a0301040310413510103500802d60107405904002c0c0400011400d422140018100640038081460b40d0b0343c55414010106081074010071103c03801041260003240100c940a141d40303589929040b41503c45003419103000e0400843c00e50080b1f4000b1216060003100005035210310360103900208180d2040a4000140c03055001c4c4501042204020414000c10b070b0071140e4481e94007818002254005100143d00c502c500c034070304440105422104d01000d42d00000f410b140d490014025405c290500c40007030450744 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 591234550 1250 591233300 591233309
    0x120040b0313061812031a21030324090103080d05180a05030403021806060a1b0618022b020103020c120a020601061128020a05031f15050a 61
    0x40d0120124512804060403940350325480081001240300030025100d80c45024075040c0c1d00100245442081c445c000e000317008482501c4800c04111b082c1c9a010015403111a94010020700040c4200d001140d900704011070141543c4580c050302c01d00943c0c070800303005c822100054010400000100300041c0d5160a40340d41c011944008039440d5111034190000d011460748407070f4a8801c600032076052200c003100a2041c2c078001c0d980c0f0b15200f8001f6650300010b080a60399240c000c5403c000718903096200e00322142289081c60098241900070383c58240c16158200e904c2f440c03103407551200c1803c500d0a81d05502000c02c03150102c00c07401170720304403c20303510450810203418541c0014407072410340024480c1821614018480075242c44d4045002940d0b50001d001711400b2400e29075000c80d01503000203216035043e00120314030700d0248103009904051007030502d0407600140080008585da540c1030292a10394881c01242a1480b00d04c3e03041c0c81c0507600c2d02030040d04011611103007031146480d0500701d0705c11748 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 591235800 1250 591234550 591234569
    0x60c08180409050f061b1b0f07141503012418030b070305060d08040504020d110c0102091507020603010501030c0507150509070f0833010909020405060612011401030207060f0e012004 80
    0x108000c047c4d141011038845225640b4081c0b20004a031005c0c090668101150b81030311411034081c0d00c400c0c9580c02d4031081c0102da26000340807000d240e0075031800007c2819a4450f02c1e100030b10303200d03490307405e00404084d800c00c8602410b11020404038560502c43c0d1580043d08840740018441c664851010a105500607113000341d40020343c40d55401042c0c0c0191199074800070040b035a5912200e4058000e401c01d14025200d04a0300c0a514480003114040c0d6081a40040100340307103900e000c0055008009050a01c81840014401100443c10303c0d81420218030210002051a1601840e9a070401c0034a400c2800c4110303c03028240044000011480030110084040010a2040181d060f4100007090b090082401e8041d0004c2060085500540d1900e4400e079002d00181d240d20003004410b000e18407103d514030907180c0040214100c0800c0040788402d060500500d015072544a10007500e00b25890b21001d1500c4896848114000340720b62724294148200001d0810070140c0c2d03400440c480c42c40b801042c0e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 591237050 1250 591235800 591235837
    0x40b12060d030c1b08160608280903030e030307030903140c0604060b0409050a060b011209120e040b040f0b0f04020c07090f0605090f0f060901060c08180409050f061b 73
    0x1000c4055110002601d42c001c11100030044c820070560081c20305004480004c0d500402040e41c13001280ca0350850f01c4034100825016542700d2440074010442c00301301790101a151507a5407045441071000754003035a600d590104024011781006026108043c10300c4844504c100100061480b021401c00c0d0402d901c05800305217100d680380014082c2c206824003500c980a511b1001c800c00c07040740d011514048080c2c81d15407000395040c0040084940342040030300518800c1e0403a40440307101e58102400b80700005c00c0021a510008041021194110121302c3c3c4250741d403400c51071920b843d10300220034400803a01545000440081d40307450344801c4c840da1201c80e8452007503240705500e58001c14054040546900da0b02d14040c1c0380d801070400c060300c4082800c5031400101d420b03801d059041505071050f54031076100914403559440c3c5154040340c59008200c8a06120344803c0c1d40c0d90203400d5140d80103034024410600e524654904120001d410b101c003031440b04510400c094034604c1590440300d0b215404140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 591238300 1250 591237050 591237083
    0xc070308100503071805070807090b030403031d031b160302091801052e03080f0f0d02161b03050606120f0111040906121e02120102040b12060d030c 65
    0x145281c2c01182d498001c009020520045144400301400001401480079860321103050300c80c481d0641d403120000c1c0741c094040c01040048030003103400c140700345000900c07802003180e13010321007100704c10303242e055040040c2c408800040388140b582e204558501810303d51115280401b00303641c140c88001d005040010005480f2031441d180545c0d00c14804000744045c0c9415035090b04048907a80c030082804017a5043c00b0803000501c46a40196a480261a4076007666080b005125402c00c1084034406070b400c2003144002c4401f4005819031040401c400070b030329005840c083e9808080244001940704100b041000881c0c800200c2c103401440a64610414186544001c0e051080488030007015609101c4055001c170740b094024001c44491060411091b5110101500302d07105c040800f07425a1020191030311003100e82c414010030305100074020b04d107811503a800c0d1401d982242e4848a442840418040b210724181007800b60311103011622144010f16580e4040d00b4207144503406031114161207003000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 591239550 1250 591238300 591238321
    0x60e0f010905042603010501090e0f07050d060302031e0d05070f061e05070c03020607111e010b0a0f0e16080f180a050f150105221418060705030c070308 67
    0x20f040c40307089000d40144c0100340c0c0d00020b07990003840350b103000440c4940001540c0c0c400a80722405040c214118200d561a4900d00321017682100e042030032800c2c1d07255000801664104092040b03061043c0d02105132041005101b41000340120054090140400607400000c070008e242000c1d440d842200040c0b88840b0142070000140b8464501684500c0c1909003c0b130b103608080c0312a000c61095080b1030b65940c540b070040b1754840d69007a402c6241c0e401101d480b148594190404601411442c0001032a1b0b441000001d40d20031071b640c4200c8000900000602150280c1401c442c0d010958000001100103080001405000003c0c8000c0c19007491801280545080d03c50000102d1030450880d110b400042c2440c036103c5051202c0e5178041d11801c1280c03001c000c040b484d260f048481c010030005c6201d6100188142c10741c00c50000e143c8081d070341c1d180c0c80d51704040c000155000341c100500005111450041e0b02d0b02c1c283e40a0940c41c1441001d20411010301ca006040700c45065040c030b0003100580310b42000c030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 591240800 1250 591239550 591239573
    0x307060c020309150c0c01050901050724020a0908070f050901030f03110313051e1c0516180b180a020702060409020f070203060a0b100522090609060e0f01090504 71
    0x640e841680c602d02d13110391020b501c014001e134021060544041c07015038001504c00e842404070441c08104148460740205840448000d01c0c1498000b18241c200d184908410490340922000000b01d410181c1c14401e0040400120b0054244009050b868074281800a0901901440010010440704150340101445003030b048901d40341007011a0345401c0301c2903d0081c0300c8254000c050040040b0001940e100c01241c0b2840c0d4a448041c0c5081c000405100b909003079031102640030360317062240720f6000101c41801071003800145551840c9085080a042d0500c0c140c9080550b094414081c154071140036202c501141604451504001a90341007280b020074040e00031980311070621440400c0c0304d00c0c009040001041708520840945140d40e4444c1c0520084030310003c40c250701300c8502444600e84600500091114561000341e8040442040802c1c00300b03502d80745c02c8120610384458cc2044070490358002c1b500540313485d01e1540401d241c0111340f00c4803654140705914119840d240818140852000750 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 591242050 1250 591240800 591240817
    0x50604030f0e150a0e0d03110d0306140d14060403020616030c08010506030601230d0b030a0c030b10050301091101090b0408120f041505030402180f0a050402120304260f0307060c0203 80
    0x101032040c4050601030b281c0c10420230840700d140104c00f2410012842807003084151042c4440c0707030a24514920034805003111540c1d08a4960450780c43c8424201010803499100360300c03960041c0b1079440d1025684440020904421080c14207085606003201c0e04000c2e01c5065600c10f032032603510703540d40c032004a89005c41c1102c480d21480005103d03044c2d0591380c100510b14003c84020500402280b18141903681c9404100680392124500c001c0c000940f01d42b081e507030014001c1c8120090191194002400c5666005040311404984940e00d07030107580000249004081c1d0300c001c2c0341844d1501500a4a81c42d01d018103003034405001405540b84a2401c0540d005402850000320a410b0780341d5018100341d2068905a220343d0181065030078150283c1c030914031030010180c490402c1e4582d0310000024200c0035004913170001c4013200882c1e5002041028200401c9041d01c0f2080c1d1086800c0c10020350402003000f20400d401c1500d0905030b41000000300d4107203a50081001603081400c040803400d50050ba0764 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 591243300 1250 591242050 591242059
    0x204050c1c02040905060a0f03030503071206080a050c030705100c0204061502030304050c030319051309050a1d061b0c010b0d0606030302100605130b0303070b04050604030f0e150a0e 80
    0x1191441c02a555003c0e0003640d050050401c4240c031107004109500c1c3c00e5101d681c2a203400e0500602c0000e110f0805560005121704150b805501542070250550380c1075044606958004011403082c05410011101d601c2400e50181207c2c034244404219a000700314600004e10140442800131521261300002c01400c080f4800c41202410000c000d4030b030360051f503045c0d42d240b1600418102c81e00d03010003150300569650b01449a40442e80d034060324150403044c801281b81c00002d10020b00030056000b101c0c42000707189400120501195103242c0644420030b5504ac0580c071003402c202103030368585e060320300c070345441282c02d501c9016001d420303400340071010502500014152003007020045d841d007091041d00d2094003683c4060f45600c1c0f1103022200248103072a4040f81d101c0c240e124000305a401058415405800d41c1d2500b03169440f036545000c000d0301c080340e13194080030400050680c0200300c429641064a4100419104c0c0e0340041c1456480c2980c030340300c90b5800541810040d009003014100e03540e0140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 591244550 1250 591243300 591243337
    0x7230304050604020909010501060e121011030117010902030d031d011103040b010b090a061803061119050307050a0e041b024c090206041509060c030c0204050c 70
    0x361054580b80300b60380803400350142c8030102da080503040c01141d06840701075039072903094201c0808004036208400310708010f40c001e0311914801a0f06500a1400541e00d10a50b107583c2c0d49032502520400d611044898040d9160100c18001030340c020840007040f8281c1c0c070700032545010311032006505048200c5c1c0700300360350700c3c0c80c4040c0c00490b0410042c40c8524002c80f1240c003141c0ea038003103104040c45234984a582c02045000b09000e23081c007070321008000305041d101480c2c0107901c2c2c1c0d4445c012601c2d42071a41c06d5040e004240c1190a015282421649504518086007541409540980036003c2e422089082c0609810703030103080c0d1a507038000802d04031140190740300c4e19500c280c042d44403220318120740000750200050720b0000310340e002d00300124454400d031070000b813503000c49052000c01c000311102e00d026218200c16002d40e585001501c080c1944005003004850707040c6016040603030320760180d000c2c02400458140400d03081300c0104021901510081000d50710078110b090709204928000385000401c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 591245800 1250 591244550 591244553
    0xf0515030a0c140d05040302100e0a0f05010f0c020c03010c03020405091812070336030b09010e250906030f0816080a030606030b090906011e12200904020907230304 72
    0x20340001d801a40290255400c62889105100c107480090ac240b0300c00364400025840000c07841d0880c038110314012030000404103485403400d8103440c50191440c006a02680d80c20b02185000e10510000b56682c0c1011071505181502103024407400074030030310350204079891044006400b03000340c2c18031004044404c2c1e6900d600d49009801c03810207203501e000c1040c030300140d40f000c0864034200c074440441c05034596443e00c0c40c5942d20803940000072b08142d425500c850000c00c4505e0200070f1110710740d1491103008041002074400c0244031a0a0307016601c0c403802d00000b08003240c441c0300114803113504140c03c250343d145211582142c10380d00d070100500441c2c0005035180c074141d142d4004800c0e5040c6540901c20520310100300402081d0603141c83d0032507041180100040060010403401c0030408040420344542d42d80700c814114019400e050b20b5425800703060340100d04c05080c8101041e4000c0321041181d00740f58001c1401941c00410060a11a03100a100302c1d1a18032154480d0900c4070292103562403130603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 591247050 1250 591245800 591245827
    0xf050106051209010606120903051303030906080f070e01120923151915030c06201605010302090604030b010f031412180f10090f0515030a0c14 63
    0x9182e0702040001410045001a20103000707102c1128006d640c0c02510020b0904120000c01d8a81c204a00b440410080380c0f6042d081581c041000794025260028200d143c56070103829003d000300801444c0242c0800c003d41240c1000908140c510b003881c0c20340c1c02e480c00700c07044c800910340882d0140032a4000400c01c1d0303800c1e40081f0100003140a4005940c0c42c0040b0511038007051009850303400c44480150340042d01145a0750043c94254103e00ea070401c602c0eaa81c980e1070307940d54640c1021000074002c0722203003607085c2d8102a5502017071185000700182c41c4469601c10040859000d0907042540000d40c0384d81c03d070703565425140a1500407503103040c1565640c4503856031503601d00c000c61303100c80c09103a0381050700804030b050140240e0301c8062500e000302c1c20407034148120140c01d005900103003c140c0f0320b85031303154a030351301411804546560141c0c50501400080030500c2d98040e134428140070303045080305140482036a0308145902808561401c1c804000e032152114500c42381845a0081416200c0f03044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 591248300 1250 591247050 591247057
    0xe280c03050102180a051203030f040609140105160c020907111c0504150203030709030f0602040e04050102090108010f12030318121e0854070b2b0f05010605 69
    0x40885d40c03034a02540c1d0300c0c00d00c1004014210030703074041d400c01d1000584501003036001641c014840c20000a01c251a9640e4440d10f000c550303a090a160364441c104040000951051649640c4a04049425038029800554000c1d4010003510401c4015040e40d5020201000300f0b48020aa05000011103009101d00a001d9003051049114641c0900c4220500394004400c0f6805079020b95600e5407014107503214211008600c1e5011203100b9801c000004070b00341c65201042c0164800e000140e0b0f0745542000040a4182c182c102e02007410710504104a900c44180c041c500301a4036040104640381a1110140900000c04000d8030100005104045560744451410042840494007201c0702c3e104503421104600111160f240b00003200301c824901d2000d0b42550741c103d100780086c40c001c0078050403837031504981d95045181500802c0034201d0030f2040600070403016282012001d130901d903031841403103e051440014140d0b05003940512040903601900804c5966611060900c56542d440c030000306544e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 591249550 1250 591248300 591248347
    0x306150f03110d0b092a03060c0a0c050d031a0405070e040b010c0c06170f07090905041e1b09020f16140d02160503030711150702030f060106030e280c03050102 70
    0x800503204a0420361450a06c8200f02c2800340051100b0354070320b0400c08281d4400160725040c81080c080303000c0080c9042065040aa416a40200e4507461444d800c51205014075180c600c21400c010400114503480294558010740490300420384d110304034016580c1001004001d04084007002021443c00d4010030011406219080407103019074a40c0c407594a1440d060340c00c1d600140f0300703290802400c4103e811064005010b45080600224081c400818080050300101c42e40900e0740990401c038500484090010a52010306618103202d400140010344100c01c4d1800803c2510280c42c018010440700d9060100c100310119101c0b004410340195071426020150f55004406040c00720300c130705000c019078103405da210310035890b011200420031001003186a111902e2680600c01d040140c0d900300540d9403d44d440901800055041c51030081c26190300d051480619840309212403480c2c0030264000481041522001030800b110389030185c9071002d40d52010f0705540c000709220a021000b04003a82808 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 591250800 1250 591249550 591249583
    0x10e010804472202090403050f181002010209010905040509030408100603060c0504080a11030c1507111804111306091b02071a07050c18010306150f03110d0b09 70
    0x283e4807100b00401200210309501d101c03500720300760f02e001410409501c036017241c0f00342480c41c2408160400d01809030000c0101607045010784607000324030f040c410901c0e80d000c10544025440c01861200290800348103209013805a170f80c5400043c0b400100b8003d0314050320780d84040e10700000300514904007408003400142d440a10303040d500c24445014004860480c1c48010140144070242d443e10406150504210364050064802242040d81d0340380e080c1c0c86885240440e1a02c8107024202082440381604da00f60250880400358555030034001010f59102d40d1044c582a000031701e21010501800c00360104200150505001013913103d0f0396000305403520340601d1040702d069026401265101c3c164072500b0010040040c200d04007815a03002849564000d5045500541130000460003807200c42c000c155040d030660006000704030040c050414040600700040306240d060419442808030580b00007044600910b46030f41f032580312040c071540d415030440444940ba107030040600b5191140d031840031307020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 591252050 1250 591250800 591250943
    0x414010b030105070e120111161130030f0301122913020d05030408060f01140306060112091202010b120604050a03080405160603020a0e010e010804 65
    0x2070306051159504c521065035034403034000c2c111030a00084049018180c261035403070307194a42c04814000b00400680c00800e1034929201c015040c040000c2001a12407846220182a01503400e41500c00b05030150340c3d0b0305c1d04040e130804d250003150310314400d801400a10040110000803060008001c507103000b4000c1d8914030756485204007043c031403084504801085009a804903500300303c10f0122005451020704260b01c3c041a9480e96403030b5400541c0244241d5020100300040901c50940650060003441c01c4410103201c2000040d80350758004000c0c03410002e84820701c8180302001d070010281c03160040b90403600d2040401d130080c060b140e251300290080c814112944160440012018407564201c40906121003c0781d030f0403541501e020300f041e0340e40d100d58280319a003140c0101516006000d20b441c0180e17a41c209010141204980541d070070b06101082d14141c0e03c90741c0007008240c0c499800100013151941000a8482240b0301058030204010480380100344000006510010350b440c5070b104051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 591253300 1250 591252050 591252071
    0x60905040b0d0b010b03190f0203060a05103c0f021e0a02060a02011104171504031b03140c0115091104120c171c0f09140a03020405041401 61
    0x100c1210060b0020480d080701c500410440782c00c40d0117181c0180358900d4130f20158890b540c211060721441001000303115400020b21001e8640199000003c003801d9529004090701054058407002098503101c00313002a140070350b86003000c201c02e100e81d00041407ca0b10809403452000801d81e0403d251418058450050b031500c0c280c624442c0000000407032001440715505d141d0130b200803030308100c681e50309540d01c070001510040503160240020b0070203011040c082c00e11070a515071030300d41000c2140e800c907804881070101003070340b00c00017a02d041c4003848192045442840e0884401940410710412113030f000c00c0c0100c81c0750041d0040000000318611207401e0f103441d1015041112a600000300c00d0110400080200c014207442c0300510b40e0180c0d0442180c15503030341d0b0188205081e207160420340d41003816a081031800501c29a111980a4135014000d44140f50024206404030700500351000960005900ca81d07407011440c601442e8060030a11440c01c0a16140e00c2d644200040100c00d5403e0440490 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 591254550 1250 591253300 591253309
    0x803040503130f0b0403080c010603021c0302010506010507200310110a080c0c07061419050c160f05061c020d0506010909110f030402030a06110a090501020120030c040906060905040b 80
    0x30a48a0043c4c1291800d4a075a8443c44a5444960360400139529000000050703554498242811600005038004c26500391400a0071500020b1001d03041c050300384150300100b0a849011600030704201d0a4828441035040040d207041003082600c40c44030705102c0c40188080c2440040d1451000035140d401903900c40101d0a4290700411a8154143e4020542080918800c80300059854448400d81d807404007149282411890244022400320300d00103100d0aa11034100128194401c1000ca520320303070f0b0304003500180020a28401e0501c9038901249044810b202c1d08806a02c031049180b0841d83c840c0381245040c060710301260070601180b00e000f00090007403003a006a20400c00c600c4081840c00d49074150081203504003a205903010b200b01c040300070004420b03224010801c8103005840341c588210b042d00500510349600f090f411a41403800702183c0c21069140d000d003008410161946a9031804444c0382c00303000d1030b4400ca800c1e6040c80f6001804c5078002001c201980c80585017403217461095014030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 591255800 1250 591254550 591254579
    0xf0402041b030e0d1704170c12091008150103110d020c0a0c060f080f130506040b010302040b03070e2e0605040602060a0c1b030210230601110d0c05010603080304050313 74
    0x117650310403032000140090072913400c07005d00b01a440e20460a1800c180c0341213241c01ca445c81c40d500b900c3e00001d5881d04c0751900180400b07400465150031481d91030711849040f441d11040403000c2c149034444d141d0034081a541d40503640c40c0b4030000d01c210b480e510030307030546540c511240c1da058402c0300d0484400300340903102d0f1504210380480c0b51100f410030785075046400a070b2480100b581000c031191001070400640144007107070090380211608100d0b035041d8010401112850301a40303200b42e000403010814280703081c0b013295010101c0d0150411919800c0406a555044040c1142100818645c04034041e50441301400075109144d00316807079aa42e80d0207402c05c8446400405020580100d140641c080003007040c03100c40351081c41503440361020202c030581640c404580e01c4410b0f40d41103104003500c009803141140c0c007140901c0c0036154a112000f055417500e030b4900c040400c0181f40300c4004144031094201400541d4888500740ea6844e01e07041c03c98594220040820614085038000200c819500c03a05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 591257050 1250 591255800 591255827
    0xe06011407110f040504030f0e030313141c050f1b090c1c060b0901020f0c0a05060f070213090b06180c07060608071412030301030305030f0402041b030e0d 68
    0x5540350000588941c02c0d04100400825840f924642c400d1015454501415000724400d440d03104100c900403201401407941950700b1800b076441404903040030036907880e40d00c085401400d944000b090f07141d0085844904040455116001441540810000005034a0510116250a41d0241000800c14240038100d0003c0d290703010aa441c00b0640300c10040d80282170710586030b4004031802c030424032544103031a8241d1040c26549004680c040c501c0d6010f0055090362142403014090a96400000464041c613030b0151310301481010030303a29020683d2000316428550020501c101c0390358892001d4010341040e01c0219012407000340800c1007030900c41c2244048040700348101c24244e4800e80d40c410b03150071070340040d41c0803500c075040015071081c1805900054201c0d140c0040500036480103214601c4007400e45460140d00c1000100042a480816203400583c03207990440503072240c4c00014040c00c003011003001d403101d01003209c92041340c00da8004031080808400761071020100314419140a07020808 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 591258300 1250 591257050 591257087
    0x1a10050c0d1b06050103050106080d171807180606120e0d0806010306051c0605070503130f08040e0f041e03021b01030e070e100b03011202090402010e060708040e0601 73
    0xca44060718000c502d48010005100d00110109486440b0035056801c00c1e403094407640d40d240e600b4881d41c0e4083c0110f0b00703184040d080c240e150300c80c041d50309022000002c1181c5a1410144040d07100e0ad03d00b03008400080400303200b2740301040903001001005044034401e510200c0e01103408544101a1030061071711641c1c40e00058541c0b920100c905480e1144020304490400d6650300340420a50303900c2190300d28004c4180e05a400740501c0307142207400c40b880541624103011042c4104a55460304200240f5001d40c0f000c40c0802a0102e4038085019024507084250000d03084e0f01001844240182518401d50241c1000004040302034a400c0810004540250050308620030079060080c40511a0310612410300d40080c0e8144a51480d80c2805102e40140e000038005500388060038204c074601c28040c1800c4021a861035242c8480d00c030014850700802801803214400040640e0f01412080944620103410744d0360301c01c100c0c64600043d43c41402200c0304e00100740003090701c44d4454559455030441954 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 591259550 1250 591258300 591258313
    0x63c0a060c08270618040f06050901031b0e010e06010201111e0309030d0e1c020106060c0321050108010b01031803050f0f0910030207110909031c0f1a10050c 69
    0x300d0380c4044006000b41120102510200c00c0f0480e15039100901c24180080404810740c04407408000c00c0d1806050a54200c90800c94207004c6a5542640d190450340e00113056121070392105100c0c2d204400d95400044003140850001960781201d0404900c01d44090b40208510320216004210500035052919801c07512b03540f0b0205072000c04401142c01c0801481160309111840002c0c0c010740d201e00c000303641c96030001d0083c44540e21600344c050103804010b0000b446200e091190080502c40c2038038000c0c0c00c000001121440c8404003e0b248600640034134020300c11580c540c1c050701e0107424550a03d900092034043c148142c0b00d00040e984400301d50540c0e0b083d1a000520711094420b8120003400da00890b010400b01000b40c0d01c2910600034042c0e10785015883e0841420183c200316902c00409008055207020000d00040c04411900c047c030310b040642c051441021540700c0240365a081d8418014a48011516045420f02070308035001c030210b4400804d070301201c03011242e03030042d0210065158003d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 591260800 1250 591259550 591259567
    0xe0a0612090203100c0e0a09021602011d030f0607020d0305010e060114040f271b0f110a05010e0601060c080702010305040f1e110f0306063c0a060c08 66
    0x41c0c109440341400281164101d018080801007100d40104480c1c4c0464204406030249080031203000c4020b04102ca0114100344030981c00706c1e070070809224028100000c208542c016030f544000147d5042c1c401408503040d1194680580750b540900340d4804002d446800d148400b403a22900540d0305984140d440000c01c0e0315000d0055513116000c02a80e0000282400081045000011048020b103c496050504024800b0b000240241c007048050121402e01d80542c0750046400c0151440010724503208001035500310088580f440b0014003110140100e105560034480150086583c1c0044901030b9256a680c845003954103c185170001080c1100a1240304c000d50300940c4036075405402948070300208020b556416003017006000e601601070100003132410501c03241500940580c0c8045d42d50b402d040c3c1c01d09000940d1214010481d505c1291100e18101055184500d4095500010100046611030405485010041588a01c9d010351280000012031600c1411000d100540040c80c613440c0c03031b655 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 591262050 1250 591260800 591260837
    0x507020a09050f090f0c0a0e040c080f0109060b0603090a110307180219090602100203070212190305070f1b02030705180f060603040c0e0703111306030b0904020a2c04030f0e0a06 78
    0x3c00c16036020080210000e8028030078001ccd200b101070b100c00005030b04071441c130f4202d049441d1b0840303450143c80f0610800c880c401c0002076059a103a04105a2490102c01200091800b005038000080304907460551500c0802d40d90040c000780300d00f0346020084880c00d81c60898150a1600c00d100060b40450702e15030b00796415a0003942c00042c0c51059400322810b004d0130800307503800154010f41d14151342071409420b5a05205d41c50300510b01d8070382241c0c0e083c00b2080041010302d0522840201030b550810590455408000d440c0040c00040d0034800304011440f2044d82e102c904494440312090320360300142451800708201c0e071003a80d112020b2481e03a0704103031141e000d11a00400b40d006055880200c03125901841004c0c101c20941001406000d40c1403100003000d8500b00c44500e80502000e03414400142da840e0410b800b0742d2000e030495034100c0a00301a8000a05810340b004e18603020540502040c10341c401407a03030004c0392585030b0084103000e403070900c201c120144c8502c200141d01e601c0c04403000c00c3c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 591263300 1250 591262050 591262079
    0x222060b03090c1e0907210509030a0e030a0c0b0c0f07240c0c0e100605070c050d0507120f02040c0804020f040e0705040e0706081014010507020a09050f090f0c0a 71
    0x5413666880e114210000441c24440050b11183c020074000140b007208400d519000e05a5a9074a01c405c1c03140307003061400e0940c5c03405100183d000b032011003901000e01c0d480400074800d403190001e80440d000e5640d00302c070b1840b50b44030840700c8810340030301c1c0302d0442d900d140000c19008a41500e90b9032502c1d44080f0700e021f00b04004601c03440081094a44080c00803a0010409501408071614248114100381007000c5988000340d210301e081c41000e0004001066081001c2403c5850580c2e40075400c0d4110b181c6107081c0f0304150458504640c10a10601c01c0c0709600484d400814405c0e6410041c0b000141426038a04800f01c2e4029408030b0141c22900050606403c006c000001d51801c83e0f1100ba103480004080e28042c9210048944c01400100300030b40e40181c5081d0003425036600c5001d2582012800340a11030015501c5061100000d40b8104540303c510408001f843c44020411640c20150201092200c2c1603030003100601c00c00080a102080115040512001c028040326401f403030130503503003810403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 591264550 1250 591263300 591263329
    0x52d1e0711011d0303030405150901090803010b071b09090308072c030c030111090f061201090203060d061805062404050a0f1b1101110301050108090a0222060b03090c 73
    0x400c2d03c00034800b0b6443c204050342c000d034881c0c005401c040c00c2c441d01c1c2d0071060000501e00e000680c1400c081c800030590744021281940d81d4400c0b0140d48401e82d040008000102005800744504028000210308607107a004884891081c4d949401c140c036022400c440300302c0940f562030b4120b00444401d02c0111010003030210f000e4005015503400801410001e421500e8403400e0480e08400050f42c1c00d001e00d441c1c1742034840c0c402d04032202030401d5200340044032042d40500502403300c1d070010100300c00303547d0302e5403150764540c0c80751081c0b20550720f01209514482d8600740842e814450030001c5089442c004404040092040c000448058076580c2000080d22010b401c050b410b9a9601078291200d60500503004081c00e0080a00d00c180000c031001031001010700304d002081e034900981514014030300c0048904540091074084800d4441018440c14126a0b81c0000d50040300c0400c0b4540c41901c5c0d60075002c044044840400840c0c0e0360315000c0306075103c11240302040350000854034107540740c404118503006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 591265800 1250 591264550 591264587
    0x50103020d0902100302040f05040903020303060d17210a09020303180a0f080102040f09020309190201050c0a03030f0e01020f0d110f070609020916090501052d1e071101 74
    0x80038541c000c44e2000d0340030b024103000681c001805006c00d101d8482a900181810303142049501c007182c50081d101d0002802c0503101c1c050142d50070040c01140b48140c034610100841856403185455141c2c5841701c890b0140445903454000000c100c81e810f8440d0888854000e03014504c0d0648a01036100340700604040140c2c0400510740c0840e031501c414100d9000f074021070000681d01c9003004504650f110259109075442401041001081000428582e201c00311142c08010400380610050f1010f0060034501405845080108001d2540c10382180c07a4540750410300708080c40c0b800c1060381c240e12070041c81d45090301d4100400310814241fa48a1070301101e51882c1c070707400c1c00d039400710301401580145015119075448040301000e61402c00e03030198100d882004201d04000300314501900060840c4685414003c0c04100b0305400341c1d10380d001503001d850071011080c02c5015081030383d4880e00011840343c14124400210004003069808032420f6903003101c11582c461a04800446000d16142d01c0d0483e02d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 591267050 1250 591265800 591265811
    0x18090a14100f0f05010f0324140702010c0f0212071203150305150703022701180f140d0b130303020f0304051e0d120b1c0b04060c0306060801050103020d 67
    0x801c0c0c6841042142103a051022500700011a030314003e80324117801c0500c1481c2c0702803041001079a0b2400081400390a184849070b009402c1441c00010701c8078043d00411903031f0b03100401601681c10b43c0f00c200e0140c91900c90301181c485007041269160a00003294404000802c54000882c0c0e10b8108241100c04610780814814001c1094102d0484554400c0342c00307500c1081c08140040d8005071259000940f40340860510301a010404212040c2051b40f409208204806901c1c40e44590804282d0140c0c1c0400c10100a40c0d0b00c0f0b43d0069401c1034802c0c0c0c80b244986030309800d08d41c5820a2010185a049805100c441c1c9039000e11075101c80d0381d071a0440a0607420015201255440c030080e6218034040c401401000c45c4082640c0f4450220540c1ea4189030007144228190b260030204006909070b0b1407000140700344c2030708081010400a11205407195840c00d01c0d19040000e14100144030701d1040409100e140304680b401c0d01a50b0f0350f40190310109000c0c00040c4544c0d4400c2c0e014020808400001140e07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 591268300 1250 591267050 591267073
    0x203270604080303010806060d0c0603020306040f0509030705010501080115150c0219060806030706090603022a030c16050d0f081e030109060b0408030702091003170918090a14 77
    0x66541c4036074001603075034001000400c070342d03001440081c0d88014146c4071a611600070303079100c50120007035001e014107055010012800a44403940190701140b40080104050b0520008455481d04018001c807020f43c240000421040810b000b6485940f1940a0b0041082d06190458a01c0c080e50034290041064040f1a400075a0b1a9035501140b1000408854640c07418102c00038a0701c0c400034641d60280d40084020489994414582802c581e01c91030010703240c00c2c550001603018144d451000c14030203918012001409004801000d056000c0801c44420581c28561401c800c103607441240c0c1c2c84429030329424003060911008603022032141d006903242010b00340c003802c0009840b8002401c3c2c013401200500c0180341034450100030b05101c100c040e0415182518075642c034407075a01d0080c040e0503450042020020203511b0307240910791101440c00c89a07500c2454980769006001641e118082d081d4414241080c45403a550085680b44064003100009440721078205000070414031003480307402003492 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 591269550 1250 591268300 591268309
    0x105120f0a050c031306020901020102040506040902030f060d1a19020a09030201140f2205030318040f0e030d0908090307030b1015022503020d0f170a020327 69
    0x244180c212110300065410306010110072200002c003d6041c2c14810028010410011380880030720b15030080003d40c1d20340300340d00101d0281c080d42c2c0c04540c00501c046404510714a941e0050b500c81c0c03c41c014000e049660700401c21040008501029140c02101c001c01050100381201c415804101c0180c64810b01460f022000200c0c1d001e01c40c12800201d400c0001e00456901c400c00c0d20712040e0250040d81400c440100c4e03030045120301984644914072044101c0c0d0403844c50320900d0014079000702500d0321851407043d46620300c1110024030348518640944c2c80c40c0d51308184101219520400c0c000d40c101140d001000000306404001514400000c1c4814403540d86e0030010000918071440741d00d41503040203200f01c00c00d080250440c00081101c1c18042d904e50381e002500d0b8400e03891051040440000c9001c02e0103007202c40390400780d0802e0b5044810024092550560704e0558030510640c95404403512904002d405140d2281c00160010402c40c209050440e00d14030309200680103c40d030442072200003c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 591270800 1250 591269550 591269587
    0x120304050102120a11120402030a0602040602150c0a0e0402090409150f0e06070c02010c06060b28020a1e1109011203021b10030914010507020f010b0103110f090105 72
    0x40340e40c0ea4002070801640781194034856008003150500340000e02c0040d48000c018041c050381c1c0485050740500040c1996030411403040b05503001202159107549a01c00251601c0301603030a604015075000100b0408200340c401c8403450009651900b1003001e200c4104400395112004159000d501c4040040115686048254050a03030300341c0002c0340300103a00e800051310702041d1954155041401046851074125854a505650910380800c3d0b0388401d14102008001d241c0000c0c1e003040700410f5030b0607006504400682540b4080c944140c12031036044080381e9a00103440b00900c4042d941d841489580700c0c4100c112095841740e20a09181d940410101d00390900036406503483e6449840c01100f41a01844455034001121425030301c8880c22001081c88440c2e0407890004050380c0780d590100740417603000412201e0190708006c0c005400d000000955454240380409070340d51810f8003060300f0f9030191280c000c0c0ca1201041081c1000c42850310940650008441d49050042c10014614012408120b2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 591272050 1250 591270800 591270803
    0xc050702150a090504020f0f03040212030c070f0b0c070603110702090a0f11030f04230f0c0a0603140105041d0a030503190203150d0c2705100b0a0e03120304 69
    0x90710346400c1c00040003005211280d01040c0150b01c108046004421041704890f540d081c1012155a607445038400304040c03600c4d03628070009502001c03a51030000100481c0d120111180200c02c1c3c0e10194a4030500c544611907400a8002a071014404000042c000c2e0415280c0038041c40c0c03051f007000841c1e00850381108085605000941d9108404a2000d4552045158001250030140d0131031070301058120f80d41c0b0000c0c20140c02d07807000c13940390300c1c05001703411403014410100401d40d0404141802e010b59200f042c200e0343c51003410030910100c0e003203200e845800648000520f620000b42d11341024080105600c1c1d000c00680c3c101100c0c5140303001c20030450040403d1280d50740540d213140c5203d0307d5105e94014030990391000d00410a00402c100d07420302c000c8141c00c0481e0b054080f0300c05464818801c1e5450f40c000550b10b003940c015041c5800c06181180c9203022201000d10003659030b041840c03c012000d0107242e0554a0a021081210b0b100c0c0340c518811304000340845406016085c6440f14039002140c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 591273300 1250 591272050 591272089
    0x130504140706051201080d020a0f150f0f0b0103020a231210210209040311011407201c0f051c0204080f01142a071103070b09010906030c050702 63
    0x54013007200c1508103220380181398500141010000040009442d1030514401808043c8041356401c00d120521681d5440301004602c20010643d0710030200d005061b104100c0c4644a00d8001001415400b03402190100d21243d5100e842c0703864032006a810400500d16103419000c0140804004580d141d840f0070b01508902d110641050300d8000304054038980c030540c21003000140b41c12880181c550115190b045a07140c14015091481d01103564010510195480036074071000052115094000200c0d110554441f012001c840c0c0402c4001a502e0b042d61080391800d0040d1520400303802e00c165034441e441c400714681030b071030301b015a81d40c401160750184803041c000c1da00080400405004011742e0601d815840000c0c000396540b0b18803c840302c2d0006101c00c01d0103020412446c2c00541d860001d1070500405000c4507152030860524090301154a180203000340316041010a201c0480010b45280d07800507500d900805092000880190074100b451409006082c4031072401a03490080303010600c0d00102 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 591274550 1250 591273300 591273307
    0x18030906070b1605070507060f2d0e03060906060f01020f150a0518060105040b010210050f0108070b0f0a050901111f060b0f04030204051f031b05090613050414070605 73
    0x141500c40d000d203c07041e04180b0904100130000154041140d42c00c80311a81440c07000301e02150b60030780780450325000c10310546407030b96005c0b02c0c0b0700180c1004000e00b001c250f44060b0382d661454203040c0e41e540c069450708450303804540000d0340d500d0988002c2c3c24000042c8181c40034804c40342d81c55807800340815148141c0e600500c0800c403070ba059910681c0ea0100030801501f01c1c13142440340042e00c455044c02094000d64540080110f143d000704500318040d41c0c030304820021890039000c00705541d0350038001c4004600400c840040c0c036140305803c0e80c0c0c0f44944c1d10185031800100c480252601c1d40311694450501c0003c00302102e03e0325051007403403200002401300c00030b50380c0807017402c05c100c68458210180d02002880306100d4a40000c2c103440640e94151030005694072045000d030f81c000640322151454854400c408001c0040180c04821708134001201030240035114000c10140d80c3c42201c5007600708804483d202c462000b84d4210350303040340c0110300c0e0007001d07000310b02000e013800d88075007201c0c02042001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 591275800 1250 591274550 591274561
    0xf040204020c0601080d1e080f060402191d01020a052a060d05040219080a20030a05030c1204030b060402160618030813050a1202072c1e18030906070b 66
    0x1010010202d0710341c1c7e003011305200828130240a0b2107016189034603480c0150002905d58442d40c3c1180e240424000c005c12103503100c4400144582c071000800701d04e02e540380448121a5000043c80703c0401c0c2c1c0000030f4440c40301088004002000e500104400c0090704000c1f08030710351140d030001c156410030f40502040310300d01801400740350034164200685440703040d4805c2040903008641f400e441e9900c4015200b0301544003154881001030705002e140c5c540580c4c01c02c0350170030000100030924600008262400313032081c100016494000d51001030510b800d07c800161080c0380c150700030304151000c901c00d000c8210031602c92030202c0e6984051481c20301615005002415004454954842c994900341024003045598031601c6003481c40000b803c90082c0c5050040300343c000d02c4014044c2502802610040b134034850703100214100d507800344152031014030220b00d00d505410040001900308080074500380d00c94140c50003240b040b910b0f030340d103060106010858082d07071000c0041883c280280030521050400c2c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 591277050 1250 591275800 591275807
    0xb07060501050f0a03020105032706010602070f08030f0702010e06120c0d0b0d120e0a03080a08010306061202010e13020d0908040f053309030105092b080f040204020c0601080d 77
    0x9821015102c1c0b03111340c0003040181c6c2c0c0f01040342c1c1d00140b50900b10340c900055551b010b080251226070fa90712401b40c6400819429800102402290f601d160b818414039613a220007500d0b07108400c05542d00030f07000c110441c0954051100e01c4a40540600454504120162000005003095809860b00c03440040c400101050601544088001c221043e8040c4541951000000324a070031540c001e102070700100041981d1925140d400071a00300c1c0d182da903a01d40c420001002044c007400103c4145140000204400c000d800e00c2c0038602e40d06071104503003940d641c010082d041c0011000c511711540c00f04044d520221150123416442e600c1291655152402c04000010001d4190001401543e00f840c50544a1021405014450820b45071344a07610418450b10083e92240420050f003540c280018000520780c0010540401c200801503088020b40d010000c5020940c01c1780400002a0054003041c1e0380d4004400050304070748000d0005103001c00e851401070070302100341e1007200250807081c14035540941 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 591278300 1250 591277050 591277069
    0x1312030c0311090604090f021b01021909050325120609050c010215040f0218040305030a0501051005040b030a0f0e030c160506070f11121f05090c0d0c0b0706050105 72
    0x150094020f083c00100e4020800758082c510446081d1612081c88441c000030301d40c1207608100707011406030039100030308000b14044d40c00004210040a0a4007002030414030030344440042d06c9008001d4000e10010070200104104004000090000e2815000503824102084182501c3c840d0300f01040d10421030414034101242003442d18150341002e9900c6001e0b0217254032146d48943c5c0910303c02152240c1c3d00100780c00b80d1181007184098075503001488203058202d405540302d100042d200380301c1c0383c1e00c80050110510728034042c40007081040c0000d011003c2190f0180d039000e01c234001c000801600d09011142500c0407600424043c1d000001c0125200c1410300c10254541d80c6102041c201d20301d800c000c11a90301c1806009002959840c1030340d0104407030144250203d100c020090000700c01e030a15001d40322400f291101059220801c200910300869003c1c0d94420f422090140031801011740c00d000c2410400e1000319003070712003184040740c03952109014200c824082c1d0000522581072005000c200f48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 591279550 1250 591278300 591278321
    0x306130c0f26010317070c0303090311030f0d0c060b3007120204020a02010f050c0901030b0f0f0d0201050d020301030308062b11010c0c0801231005091312030c03 71
    0x8035466125031010309410710083c11a40c1c40011390380c206809601128040c0603d00c402048000036a000009040c0c0c0003203800141e90083e07281c0c1022080b000308040c0d4504034404a5000fa4101b04241c049660241251003051402000d000c0f40200c402d00000c1e0001c181089002400503000110f040e00c4411350420740400c5036054002d00c10300d402c12507801100001180d000744036a030009200e1b06028802c0d00403d1400049200500440c14104100c3c0895040800410f0002c2e14001d03054075985071600100c1007040c009445480c1e000c40240c18040b81c5c1d00144810b07814400304108090341000c0520095000714001d81d102e04050804000300107851900f079404c4014601140100c120080514400d080b1081d402402e2603c003621410041c0c51040100c070001c0c3c9003da12030b000265031101904050b00005a591112000780c0d5194a8041c01d480103580d40c47c00200709010600a070f04014180b00d07040b001110b00540c08030b41c2a03a0741021035102502810004c0d4030740105551958140c000c4440c50b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 591280800 1250 591279550 591279587
    0x307020c0a060504120809030f0129180a1b09031e0812060301061a0d0605061e070201020a0b131a2a07120c031205010302060f0306130c0f 61
    0x441c50480010002c0c080ca0217070201002d80c095440c0200480e1108580c079000001c0d040d0b8556500b40004240244511342816651000055420b01010081505175003c000300800d60264142203403016600c0c2c4800401070b40e4040e070f030f80c88001c0031960807841a107440051036927841030103411031a004414482d001011110140c0c48445400040e11603410740d603603000342d2700c4103600d60356030400020b02500e0103504c486c09080000d1040051b809200d8002c02520f294442c2c14821169500c040c812a4401e681800400d040983c18125000301850000c01031140140f04460902c40262076100035244c09607824104c40716004010410480e00d0b804080c0d02c2400f80c003810500d4980502d80e44481c21804490640c004016560b22041261910641e514150444c440e084010003111020b400315040c0d2030142e020417003e011072407801419000d007505072036000d45214101101c3c00d10228241d00050301440e032202010441c07194a080d5403050715498810340da00d40303441c0b010f40c0d8405800912000800380c00ac = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 591282050 1250 591280800 591280819
    0x12050d08010311010503060d02100302041a04050d031206030218090606040c0806040e070314070e0a060501020705130902030d0503010518010f0e060105040320210a140c06030c0307020c 81
    0x304020095020f001e50081c2015a40c0750b03a000b001130070300160810000e45c4846c082d1010940f096165000d03100356a007a1181c071a184241103010350140c007403841070070b902a8001c0c1001001901c41e4480d4400ba4106140100b52a82c40380d0000b001d1921088030202142c152000708000132408100c0140c01080036a010030120606107001402050020034441c040c54072014041129442000329400860700303d0054802254003130381d003944402c0e00c0d100300f03031881020f01e0104108446501c1060300301c61050300200b80507841c000a026060105010300d0381030640e511928000340c2ca0a00c50101e401089036a507586d01e40c1000304004041c200022110f8043e5001c8005008401900c0c4100342640d81c090f20b10f2410b0340d03400300101c03410700c200e0300003c00c000d4a00110080704854014414202c8100311140790b802e106103034036215039118406036400290b0014051704c000c94800e00340100a450030005480a6a2135080401d01542c400d56500d440042c00108002c02c1c254180090380d01e569003218034400b07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 591283300 1250 591282050 591282053
    0x6032a171f090513020d050d0314010b22180f1d030d1a0d03080402010806010804080a0807030b04060f2103090b0c010213080c0112020310060e060d020412050d080103 73
    0x1c03a1520b01650106a41e42e401040400e00004400d07140c06900800c568140c800520b4107a845200c1c400150b00800e003440303486400003402c403810034181e03030b07410244074100704028403042030801c1c0b00e1084ea8248028010702080600b99420b07141502c0d081000301041c014800060a02200c000e00c03034092108510644c0a01030800c04012034500e00d10014002c2210826410002e50301488018003a0f0311004103d0607404060308801000d110b14001d8031132100d590744070b50064424a41c220703002410280104104510180200c040302c3c2c0103101d81c138001803800a8040400c0454960390800f07208501005401c005103025803c03400d0716485105c00c02181307111190303009010403125000e070b058030b0200854003040b40003095055446100703440d141d507400c5650300e004194031100080c241c640018982281004a0080c900071070b4042d40504c04810103552404500b16071220b01c6c0d0032045d9000404004002d1502c80c0c134009131020700401064020740501b207103001850203070511501400d22954400400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 591284550 1250 591283300 591283351
    0x9030c01051806071b09090b01091d01050108100f0c0e0d060e010c08090606041a0f0a1a041809020108010504110d0c030c020106050405060a06032a17 66
    0x5260010a007080307078032480108103190340300c2c0c500d01469411070800b1613070318203104984c1e19400019500003141c907052520b031071a503815640014005420325021000402031100070754048420240c006140c002032400d404903103402d4030001ea00518080d40160701608101046100303815410f66110005c100e4030808280140c4a8102c400b03500d84a040c002000c40706001460f0003408aa0b11018000c0102e404209000740501c0420f48a90040f8840c4c400000c510b42010302c0307506500244901c4412075400d6590800000452002019410030002100011001200032071300a83e1808181016296810280c0000d4500c001c40040c0d46024140901003000d40d81068906054070001d903808507083c82d001c032002d20244514805d41894500c2c00d030220895607032552040780382d910b243d0700038003405a48004010648409581040c1d005031007000400c803c80c001e50103680580701003402d00d08650410305015904403038150300c0d60080380a0000b408240340c04800322507400407541001505d008034084805 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 591285800 1250 591284550 591284563
    0x91005120616030506281d13081b1c020616080a0203130f061406041509020c0a0f0f1a07081302010e0301020406260714130e09030c070b0903 62
    0xc00038541e45030042801e83c0c8940b072600c0104064040c0740250f05c880203a04c0f01c164519072058020729201c83c02d091680088645113030b070058140030807208441c002a12009c1140e031040070740c000c140e01d034800c101d0903910060110407650111902000040901484080d0030850020180c031081240c48843d84407040d0098040303600010206401600e03580c511100707120f070708c8090798040c003502c2c01401c04004104040d00880c05c0c050441030901c10684401052005581c85038500c80c0030410395000904c20950f0b150301510b490030b500c2d01101c0c4543ca42c3d4460003850200c00b982545d20141c1c8405050912828410345040c102030b000925070107180c0039100030001d00028140c1d00c400075003e85900300f9a03200f05070300c1e844980001c0003190380300d9031044064010f5040d00c00810703038054840844941c0307400e1251041d10a039450703129040c510700030a0701c2c10340700d9200c1e05440c0c0190404e0320000c41c2185400d8142480390a0030b01c000d55030b5040c0c0b0b8048514000190740180418102002200c0241d200030480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 591287050 1250 591285800 591285841
    0x10f05190915020d05060a06090506120a02040906030305040305010b09130b060a0e150315090a020105160614091507020d030213090c0302070b10030c0510020c0910051206 75
    0x303400d407262500b1900440c1e584511004940085059400407010340c2c0543c5c01500c085400000c1140e441c541a138010701c440c4a0280d00c043c045c04010b1a414a120f130080d44000c8050005207030546407400d4000f110051f800030390000d000450180308000c0c09100b0034441c0c10301110000f44600d0100c00040c0c1800072401d0041a00c1100d03400b2481c1a00d6007480f01c009014817001c0e0309071610340700a050241d280c0520091b44207208003184155a01525850103002d101040c0190580005940066800c0e0744240e01451007900010b45880c0070500501c51291040600302c2d83c06a54208181a1f9141c404000c515482020001040c400b0f01030b00050382c0c9405006608002d40c507080180d1032601101c50f01d600603d60036050403a8808035580c10750007480c03541e10900f501030450301c1e00c00e01c0c0c0240d01554003004040003079006041c4102c1c0390211691818003110720460f1003030b072005004070f4100f003c290f841c40c14903031240106200900d083c442c64081e955284000b4000740c42d00c11400001402c00559 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 591288300 1250 591287050 591287101
    0x506040201050c031612230301051224040b060301020a0e09060a030b010305390103112a011b0507120e030a08120601080c270a080f010f05 61
    0xd550806000500903248038000c5d43ea9100741040c400d003400e100c408004960780f00043c2d800c003995001c000d0600c0c1c08402d0142c02201c03c90841e82406d003440402c540b103068014561040300b851803211000e03d0160002c0100020991142e800c00b0301c1e05520301300016010500c00c6e40140010102c69074400c003401031a40c0112101d101d00e480e01d00115180c0a4550805042082c0c46070021080c0700c0f0001b900404403044402015801c800205007422002e8040704101401d04407001521841d80b213030b0400b000c0c030701c0305a080501c3c20507000c030120344105803558042c050302c8680440401440080c41080c440d00e4005101140080a1640041882c4648003001345080a00139400881a12884e2000c0c0522005400c44015604c2e500740aa11034200c2c2c00d61195009055002456a51040130002d00988007520343d01d0811819039640d508a0310410a840400c250000d01280c40b1741d1402041801404488050b04107480c0c06074650382510b414480ea2030840d0b0a100c24880011144802c12036142e0700100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 591289550 1250 591288300 591288307
    0xe093103050d0914060924060310064115093c06040b0309100513030311070b1b0408012c0a03080c130305010204030b0108060f04050604020105 63
    0x38060794030703001d945000504140303080343c200c081000e1030701007000440c880300480f02c0b940c3d500c00103159500c005c0c60b400220009202202e0156054013040c140e00605c0050a4444003607602e0089800c40b6281d911440386440510351951004d81d440c0004108010183e1a200e0380000c114030700101400804600b900403046500c810100d554050280c07540010001c102524103002001e440d80300d0000c803150361050140d0203500c00d2180d1b0026040c05c00260001e40a40c0c105442e00a4640c0940c00c020031040d21030146008828411a05104440c89024100c84569403210a41001011201581c0c0d500c850040304120080100d84080e40159125546480b40404002804902170302805154007100c119824920000d8000c840414480e5401001e80240c0c1c04441c040451281d03115009600a0046240b06000c11a0285020014030900c04240c01d02048142d80b07555090072a802944152507008442c8014041981d0510590703802c8007003a00c00d05650708158403641d44910001c0c0c4003d06204000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 591290800 1250 591289550 591289553
    0xc01050906040504180309090203010e221b1707081018050a2001032c0106120c0e160210090309090203040b0402040b01050c1005180307030e0931 64
    0x81d08403070140c14007510902080b540c1c000e0302110140c0c81402207000c1418100d0220b1143c01c5882640d0403900c0c03002da40d100743c0c6c03907020400f10301154141502088800c48121200400d292800312039080d0035515030450910b00d0407031b40032500c848440aa1032682c200743c00801c50440002080c4100b00030800c0d0010f802401039030041c40d0300032240030050244c050507042206119142a0504005200c0c602d0354681c3c06803030700110103c03002d0034007450038600c50001c4e800381c100b540302104042528410000611648590b0b1409408100a50489107041705800038040e003980c60b40525001214208014011056040080e483d104a029507810540e5100755420034141b19071403110003402c1d802011503903810030742812400d4840441d02a400703241428004c515651245c42195084c1480d40040c100c01110032031440d02030a8087c2121150410484e920642d0500c180000e0052501c43d03224001146517400034041c61050080110010341c55082031400707d04425202070f80c0250043e2010800c003043c2c1e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 591292050 1250 591290800 591290809
    0x303020c12150108010917040b12150409051e010606050a081005040204030807020a050a23043306050306060307050a020703080f0705010b1212070303020903031303021f020c010509 79
    0x302c480041054080c00c00008520300103620910940340100490300720001000300020741803140303204982540008014240a408a50034034503000442120010b0f41c24200f080094261185140305035000d40140008a00961400c03402051904e004c8000384001c618200700504580590b100802c1400583c0001400100200b02111f001e004010320071500c854072401c20009981001004038010700c50210080760a1500310b4a16040f5201c400c3d4528500c20403115003461a1201c81d0401e8101c0d4803042c0f26076000c0c8680007140d50964050301c061541d91000c1202044005565000200b442000c1003803154603120312007280d5100380c1c641011960741884440c100e00c4d00b0140e80c8007070301001c1c021441900000c0d048000b170083d01e0191000b80000ca803600100200c242502c0c1c2d444005903c5518548000c41030700d0003501b02c1034042d090060a00500e0408070f820b50384542200741c00c00c881d80005104500c0d290744410002405421520b070302801c0b01802a540d10608040703903050100210f4001c2c85982ca = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 591293300 1250 591292050 591292063
    0x1d0a051f031808190215151815180609151f0908010b0301181b170c0108070206040b1f17010b030d0c050604150603060e0a03180303020c12 61
    0x4040540100d000600782142c03a40c100d0001c1c03903209144c1c1d00b0fa1240d80e902c0010314200032054003001c0611512402501980903907050040b40c0c001c440c0200c21403940d452403542601c2005281903880c0703441e5508040000a004080500000128200c01c0c4200c945504001d103601100d1a5044030000c00754000041c14110030744c00440c030460340d0900c402c48023548810010104c5604000911007030102c0803c060a0329002c422504603030440340c2c400703000b00f894840070070340414407020500c2d0019111983d140c90003101400032440c65100c1d012144441d40d22038103140e4013501074400f4221609040c0e07a55190200301070100380b55910918032841003610400c0b0050020144146120f001011000025000c0c5c0042e0340624881e0040c4024817000c0c9001d41d020390346c016400b80140c02269943da0b1458601103a98050807100c5a4414010002030710034881c6038547c3c1007040c02003500c040c10b807500038000142626003403003655512000b00006500001c0c0742e400e9160444410214000f9448590f10307110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 591294550 1250 591293300 591293321
    0xa080d0209060c15070e01020a02060a090b03070f081608060d080f07031d0f03030a050a021c0309020a060905100813020306070f0906080408030a0e011104061d0a051f03 74
    0x1400007501c44000074002405040b0f90351403030144c44c0541d0f01c80e5000e807800a1030104490141e0402a05035005103040c0740149841c0120707080502c01c00b911004561044d8004540044c08035242603540c405e01504200ea030350380400c5d214550404a000504010401d02025100b503000700b07010000321041000c50b80544a4000c0509800360301d6005c6030600420340e02c00400c120308580754910100646051100c0c400007a80b201070010361a000c8006030890b0260b0010310b40d6021401117040303080c410300900c2151000c124560341c010401e00ba81d8010010416015403080c0103200c6045000c10440d02e0b0214020098507503810074040c1aa9011004080f00220340002540340c010402046003450704030381c98016649580c0d407900342c1c081c2c60314401d0b5007042c0117840150115030103100041c400e09054020710503100d0b0f114004504c400b0f40c1010b507040c0760015080030b800700b030440131110740407528441d01860041c01216000d094610303003408a240036103110343c003095400b400040154030078000d8012035001c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 591295800 1250 591294550 591294559
    0x809010309050102181201050f07260a0905060f040c050f180a0203011508040309030209041b061d04090807110d210e0f01020c090a060308040b0406140703020a080d0209 74
    0x8444d890742035a001041068291b1089495103070ba40240241480391b18803d18042034204a152274000c8141c5048007034900940500c001840c040d6000c82030980341c540034094407c00800e07140090b02e819814028028a0024500c80341c0081102042c802c4c001081215802c0d510380400c46003680104225030982c0b222101c0a159003402c0c400c41c0d00d05540154100c4809821820807036407410000c413088542960082c0c00511440b80900241c503100322129002442000120b219600306420040f00e51000d61020000c5074903000c0c00f000e0302001d81c000050364002160104000700841d07540c4400303801001400307040c840000c02d406580c1e03112500c400c585107400c217409184512450b565000c000344414900e00025950300c20061003402d00451005882405070098a0003298441c107201211743c000340f05410303540e181d80c0f001012900b914000d00190000103c25541d071030900744003418180c504204100740c1c21b002c00010002c13a9000c980340c800d4680c0403607010390320217410201c10040d00801ca242c91f4071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 591297050 1250 591295800 591295807
    0x60f020f01060f03140303010b0f090f1c0c0b09210f0708060601140720130e06060a06020304061202070f1a06012309150409061706150a030809010309050102 69
    0xa280704080c00f281124802c0c0350031030002d05850b04054032400203205840780800d0078005040c14044090142120740d10181400001900d48030000f0500200d032182d051425004005078403c0c00020041030f00500003d0034001d00e071907e03c0d80071800311820407010340401c208000c070080300c0c01c10070b000702080e00703c1e21003c8905c0d442c1c507000950b03162507041e40d07560702103410300c4082c0098260380c400b5615159046040c4c0083c41410490341940c80d5a0020714607030000e04124040d00301c0c1d00510511681030740d911700400d0340d07140c448180800540c80c2d4100303c4c25580140010400380c0d500c4103c019140701c0740c00d40903884403518906401246c40c1008010451416580d0441480c00001007041c0f180c01c0c00da0b10094043c446411a0000d00401030f2810b0481d0310411401c01141072840341c002506030304500c03d614281ea0b40d0021001c88415801242d103170888060f00030b00c803800030000346800c03140880f5280c0501450f800007424a016034400204828400724104465a000344c2c0880e40c2a6007081c000d559 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 591298300 1250 591297050 591297059
    0xf0d1b020f0f070303050d2d0c09080313150e030706081f0608011e0b0a02010e1015030f030216060f03060b0408060f06030f030c06100501080907060f020f0106 70
    0x4841c207030388031441c10911407201c0401c1e0310400020718900f101d40548566280402c000c1c1000003900301c000424281e81e245070015401c0e0b4000034101c10410020b0100025440e456000007000000e0030350110066601c144204c41a540f510099030040791001c0d015070030b031280c0085080e40d4203403181e0398199150042d45000103e04d50803004951003496131360085051255581c0c2c007540c0f402064051000042c0041c0c0040c4005101d1182011107800300c14a29030307619545200480803940031543c40d83c0181d45a00c6882c102e22001c0020144801800e0310510050010704400218440c092001130600f6004102c201c0c1418002d01080e1440520518014191034845130701030119100e002814000078540780000400016540542d016118060040c11030760b1902c103400d80204d034002e1310041d8903002c0c0040b107034030303a00c1d0410041201c18642809007107646041c01d00011a21120390156050003443c80400c021844080364840031b903450350611154015118408a281400e8000c82000c40d40c030780b03100400e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 591299550 1250 591298300 591298303
    0x20a17010207020922030e1201020f0a0912121218060b10051201090203060f060c1f0c0806010807030609090312231605070804030602031501080c0f0d1b02 68
    0x101d41c90007980e018100382c07541c441804404e51030184140e0502d02215030480028402c10305001f80c2d80b801003400c01c80c0c403171030b40c801c5007280c2c0180740f4541c1e40d06c400244140c4880c0c00011040042c403125400075508200313500c0384040382124401230004c00603520310704546010550300c01068407002e0450103410702c034546003030402884886400c2d803242c054000400c003124804c40898005144004140e12039901e4007980c4006508050b000940c0700740340030b0341e000f40c50301c8410180041011400040c05503071080c116580549849040d00069203041890102c200b85c3c1100c62a9080f0320203207404440c40e65400800c9008003ca5008111800d051444d003e0606500c41d0f502c5003130b0319411504002800381a881d125000c2070000364441501c40000000d02ea07408500c18240c540005410158030b0000165601000c81e4402d40085403c641e010040c420490451848007811034400e080c42c5040d800d0000402d1068004d034800f00c150307013200180d003055004003900490104403104d81007502000395110041d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 591300800 1250 591299550 591299557
    0x60117090d031406031905030d0915050108010216020105070c08010e0c011404080c01110a0b0a091506050a180605030a060509280308091e030408160e0a09020a170102 73
    0x2070000e400c0070120f5101022010b8543c3c00381c10700900420405009a001601c0b0100e044020740d028042803107610443c6c10355014060819110349a50a40c101203518220100c7c0c0068114490a0f80b05008074101c0c418500d542020607502402e103251106842d181644601c0d080d90010550755081007080c002804002401c081f40d007200741c88440300fa8800f00340d00070490045110b1100e556005c0d10140541c2c4d402800d054030401303a41c2046d01e0200003180c40c3c65183c80c1d0152052030f0ba495407140c10780240041980d45c00591448040103015140c0751000284a0311503d0142c0b840441e02844600c50702d150950040009200c05801da440a00d0503007000d4004180860340780c2014000e101c0003609251020309500c540800c03403a8581c0600000d5201104c030124010507006d074078450503039090344002010750289568481c0d2001580c0c0c032403c210b00c050800d010350034110f40000d800602407000501c00005141e2001c9600c1c000141c0480c0c60002070f0b0381903d6035120031012041c04e01112055001034004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 591302050 1250 591300800 591300823
    0xc090d14070b0306090109050408070c030b16080f0a02032229070203040b0702040621050d1b12030207020d03090f0608011d0a0621140f120306011709 66
    0x1912241aa9803007407065500c0104c80040d403050100c0300511101a00b580f01c5030301f06001307a41890420317229940301d442c1c3c103000760010744040c8204010081c49006154111400803107518200d40f1070300340342040c0018084042d0110f514243c0102c00503034815038140102210383d41010107450a6001828030307802e40e086c1ca003110705000d541d00b0070141c8407a0106600d03c2c020200356006500e880d00c0c0145580058101a000301d9126484203c0040d800c481030314a008100f0000b030302c41c400f00b44a45002403501d40c0344040c803014000c1d91102e201c1d08207501e12041c044d05400010b0039008194150342140207200d5010002d40c814030540242d03003415030001c540010703032360106100b4042c180c540f80e00303070f03002c0302c00744156110780380c9401560b40300c803507142d6486404c1010740b0b0340441c80341e0b00c07114624000c00348118a0388250151000200c140305600c40013800f04400603000d0203080f83d45483d0152103090307610985400441c00004500c059118401d0500c112503a1220440c442c1480e001298652010700744 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 591303300 1250 591302050 591302053
    0x90309030d09090e0a020105030109091a010303030b030d0e0307211407080706080103081c0f020315030114040b040222020d020c010507021b0f0103090204020712260406050c090d14 79
    0x44d42c01e018540020380301c4506805864050441c0e00c2c120101d00a0480c03410100c54000185002ca0a02d00d1403201c118061482620045000c00c0712000741441d1000c114140410402c1c160350400c01900d000c1110000c2c4c0c2c44209911a0400d2111002c0c05003401076800101483d03001800ca0010240100301401960082d0303007610318807a62413000302c9044400b8040601021410400d10340121488204496003129010380490300004c0395080c0c1040342c000f00c501c000560020300603051f80d0724083c8038a884117518030000d01c90b03904142e01d5021820310020b000902403004c0901003c0d5070b00f04076174032001000003d0802d55a40107090b40c0d2601030b41001e9244481582840e01041c5010700105000080b20f408100501c3c48001e68000c110300c64498511050515942e00d0b4080c0143e00d8a00080641c140920000304400c171885100400102c4215890314461390030203892038810383c181d203501c0d40090b000540405c180d15a40e09510441c450800d08944c070040b240300030020804115480c2c004100e0040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 591304550 1250 591303300 591303311
    0x170a0e030601090e070b0a030b030d02010b130212040303020a050c011505120d1e17040f0b0106020a03080c090f19060207090b0105040314011e0204050a060c050d08090309030d0909 79
    0xf0000003d80e99003090002064010080074881c1348002005000c0704c1c105840c010030080c580c2030100303091010b18021000107035158020340506042807040410349203000c81c8114904903c5200007c0d1503c0b01070700050400d500090103c0d6400d1007a0103490780100b00200030081c46004110400d9074206d03030b100c0c180c09040710b0103000300e50f4800400c1c620344204031034541560201404960340920080051081c051080b2004000141a40001d21740e204074490300c031030520004d56040c10a11104164400300865102020b8400002c1d4032a00c03d039000801910243d07100d401500004400082e0340191641062510380081122055441c1c550100c8455409880c459520f6144a90070344603d0a15107010920411080000610f0110032030780c0042d419000041a920720034007003038090b0124a48820154004c030b82401545011046403004180c075041103180b0711039542d102c0383c9402c2d01007018030030300c041d000026021840c00c0c02201d07600c090060981ea9081c1ca0035001405000341400744026061804 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 591305800 1250 591304550 591304559
    0x60d03091706060411090319020a17010509161820071a1602030717361c11040b220e0c01020604140703050d030b03240a09170a0e030601 60
    0x31704984202c440680130b40740141c4d81c611180c03030700b511000040b6080030381a840050900b103a00c8085200584e103c00200e040e003000e00c9100e00c1c211602d4405001051070700800c1001d8031180b0310507009a107283d2400f0410700210b20741e118100101d4580b520f1f40300b100107035810802c8100349030b4898062440c00d5680b015140c0d20310b44652081542c120b5400740c1d004000000100302810301080100d012002c0d0a0301d0301018110789420001c20f80494101040c1d4600d41841803111031166029092060310301100141d0140e442d040300c00c800b044098030800e125107140c105900da982081d408903901501644458900b50421561140a80e052190b214981003112032002c9010522004a10059004240640307403a104c1d12002c00402050442c1c0e80f00d030840000019006118001500f072031520700280c40001c01080c941043c120b070f5261581c0d000d0b000494983c041350715a100c4d4001c441c010380012080c15519201d900d135000000c405c1d5071a80d000c0303400010240c0c080e51203046608264142c480c2640d0302c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 591307050 1250 591305800 591305831
    0x4030f030537030b0f03070e2d130203190309150306080c011b0b0f0f060d02010c030e0103090605040b0a0b0d030806041503020405070f02011104030308060d030917060604 75
    0x10ba8152090391401c0100d0101824802c2d00070042c50b59000341140301e20480400040e1600259030321103500d59644400700444c0d074031011800c1010000c1d04540203200c0390440b0340c040080c4402444900404800000b203015514204441c0c075461202d10b1001c0306c1008142405040d2603040e110394454410348204812405200303008a000301c0e200140109101c3c14204010f45078103030680080128243c6449060003c04c0c8000c588600a190600c4500c0e21814801281203075a80c2c0140748900600b000704a120041c0da016103407100140e0589000305007a100040104d0180040041c054042c50611040c0403d102503103450f40e000e0703072412208010340c6101005015480c048042c010700468405000030b1000d08064100311603080540e20201d03011510307580024119075040d140a00003035520109040442e030248500c0c0003008680007c03d00f02469950f0007013400d200280828051995400303184201070007001c2400280c0b88000b91a00c1b250780702c1c030501d543e91008581c9030340301d603040c5a0745c8502d0484 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 591308300 1250 591307050 591307117
    0x42102060115140d0504020d020d1103010c0f0210092102240606030c0903240f0f010b0f0d02042c060d121d031b01080606040e07120204030f0305 64
    0x95144401d0701305108203510f280244001070040e80c004805d10312600043c0e55801744c1c074820500c200381c08209640b40c0401e2508540700240144140180300d20240c00c1160006a0308040008600300414060624039002c0000a0b0440d21084d070000d5041c1d20001950300403881a030a80c0c500070004828441d09400080301200030f40c1d0f08c9030010410004503468091040c0204440c6030007804481719004464980d00810030f8003184560065544000e00421141c0f030b903182500002550907941c0d241d4140f405c3c1940c030b44504d0780900d502d40c1000650410403045901540c00820403421030190f82c0c6004070617000610071400d100b030006110400025103510341a98039610307039600014209195600301100b507810700d8820b20089404030700c01d8030b505007580d82080550300e10102014641c0a4042110014100410142070503100b00b40078002440700d901e610b541550f101880d454640d140c2c44148061800911482c1c00143c909002d2141c028145a0000000e20a0308030140300d1003002d100060381804c00c5034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 591309550 1250 591308300 591308327
    0xa2a14030d110901080403051e0a1115010b0d0228020f070801270510060b0d0c0c05100519090c060806040e10110c010e010917130509042102060115 65
    0x418800100700802c1c80341c0c0c0a88a611607274100d0440f941010801c0c403286404c035460103c00201c401002d10321005051003188c0790325032100c00e066130a5040c050603800c00c0c09007400081c0c1150f0301144041404001141800204c0d03026207987d00d034003c01d484002c3d1034007181c20340700d43d80d880303007010000d903148051103100303000b420140003c01410585080d0341d0204055100c1504d451244501d4106021600c3c4034440c001c28030344420316aa40015030655081d1544512808140540182d24a010600100e8000c85041c03044100060503a60b45014550035a851007046d890380c0c0c030f48000b0310101300a4150307a1341911515158010241e403890104015203890035403503421900319180c0344402080c540c0140c260042d01144180c2007002c500001802c548040c1050001691500200b02c18807c49007a44644440ba4031040c1e450040d060b2103c007442c1c0740500c6007030700412886000605010155000099010f40601c1c0d28090401d40b0f40020b603200c0080c02000c4003d40c2c86001d4440b454025000464103c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 591310800 1250 591309550 591309557
    0x9140a0209090a0f0609060b1002010618180f020127091404080d110d0c090e070c0506010312021e06150108010f09051506030c18060a2a14030d110901 66
    0x25134060351a44007510042d0030483d005a101c2c290108151340d461005001101158000240240303032281d40c6441410403140040d00e9403521124591180701061450b02032034011040c049141c0c40c502c0100e5600e9200341084066904404440c0c1c940100b941c10082180c0c040001031140307511064840714600341c00ea800906205041141d03000910117504912945103002c0c2c04a41030010100041042d100901c4801c0c2c0019002e82d02444001c070500c20094018900d803038030384405007a0f0358038107645a2042c000603201a481d80c07401c500d102d02c00c10200d0b0b111454030510000e04040c113030005540d20303015284941d0b40c02d45041c20720840d5115042590480c0ea40e01c584218580c504001c60b402803202a03c0003011009030380501a803a12008001d6005040c060401d9640e410412585180300351500305440c4148000c10000740c10f260301154420140310803442c440017035011880901541c002c040d00c02403001c3e41103500c50740d0740e08001c8094808000a0002070100e1000c56010b60000c0c42041c008a010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 591312050 1250 591310800 591310823
    0x705090a09030e130f060801060f05130609060b071401142e240212090405180d0807030e010b03301201060f0e09011809140a0209090a 59
    0x1010854004841c0503000381072010358015041c02103088001d5008480c404140ca9a19600304099240b06410003000d40300020401a401e000d410a801e80d024416107210b40d808001d1000c0541d41c99010350002d210a00c0100301090f95400060ba03030360807264003605c0000c01e42d8001005440d060040c034003021240c00c40c00d01a07955034045000502c61810016208060359044110071002d104406405083c0441c880180f21070034682e070300511342540180f0340031500000d080c1d610411100d000d58101700c40494005c2091b541e8a000401040449007009125204801003030078015004001140100c852396001c3c480c03c1a202195400c0c0c86d00c1e8070109816078000007103160400c029440c15000a80000080c01000b0aa5089138140b50002d0051700031115401c0010810650400304840e02c8156a090903000c1150103000109186070510903031000d22203020004081150035405000b500303610031200c8030600a00c901080c0ea82051540c12806800300307101049907a1800a41c45c0442607003e1000ca40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 591313300 1250 591312050 591312061
    0xe0907141e0603150d0605180a0c140409020409060506030c190902092e0e0a150309050f01021219050c0706152418050328050304120c050102070509 65
    0x2800c1d8001001c581314000100030309001541c43c0004045d01d103000e4500403516041c6000c0e10015101d060b031540c04580d0115401800088007100103100b2211400140505001c207040480c01802400c64001c1d80185000d030340a0400c21241c1c411409400c0075001c842c0c01089410034000020200000401c2c00b20b507115082000c01c096800401d40400d0190450745105140d031070a52035040003181603110022001c00060300940d02c081e1650107042c08440c0d0200140c0b821115007a0900f41140000030543c480d405a42032040401209110340000d100856403004d100040f01c51420041d01d2007140c603020200f92142096103405101e02601c0300a04682c9800314955401000b4032540c0d603401d50002c02074030002441104803403446001c0a440c25441c600d1541c860700104a40d0390310950403e66411450207125540b0001074610700101300060b101d2181001d0b20542c608031180cae02008025100000d0041140400c101d031031941e25114445107030340b064490005a07143d001c54040d0f01c4c0c001c12034000055 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 591314550 1250 591313300 591313309
    0x3090f06230c151b040f08120906040501030e0c03100605030609071a210408030406050f100611010207080a0507020102100b010e010e1309030e130b09010308070302070e0907141e 78
    0x1900136114120030540c4002c2c000c01e44031190460361100707000074102c20007041205004d002440c582075907040c00c10f02d0801c0d0740000403812700582c000d80781050b540d584940c0d0440030400071030350200c50060488202480c4900c0d0304006e0220b901419000e0f0084402080d25000c00040050580b0b91340c10601c408960b0000403d0100c1d0412001ca04501b1907034011041c80e451480541e5006501889165940b45001c0c1485015600054450210307003246108100515420031069400c2d15460328000702003c4082894a01a0150a03030243c400c65000800e007a50541060040c41c45c0c9100381c00750343c0040440755580b4112140708482d40c0c04141d100745011490b610400064004080062514024406d03124410b4111190307010701710082880110410191325180e010445403030f10100c000d004140407000442c88404040c84024030000300070034807004150007400f841000d00310242d00c0e206185424562161380d081c5d180304221000070300060a4450341003000d000d24116588140b6089814000d40600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 591315800 1250 591314550 591314593
    0x10c053304120f1e0f090b0c060711031c0e0705060c0c09060409051b09010f0627030f0b04030807030e190302120d050a05070806010f03050403090f06230c 68
    0x30400c21000080304101a204550601d82c1c4d200c103039a940c0c2c00d010a40c0800b400c00210764011607a0240244684040c4503030000c5d240741e101109250013540c0c915098915840c60041c002c032103841c5001413207540440c0c0310b10350103203240154540440f802d4070341e0389040c491207200e0503003409101e4003e20900358960030418005c1ea0000c4001d04005024001e41d122281000c5800500180c0360140c12102141e61070510302c121301420100c10700c02c05407464400003518030041a00e4542c504140d051440f0b00c0061842121002181c00c80b8190700c40b240390303103011880110100c8003100818503480204840070b00c68070035420300056060051a4882c00c251006c051100340c84822400c510404851400c9214000c021380b403603903035501700131511381420a1054190b0314028419820048400100042c036a0300040340420441c1724100024a40c40301e0404441c004c2c1e640c1c10131186c510305401c0c0040c14650024150440034184e9661148001420282013014400c001405020303900c4061058000c09000000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 591317050 1250 591315800 591315827
    0x70909020f0d080903010617071208041a0325091206110412052104050904060921020d08160f05040801061d0702070e0a0902010c05330412 61
    0x7200c1055200301c001041411070600883e030045010515208030304007400703810090141000100c44000c0d8003801540d5802461103202d24200314450044103002c0f015088401500e210841102800f02e402c407690b41c96801070750144400e00c4044003620710841d64070150072108a15a072010317015843c00140341e0700c4c8940040141c600e995507118071403811301081d0050008210702c11000801da281030401e43e00f003107030a815051942c0e002520403d0762050b00c3d000ca5003960002c4595a42e2a1500d081400080c01c1c41c14000780301c40c01000b4002c0a0030415040c008020846900701c0c1c0c0302c0d8130041021154004207440d00d01d40783e41c1500d8401078841c05681c14000e1460309103442c07800c0c82d07a40c220003400e64000340d0000d034010407200c2c0040c0040301c152119542c0300c0782034001041100c0c03803c8403030005c14030001d242c0130100f640c2d60303045000c42e0f00c224003a004003504901291940341403001c2c4c00b0a8010022815894100c11440ba04013800d60344a1a0703103d590002d8070540c0740d452852060300c9990781d5070007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 591318300 1250 591317050 591317059
    0x305090c03010608010b1908060711030706020f070c0b1201060818070b030108071a1615141609031703041703010e010807090603110f0a0b070b24010207090902 70
    0x521035094809108090040004034008200b0700007131403c1c4000f40d1860b060407103c2d8806c4500c01e1041903000200e442e080801c610b460300b2902080d500daa8158001d42030004d0880740000f03000301c0044070b0040034142040c0610290010745558120324940b03072260074525102501c201004002990250080303682c8000f2800e405101d00c004055014207158054110100c4000080300510000390200024030161200038038208840e01c0c2651840b0350341c02140c0c003140b1395480d2120114104072605487c00103002600d10240000780d41800c0f5566042000c4804490164030720443c9980c2038400c4500340c04072900194400004810960014216480240160382003803a41840741c4005400b0001140280480091010b0700d5040811050900c8610b50000c4032940c1404802d10220b400c06010304a080e4044a00e00c5007035000d4004191005000d52118009144c042424024840241c80081c0305403c9400c60240d803241d80a10f014140c85130700d03091760059004100a10040e41d0551001140a000a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 591319550 1250 591318300 591318313
    0x5121908040f030c15050901021915050f19111c060305030c0d080109050412030c0e0301050a09030908191415040c03060516140a051309051603050603030703030509 72
    0x500c5200c860b14180c2c01100c0021884e83c4c20400840c8060380803010f05403d180003072138005c1d840700003036075000705000c2c00000c4034040c08100f080103040358203d00d2060241005000b14030342019280d01c080e03403c4030800a07030746050400c261f400c0c001c2d204500ea18240e14204a0170071131400c14204004d140701210742c060564940d0048040341041002d03100e4411143d000740740e84a1003980003800e000040c0c1c0316629050400d002d02001580c40071048859402ea483c0020320708140e0a01240c072003a401030401c0d01540390200740000380d4815040310040d18080e0b200d6020040d5a4540150364138204410509918482ca11500001c0c1c0ca10312001e80e248440c0c41128480d040e00c1d90108510103083d01d0403151118104010010000c050080c2680b064030720071001c034142005040079103054200c25040e100074100180680045008500f9500e071130706a54000c1c103a440d143ca110100400c001e40d1018030120070381e580c10507000d00c02c5c00740d40d00c41d030030150140d42011030542d4160094000544034400038001c06 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 591320800 1250 591319550 591319559
    0x109030503220c081609090b0403050c010b21120f04030206070c0b04240807021b03010e030415081602120d090b0a0f0f020f1e0702090c0307090512190804 68
    0x809500d0084e052000c060500300300c1c40000a2510055640b1148107642001c0540011410080300ea5a00c940c06050240c0d45402c40d04405004105030842c4e50351152405000140381c492408803c0304c107035a03103402c40d540c1030381802d06440c050003601916500c8401c10002403005081440240040501ca4819030907d50740b41c039040189038000744c208000c058940c003480d42c00241103e81070b070b108002500b0800f080741021000252a10b00c60f9000205440044008003880e840950200001c0f01c070b29000d03070ba02d071602e03140c44034083e0005042c1880021845804551400580c64000507044207030340090408016582e01d0346490f400200f940000c4070790303a000100122340d0304074002d4407884e0541000a4030280d011804e404507030314440c1e6007110398410b004140c031383c50454088406c0c0c0203600f802840c100008a0380301000b0300c50f0070002500840d21b2000c0c450042207450141d030041599454201d400b80d122014052a005032002070b0400b50701581a01514843c5807a0080040c1d005480c0b691806484 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 591322050 1250 591320800 591320813
    0x180a150e150a0b0a060f0c151d0f0d020a150f0218040f1109040e01110a0807110d2a060606020706140909010b03280501060e03010903050322 62
    0x81c0c914080d07403101d01020003000307644502c07400f10403110485580d0700c044c1c00c1080040c00e144011000d0707018000740c089140203109000e8062248007024003014001d10940d1100e5540c089020a4141482d10810000440c0c40313602040c644011402136000300102216500c0710301c0010802403084c4403499442c001d907010078515000030300c181003001400000f080c000000f40412606135908480340140380c45450340c4180407020860705014000c8a011900c84100070700b041c010100c2c400c2d15100c44030f001840d858800e4115055504c0744c032003074851154003030381d03845019218404118070f0f0703000a625100c1c504022071118200701070720800d108548050815030ba0b41004a40c0c50342c001c000075030f201800802044e5071203800d004401076101c1c0001c1c14103440202042c2c0040040c05401c240d500040005031485200101d110390108400103800321440c020848a4000c107002c1c040c401c0042c075080070142c66420140a204001c550550fa218515650550071510000e04001d00704201819076100c42e0100e0103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 591323300 1250 591322050 591322063
    0x6030705120c0c0d0c02090a0c080718121a090705030307031d0a0b0c0d11030d0c050f180901050402120708060102031e0903010b120307030806040212040308010905180a150e 76
    0x41648441e181c0d81796070300400c11803000051207160064101006140055845010260400a035003055003c0d018000e00700c4200c10300c1904021400d401076040e1130103110b4036240c80c40609100000030042520340c40303489a107502060060641644c0100201e000003846903030b002d082d8517240380550400001c1c1900080c02d0f9103250380415246140412903940700355060000c20003543c03060518a40b00c6020b4292903890b8015290b6a100d41a41d9881c100440d07409041110a03480900c12001ea803041a006141d000c0e140a03002c0380d0161050b0000801c0303034141807003241c2c198040e40b43c0f09292030b501d00b141200c084c4c40c001e16840c118003040c4000d003011700e002d0315207100300d5121503022070f19074440b0400c2c142100c0c040c2d030241e4403442c001181040540c0000c0b0842e5070060b0546001c01c12540c0740c0000c00c01034410400a00d071b401088408220a05a014100700d06031480c0803414041600e5004c00c3d01301e802c2e00727588040a550040360440c0e00180d0042045d0b0f0819044a41c0803c0a027118200e403810210f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 591324550 1250 591323300 591323323
    0x12060d060f05040f050c010219060c090f0306151406030f0603010f090c030b06010e0919060302270f0105060a050c0a211707050f03150301060602010b0f06030705120c0c 74
    0x161341880306042100c04d00412900c00300070b01c000e02c00e2100310a08420b25084158000d40f0322036131502416070b414803400d9460050801c0b080c60340406603072031801600411108508940c640f0842001040040320000c0040422200078000303400c1d9151030318140302c00800030340316990642d40d611100c110189035003c1c81415a004a200000c0185503003070000e42d09078000d01e40c90410581c1c06660480380d884800c0c00d0703041196030b98805e000d1043c5c0c420a07401440140c001075804030368841e135000c144c2c094255080143c910b000c40d81c00540c4644400003003004081c0a805e502c0101407100c40300891161020b05041410113007264444511500e401001040d55900c142314140d40c0c00c000180c9541080c1008500510600c44190a2130080300c01030250044401c04540701c140003000c41d8468a6068140d880320400034020090195a0400a8000c010b01459075000e000c0b1800c1d2203c1d98902002524440c6072940c44182c03820f03500c000400300c00c070001000000560014443c00c1501c1c40c0030002803401c1c6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 591325800 1250 591324550 591324563
    0xc08062d0907092408070503090106120f0614010f091e0612050607020d1b020609031204082803030c1407030c031e17060a320612060d060f0504 63
    0x71401d041c049150740c4000280149041d00d60000d940a450f17000303114651046051034007e440741c80d103aa10a000d80301a81c0a0044844401302820a0241c60352072510428420401005003040c5048400c0f0400000d10512040c80c40715402004200d10907048040514411000901c800c44c0c8442c00348200c480340d800030074610040d8603812040100820a0503000080c0d40001c004136842114014642215a0058410f0000308402d02085442d020700380c07095450010103403000300c01c1c0200d198402c0e41151140040c0762040f061203021002001400d50305030000c00003140b03440101510143d0180c00c00c4a20b5030100a00307040c00c61130200e501800307403c02c04d1083e6a0700e11240c00c141401031017117040051002c000d0417010360180d030442c0c0140302145c00c030000c10090103142c0d41d40000540a142ca5505c441140f85603401000e200f04419441000f03040038441150705015840d10520616000300b8225501c040c19910101d015490a20b41c0c403e51944128404108078103980d681d03000740c82041d2400c0711030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 591327050 1250 591325800 591325817
    0xe010b07021c151503021c11010c05061803090607060f0c05040e0402011d0310091e031d031207030206150402030c07060203060409020301050115030c08062d0907 71
    0x840c41c00d0442c800c4002151907407026031410b1610740460300c501c079420110352155100c003032061802640c0980d034002c50b00108502003030081500f040c1403007a40c800040380c820f22034400c841c00304d60003001400308490300710005080a50b031b01450210b0607170841d003240c0540d210622120003a03980301c07001021460303c02c0310b001c194031100c002d1a2064801d29810300c02032002c2800280400c0c99041c0d4503541c002e40920741070307441c3d0a600740c4604d1403031800094603405018401854240b901c080c0c0110080030b206002c0c01c1d0b00800305448051811f10382a8009000950641000c04440080100f0050303c81d002020b481d181c070124a426401580140021000340c3c018204205c2c5481c41107002c8145544161020741c954a0184500e021910070762100504c600e602101007410b5440b01e90050714800d60190081119585440460704441c105d41140b90007c0d040412860039a48100109806440068000e501c03000d10303084030b0303440c09900840c85e401c00251151821059950621190f014172078640f40c010340c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 591328300 1250 591327050 591327053
    0x3090427032705060d02090d140c030708030a0503010e0c0d050703050711010c050901030f0b2e0c050d11010905100c020d090b030103111305010603020d0c0c020d020402030a060e010b07 81
    0x400c40c4141042d60180c880b4403400f0003403901d0741421141d030602048030045e0307103520540024668850480c0040d141c000144403071040c140c000501c98520f54400c07000c03070b4542965035591550b644200500c3c00300048050004004c0d20941011594101300b414081505003041500a10f0441e0f40c11200000000d40350410701c0f07540c9070000500d1401981c0c43c002800360500e0701c0c8014001c0d01c5900866810144c0c2d40b0340103620b080c45036004881c0500001c2c14004150440d841940d4000c0301c03807241104a4094410904e121030081035640c203080d40c80009043e1804402c4000d48150b00c801503490f07159502c0e242003d0004406002c0d031460614000d00004100c10b40510091600c074441d400e1606221408406008403503000050324112640003012025040780040815501074010381190a1a030900001140841c0c2613000f80410f18240c2d10200030b182114035048880441c0d40d000a5009000844c0300009400c00e42c00550b4040d40040300803030784a03034941c0030a03103180d4264051000302101080120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 591329550 1250 591328300 591328337
    0x4060b0103060e06030a030813080c0706080f1012021f03061424030601180902030609100e0f070509120309090c0301180917070f0b06030f0309042703 66
    0x101502c100900c05000c0e107016401710b941ca03011b0074009828010101d0005401244844860700c4056200440700d46868070300c1c5d80a655140d450180401084070030700083c6039900d0300100103100d5110000c0c649501854500c2d480390054400c8000c2e600030401c0c0300b02a5011524052013100a603072540c1c00500540345c00c000803901080c42851902c901c0941c004080c140c4100a0a0507292190301240b640d00d49980b00140c450010342d000504125821520000d90728907994003a41c4148025100104280c0d02d4540c000942101030181c00148006040480c4154070b1404040b80d1102c01820220300c1c0640342d60028000c00100e00f1b42d00c203140d000003072411003030918072243c0740c001802c505200c0c00c42d414014003440040b865080704030f03459941c1500905002e008502c1e950500750903100390340da92040f0300b040481c02103003e909544100340040404c0060600049610050310b119010f5414800ba000410000c3c103507112080c1c4203406854005816500c40345412003000748662180000c9400041c13419 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 591330800 1250 591329550 591329561
    0x10b0307121107110f210705030706410c0c0405040f02010f02071e06110a0804090e010605120114091504020111010e0109080a090f050604050f01120504060b0103 71
    0x20601802c21511214503800c1c841640c0c20a548100f808061180c0c00000c1501101c1c0e041e0360a0340015100320301440d40541d0a03034902c5401514041d20904c0e42c07641c0501d6500c14145c82514000345808601c1003808100a00084102030b00030003211401203210b84625034903200f07000a030541a000168a40c4c201c1040050448621094070207025034a400e490b19014401200f401a05100d050076110b1000d40c404e0040b08007800c00c0505910484440c4150018034405502070503010840781e415845403060005024103c940e40841c20a10b454148400304020300103416811085648030040810195507008420503902d444a000140c413181c2201c1043c61b220010b4002e5245030450342e41d00e2070b03200750b60004691058081c01d240c81c800d902d4651a6004010018a002095180481030401c0082004c010314187d003166898034421a1111050b004d5030000707104556014400300420062401c0c412070200c018041418400d007081e07480d004000c103030740c000c50342202c00f10381d0745550f4041c941e05840f94 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 591332050 1250 591330800 591330827
    0x80a031e020309010b120706030903020a121e03090b010612060e01080312060604151412150a0812041811040303030915020304051f1803080906070305130809030a0803010b0307 77
    0x61b45c54864000003030382d21011240540790415444107061028140200440442d01d94082101041e44141080080405000707540d40c420f091402840900c07900c3c840c0c01040040e64200c1c1c80c0c1503c5928000c0d05171100088030f403121081c26150040050508010010341d402400c0307582c00345680c2c0801401d50a0a07081c010100c601c00c28090100380010083d08074040d04110369801c00301d014040c801d01c50680c03400350b0084515000400000c0003170514010309510000003041c2d60340c030344494030390380081e444008240004000240c1480208500d03075402d0751350030649402e002c00044071000d05000c04120707031141d001036000c2a11103000c1c8040090315508641c3d80070701503008600b103003001c4c0e80b40344d00d41002500c20041d504e840803ca00c940c200a5005d4444001010080d02c0c0d0181c140c5030140c2101822a103498660141d034001900060217400380b140b0a24440c0d182c052401000c1d0703a1100190031520440f9050720510320b58100044000000310302070b1241062a0b600c030b1809500092544048122 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 591333300 1250 591332050 591332059
    0x1e25140102070e280c110c04181106070503030f101d0106030914010f0c090806010311120f0a06060302091302130b01051207030501080f0303070903080a031e020309010b 74
    0x50800811251820f100c0e0403149039081c081041ea03103c6603450310a10341514002407985400c0c505611213400c1600580da440b1010309860031501c0240422044a10850b19107201c0d01c480d0ba4140000744032013205e65a41000240141d040000710345800c1e141d40c05c100c60010b14440c01c45e0038016541000c3c00f03c80d0040a111000b000903038078200c9400f0300c06006100c3d4009040d265007070b0b20100091412002404440c000081040d0000c08900002400070b1403107280104043d001c01040258011655a050701d4001e107020614010030020b010701070704081d6146c140c0380200c81d003030845800c0074406c0b6042039000300c1c6c000ca0b2040c19801000a030174405000707030040711000c6007054016102c00d1442800c8040c0ca001c001865940b43c40180c03079074130030740c21100511000c9908014070260564402c5050300c0b40c0804440103012100b02c01966480140c0303a0f00e000c036505c1501000006c03a0b400003800c0d6036115160110f09014103a409040b01e202880007684595000700800c2018a03091050400c1035a0031078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 591334550 1250 591333300 591333313
    0x30201061a1806030402010e15130b0702060f03072601030201140910051605011104080607020a08031909140616030605010e3601080105070f021e25140102 68
    0x21501003894030942d29016000110000341507a00032640402c0c160405844030310448508440c08645034442180c98a800b8010000072803000280401ea0f00c8140d800381c8554035140505540a036981c10041484042141c1034090070001e05e45529102c1ca000409142030f05076504620000d400c0c00307240309141c928401c1c24400344500e0380e0f42d0000400600b1441c1482992007000d0829000344500c0420041c00035800c102e91028288001c0c40140116441c4030241c03109601d070350900300d1b264206000003814482082c004514075030700c40c80c21480d154042003c00103040640380c0d1060405040c0319110001078211348108410800745c241c0ca01410305182c601001142c0c10440040c02c1e0f0825078070341c0c502401510301d010901d18841e0880000400da20399070b03060520050b2500c400c40d4007090040b0700e946d5080c2804107a0450140500700400c0000350058241c039104001c3e880c5d8140c030000440d8000b48500e1030070740142c0000c0c405d4200600d1031021003501d500c0c100300c4d0499044900e404440d0441d40042c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 591335800 1250 591334550 591334567
    0x10846050a0c170414030a02060402130507081807030f0f110102010b031f0b220e03211e07020304051801080703080307020a05030a110607090b1e070f030201061a 71
    0xb600208070f0031a0344500e01425100d41c00d207203409803100d0320b000d0300500c000103000700303419000640782d482584200c4414105001d5034406006840b400d60f000c002003440e0802060341c2c030300180c4000c100119250212018030740d84c1c0d1101058004500c00a48a50488151141c01d0064100b4507060f004020700007400030514090101ea03440500ca00e001c6004003442c600100031a0880c1c104d0a84140010300c01c584030180d90780100342074a4088100d106031131929081108914011003a150024500103114605d00c461100c04101c030b104c0200141c840d00d0205540c1004004c2800b9868054600c41c1c0c0191303101d81c24401800300600d0201604071310301e52014010444070000003500d60640340d11802c5142c07a81c82d1110284e25003019400010000d01000c034406800b41c2d80a101c141d4102d41c80003c45880fa1503203601540c074450340b4000c41004210401100303800302d01d0290444c0c4002e1603c5003440c50480c003500e88844c080500c2c074080380141d4540204000503248072480307546d1007011110f4549001c500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 591337050 1250 591335800 591335807
    0x51e1005040c020c041103070206070801120609050307020d1b090e0d050c070b0403050a060c030c0f032004030602070203070b03091515040e01050609070c02010846050a0c 75
    0x240c429284155110b034021007419200f44000440c0442c050300a02201d00c00b490340400300c0d00100d0303201d0014482c0e5400a02003030721030720305039048525502d84a10301361160f17140c00380601040c21098601c3d1104101070001600c2d084070080409002c0d0000c6134040316821820007aa82c0b040c0d0050010300e0602120802811021698030060030140c01c0081e030390051a0170780ea01300003c9911200805001240001c203020002c80c0307250000e442801c042141c400003440c150102c501903615040091590303007c481e0998065030045082540104400f032049102c1c0303a0303580443d4840d420481d031190300410014118281000000d014001c0c065a079030442c81c0c00d44040d41c0d11001c01c9001403000c00541c2c04210690b001003003420354075074040d1003800080c085400032030280505881107030044801e040042e2120b0300c9218041c29a40d8143e5490340c0d1030701d1b1402910b00c2000003030040b42c042c03400b40c0c0c81074400424034851030464022a000021140c2c800c00d0035441181e0000744030030262814440940e036407551 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 591338300 1250 591337050 591337081
    0x90b1009090e16061215061b03020f0a030203130602060c0304080f0f0a23040503030a120609150905010e06130c0212270d170c030d0f051e 61
    0x9503050300040500c801290107140440d040c1c0039041843d5010b2012800d0343e031140203482c11840c4174005000220040d001071901540504c504c0c40011a140081e940c001446140c0d90482c0d0302a204840da60076801340464204064000704070f000d6440040c0030741d2440d05005010000701614005002c0500d03150341d0b02e80461100a20042041e0b10029071500d014150750240e687d4140041c40d0181c4644c1011805010b600c1c4c14450144001010031442c40e6a058041c2100d0944d84080d02071400c0c001c00c00c80c1615041c0e0740c0981200c045441e08400700d12070030984200d820307020341110220803040c80c141c8004110b41d01038211412218014080040d16140c0c0009200403010000002501030b441c01012810320b220001c842d035565000113101300030188204003411050340907603a10740300302019504000c000c142d4a50020100505c0c040003003a05274210000d0a21125038400b40c9180400e099139807800c6806c0102940e048035034400c01c0c8100c13000b441008a24bc01030703030070800c1c815003080200c28082c2d42 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 591339550 1250 591338300 591338309
    0x91505010822141204030303060e150f041815060e0708100608070e1f020c01050c1902190b0a080a0b090402040510030b011502061e060906061209010501090b1009 71
    0x100d40000d0302407140700b0130060034508110000c8039125034503481c0090141046110301c4282120540114025400c0d10044240041005200d9208002e800c8184009050340d103070707030804003003003c030410002c6941c09402094045100500044507030030043c4e00c4445c15405405001084000f00811080300080c03a03124050b2903084c18940c200d80d56030710701240d04020a52900e5000411011040780b8400c4449140d07801360807076000d4500f141c2c00d04c401101c06018001d0801c002e1342c01481081151000c0000703d00985001401100b14500141c0c4614440034659102844035500000c60103130301c9501045c181e4016038080024401141d0030b0b0000760700d252019001130710480d034980c0450810545904800011940301020307141319070b0f41d071004000c0484240410300c05400740341c00041004001105c081a0f009101d8001c510f42d4944070148028030788024803280e04400708111100802003440758080c480d580000000c904d0b981004622015202c4154400c1c0c007801840c6540903203590417104503070a59 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 591340800 1250 591339550 591339563
    0xc020a05030d110d020c07081908040510110a050307020301050c0304050604240606030e06010e0c1611060301080105060307061805060c07240e030a030c0f020a091505010822 76
    0xb04100c0c030300f4025102c1c07941c0c80001c1c140b00040b210411340c00400c4000c211140340094500645440850407108010310b00e0041c50160104401e01042c81c0011b820194000c0e2480c09800201c0000b400f03030b00e006041c3c102540c490340041840f20862070309004035030b0f110590000b4141141003580d291a035508019000419059401c02e0500303942003d00c480c1b01070015100d00520400756504000750040c034030542150a513028000020540020a0304107901442403481c0503450640001040c04100b404880b040325910b98179184152103585100c042c5028052802c000a2141000010507203089419405402403003507021188107a0780d80701e00800304030754041d250b2640d11018894010f0802c1c09580002c9001d1013900c40844c415814442c0f41c416101e030940b200003034105101c0405179107150000c402000a092600441c0c0080c84156960f03104610103407024034411703100d0107000107880b85100701c2c6d912041603001c204803035a03000e000c1e030340c10006100501a2111154401d228611440c00b03024081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 591342050 1250 591340800 591340811
    0x607020d080a2412170f0a18050915040e060609070e0a0b07241a0d030309050609032214061b07080606150307080406110705070b0307030c020a05030d 66
    0x4400701440360500082103c0010303101c0c1d4590001c14492421040e043c0c0e00950b5500d81d52a02c007003500c1c00c0301e103540c4056442504061101d44202c0c0c2c0341070554081440c81d50a941c002425896400840380141510b01d076034040d038100c02050204035401e030744c0d0348101a4045400d00c03440e80c40352030300150020b106180a1201c42104008141e10060541c862218030300b0024102d0180709084410703c04000429402d074041c0780c0b0f07121081041e15070b106440103042c81030069010b02403500080080e00307503221f42004101c042c4e85403255820240101c44c2024190000200c00c08425044510383c1c804100d405244a0380c036081596004003d2a4258200e020f501c0c0000d6070502640080703034401961840c10100c0d0100e070707242d001840d240d100a481c1607000b0482a01c1d0052261612410350b071040c0c0c50795858403a281e40c3d503158440074007076100001c030b40040108004030103c2d805000c2d8001070301c034a81003907a82e802c1c4841700400701d601d1803080d00c1c219000f01c85a080066004802c86201491519012a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 591343300 1250 591342050 591342071
    0x90302100e090a0501060e010c050d080a18050601060e0411030f0411030304080708100905250504092a030807140c0a080a120509010504031b08030a09080607020d080a 73
    0x8510045a481d035500c140040c0400c01c40203c160407a605070391741c42d036607406201e4a40005480c0d61000110041c120b800c250000811548100d080d198460091140410a4282000328000185c540c01064969030010300050120940111072200d0400d0240d030200515010b00c0030050301800003810090410000c003000c1000e000e882da404c0d9041e02c80080076039607030b107560700203c81c3c0c0d0f02c040f80b103008214080e055052088003090b100b5500c2c280d400001411a10044000344240c0940d110070781c5c10440000713180402c09840341c0c45500f4103d445503240c035510107605240d5103800c407694640d034040114421814000558404107441f00b0503031044041c400400c0250185042005c0040e285410015048d00000c2850380000c1401589000783c0c00603070350a030207070340440c7d0390311440324070501040b001c003c20000100b1403903124070040c0011598161403615000e0040c159032099800c6030001e40350000611299505210311a0481c1c0c1a00082000c038582000c0600140c2004080e5005240c0c0c408550070b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 591344550 1250 591343300 591343307
    0x5090a1a150f01051b150c030103140d08060d02010903080d02041e050d020d080c0a06060501032405010f02010608251509031106190201150e0606030609040510020403030e0108070c0309030210 84
    0x3542c4008525140006e0302c1c0195170202c1a410911054801c0120003c48462800e4041111080000c0d150340e11081c69850805022410482e08030890400544800000c086880500a009000c1e403034280580d540d86071403c0d03d260342070400c1040700580061001002030359209032492554942c10385903103c03d5180c0f170601a40303e01442202070010b0040b9040701c1d00300300150b0710040070b070350003600c081004509115a1410945280c08041201421342d0018800b560191511150389800c51001041603a165542030341404c400f54400703001c1f400d01705000c00d0300414a441410292035005030002c03500810400080c42401c0521019041c40c1070b001a078000c83c1c4542044a956080c40340c3e14804001440d00b00134020f0140c0400101c1c01c8810b104007043c10860300c40300d1406490001c0c003003800c40d160801080381a00c0060003c981c140f0545259082441080c00130b00020b41c000d4603800307410443c40b000900100c100900c0c940400c052840440e00294200030300c4020707a9016140270400c00d20112054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 591345800 1250 591344550 591344563
    0x171f0c020f070f0f0e310f0b040c0509043c030905010311040f05060c010b151e25060b041104091104030201050a0305090a1a150f01051b 60
    0x507281d0081007400300702e0148811004040760045003000b003086955550714610301e541a242c80040c460103444440c8401c10310380419030342e106440100302d18102d117640c4450802603890400c5900381d032000100030606c600040700358001d210030b40360f1324054541036603401c01c005c0070000d18565007800c903200f10034104034261803001c95807181d00300e5214071186820041c040042d83d2040d2800030b8100810407035802103080c10f5504940c14010501d640034180820400c00da00100302241c010340d6505890300a955074506040c0c580745e6140900c0d56180b10400068949003294803c0103d8040c040081c1c00c40c021810a111150907000070142c4a50388451070500007030716407008a43e51142c02c1119191207034100d540100101c400d0f40070200845000440c0e4881680038610010340400c80c14800010f40900942119910400d100e0503544103035203036641c07801c00d00301c41000800d0700003030384d410041c0c00c140c41070341d080d2002c03822a0095040442180020486c1c800c0c0c018202410b4100b44181c60948400c1110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 591347050 1250 591345800 591345823
    0x6040b09151605040f26120d020f090a060504080c03070e04080a120e030c100c1434060e210c0316030e0306070302070f06050606091009171f0c02 64
    0x20145e510b555190b2444034401000ea400900f004025441464100c00252200061007030704a241c10051860410320003508910400424003904001c00891680c03110840b9006d040c8580300d45458900300700c44185400302a00707005000c2ea100d40c109001c410040b01c845540594842082c59036247c00d43d41c00ca0f034042507811340c1c1c03460f075040000d00701058102202414500540f242250013045014440f841030314100c0d106100410748210309840d0310b05d1004010910a40e4941c4a1900c081070829416501111300c1080210100f4201881d41084418010b5100d81c0c400200180702c403600101681c03116035030b40030358130014420010300103042d06000c1c82500c0f002240038880d600c11a005082c080c1c02e0150820060f8030a0040c4000034107c03074003038429164400d40000d08000b40010940c1c1f0b000c020117018180941c007000c28480310b041075550407690084052250345116145103441c0d50421250b44591200c1c50035000952480e40300b102213407001c1c0359064184000310380c00c08001070690601601d90b88 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 591348300 1250 591347050 591347069
    0x21804030513030b01062d0c081308070302041a030c010e030c03012a1b03140d02070c050907020318041805070923090d030b06130806040b0915160504 66
    0x100106104c596a0082e0494001b0307219203a981c0078420405000c00d8013414109543c2d412420303200a5640305085101ba05885045200c1c81c1010404030341940380003650100c503460703000714001e00c2142450b000c0c0c180c081e03141c41c00010300741202c1d0000a456000501c4600d041010050501da000d903400c0040c09051280a17000704641c001c9200c144412942007004000e8208855014140701c600c00c01d50011448255400d5400740b1400d96021158481401000206841c05100c102c1c68200036100416280780328004103800340b440d220901041d850003c04541c195082801080e400760001c0b00580b04818045a0000c0e90701c18079103d0b00c8040945150150081c45109004a40c201c0a41d00440380c903101011580b501c05c13030f20404001032940403903d0180c5c58115420411400c0d000c1d800035003080714000d06442c20141d5000d074620103000c044d44428400e0703010b5810b000600040880241d08036045030082c0140ba0414440c00c14606c40c0a000341c212000294031124a1500c58002d0341c0183c1001c2c034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 591349550 1250 591348300 591348337
    0x302190e0f1201020d0b0607030f1202040b04080a020a050109210501020f0a02030309010501090b0d0b07090504020f13090903141c1806182004020d060603020301080d03090218040305 80
    0x54028000d4000003103a1901503d00703040246d407494008280c8000701d500d03a642031009100f00e00104c03590a1800b582c0d0b9441130b0240004501c40c0d0b41c0801800213070445000901c4071081c10700400240e640702c2d621450620261400a00c911400324200041030010381c4513000140b1503520f0882e0080c4240a188000304502041c0701e03180d958040002c43c050345540000f0700180e41c0f00c400000c11a0705144030564459140f9691000041422200c03a0b4030010506002082540d603001180a036849090050340035140003441c00c8040c615080d00b08041c00002d1402c0201c86410741c0c000c1c1ca51356808010a02d642e50209400e004000f0300c0408843c9042111028803045030341200c0300c458152072800440e0020308001e1122102204442c00032140d58008402c103c0310030300d18018030307070401d40b010403507410540810144100c420b940c045c0b0030003031059650040e07496142c031a125007080755640c50101014244003102002d43c0d112100b12201d01c41d5042040300e03c0d11185020307a01840f9640070f07100c50b815481c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 591350800 1250 591349550 591349579
    0x10b0d0b0315010e0103140c01021b06070b040b0901110f09060717040303080402040e0c0d02040506151204050c0915010503070903210306063b0306090309040c0302190e0f 75
    0xa04c00b641c1202e04c03409020711074904142d032041c1c680000240c05030040c0c1c00f034900041514036a5a4240b80150080c11692070607206889054014504807000d4039070352a05414408140c0d000d100714804501c0301c440350b60804402ca084081180310300001144039107800f1480506101c0c01c20005881d25031030070b0760fa994640d56403602510941e02294142e100ba481c0c072030307002400d543c003103020a4601c900411420005049608120080c84041e100c160042100c01d1600d001074100070050081c0392110100017600e10b81803604614041035403001c01c1c0514203140511440000039035010404603024203085440e5900c1d1002100c01da910346c0d0002d0403d44603412124042540045466109006903506001c802e4a5450a540e00707202642d140d5156410000c01141c800000c40366400454107617060745001e03d0307042c0d0000f4584402a107107080e06400025041205180c54400d0400314655800e05504080800700e05440d100c2002c140501403000d08403041a8035650500ea00c03d034814002c21446015114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 591352050 1250 591350800 591350819
    0x2e050915040621030f1d0405090102090409031814010c080a0e0a03231f09060b030105091509060f010e060f15070201030b0a03020d080f091c1a010b0d0b031501 70
    0x1800303402e0740440c1c00c0003802005e4a1141c0b0325050318154203644101402101410320000b460f0042030000955030a0101041aa0381c2d40120aa824000d903200c1c10784100d020741c40d01d018106a8044043c04080c01800f42e5580d8120040e80c200503004158140c91746003801c000c1e0f90fa40b050044003503010541c0c000c084100007880e8943d2401d02d269144d0303403004100490f04581d0ba840c0010390103145500d5890074600392115a00b00d01582441050046101c26009001c00e085d00c000b0f40300004660480e0342c003404000f500c0004a644a000740009010314288000c007000c1c5001c1c1809661881410b40c800201345460341d44140d07040784405002a925819000002c2e282c0d50090360080340020700b0000d040140c0e1401c03804820950350001c1001c4617100c111303901c01d80589c0c02031141c04022181800000300a40e11100100120204032040007030101b40c81c034107086001889806c9111100c0f00c40700500500001c0302c192412046003400001c2d0882100000030715001008080d00d100c0074900c400031444101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 591353300 1250 591352050 591352109
    0xf0a170702061b16030917010c021216231009020d121b12090608011815090504080909060d05100b191805090a0503030c0315092e0509150406 62
    0x100d01887e55429814040e0300d030131703144050a590016807205100d5020040c03c0c000500d0384144d0241c2840c0d400d405030341d45440048118078103020790007044070280404001440740e01600445058104074041690f40000c00b2904c00c070301c025140250025602c0511030003503841c0110580e1100c044c903a0816945060814462038030604800901c1010001400601070b0400a05071a00d0b0614410b000000003048801080111080240034403050800070361802e05105035800790f40298400c0da41c8001c9001449002403000d44009d019000c440c1d200360100e08082030b078800d2241c0301e50010070005080800a40c80ca44094110030f02949448000a0010740007244102d150003c00c20078000c0e41d07115502c00740c8400c0f614001400f2500104002103808420000a6070b02041091a503500321800c603010500700ca9023211100111203010400a880282c400728442c2c408641c019006801d03400c00e4003142c40b504014040c910025902c05110003965205e0300803d000d00700e4400003d00b00325400d49900203485 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 591354550 1250 591353300 591353309
    0xb15040204031e051c210209121b012c060f120105030607050a05040326120403080609010f0302010305040203190f0c050301140f090705060f0a170702061b160309 71
    0x1080704030050790b02d540190174032041e40840d100e800d40f512842d10700100b15005000290700141c0d0800840c049652100182418209078400400e1003001c4d9209101200049400060500c504100d290034402103040500014403404501621100c0e420f8010036198000d0b0000050401c0e8081070618a20140c60700590489000310212030a45e01c1c0c070740c41075880b8400e10340a070002600420062001c1041d8020800c2031407249000144294862402213902e600f2865081d00c50140c01d401348414142d00105581e04510200c9082e6019494503c44200b201091b2000070306040c1c4440029055642c24172040182270b0f51480039104106070303441d1000c014420144100c46500e145000440d0504051298a280140726100d0803581c2d15480103181003280000e20074581485100c1c1e01040d0f980fa40406842101040c0600c035072030305052038015102c1242c0c4103000421022040801200b01d60010f580b9400208100c200700c070f042001c400501140c070961086480004800614004040c1d10601c0e010484 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 591355800 1250 591354550 591354553
    0x50106090f05010f0e0f0403091d07021e0c040e010b0406031109070806010804060b030a05010e0309010905060705060606160803010f15050c0c09060a1706010302030c0306040b15040204031e05 84
    0x1a13880381080716290660780074031038411100600007801422807040c0c0d503401030300904002c00d101e81e490004000f120500d44444400d0001c81090141a540400ca42e0465400401d6610000c00c0c5180080740d80e4003440c2e00c91440360380c807100100c0c2c81b14029480310300c1d962400b8100f4051076031a0b0800104000101100d640035411101c0012103907480381d403119000b00016510000282c0b12074540344007030303c0030441056160080210010004209215090304609510040c50322011450000341545000c0c0d400740d40580c000b0054403001483c0851240e0344003000326016500c448183c4c06070f03c04000c40e16401006d02034008008518007045804400848013554540d50302071031449802c5642d030140d8541c10155600c9045405101d2500c0141103030b0200e0041c00c1410306c1503640c014600004100030496529800c04001841075060600480d1892002a4003c0042e410591b0380c124206000600100c0d5540958240c00c40380c0c0e40f660111001950050700303a01d10003045c42d0018401120700c1c18101c0310b9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 591357050 1250 591355800 591355811
    0x405090601050a170c04081902040e03160b1b07080909010b04080a021003180605040203060a0e03040b0d060b0309032101080a020909031e030f011a090d0f050106090f 73
    0x40390320500441d086002580e640f4103a00b151030154105131040548600b403e46810312000c240c40008110030602480034a180e451441d075980140403c0b00e80c03483d6216025003040019100060351205140b0f030345c3d6400300c5050030726550701409562196915603904e0070690005103040131b11810b8000f400c1131301800c40341038210b40d9070780f00c6168561182c4c0c403c0002942000c1401005440c040e40e00e00c0300305034a130501203050402c00c414a0350110307000d501100c00319910b00c20b100960808001850380006107090400420003110700e0309503680114801c00d4502d80e000102d034004001036411990007032881c0c0c0396964890900d00803803a269041040c22844882c9105185c1d26101c03881221035041b51700c2030f405041c45c01159002e00500c80c60050402b1414401080940b0340e00c102e215401340c00040d00300201e526814202d0f00c40302c000b078040c1d00019211219580c0000404100011100510800c4401c02d05c0720f80e5a00d003250903203c03c2540a80303203510348580025402c000382c1120442c00c4034800100903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 591358300 1250 591357050 591357061
    0x3020601090c09030f02010516081603170601020312070905100809011a1c020105070c09050702100204150818010507020607091e050402071b080307060b033c01020c03040509 76
    0x3803e0b03d0900c009031864504a80d01c0001d5405030000300007165582c13694201c01116616180b406a00105103503035030803003c00c810420f00d54800b107242050f4030346035640b01c1c007403c100c00000d50301c2c090486914484d6240601107903d290090750b000f40200005030a0820a807001400600613210807030f00c0400c03950820041804002c04680c0c0714108a030001c06964020340200b40c41d805c13240e80d06000301c2c10b100c02000008042a1158501d03401008002c0c4081050701d0548002030420000390051012540180030901c1402489140d08551041c24900701d94959202c0101c1c0386402c4440ca40d0a20715440c11060142c25940441c03100d101c0c00180d140c1c050328540e103020001128545200c0b094826403d02c9081c40b19141a40003020b01e140601c0000316182c0c0300b132080300c13400b22071540410b003a54000106101040040d0003500c500a504802030480b04840320302d20320705003510200100702610240048166581a041202102c0c2004c20085485200c080e603201d41d81d5001c3d0080130311a0044d07400245 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 591359550 1250 591358300 591358307
    0x100803030402030a03110703020307030807020301060e01080705220507200313050409050307081c1a0303030708040323071518030c030c06020f0304110a061b0c1203020601090c 77
    0x240102d038050010140d024503a10704494074400f140d03040035540a07140c000005a9410402034002d1800b603001c103541c440048c03041508481d1203601410366443d4042c01080004004074070034044402c15a034200c00340d0107049091100940441d10329007002e1030f150900c558150310545e070f032802070004940b088503442c40180b401c3e1341340101290013100051208003800b03d402e0503008020305038440c80490741400c6180d900c200e80703500030090349001c0610b07000000803070081d1800341d4034460701d2a403045081c8810500c04a0784a100017840d41c8284004040400c1c1007610030599030000358082d0304400051840080c421417540e100312000d42e01d0020711149a40788009501c0f988400e034603c0d8003c0706550241e80d0b01580d81c0340e84a1010317020b02c5100d500d45004240e440c00240f0060700d41004280d541d28051904000d44011115554005c5420903024004950400e8060084d2851100e8001c0f400d80c052501161801054000483c2c001160140d402055000100309040c0c800060050201c5505110201c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 591360800 1250 591359550 591359557
    0x40302010f110d110702031212011d0406151707061202030f070c06150e06011b0c090e011806050f070e0102070501050703050d09030e040c0504050603010b03130515100803 75
    0x607240000308050f00d0340b01e40e01c0c0d2000c901038080800d4581003016640010b410030407803003c0102800400140300400480601a12303001d003100320307800316842c40b1a801d4210314240042c40101540d03039a05070b90180c00e0741583c81788d0007000da13802e54180c0710b54081c01c07a5031100d41d54828280031682040034240044028001da910500e060020340145541d003200407900d2140c44075041c1c48007641c0d804000c0c4040c2441c62840c0242c9984c100384407082c102030000500c02c0c1c0c480ba00700b081c03420041e0341c0e1b440002c1000840c00e04a4442200c046814400a40d0060050503201901811200070360011410403a0300e400140c8140218600003107140c2d110407082d151a509441d0250058000c040d0501c141d41c000c201410b4806d001c0d02c0c01906021090f5210000c680c40c0074002d4000c14a00d0011030903614050080d400030100614040f4285883c08001c0340c503e000c107006103044ca14011000410740000034a49614058001d011103884603002c0880384405d04082d50b00b840c4480c007a0300082811b00000044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 591362050 1250 591360800 591360821
    0xb0c1f0c030c2118050115030308060619030209040f05091605190308161e020a1706060402391203190b01030b0a030510050702070510030e010b06070605040302010f 72
    0x41088100019400001c0c800a0702c2040440c00340c84c0d581d07021030401d01c910030310381030002c0540c04442d040d4203015180c2c0301c008200c144500c100304140341d04500030901001c0c5407000c5040160316207801000180c0904180c04011104034581400c10180308000210000303034289191513003414075150424007405078200c3c9050311003035000410800c0000c220702c0c02002384040e0090000702c440c000b0798800000c1d80d4000411210381d8084e007100030039850700042240007444101d1020442d80300303001c00355840390001001c0d0b032f11503035010901d06005114030709e80302000580300c0382c10a15041c40000c1c0702c1c41044103000b108414819400c410380b00070601d0382101e001d10030b045041464600c001c1c5d0160082c2400c0f02801d410561074000c03023026070300d92007031000146226402410b401c18480201c0011902e00a1952085600000c0c0c100400c1d1100b07008110381001031301c3c01080d01e11314004007a0150690103071064011000040040920516510150099109500922201c400c11000109030744095a8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 591363300 1250 591362050 591362087
    0x904150e04030815040204140108071812050a080a1d06040b04050d0204140a020703180e0c0a0215011d060a0303140d060905040c050a1703040b0c1f0c030c 68
    0x40780100c1d015150180d400101c6040600c0f80d80c20500205084e41c203c0d03030140f00b5900c4032040c190722540c0c000414650202c0d0619000400034003850341c0e031000100038400d880305003d0f070490300c4007030000a104c44940c150f04010780964811134504000c1c04040282040400403071042d0140341c543c50981c2c02c0b40c0486420964443c2410706110812848142001089034441c0c0d60b1401c0041415100d03a10501c2248400401620b40c0d107203040c042c00c00004c3c0f1400d00d111140501c0d060010207190315038a500207001d4411207444240301d00060780790418160852841c03e212000014a848041c03420f4100146a480b0003501a2601c3c802e104560469000080200d0054441c2403042e00c49040500700d03c031020130b008280300e43e81c0c4800004403a81a541070b5000044114140302e40c1c10034180000041c130510b0442400380c003c540413a0b40f68003460180008004000030000b0003010108005602c0d001c200b10400d080e502c17100c80420041207151200070200f41418400940a406201c9502c106481040d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 591364550 1250 591363300 591363329
    0x60c030816091a0c070605180411030a050709080f03030a1407081503030d06180507140927130606080705060702060c071d01030309090b010c02010305100515090415 72
    0x4050070f02c40d0600d84202028840d06201e88a14984100140e80052280b5100c0c03598a914a1184a02c1c0d501540c2c200c6008500b4a00d83d609142040c1040300e0780400a00310010b00d0b030319007840894400c80b00c0d0380b100580b4400c254030030112400100040d4001d03450940100620301055103010611002200c981c3c011581c40c4d00040c0440210717048440560301c0007001e50b072500961060100880e41c841d0801051109020100d5190071002d1161541020903410b1090a40d0b1810880c46898820054403500460000101501e43c1141400b00e042007024001c41010900d800e0b000c1c008081c0420b80151046400c1c0000040d00c4840454920152900030b404140340203c0d0360280003182c1d004040703d440501c9039500001e0801a44007031040c40314012048064a54036600700204003480c150010202e03a468014a007007540e03000016000802e0f42820046030030b076a500c810400c2c040c8c0580c0139035041320900080d030107407000c080300420a140084504110340c0c4a4280e5503040c4a1150144070141d569a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 591365800 1250 591364550 591364559
    0x1501080123040609150f1a0a110a0b0405030706060e0c0a0c1a1608070504050d0b0414031c0e06091e07030203010603060204150305090304060c0305090a060c03081609 73
    0x1440d0100c0c022034041e02c04506550380b080c1d88400c80d4100c0a9280b200d2090b4602404118001c55a0320001c0c10700c0310f0b1562115240d40780120552140700c08034020302040d10940070201005004141e0240d4010500450034542410002c1c0c03681c0c403c0e001183d80500d40b0788041041141c042416018951050f045814543c8041c810345080000b9102a18100b03411140c10810600044105101d5481140c80d030b03450904065000c2c003207140203420101445000e000500c85e5417a0040030500c2c0303a811401c690314030388079810300c40c0b026140441e2601032800006000c1d034103d1888a030b1040c1000000c2c0081080c81c060307214003a00d8050a440d50203068010600395600303080390001d095444a8207106442c2455625400a400c60700181d100f2600785801180070813028521214055803060982018005494026006600c2c0d101c0c5000d00024031500c03511001c141403156040d602c0c03c400140c0a07901041c0c884002408240c400381e0300310009251040061f244440c103803607442d40c406003900d4103c400380c01c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 591366906 1106 591365800 591365849
    0x111e19030c170303060618040606030e10050603030a0809070b071a071b1b050406140a1e090c1101051510050a0e040b0609060705030315010801 63
    0x78002ca04148012044940c0100704442d21355450103007045100b0140641001c0e00c2c1c00134540480410400d4140d0b01455590700f21204071a8640005c41c1001c1c00d0324070880e00c4030b070960414041244032901450009402c1003081c1e0a0f00c4001e03440d4900c2042a80114605585500b0404418a050441c00421640000303203840c08403580400005500301c2c0f42e4402c80010b00000f00c8402104804184200c00e0340178040c001d001b400713465a00c051040000c41c0101c0c007540f090490400010708100c0300d5502c200c82400c4005480704007071400e08024014042c0e49401c9052100001c0d1180c5042001e20845108813000c101170004400c600703040c400d01c00703809070f81c11041c08010010104100e0300182030000080c0200d8010480180c88408190b0381d00401512a410030750204040d420881c1c04030185205844c0110481720700c618510045400359020302c11030080010120841c02031551 = true := by decide +kernel

theorem cover : BRFrame.Cov 591187050 591366906 := by
  have h0 := BRFrame.cov_init 591187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 591187050 ≤ n) (h2 : n < 591366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
