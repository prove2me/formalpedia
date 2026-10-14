-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2291
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:15:21.738606+00:00
-- url     : https://prove2.me/submissions/d98b5326-18b9-4b4a-a00d-d2324ac39302

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 411870503 ≤ n < 412050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 411871753 1250 411870503 411870533
    0x50a0b03011d010b0f0c15040b07110f070320090c030106021b01050a1b061802010e090601210f0c0e040b0d02011b1403030f10090903080403050c1603 66
    0x3002c001c1d01003040100281c0041c9040b94030140c07a40b4100201900021107035400309901c001e150082050031201100229546401103000705103940395031614080141022142d080300401c1070f40f014850461000c00080e281007900e901c0070f108003c42041500340b0003c071a0348015541d01c11403902c1003000702000c9802440c12941c8603422074103a01c040144480031042010145400104208041380680f405901200f4207000301c039850410880d4141c40d060112203009080105004c9500083c02c150741c2d1250201115041c03c0300e1803815820031030000380040040188054544610005031400a1000c0e800418480e551900500c000c0d076400d4401043c0b000702d00c1005100b40d1419005070340c64148060303424230466040e10743d0442210420b040a1111176004000c5803400613504495602400034806540a554100c0a55005c3e08000388012031a07600c58100c210007901d01803038140443c2c0d1041e405500305405050140c1c1c1c4401b80300c41542404103581d40d402d454605558008208020142c140c01d403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 411873003 1250 411871753 411871769
    0x1e0c081b0301080304150e10030c0e0414070c141b010801121203110403020d060b0a0e22061d061602030405010207031202030c060112021f050d090606050a0b0301 71
    0x94480303006058400d80000c1c0900401a4003d000c280a60f004c0b501e02500d0b9102c0701d050010f10603c84000040600141242d440000b0707441e401e0480216402c030349010ba1440c000c80f010300c101000d2200b140354441008040d8020800d40700381c1c072800d00801500c03550001c03c036501999880c00d441214200307001290b0726000e00043c2c100c03000250310745083e500014003640c80200c01207121001c000890291190807000c01c0f1440c010400000181d41e140d601d98015882000e01003039586c400810000c107520b159004034404014503040009000031800f256810b108079040c0c51030b0032040ca040c403100030146a00c03004a14640d07240004802080040c00b50301c074226a4140011a0541d01802c80c0c99000794454503001d039110200600c0061500b11484010b0030f000c0c81100e05241407505000c0c9404009ea100d07024881c8003400080030f505042d100403145004202c1840030f640f800340401400c038481c4602c1440580d6464100300100300d4540c00c044000d0100401444000c3d4483c5c003000c01b142d01c20300c11000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 411874253 1250 411873003 411873031
    0x11b06021e12070806010c02011808072603090303041203090b030f0a0b040209010f0c0f05250617071b0203060a0b01080f07140c010b091e0a050f06041e0c08 69
    0x60390351140c50091712a03101070f929082c13020344550041d6002d01c05104904082c2e860300e44c1c04034000104102081c0104a145070f8008420504e1401141c00c603200d0810002582007002441b540b610000308a504440c034160390110070440c5410129920010303a0403100c007500b800014000b18550051415000741c0c41c0200c02c000341960b001c10002240f14096580780461108030100c03045c503004440c45142e42c0e005540410081c189607442c582840c0c0c4d810380400e01d02c4c00d461210b09281d44072040c03c3c0c000d010b00d414451441100307070300424103540d8018084800c21150302034003610301c80b01b14180f408155015040340d0a0f800d12481d00c0000c1e1600e84031840c00200c095000035000440030400700d0103210151a0307082d4000d19040c0204203588040301c024169074030303a405440305882d980e40152040d5548070010510010f58a0070040c102406441d010f481c43c200410301410014958103650080400c60300021030001c40452681e069000582481d2203d1400c5502040603401401c0a4451041032036000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 411875503 1250 411874253 411874261
    0x406020c0406050f0105070203120c060906010608010b030c0c0a0506010e0105010e0a050901030206220f0509160801060e0411040906050a05090c0d0b0f061314040b011b06021e12 78
    0x2008440b868807506a0150340c40c03500510360350050f0000c0c1012030010b01a1048e6403440704400080750b00104201d402c0d94080740400807207032410701a203800b41c5051711702002254500583d0602030302001d096105003031400508100c044004108000721194080140d80041d0b03074500648080301002d100d00d5010031900c03001d19002d440d041c100c00c5c058540040c00084035908507028081350f07030085a4050720925140c214410354110303807520a802408901504082242040c0502038596001b500c1b07254030b003081ca24900520754001c101681234440a01c1c000100c1454003001034003909029002100c2c040001a0100302c038080740d0400025a8030655001e0b040344e47e103405002e00a90704503800c12202d0010300010040b081990412814420002d040450720000500040c56a0340603c08080744001040010080c102969810301c49500d42143c040000780240e10001e4000c0c039000b481101c4044410b00007404000007981034860101007040b0340f0500101c5420b03203103880c0e40200c040c0c0d011203031498005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 411876753 1250 411875503 411875509
    0x3606090f081b0609030f030315040e060f10150302130501020f030a0c0c0e13050c100c033e0c060403170306030705031606090f03050d200a080406020c 66
    0x40100c81c80074000b840d1203110641012410b085028a4075405102000b1520007a0340c00c0003461035101520000d141c3d84d00300300300300710b500942019909001e1400c104840b14600804a202a84440c0480c1c00c2c4101c1c0d0b884c200015038140194100d080d44102070300f801401d250f4154041d000701c001032134215200c281c85d000107981e01c0103d402848407581c01000035503241d42c8514030311203545124101d8400c10f19244d507800d0854110469070800302c00c00f550202d1b0240030040040c000b020b101541c05c040f0440910340001c1545c41300c408042c0a024140301614003500c0901e0990024682541801c0c004441c1d414a0400400000b001889144035143c2440e0342c03840d10707000f22000c603a44010390042440d5140b81e001d80300d400080600340e150140110000d03082d1020710614454040c01c0c10700007040c2d0b050040c09441d00c40650409840e0342510401400054000030b40001f100141d0b01b0311000d02c003074440300e10344000c8400b403080200b400b4003110030040100e03403006041070303e4150302070b120340007814014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 411878003 1250 411876753 411876779
    0xe0610030804170106030501020f0a180308041401020a020a0b120a0204060912020418081902030702060a0305041b150f030903021e030d0911150a0807360609 69
    0x40c18001c001c020400c10080084940c2d11540b44910000ca001caa40c0c0d150142280c015200d43c3d4403400c0005034805e82a503100c3d1440b144142d841d01d0300c40f00241140c4a480c85802140140307010034400404510b243ea00070050781c5280d82e4024040c0d142681c45070702600e08c6070060340740040101010000b04680c01654001d0f101555115540d09180b41d240104101d00b1000d410f1090343c000c4d6440015441e04007105e1000c0e50b203a801a119540d41da42d0b643c0e009a450070040c0030754000c43d001800718000698038001110b100902c10b15001c00d003a00c9070b0404032921401c140d042d041c440a041e00026850740c0ca0343c3c100d503201d40070fa11070406402c082001902602c1d01d802c00100103030080d046443e40c03600c11001e54020910200b003200e007001d4007a2620412200308101c03c0c0d5091401c1381003a94285804500c43c4010b407149014542000d1680d5400352107908040c1c800b03410f01282c0030310004451010180c400c02030002900b000000480c2c000070701443d8040303014107000a2040c15011540c0c6140c0c041d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 411879253 1250 411878003 411878009
    0x21611010c210c1406060a120308010b220806060a05100e040e03090d030306080607170a0b0616030807030506330c0d021b01140a0c0201120e010e0610 66
    0x20a40345810110700300700b00c1c40c140c1050088244488000c0c2ca90201c1d140d4103410f00c8400d1380600070135041c10154100f11050140e83d00600d01c1d50034504080d00000e0740804042d044440d150280c1340c945103942c0400c8444008a0005d501c3c07000b5650700040d103040e00040a90080500b81c031000340c20745c2c4a030300b800120702d01b00d1070f1000421140d0a050300c1a05066100804428404040ea8145161800001c660f698500c0094001984030b082c144103454007803103160380001560426034107202400643c000c01e2000104a410900c1e511102c0c0c2100c5d4483d01c044074504c0c07460b0746203160345082602d03024051150035100140040d14103000503156080c1140000d40b181a944040c60400d410292403212103040d200b411103540b8030a0003100c00b400c030200605042d4030f0310307038010302418480740e280c0c044000d00c01884541001070212401c528400c009085074510074451400c1c840044c403d00060352284030802c1e10042d4581390001c6c2141b0f004040d4007403101c254040080c1c0d90b176600c4019803104100c5186c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 411880503 1250 411879253 411879263
    0x4060608190605041503050105161e1b0b0a0e0601050310020a03060b070303061701180f0f0f06150b030405030d0c0908150712200307030609021611010c 67
    0x140400c101412522400c000070145400101c1c040b40c56001190980300304040302c21040c3c1ca00c43c82403003001001e0083c82e03801942040014592402034030010240304131325240010019a40c3c084481462140180046a0302c8103501e1282e1780c141071030105070b07d000840356083c0541c13600c481a40c06649c04182c050499000074010044540750b001050001c3d8030078064202415910000022000700c140080c04906000f0344001941038a00011240d064400641da4610380c0d2400c2111207000403041c00e416034803a00404903002c2d03a82d60340b5140e104800d0810016090004455060042000326000801c10003040c030007a00309030780d0307528460b80103000a4070000c01035007051000d03615920a40c2c1c4110130303ca01030301e480702c1040c0e80e918149043c01500308105407402c1001042000558114828a14100442c6800c103c031504c4a00180100504c120601020040002c081500326120b074014034090600b0300d90442d541d96582113054119170840c1c0c001c4400c04d039142c2d03113600304d50701a4040881c140d07085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 411881753 1250 411880503 411880517
    0x30c080123060f041d01050708040305070f0c050303071b06020a020a0512070509070c03080c09061c1b030609060f08060705070501021b06090c1e0609040209041118040606 75
    0x10104007041007000522083d00141180c1da070301da20b0740c4da50107201101440808103c8520400440e01d9007510b0b402447ca605008480003488006030b841004c132201e01c1d4220100d040b034004145000303180c0082c241c2c880b82e0326200101c0d000341442125108440401141e07506c500c920350340c0d420705070384035448203034082c0d400410300c002000380f41002140540442880e20079590802d443e5030000d01c80020070b50701ea00020780c1000c440010140c00800c4c00340c1000c04140c0c104e0030446d10b03074000744051007000c1c00b00c03480c680e0103c4c2c0020403200607004002494021003042081510303003180100285030714400d110b00700f402c0000004200d89406408019a00303400c029001e19560031006072801c1d03000420031601d56601b0800303a40e0004984110712511039140001c5c0081d4100307124210325040c0c0340c000b0244640a0400c69211250b00075600340a0950b0a4803020388460300400041d000740500c00030150071609004181c2009001000100f802c40484032100101610000600040384d009008a0000c1408 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 411883003 1250 411881753 411881801
    0x1030f051b0705030409090b150a14060c0a120f020106050d02010c03140409090f02180c0d0b010905030a050c010206070e0901180b0d03050912010b0d3504030c0801 72
    0x864001048014003c504581c07a00350340b00c3c1c681c42261060b2100b514402500300a03c44c0314480b030000a08540c404948803602030f07040c42c113400b8144101c40800c91045034000740218440900307121111809802414000381074824400c094205046111a0b10055203800b0001c211403801081d08090150180c4d543c0480444681c1c069442100e0380b034456589640c280700002d04c500e858014160603030703c10a207841c80d4207000c0c410b1160000400f15905100d120b150200056031b0259004d1307480000070b2000100d0140c02480041e42c2c500c041c1d4000c980c05000e0351480105200001034001d01a03a0300780e00301c0340c40c0c1d5284102110200d031140c0407140e1110006c40104108001d015014881620741540010210301c00b0002030b82e810f0103c2401c8001c503101096015081c501800011454400c280c001e101c440070310b00005095500c030741e400400070b00d1082d8464000380380c4103001c0540791020000c020000444080d105150f604507100884035030450384d10105800806008010100d50203c0d01e555000b00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 411884253 1250 411883003 411883051
    0x512060402010c0c08070f0504110304021516021f080f040b070305060111030c1b151204060b1c21120c1b0c030b1f0605221401030f05 59
    0xc4041c4055808070003113500800d0f10300b030074400c1c1001403005c1403598241e40d00d4031043c4816200d1039144003501c454144100b10141c2c0f034040380307117406000078020555918907907031041e032200248000107500140344a11214005184141e0540813140b40d4031041c4503607580071507151140c582110b000301880101c1022440c803c0c020b8210540040050501103c1410505101451a0070494103842d10b0380c003a007600314040c4030b240c00c0311040707010941c0d01a00814070701c0b210b54002c1c441c14245148985981d070005003400300c1130b803003103182050080c0744190391400b480801c9082c0756101e0041d40e5800d401c6485418024400708000d800700203030780381c52503140c0d45110000c0003402c1c0050000140200003080180074004c82a05100d050305c00c0c1c02c07606600c1d096003444032480d50f004050400b21034400486026110200c0c0d210400c42d03071135240555890813902d0010b9001c1c040582284a00001808040303480e40ca80ba501000c0e18034284da00708a610444800402921410360b11030445840310507880f842a4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 411885503 1250 411884253 411884267
    0x50d02010c030f14121017030a11030421050601050d1e11090108030d0f14040b0a090507060e040c1701290a09170105010506031909060903050d06051206040201 70
    0x2484909025130030454007480e940e419400901d0032480000a0810049080074180c00400500810040d840d5101120405030342c1ea44180034244043c000004001c0701302c002c0400846000c1e02404080307500080e2001c0704aa81c80e090000100c4042c00f6100000c10f00d82042c048018900b5080038280540ca018091450840d0449001c1560032001044420075640c540b00f45050007001c050004555512191094608031801815081c2400b4100314200755624a41090b054002d500b059110000d45c1700c202c0d04078014156900020000d00803000c0002d00b85421810400424406480a0000d548004802c8920700d2408007001e603502034000c0107214480b102540054101d40841202601c0e440c00d081c00209900194140c1d40040c4000c801440800240d10b08010130350b0800c0e0003408554100300c00581d09010081c40b9038104002e4080128081046400500c02c5c00d41103441046111507a0400800c5544144803070b15003141003103400122400c102014101d030503c040c001d400c00f0380352640115410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 411886753 1250 411885503 411885527
    0x115030b0601032004091401120305030c041701050402090c0325050c030301030c060e0904120c030c02100207090e030a0203180a03140a02030d05040602100b030106090f0b0406050d02010c03 83
    0x1d0b648494000182c101c04685070141d01c2c42045554031585040c0381041568210442036401101c00d1f001001610010080d440b00c0683c5414981d1301ea54541480d140345018680c0300700c2058206480c2c038446203d040d4040c034050b038000c1d40c041d40d66980381c51200d90240300c05c0e55840a8004007515034000c40854214140b03140800d032a0645ca0034280c80b609030301e150000c0e042983c46502e10b00303042200c1c0303070081446144400196400c1c9418a03064a0701c07014015281c0f603081c180300107440b80303504041c807803a102c9008a5009107903000801c0361400003551641c8601070309044c1c6244c02c1c81030280c00310010a562511140b680203501d000385001681101882000706c0540145200c1004400541002c0302e6050021140c001056400f401c0d0041518000e10348250800703110b8104018031810b980030540001ca0800308501151405083c2d001c01d0046c4000c0d0300110800307240903030045e80c1d000f254210401c4076604550902c626602c440402041090042c3c0003408070307100342005c400080c0030b240000300c0c4d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 411888003 1250 411886753 411886757
    0xc040207020f370e09010b01020a11010e0603162309040207080408011107030e100903021207030b090109110a0b2d16140d0225150e030f0115030b0601 66
    0x901c1150510343c403214402000c00c90f45110b03548a05100326101002e911740c1c131041007002070245c0034175036002035210844000054072000e4082c1d1114101d901031401c0e00c05182e40904155607070320b41030042c01c0c642038901604100185a40c01d4004000303698400c20110b106400382c944c2e261010400c100402907000810440b1403d00c28003000a040d0400c2c8100d8400442045846603a2240f602d0014000c9960705017251007107225004429241e94055580c2091703942c140ca140808400580050307240c00ca85070300c010011000482001084281074000d4600380c1d1240d03801803401c2c00750b00e007045038995150044080c054001d111400b180b071900503400070320545011001c403c0040c01c0f0040803d0364048141481954000c0034440100b0080018900c04010080b0150007005035418001b5202e080300142600d95540b580400d0041c8491090440c0041c54014001481a0301450001d4155403211201901c40d000d6900c4910340000117018000c140122402217060090660380c40c050340c400b0140c00c482c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 411889253 1250 411888003 411888049
    0x709170a020a150206010b1801080a020706090c14010305010311041d0d020105100e06150a0201020408060f010f060206130201051e0a0809010c1d09060f060409020301080c040207020f 80
    0x350b1109071245025042d488007100b1001d5848030064a86003040e03201d0b1101c0d1800308072401000703684641c014030300c040c240f8040626448803483c10029004907007000c2e002078540035003001003000b4401860100c0719074a14004070b05001d1001981254030911000d0102a070460483c2c0c22454154401410f03d03281c695a1000c008184201034030b030800c42d1640c500540e54410500043c41242100040140412440740c0c0c0d01c0d15010002c254100106645511200c9010034080701250017901a00c01411588007100c1c003a281c1148484c050040c01c0c450540c0b40c0400482c0402d4151000c601e5910070b903000c4c03c1440d0005030b035038011101c03540300400c4003440700264100c444c1a900c202d0300910004036036079620000380c140304080ca400c403107005480c2c3e01440205841d0038400c09001002400c00401220030031065502c00c1c01241824008460a541c48080003c0c0800c000041d40e02441c16240c0c10b100700d941084070f030b0040c8000ca100d07203034010794030100da25400a80b528140710000120460b003c150302c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 411890503 1250 411889253 411889273
    0x3060b030f0619061a09040b12030a03020711010c050a03050f2703070f0f050d02060f030903131509050409060e0d050901030f1112070207031505070206060306070917 73
    0x41d04010781aa220555050341038020303280d07032080d8080c4502070000303c5c2c211101000c01000741c41daa0304c42c407008079002e251100101300341980c45007a090194407042c41a03035615880d0410050080d48550001c4501001515030103c07103520034611140d64503440001440d05203243e46045d02c0c0c0390072034940d41591403410000c1c0c1d08100d0100d0741c0d6030311f80c0451600f030091001110040508091403504140840c60300030004108103200701a07020102d42003500c1008003002e050001c04e006206810900b072840b8400414090072101c004018041d401c550380d91460003580720344040540c1107890601c40c00003035400c0d400b80b08030320b06980480192407040c01d001552440800c842400c1c402d0310268000854000324038203005507054012040e440214217801c124621002a04034a00e00488055a4040072a0340004072060700800240c4050340d0003049205844180b62000d2002d040c00302c601d000140100d20104031241000900300c2c1c000c406a0303c41c8410b171420002003030600c054100c01002e461140760000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 411891753 1250 411890503 411890533
    0xc070e0c0f070c03121701170a020d05030405120c15180d05071a03010503070b090102030c0105010e04060606030b031b010c170309010c0c05070e280e0601060f05030103060b03 77
    0x20211548075080c0b40d0fa0f4545542410701c0809100340e0b401040c803500d40b0458400d44841e180d110b043da5078442c500d40402e0300f034035069841c0c80c0e00e020700250041886034540007800b03800401b401c222142200c203442003c4001e87c12a40303401d0a441d0346030708803078007040325040c500311400034248003080e0007403031101079042400041c0c518000c01401d440b5a04800000d03c5448460f8040c26036520030189000e1440d4034004c0802d5441c1ca05110748600d405c0c0c0414050701c1a032082c01240c0c00c00d0001c070028882d07540c481d1380d60700f071018085c0ca00711522494960700040300d80c0233000707180700058028040d221120510445014401d04000618104980c442402d8001040b4501c0c03120380e40b110180300c42d102c1c54505512402c45599054072418000e4040c41500080c40c0054100103aa015a0721070216480e414640203845440104240607000490ba13441c160800c1903100410f81307452801161040d0f41d130382500b501e40480002000000400410040c804911160004406880041c0455604076004901 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 411893003 1250 411891753 411891757
    0xe06010c02041b11010209030a0b130c1e06030e0604030e19080a050706210f020f040605070b0f1b07020a080a050312100b2508160201140c070e0c0f 65
    0x2d080710300242e0000b41e0746442e0b0301c07104134400000900001c5151180d9240042e03a1441c2030320000741003071010300c0062a03981d1b02c14420140541c0c40010514030342c4d04c2c1c40600b200b00c450b02803d0740300050705800c00aa4244203008204003030200740e01502d85a03c0707948044542c02010002181c009140e504008c6581c4040c00b0580c004040740405040850424a003250074220950b01c0841080070a120014125140c038060b800314140c10840042c0140041004401900503941450380c01030307011a0014285070044014500070380700340d108400654491409081c10030090340d84020381c00311498200305100b06900100704a03800280a004015610458180350030502801200d0540010510020b01d4103044056500305040800d0b464195003442800d140902510000c1c42c0741e142104081c2d80580f82503000019460b41104070320355125041c88081c84843c030b00740301c22400942030b005500080b0181e041900c60740032a110182100501d40404c914240001900d1550480400c00000b0412181140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 411894253 1250 411893003 411893021
    0xc0d110103150503030412031103030618151e0103051e012c01171207240b030d0203180306060a1403100e0606010e0609131e0f02090901080d05040e06010c0204 70
    0x10a8a240c840c0310708c0c1c010700305803000e035180300283e10a00521072107940700340035504c9408400004290b031b40e13120340944a015400107141a0014840304505010103500d541c401040030013070300d00b4001070700c50700000740038480c00c54082049020048018405106115091201e200c074061202c0001402080750108900303003a4007011400603000d008180c050424420101c0050200c0c42090801113161561442050003901c034944d10100800749801714019903110034a801d03405170482d111708105a9002e55030b54051000e94120782a03249000b2003d141c001602d44c4100c130040c2089600a242030041d0301300e460052140755040c018036104028124142c0b10701503489207200e00520352414650000351103c12074045007401024100006041034591500c03545c0010b0307600000050b4000420b69003c40c040d160001d0300403003820000014480c0c015500944a024000c0752400050b0341e8580500380c0e5074180800501c04908180f0040200300e13240705842d98000c0f4107050a50f101441030740018115020f001d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 411895503 1250 411894253 411894269
    0x5070b2101171507080c0d0e01020d05060a232106040302030a080c07030c0b040203010b0301020f0d0c05120c090406030210080417030121151506020c0d1101031505030304 75
    0x341030541e202c501044007886000c2ca44100c2e0b0010f0a000303c00802c2c1001c0206046081000025902020900c1e54010f007042d01c4114021501c680001075850003a090584500b132041c0300b502004070306990220b18000c2c1c1b0118440041c0c00300142c070424012026164440042d025080601d55003042074148034251151703120382d0186945508055010706034542c06000084480b40510506c40003c0d003005140d45038542000e4100c0706545c8901c0080c0c0501344004040d609940003003207503404082e0003070141c40280e0b45040c0612482121503421a406d000e03006003e620f00c1040c401068143ca20f540040c2000d600c090000f0400c15165004100728a114809400004601c80308100510120303d900c000c0295201c10842d01c0c6514003503a103006400200c100440040d06508440c081200c00c107a1350440c00041d04090002d80b00e45505000085914881e040c058007034120001e20926003503100040044d4000101d4030020300c090011401014100001c500c1020700700c0010545603810005080148084 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 411896753 1250 411895503 411895529
    0x51815100c060609150b07050a05010f020c0c0f0d02190b030f07020606190621060905040203100e0a030f1b11190e010905060d08030901141305070b2101 67
    0x2e00d44001100c045900c560440c914151851030360380480c40701a030483d04005d41a0b83c03070b02e034075040460a003d104d05004156618002c440103601180c0c0d0050101544c080065904040c100814802008180c0001c0c5d9031043c2031406100042c41c00d10704070710510080c850440000f40c0c0741c65000034107510a6440c11070316820801002001d540c10090107078090401d90300408034211100344a545101c3c180907140a2204103a1410010110300d0b071b0586680c0081441406178580d1100c2140083c03405890a0b4000d001d142203051154442d0300820b06400707921402043c41099945048603000c039008400000c0080d05c914101c68612000d101c403810a01070f45a0a52201c4d200c02040900311402d11120070070101e8034420480014246c40e5a03044038081040428665140c80c0000d842845902001300001d01c00300c20301c980d0b44030560201440c200c03a1141205240c4605181e0310b03c1305c46d1810000c0c069480721000307000c80990360001d80202c000c1c60115079801079401c00e040301456000d03048200c070300081c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 411898003 1250 411896753 411896777
    0x10c050912010e0a0201050a02010b040203041112030406090e040c150f0207060c240905030a080f010b07120309080c0a061a0109061b080909010b0304170405181510 72
    0x945007140803810200c1c02081540c1ca01c94100d0784034101031070081d051000200c1d80800c034074000c0d003200540c40b9008104550b646020318050f25111035003824280541e031503400401c66a50000115020360300561524507440c0c1c80d00030342e01c0000d03000400c03c680d0140c0c4460000341d041c018945011189809890b110764100049c68001d01d0419154841c60402035000100c0011401818986450710340c111503903440c03030000a07501d401529200344010030301d21001440d00c8140341d0042849000d0411f00031908800e903a101c4041200380582040030306582080115090424041d91148012500c109841401d0044d10300301503082c055208004d50f2000c1d165000d039074050f0ba0314014280e120000742080204241880c00c0105201d60000301d40001c640042d101c1c1040c80320703030000e45102d900000c0036620355607141c030790300c2609410a480c200c81a28062601e1050b4204850540c0c094850190034098007520f401d85228050f4000f030f181c629440300c14a03040400f41c6845007050300c07990300b680750b10154002c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 411899253 1250 411898003 411898009
    0x207030221120a11090f0406080706020d0801050603060a120201030b06040b0c011107030801210615080c040c1e05090301050406091a0907030f03211505010e0f0d0f05010c0509 77
    0xb00500c0700300340d01e24080d00c010144161600b501c080c034005a0314219030b1041000032400520654100031814803603a00000f815039400980c407071030b041a551b80c004050b41d9440c140500c500054818a0340700030007007000d0060300c0307544501030350480c014134002c40d0990090f00800c800c0c0c1e0249d0882e034034060340000c1030b04c401c2c2c8090040954482e4dc14810515013a0309885c0180600d0040c05141511025011800c400c10b5a00850b40d400c50b0300300300c04002c100d014000d0014020300310701c2465407078000d0282c0480c40385004d208075000d00d046a114403169030100790940740c40604058104050020600282c440c079202440340768801d03841070b01c0015800d1070307134248440120201c02c0c440c503440101d4020002080e0340420690112a84084045030301400c500d4151880d815400b0301d005100042e407100320b540e0803580c1250412007000d207500000075441e40300454030320004e007401c180c000c14168818480d80c1020183c1801103400f602c0c4d1040313803040d555070306800d5905850407040007a20110b144000341c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 411900503 1250 411899253 411899287
    0x150f0f0403231b070506090d210e0f03061e0c0714030702031204082a0d0f1502040f0509070311130608060a0501081501022812050a0c060207030221 65
    0xb900030f80080c03582a04d48800074907540716506219001d070000e030324188100080300c5060100c104c1281c402c140800310040c4000c00e41c5001c0c0c0c11a52181b904801e00d0755982c00d002c12864000c0ca81c03040e9092500128182401c040c200140825038240702c03c210083c0841c0004c400080b5480c504c030059981d5012500401d86007100040d40b90001c0c19040004000c4c0c0803001031003180c8912804e42b40c421240b4980710b888101c0d02051445504801042c143e0030070042100903007c2c0d000d00c10100002410700e10550703007089000d00d010361040442120802c2c85030b850120940da031b205407580b9020070f101e1049a00c2c46015004100300744001a03441c0d80c1407282603046094668050300c01d4491122007450b100000b00100700c040d04241c1d012294800d00060350744240700a0844a0b0460a01d0b0151141e01c2e80c07014048445441c2518010248164034030524420000c4902940c041e640704400d00c06a42c4852000354271001e1304505512441985a021038030080c0c2208045403101a071a8070703000e51200400c010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 411901753 1250 411900503 411900547
    0x1f020408010c02030f0d0b0402072004060b0f0a03200703050a0f021f0207021f020f060a02090a0608131e03030b01030603080a03200301080a020102150f0f040323 71
    0x264205000b40008185098141c0d0078011b03a1200105018600c000802c000f80f00d0440301400030b0000c094502c03c5400820249600084103480821440f5500d100d0b030001070003507041040318140f0800207101903e2103608109000d5030290001208540701fa041c070200d90380968400c40101d0400b040e0405025000051014901818000b4055159200080e900c013140025603840301c1c20790116101c815920307a1044010784c950342000725200c5c0040384002035034521034281c0601c000e20032403000414180080c020380380c850401804000c1101e013451020344071000c008254443c60140550010007082c800024001c241d200c60030301454040480c1401801c1d121010b0003107061604010f81080050804804c81d4912500c5103000940c10349034075001244070000b5540c00a080c5c0c0040001b007511000030444c8004e0300d00c03d800b01c44543c0d02e100101501441d0856840044840900008011401000715503034014880e1501110b03d4401c180b01440d2544d0f01541c1c90341403c0d011074015180903407481c0348805 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 411903003 1250 411901753 411901757
    0xc010510030c0e01121e02130f0614030c101206031101110f060c0f0702120607230d0f0605030607080a1a0f06090f09010e04020a23121f020408010c 65
    0x320b58100001c00c0e00003d0f60810042620800e12402e450020030400c403201e800351f00a25545c01e801c610015040a085011824003040e4a0030310005070020001440c07092052015002e1b04145508000700100c012a4007807140074800440f0b00d440c2080498420704001c1c6104021440850041900041105004c042c60295680c0008144d0741c100c01d00164150340300d6400700003195183c03100d0124001c280100c0e04001c4d009504401010382c0b0700400f00700140309070000e585000103400075050407425840340c10520000343e181003111074803000704d68100c01c0111081200100d241a0348001103882d20008803980000560100e0621003000100e00507105420700c048840780303180c0c400000045600300c8154000d4498000041d8180481c0c03602880c03050348145c0109074241542e502c00c80402c42c0c00c0219000c074811044804003043d0f81800072440b80514044880c00d80c94103c0000c140a04110315040030071051040c1c40458102030091800000c4001c1ea08102503211440c211026094074100303054170701 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 411904253 1250 411903003 411903029
    0x110d0b0a05011502150621031e070c150306050604120210050310060c0516080f150c030106180504022a0f060402090a0e0318011e080a110c010510030c 66
    0x22040780e00040421049450140d40081782c5c5800c0300042d03582e0002000c5c41c2c041c0016442c0d800300c0c1c45020014140402290f248110442803e0141d001c840c4140a8002d05042c18542c0034401c0581528400c2d103091020705000070016100c80000b090740d0400e901c04845500102c4002c000c41c00c1c646c030301140182460800a00710b051900c80010428118001c027030400c248400302078240642080070b07a01034001c0289081c00035495003502501d80d9910502c411491103014202d504004c45001c8083c0306490091f056801c43e400c01c40c0031100d12100d9145041c9907845200003007010355030b51008203d03403580094861041101700540251420680c5001c0d04250405455400c2c0f6103000719842c0e034050b0b41165141c099541e03000c0890f00501901000050310311010403680f241285082268440c1c1c1d009898890010003441e40c144204055144604d00090700f0501081c84040c20380c0242c4032400c03034a25007601340040150203e085405c1210100b209580518040082c44050703c107040107010340401a071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 411905503 1250 411904253 411904289
    0x1416090311010e0f04180b0c0703080105090411120c040b0603010e07030e151303170702070b0c070e241f1206051807030e0a02030a060207110d0b0a0501 67
    0x112005441035405040c00340781c0f00ca030180381ea50342c0300c00c3c42e0503880144200002180100d11703c000c0c10f0304a4003110030303000d00c102045010003804103452070150706a89884540c0e0800050002100c0d01420441d4000f83c0c0c50698103042d65142e0038040712054030340003070402d01c5d5003104000c25540c0115415020391010001400390341301124045138001c0941c00d02180000071801182e181c40b03404105030f51079040d11001e00c5610250007562210580c000d5072511440005440c4584c1e01600c1912401c01580c090902044072000b8440038106510003207064401480d910380da083c513000350403644050121075041004040b004042641203046000b5181400c5002501119182210507440894203200500051145802c03003900008003070314025000c40304500c820809041c0c065022340b4448046070410202030101c4400140003200640c00070014100e0201644440009611221044d1090442040741450075142c07450141a224031440f000c030341511703140ca0100c084032010b0f0080024903008601070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 411906753 1250 411905503 411905513
    0x5281202061909030804120903080406080f0c09100e120d03020903070b03040f0809040b04093c0602030a0f05090a0c080d2c03120703090b0a0816110114160903 70
    0x11607000c0c1c2c0c00024901011070009040e00e4030343c0e16500c000d00e462030014010802d168837988150140c4071300115413840e62181c03094500d10740201071490390000f8104040c44a820301c10000448035000107003034074800700248500182040b02500813880469000100007000341001c00c021401003101f0703074400b4114105a502e64084502446001c0c2081201142c2000310355103640c0264507002004104020510722031410b601d140c02108145200c0c000b6564042e81000500d1800e4002c00380031401460750074846a031818029040900808402982e40d00141202c0d45244541805440c0000040110030740340d1400b040d030f4a1268200400540003101c01c80b2000303411a820241c1c51941d038212680f014400901003403035000ca84c2409525209076445201c080da02d0000a0a00c0c90180e41c03415510b03902c40e8044c00c01031160310a40c40c00aa0060001004a0702e0440000b0400310305107071554204140c40c10b140d095070181e81d21310408038400710070b2005131454041c60b20b106001c50f09103495400d1039910780d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 411908003 1250 411906753 411906767
    0xb0a05091b030901110409090303051305070521070303171b071101030b0a0b0301050411120402010e1c121b0302070b0903031b07210528120206190903 66
    0x2a0000c00700010000c200340110039001403040154208030940c44a43e01c800790409040a05400d401086c85e04001c01d05402640c072295014a8004004102e80c41c80c0c28140500040f005104582803120038950004069041c00b10f0030040d8065034a80031184038003821110607042c003900e03002e621440300b9564410b41498205480d90942c2080b403155a03242c2810058000c5e1220380c412551201c0c0d80c001c0460003a405901550503100c1c290f03020003a541d140c9600f11136501c20102c000c59402e00007400200158401c108640c0c1035140500890281d480303001d00032070707070704002081112030300b004070a20028039a20030001c0c40c0180880601026124003901c01948a50490140b02c04003140042c1c0448a91000c104560a1542184c0f2105940c060165050b03100d50702030250b912481074800c0c805c00b101590000000350710b078005018000d074030000540300407200c2d21242c118124030b40000884001c6039030b980d00d8103140c40c0312350058022403424803540349044989680072403425160a05080110303a100380 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 411909253 1250 411908003 411908041
    0x180210090303170a110d1b05040501200c10050a0f030b0616030201020f0a0507052e1e020c0d080906010b0d02090a030210110709090b07050912100b0a0509 68
    0x701d01005512602d44080145c021108954918080091021503415455005d4031355842d905c01c4003000000b40c2d1104445500c11441134600042c0d0000c0f40d006c1e41c9085260b00a803a207090012282280d6510011402c011406440000490004102000c0103600308004090784043e0f0726081003100286800611a030142070300d06141e5544d070f080090704141c000d6040b20000c1e1101c5015684581701560020310983c0804801c46550040345c10340e07581494450101c0004d074401e98207007000c201046504600800c125965084086015441840506a07910003402110614006810140341c00d1001400c842d80142a5029541c840740040110f0384200080d580403008250002d6620811500000d142408940000c0e6100c2c4010341d05864298004005407083e14100007540c80c25559182103100303d803d2520054640007400c000a03200f64400c00081c8a00e0400a1411400103078111a0714078000d43e9003a030b03002c0155500002003240c40c003800944000c020449588210b41b0b041005402d40030f90b007403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 411910503 1250 411909253 411909287
    0x9040b060109030501110c0708070f0b070302010204051c05011b020606011206031505160801030201020307080d15080f010e120412030c0b0f060109050f01090e19180210090303 77
    0x804502030340c1c86080e07000000c40d0020300a001d646102600100140e02091103444540308070280010021070101c0da881c2118220394210f808985000e50781d200036440514100e003155420440810650303580700c1d400034903070720020400310804607501e007007030031114589041c40043d54170719034080143e83d001400f164030075002c1c604038a00c0c1d143e00d102e102c090401600002c00704030344000c020165079540c3d0703c510300c01d850312603070040100880242a00c003c50203020103401038000300040340125007010010089a83c8103240054640c20741401c40790700d000c00760441c0c4880e4100405101d00799809000d00c40d00c400301640075101c21410960010380d184560720512025449940518081c14002c540e0f00400e6500002e03104200e150211103c1130482e411540c1305e01091510310041100c0c141b4003a641006001a1107084117035080ca0015005510010100d05c40840b1055540003084070b1401050050421480450300403160b174070411548060065030081042400101040829409503001903014148 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 411911753 1250 411910503 411910523
    0x30609041509020919180302070302040c050d020c01150b0a0c02042309010507080c0403260d09050f010c1106010e0601051b0f0c03030301060909050a021612120207020904 75
    0x10503071000c080e012034100a5405414501080658081700d44100000f1030041000c100620401c100b120f04030035801c8001d4010b038400301c820300040c182544602c1b00c16440d801c1070707420069484034010590f0b100030002c2c511030b5129020141d000041ca000381e0044e0084445a9080020040d002003040100810103031007a6100c00b001c40714502c01c1000440940c09107040c0e0712480c601030854601800f004d807200340c0021210030015071185401c1058034240c0e94820b100c8030352800841600e01e04c83d034039036207400d2100720204000c080d00c1080740300c0c64003160311071005030901c0c08150483c103003110100b00240090040400d454105500086000c0e8103541c0701d103400428589a400040366540141c2d004010802061848941c11080c00140381143d011000101c030b0020000e40d0515032207020030700c41d050103e0865038060080c0485500401c3d031242d80400c0050a060a547c003580c44540060010358444450074041c00c00300380d20900807003240000f00003e529207400c9a000c9064a44010009052070207a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 411913003 1250 411911753 411911783
    0x6010f1202070c060915020102090d02060304030e121e1204030312060902040f170c06030604110702151b0f061306140711010b371706060f010503060904 67
    0xc03075040d01c0440d81c00c102000100e07902c41d000079042c0c009500607036000d00307075500e0010302c1c0342d205000b200c000d0400a411600e01240a50a10265810140084007400680b01120000361100392190820140f145e0051110100c1c00d41c10b1000d00380401e08801c40381e08050341d82d61072051201c0072181141c0d41071600420782885203211744001c180c039030000700c6c9940c000900000d84c6491540d600c0c054916201018500556004d12203648620284205811101c1407000070110f241c01c0d4070041d00610892600341ca04138155001455041801111002c414008642ea1280d10203826201d000240c0b0f0400803c12105c144032803954618000b4040d6090b040f041103080100250f40d00198894a030554a90086040110700038100103400341900340650704e08101001c0c6450405080320040103100c440202903900e1800d0176110002d143c484040040c122400001c049a200d00d00310245840c501c041d0020b800c042c020070010102d03200086d81005018010300405030303250100c0381d800c0b5034004400030352480 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 411914253 1250 411913003 411913037
    0x1090b062e271203030c0c030c11060c0609011407090b03010b030c040308070f110607020a0b07020f030d0806030d080708070804150908030411040e1002090a12050a06060b0306010f 79
    0x2803500b1208000c041010010341c64586103412010b5501c41c0d1010300c40c4540314001210341004180c1c001d4001805092503c011031106502100034072405001c0da80b4200c81c03c94107a1500b0020b684008040e950f540310100380341c1d04203070215004102d0340b500950706450507900080b00d01040c0079042c801d41c0000041000c0000c0282210010759003c614a5150140c0d402d03d0b04444481020a4a840c4005401a0031503d060741c00c580c0c10f680c0c01000d4040301418099000400c1c0c01c50303d02280c020b00290710a04903664100090001e14081d507890207121302d80281030609100c0e290968006204444007803003206900901e465501c01212b01c1c20101503590b9082a01103940104a6245c40c2c070300d0081c5180a105c204001940718901a01000f00185151428403007214a00200b07180190460302540b1148982074004190200700148811841c0f03449540110407102030100c00c4696600001d4400c08101c541d000360801403141002035401e5180490000e8a00000180c84000304080f880002402c85 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 411915503 1250 411914253 411914297
    0xf111909080a03180e1305071e170a0204050c0c191e020a15090f0b12010b0d1104091d15011e08030f071e03050f071401090b062e 57
    0x44205400c154071b041480903980f03078802c105410b6429004016000c541e942c01198000794505018180e4140240341119480249441c60304a54550280c0314400c001369503640941400ba084a0316115954494043d01c2880c0400300c4140200c04444459a05c0124540100c420b00a44200c009810b50444a1002851b0b54460b9040100407501d21000601da0320f40c8000c4840980d1805005444001e880701d0b1719001c540140d4072400d0a031310480740180a680300d004064a0603420303000c804a90b005002c4402032aa822581160020300d54a4403102a10050810441d003140c1c81ca4002d08441940c1810300201c005050117803504a00d188928003448411406023000140148825030341c85290101024034164012407041c1d407580a100c0010305a01805c0e030036044019407648525180983c6c80100f0652600040c1c02910b4900403c01c04445406088c0508640c4501c81c2a1005032843d00a08200d1100d0005410041e181000e807504904200418842c041d400b80501b402000e0321f00c1c4151a680718 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 411916753 1250 411915503 411915509
    0xe0c040b25060e010605030a02100f02030d020c0c090f060d0201050a0507020405090604110105030907150c24050c0f07020913020d050703050d140714010f111909080a0318 75
    0x14400c1e030100109020643c1d10188458410000903c0003540c1d1b0410141e59a940703610281d480030f003c45041c100c50780220000d20700500b40f030044c2c034240701ca032511002c00c83c0c2204681c42015040103278500c0d00c0d860030340117440e401907000c3d01c0204141400008904100c5038420001d050080005610103401d010b41c040d61410780e4010800c2c01207103058442561900b03000d4030300300c0e545615101681c920798051000c0d2407085c0c9038900141440c034a07203581a80780300c107401c3c0c0c00d1050244d4a0280c0011400c407000c070700d441a0715814044841e21190451004941c40100304890b407282c00d101441c14114420225509aa0112001640c640700e600d16042031b0110704100a500142d0010148100000403444008a80c01581076410b100b06182c001d41d4081c02062062003142c008001000c00103010f52100100c284441b0300005240c805120010122000780c00d0a81810001203003a0b240c10345060b1401c0d00207001ca10301100c2c1d1901c0c08241c00d41d100003a034401000c0c047c0680e400900082009901c40c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 411918003 1250 411916753 411916807
    0x40c0c0605040c050d06020702040c080903070b131406070824090a0f091a060409030e06070309030816020f10080105011413090c03050907030206040512010b040501090212010e0c040b 80
    0x2103a01502d1b0a00c000c2d40144812401903080c02291040a03000f240710b40d00ca0356051001d54607240e400d980d0f08481100040c03094000c62039145851380880c09803980c1804500c0680c0060400c1d09141f00c01611150005050003101c000006a800100702240c40044860350140e809103a26250082944054001c00d1856580760b490005c1c801c062000590740d41c0c00180518070280150b446940c144400d55074040009400715074503140790f80607418070700c1c01003d1003806480c10050b40750306c0c2e41d035441203030b0301818851800745c024066002c1036192100d04c03640c0448044860700d40700f807004a009802903070140704041c10321110460901d0349444410482d4040441954080d1941792511802c400801e0a05036400010740781000060340443c00041005c1544d030010000d0b42081d1030541003100d10304220f15081c1da29500c446044119032180d0007150701030700490030b016032540c4444841490551050f841005444007010511a81100000450301074071120544c0c00e0352002070340c00c0301c0300302c040114240303070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 411919253 1250 411918003 411918019
    0x30c030f020d021e030606030c0307110a0c1d0f060405090708010903030515060a17063006070206010e0112020d02060d0501051c0201080604090303110d060f05040c0c0605040c05 78
    0x1080c2c1c0000c0e401410300c10301c001c094070183d901d1100321102e140011582c0540080e02040819901d0a0000c040c550059039803600200400c03908040078200800c2100454180070004010701042c05400f2091041784c20384000720302540341074004502c41c03400180115006641c2c45000c0b40b5201018040200641002d2000380000b01d102e20340200103060403100c001d2480c076889810f013401d103403030b80031242800d0072a501c803407030515101c81d000403c0034040e000551201021040c540304120810340303c0342c2d00031a031140705c0d55840c204100d207040200017030001045401660040c400e6014180720349054403580c1003030b40420206440400c2d0005036250001c1d502c00c4000c5030100180c41ca68000a059410a0320505034005564050541380a04c6120090101d054440090483e007080c2d480340c95541d00900e000301d8182074124a00b0540d50140c20008401616140d040c018035800d9520280100002c0e04c040001040c0c0c5032008002c1c5100f10710013814103464502007020320001145240103000c0003440c0e01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 411920503 1250 411919253 411919267
    0xc030b070c080f1903090201020a0210030216060603350f0f0301080307020a060201050603030d051314100c020c10030903090b0c071d100302091e0c04031b15030c030f02 74
    0x10f801c0c0c020030700c558400c841c2040c020038494070070300131410600c0d4186c000b00443c80c1070307a00304001421400c1c03c4804065003840140c1580e01c02400200c8881d008000003e41c0ba8294100324000301c0681e601100c8003551080c110b01050f1403005d012035181401b0380c48503110810448200040e00c1020091030b03141e50b010001054082e800300051000d01d00c01c50715010815a03e40040c2e00780c41040b640306c1d034160030a02c40c017a00c92985422981d0b01c89001d00d14010390b00d07030641c1c032405c565043c810305841c2a8440050f41000c540c0c0b6101d1030a181986000600380080c101c0700252100d00c441c51800201510f80e5048000c26004000300320150281504c055252503800c1c04082c2e54203403a02c1034140c0060f01c4201c0c041401c8880e80c115000300091007402803030a04503001d1104040c4044c04081e030101d01d8440b840035480d905941a400364917110a4140d40301d213182400d00441c0052503890400d0105845c04201c03409416104004544490401240034000d00c60140c0040520359440045180001111 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 411921753 1250 411920503 411920527
    0x90c0a0302090d0c05011b0503090f06090406090c120b09060f031501060807140408100b0a03080711210a0b071106010e010e07260c0403150b040c03090c030b070c08 72
    0x24050301e50031f9031081c0b4079144841c519101900c4c84000640786410130480c0300e005040c45140110608030240080e40782c1940c0038040707021514030364015801d00740c0e54880654202d601c206d01c0d041a2a0070a006e2003055203070800540f11440140c5114800c1c111800d04003140d40301802148542000280d248503e5070351004041c0000f03208035003000c0000d070b4214400540319a41800c0c0c0d002d0321111001001d1000c4e0b0310380c0300f90041601c40d6a159105195090000c00180c240e0003c0032110700c14070010260000c2e00741407040c2c06c070140903104002c2c1402c2a00e650b40d0180042c0449159801000e0142c95440d241ca05030b85200b003910728011280601000411540c40a1840c10704031036603062010320b580e5070160100c0e000351032034400c0c01e008400600148000114000e200e50401070f50821280392079580e5803070b40c0c81d48507115030201c5110340701c401d00046450588035602c0c2445403401c0c00d000c4680181e031540c0700010b16000040100f403030f11000c0b408491117810701d000f00550144400e640c400d45c0f0100307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 411923003 1250 411921753 411921773
    0x309020d0b04031e02030c0c0609041b030b01120506030d0c0602042312120d0c140a0c062004050607050717100c0e150313150b01020105010f05090c0a0302090d 70
    0x1301510601074030b05000030140300100315030341080500c01808020079900c007005420340c801407040d07600c20f8403600b0307250400c4209450708044940c03d49000400c1c400707100000d0454001611101c0302c81e03280208106068402140c0c5110341c0c0440d01e4201d58012451a000009009580000e05400e1058000d4a415002c01e00192100e9004440c517100511000c064156500c40c0b40c100c1c0303940003d0600c000c40468116411451001c059400c0030103440300c540300c0c4d007001e035040400400001411509440c050020a20555054a801040002045e20031600e4041944110310415004010000c0c4480521a0078854003024028003401d01070300c041c040360641d90300c0c450501d0144150b07142600e20a81e1038000c51084c9444080603010000c1345450030907480540d00004c0158030584001c42d5840000f840450b840e00e0701580700f1000081c2c28004900090850708140c01842914560000502c21548c5500040c2d5001440701d40c9180c3e141803407442103010b07002d41880c55410121072520041089000e442e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 411924253 1250 411923003 411923027
    0x10f0308121e0108010c141602010c060917030604051506250606090e0d021b0603090c03061807050d050c0904050703150605040b06181002150a0e071a0405010309020d0b0403 76
    0x928081c00302084140c43c0103a1048c0703520001613081014a500065000351000c02809014405c002811409501e030000400701e4640c0ea804504000030810159183c82d1041641045482c4100120314100c2808a10300d0b10840c0c86c02c0c0000c0e00b00e000d241c60040010280a90700c1544003038140006070b5221030742c0340502692200d20040340141c0030000c84407071001408030034402900702031486038001101407001541c000f400311461405401210061a01c040180320300035500550740c40c0745501440711450400c641c2c0d82100744100c200c8004000881d10001e001584000b00316113100e600d450b1460100c0c50070740b196200802701202c1414240c0501c0d0550f200703000300d54080d90140f09070800c030f1003009140d02c40c08140428500c0e0079000b1407903c1c182555450301010301c03401146c0441e449204c4a594040e42210f054031056201c28059041841c01d016440050000a009040c5002d09034100c14690017140617460406070784e4900b110655a0711a036801c041ca4100b02103088505040c1001400000060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 411925503 1250 411924253 411924257
    0x1111e030918040b0a020d060b120f09010c020a060509150a060603140705070f1118010311030708030a0305100b0705060601020d1806050c01020903030c070e010f0308121e0108010c 79
    0x900c14070002d03507020314854403c540c0040500421317a140590000250461070b0714020423507441d1804502d81105800401070075486c10b880242c41d140c01c9084108000c0010485030081c1d04141c1d22480742d41c1c000541c0701c1183d90021010034155071b5103035400c0c40c1500191680e403e0283c200c0034004454415402030003584c2c612341d0244014a003d250f020a12041a00d4000005600700707c413101040e020f07998002c103a4800d108401001100c0800185010024429148401c050100400400c11407400c03220f103500d4281c010b009000d181aa00ca030312070044030258001e0586803400900f0080451035040e01500c0301c0e11a90341c54504070705003185c1d658001c881107070140c4100c03041502040d0250805101034100107030740c0c1700c00e107041c900202c2d010740040075042011364092005100f95034042c000381160f00c1a290050034054a00311229003005010b900c1200344910041b0244003040c4494200d0300201e90028841e14251546c0304490184803030604602cac0a100e14900200c1d0709403040d000011030444603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 411926753 1250 411925503 411925519
    0x1060605041505091003180516050306090f06041214030406090b06151818090607080f22020d0203010501090203010906090e0319210c11031801111e0309 67
    0x1840c000d480707904c507a00d5880c0c0c0c80a82103c40c0c0c00c1003440394000c0108050114107030040091503688041c9010700ca1180d1b6024480150018801c600f010840c25138003903228001000c510b03410345003c60702d0f09000362000e015a47d191400c080e8203400b90310b901c40c0ca803100500c900c1d80c1e0300c2c090178084001e20350260308850003d014004210f8615040040c40001e142c0e140034980b41182c3c80340180002360900c8481600205141f160301300c9030094500e210b00c075006a2004d0045441c0981008007207210044c03500c1c80031081001840001a002c182050304a1401e4402074503000860001600300312075900300030b5166003454000719404219030003071070480d00340742c00a10016032039811a03415940045a29100f0354818020030300b541004a4102101000700c0c10180d40251351403e20080500380384001c040c2903503c03402800d0315160f100440000143c40031000c0e606010200e0300c0d6030b00006500001034108104d050340b00102d49001e00c89070110050302180d060308080075036a055281d03085a44014854111 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 411928003 1250 411926753 411926789
    0x501030504050d111213051f0c020f04090501020304060f1d0616030605030a050d020c04020c0c0d05190b09210f1e16150209130b030f0106060504 64
    0x2805603900865001014040e20141a03000310343c1400101c40c030307180754820301800a507210060401004681d180c03920807581c06081c041031015400200e034105000f070620056182d03c0702d9100030040015507040f20344011004501c40010090301064070054500d510000034070081142d654000ba542d41300a4000340403100f0010807a1a41244a0005458542103000020784900090aa58030741000d1400c000405980b14408203290451403a02290554400031002e10079070b03010420700b04140c0080f06c041d4900155084619242c2500c12078150184510004110801c0300500000c00400c0c9141d40783c4680081a06285000303040aa0300c52909020380700741e01c41420130341f103662605034880281032480c085410301003e0103544075010206c1350582e440181580ea000386001000807505c0c03481c1d40c6440c114141001105d254450031f80080541c03041250700681e840d075400390061602c1000c0000f440101e600c000c2824424103a43d655429480c000c004503d40740c109015000307a9404100c81050424 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 411929253 1250 411928003 411928007
    0x1120203010b191115180601031203050603013815040303030509010e06011e0e040c090f0905100207061d030319060806060f0d120f0e030a0c050114040f08160501 71
    0x11110642032045c1c0c02048500701c01d502903001003508204040701c24000c00b00303100f16503424013800ba0000c5404100741004140303050340c9405440d800540480080111558a0104a80103080b4081046807800e1492a902500c12560030101d2002005030600c410f0401c6100c8030b21880d40b060208501080c54003000c0b401e105014450100d4060500c00200711507400d14084800814492038071458200403041e0100381180310f4004d45015074418080d042c0c1d12800c0014400548101c0024090300e20700d8801d0f19804a0710000c2d070030441004102005a55004609042c2e000c0c1ca10b408070610542c1c4103c0b203075898500c00100462250040f4100b1005001c411850601581c285120340c91060b0b0204002c0380c0f0078508601ca01090260044c1070210704661507542407900ba800c0349104021441c88000c2c8146140c004005a0030208100c0140c000040165111003e403074403802018100700300b5005000440c00c17640212000f4119041e00001c2450b901c0301c203c3e541d15a18100000c07100c54041000074254 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 411930503 1250 411929253 411929267
    0xa060f0e0111030a020c101803090506091315081f05010b0c0703030302210a0903090b04061403070516111c11121606080405070f060f03020901120203010b19 69
    0x642c1d800700491a648918694901035089548144624001c1b0041112450713072603c1160399404c03800200a142e00d40c1c60902070310f005055807009004160822660f03285d5580d44090200e40b110f203103800185482c1c1c4030132038100c81d985a003001c0c0081c41742804615204c11401101e641c40c0d04410828001d82c1c3e259035100c2c8041c01288900d440d164030500f81440024003907000b601da10340a90300c0c1c0055525401103600800e00c4142c40900010707956040080034150b100c0c12000c0908a25100a4034040c07904400408198000000342051503010010400d841e100384211220180e69010f281c000e1821800c10003c00c4124040301c611818200c2c0511414194101700d1680382508048410000c2c0751610500c840d00b2101c104c2c0c2c000740d0080c80c4081c0303010014450110301400c01650b46c0310107840c003813602c54030b00051341c0c10081443e9594a800c1007131307580c4031404900040c02c0345400751700d40a0f4800141c0b100c981120031114203138000700c00810390703044200140c040084044e61001500007031480a54102c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 411931753 1250 411930503 411930521
    0x50a11040c0210020d151e0608090307200a03081c06051005130305030c0f12070f0f1401060b0c190201050d0917070302060601170f04230a060f0e01 65
    0x2d60004070f05030941d800503a0141885000c0902c0105030100044100b09009919422200c0003040045e1308180f0700074044215400b80403641400c0b0100c3c1030072942256603025407a0003d00000110f02c21030301d80385015801041e5800040c01e250407d907124602981a03030001c2d41b08900303141454100140d809000d01a2104032400540303401d4071556a014101da60b50700000283d189000300076800800600108010301c05c0140c01005004060543e40806040031401c2c1001e04400340180000e40110f01c0901040d10050ba1012800110b480c20780b40070040d01500c0b05040382c3c50b5280410000e103840200000748248000b00055032511070800040400007400b07494007038005401840000d003d00e02d1039001c010702e24080d84c000c00c070001c001ca03540c42582c0c1c0000d90072030040e04a030090040e6560085260103110540c00151a0301d40b506e4101c05411140040c400341c04450310044403020840c1414882e20304041c0002542c0c51219a0b0030710300003510350f0a900d1684d952500c070b659040548180309529070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 411933003 1250 411931753 411931757
    0x11802030d0e010c060e190302010b040b0607020a06030207030c120f09050d0c06080622020d0b0319062c070302090a020f03150303090a060908011802062d07050a11040c 74
    0x5103c613030791104001402902400040ca114000310011180d290a4000107000d12030b60020845000000901003034034000782816024007028001007005030f03a0b051550040c0d8a01c2d00e80140c5816180c02c01300da03407020750131f805416600c82410b170780001c551103840d01d00014003546415000c41d5803030341441044240c01c44081c003c51265042032150314071070900305401070300040407104142c2c035817000381040780914440c480c4400d90000e07070918000d045d402410100301044002d4003021603410082c10f404c4410600082c88030390765940e40c200c40c062954591481c0441c441000d079000e00016004e40ea142c03c0c60006902c940c083c00700050303008405000303c5401c036006d91201821502c441c01c00c0e00452070120755030359050105004060302502d40411050081c150342d07442d140c5103458440b0050854030311400d80301311800805c0b540e41c0540c0b6100c08440e14040c0440300501c540508035000124001c0c00d030003030000801c00040600c1804400511014000d01651709001e01441103020041181c1c4119800c8c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 411934253 1250 411933003 411933017
    0xb070801150c0f0c0504140a050a02120103080706021201091d010513030e040212090a0606060c0809190e0910141e070e061603020606030c010e060906040305011802030d0e01 76
    0x50385120f012650248103454500b141511800000c0603102c1c0005002048102c0d01d0400414040c680200d6800142c003410861a24083c3d03031000b000b0100c14000a44103c100041403400c00c0410b60448150001404100d02c580d610b500045000d400c1c4480c04050300e58140601c02d2320104d0611441d03014180781780f0001c241d5000e95400340ca0700c82d24402d19681c0180d0078010089040300c0a500700d40f08940e102d02604c032505151604400f100c40707a4001b541080b11a04d189d50004201d001101c580210031682d01c031403048900303091a80505950010806140b603030050016101e0300181c10000300142a00034041c0118001da020302c0010201d80c1d070882d10a40c4481202a42003080140b60800c0091420072009400a008a00c06510074039080e060288100c22400501d0303810720026070007280460251101c0c10205000800201c80200c03072601c140340003e40d181c640e540700300c201e900959010000f4014441c10194405101c0c80c4400181c0c001e01400c0303c82c0b03081c9842480d044140c2e01c816141e841e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 411935503 1250 411934253 411934277
    0xb1b210901111507031d0d0f0309050109050d030b0f0612041209090501030b071e09180b0a140f0d030c110a03080313051204081005150d0b07080115 65
    0x11020b803580241c0c14014002c1030114445555180e100500c6440552008681c424010f0100702c0d8a004280010740b181d004048101141a801002ca032075003400c2c1c1c50042641c0c01c950516030b0042c10740a0b4000c00300d02c01d80e100d8a00845d01500445ca035044c0c00c881000064601200740019803084902c40d00f11f25941400150004001c540e02100a0249180c044981b41d103d0b00c0502c111034080c0c01c00d64441c1800b40820135143e030300c4040c4040e11941200341c0c500500b05600040c20603110360003041041e00f0041c3c003600c0d00e0b901641c080040801d005254500d03256075540c00c90030007101959110302400101e841c0310550b042c000101960705505580d8500c20102644074000313001c001c1e20f541036001d5170161001000c148468042c5000362140c0b40c40034610542c91804902d45000524884040d003005c1c00104022100401c8241c50040801d1011605030780380d40e03402c0c001000304071450380d000387e11440040a204034406c03414840d408a84504000d07988178541001c964203508041d40001c1c40420082c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 411936753 1250 411935503 411935507
    0x1090309051e180f180c12010f020a030213050d02030a030c050a0f0b060a09110901050c0f030c0a0c0e0c0d1d061911030403091a040b1b210901 63
    0x501228028070606030b00310502e200090f194202810022081802a0041c080e2900107103070f46981021810369501c0719903d0000c40c036511003400c0c6010a125000b180d6022004e0f100a4001c0443c80d2045070045588540307061002d0025004030000c5181c0d080001070104048c10408170780085560001c00401c0c84030f14580d0308444115402100719201e004800b002400551a807244030003e0b8480c0d00c20400e186842c03c14000c03803120751743c003040850b400c040d4188081c0700710004860b403850082ca003540c2d85a1200c9415481c101080350008030034400044c883d0308219020640e8440350388036010b268942c40e07859450200308a01901d246894030001c0003003403084402603000e4a442004000344030400d62503010400d09000c0f00320307249a8515201c13144013200f41010710549000b000d1060000e0b007035007407a40f0014107080b400d000385122000d0189000d000f00e8011400d5400170300580e10f40d56692203c9024904004103600b40000e040d10071581650a840158803802c0b5508002d403045500b0b1400c00001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 411938003 1250 411936753 411936769
    0x510080708150c07060e03041512050103120c030c0b0408030f1006020c0402070f0515090c04060311092a1206060306030c060913020706062402060103030804080c0a030801050907020109030905 84
    0x412245c207035a8501d120320840041c00a40010714500700d00002d0016040006031201c81040a00c00704241b401006100080320302402e1481d01401d40f80110b8030001c42d00d801d40b403c007c60007029251a4040307040004110032003009512a00c1c90041000c4907848080316220380f0085800f40d00b0158000141e90074040c01c00354040c140315402480c01b070152010070740b940f0303040006481480e0031444402041001c0e04c02c2c00c02034003645600c241c4080180c1440c60b1600710760381034075406180c8119069008104070194481e1084000c000d5100d0180c0683c000c02d4141c0f949500421040b00b684c103c1c000004c500d4030300700007500d01c11032003e0040c0084451100400410b5400303102c02030b0b80041403241202071485240702400c030f1503101c0c48001503000e0a0500e07003440c08020550710041c2032001950801081e07404500c40d81102e83c1405e0420082d101c0d440c24241501a001500301d40e0300c00e614028051651040240d812141c068507203a00342d40320702c0012400da41e038652005d00442e0303021004202504020b40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 411939253 1250 411938003 411938017
    0x40c08010e1306090b0708011509050d02090618010b0a17010501020c21100b031c120b0604050d030f09150504031e0501020f031009021206040f0b03010510080708150c 73
    0x40c000b03a13902003607403400e401c10000d032058030004a1030700061003a400400b82c02a5502003d0814102aa1920000072032100c200200280203500700350100d640d40d2070318094000d061800c210024070944e1907003c0580036401001003080000c21a1040d90000b10054852505892069003e80b582001c075200340312503900d0341c2c14240c8900300840720004000b00c060103501c031500300300740011400f0807800c410140703005603566200c920308c070191900c00d5820750008041c0a0350f03800b4400204050300390320005011400703203504c025004841c4000010406030b006001840c0c510340348c0c60326903c0b6512210007080350110820307200049081004140040748481d280116601c1001080f6054082c09903580c609a8100c048148444903020090005a0030380e6051000509035480702141040c0110b03a0328100000d01a16480c0642d0b2364508861100100d81c01c9100c0b000c0019000740882c0c10210049070b003180840c450b00d07250b40211003002c0b450b0600400e80c1286207082000b40b000b1525600d01e80e540e00c1d88806 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 411940503 1250 411939253 411939263
    0x60f0203060603040b091507020c0a0911090d0510020a0504180603170c010e0d020601030b0702190b0603010209220b0f0d11030f0703030519020f0d03050c130311040c08010e13 77
    0x3007015008101c124481403088d2210360151100c140305600780807601c110f94102c24041030428036440307160707541d580a07605a95400c848801d074845060070402c0c100b214000010311800e00025030390b416260003000610886003c081e0b40d01107c91003d200200300c4034035000003408000781c1c102102032060b810700603000b5400034400018850111a003001e1030311010142010250704040010000d05ca221541c40e0391222050024100c1070900359002c80b40390f0000c200080c110010000030841d1914254162078003404043d1174501d400400c00380d903540b00032281e1008000d1038104149405a4104000b81640300f190190090400d19007a58070707ca014207003540701d03541500c581000101201d408009240c000d43c026242c0907a501e16050005800c404102407820039035000e0043c0913040b25001600d1509002e49143c00281d1751198950510b10340b04008c2401403000c020340020041c012290540d81c0500000c41d01081181d56241702503440b50800d1007045d40c0310403c207000540c52040c10f80440d4004d40300f0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 411941753 1250 411940503 411940513
    0x308010b091504090c110a050d140904050421031a120309090a09021f021f0f06091a0d020307090b030a02040e0c0a050402030919080906070807060f0203060603040b09 73
    0x40b650b5070342c580c0c1013035205124880d22550b801e00c01303940042040c652a8003007405407000d01803603168503544202040f4044100846a0070101c0352503e640c05849103440010000d008070300701410080319140c1c13074142c07004860718403a000139032440c020b118002400120089221280d26660100f07d00d010641c02452504d010404c421402036417260038040c4501060000083c03524014014003100050804c00e101c030350b14064001d02c8110ba000211075500c00000540344150a0b00c100142003d00031a0309105111802d085021580030080c1c2c00159841040d4060550784402c540c0412501b020315901c00794068000e00360920202c0c9054201c00e401e9040541100e407000c040c0d0380800c048940d210200c22560304804071104451811840000c0200400c440550450404100c0142c0b640c0e00174020601098000d09900100004002600d10350903004041c0c5490f414107041c1403081e9800100c08031ba042d4a020308008041400c0d20a40740280f00241c12141503568968400b08002c002510100852040c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 411943003 1250 411941753 411941779
    0xc010f1e0b03280b0609070c02042d02040e0a0b010e060309012003040302100c270308130807090606050315120a031e05090f060a0c080309011e05040308010b09 70
    0x3e82d41020348440d40c184441c01e003040700790130418544103002d032407180300d9400322040c040c505521942081c150350701110700103280d21382081000c111340c2c000c1140c4e10401c804241554014000381d800751080320115080d034052643c9900210045400802c1040e0102d44504400e9166003170050196501104000000580086000d1400c00d29404031001248180c2c0001c100070805074140842c0381c0d0f04c15044402c2c8032900030010302515100a500160b0b2703540d103030441020070921141004500035900a5021a9580304500703401080d00614014107890b4820104c00040407001e500c075040440e0b08079a241411a1201400c0c001d9001c003100c0700c0c40c5d0006180460381d10840042c0018182c240c0300340c84014841c69903591500070072003100200028000d0503c0070f81019114032071142062003007103481c2661021542070644411064803000340c9410b001108004804805501a075418000c1205a403001c1e014400030038241c400c200ca00500141004004005890000c0d01622140c60000d012000e0000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 411944253 1250 411943003 411943033
    0x20a05120c091005030f04120c1509052b0509010903051b0427170f0c0a0b01170c10141314042903100e030c010f1e0b03 53
    0x10040d00c1d074200d0750100140b90340d203514040045078181407440c02c01c6400c528050100000d410b0005101034004e201c0403500c01c40039031280d00601c030607030b901c40d094200c0c0144054014004040124080720b1500c0740301082205100b8500003034294041c0c804c49000c030300c950020211415004941040e040c03000e10140440041c100b844852031122403034036403005440f0100f0410041d540102c108800e884240917130458642840070504503480d0b04070031148294140640c2560943c464a071080900c18004541642040b4001c150009180d000740b00500ea166214080d42d00721142c1d8050b010101c0c1e006a0100c41d10382425000c2180c40c9583d41400e0134601444144c0342002e0740305e204500c1c0003485e190020301c070a0391510034130181450b0555003089580030140012032020642900e8000160110080954079581000440c4003e0072503441070103103120640e4032035583c0c0c0000b001e8900c154205540c458690485e44103c00090007c1c400e82150240c044d400280200030b02e501c002d80501401c400c2441402c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 411945503 1250 411944253 411944287
    0x1802040308270a0e100b18042304080c07090b010f081e07020c0103202b020708030403030c021b010c050f0d08270c01210f021b01091203020a05 63
    0x4010003d0610799031078590800100104c035904034504002050240d80d446811f4206200c0b04010207480003d020403100d8200c1000040413501401800c40a00800c42040f600d1005031038415035650880d0441a02d810b0700c0720941e0210300c0f40a000541411603600741612400e6181d4111644030941c6071008544140711703000c8e45044401c8030250748541c180340d1503564544112034a52148000044c01d103844400c0d0611940b103001c541740342c8228400c1e2045d00403061405d400c464600900401c550314080740c83c007102039400c12582038012a2821102e00d00250000ca1842c80090a401480008100c40001540c220b41580c000b0382d0039114102243c6240d26081107080441d4245c0c0c1c484001b14a402802c000742801c1d40d8500680304021900c0302070085000042c104121002401c0c0301c500b41c0da0b0004480c108005640e8019120350a28400b18220b900350b6008007502450b40c065001c8212074031400302d00340d03044441e004001c520b12440d000000341c400e5000d003950001500e007643c40c1c5140d0b445a405c6207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 411946753 1250 411945503 411945509
    0x60403051837061106010605090a0906060306030618020d030525050f0601080307112e1d10020606060904090b0405100c0e0306060f040b0402131802040308270a 70
    0x416002c0079000300084411000e80003041103150084141418003100ea07194401841070400303008022821800f1076aa1000660103001b0750078040000070f1365540010040c00d1a1312007075920394a40b200f1540c5e02000c0f915030742e030200e4000e0300280d400d08165400311000e5006200d5491aa41000045611104000e01026009014000518400201d108154102141a40440c0301030380100f0008000540c150581c880f6010300301e0f4498204001c40043c0d1101f0401080200300030b00b0600c020444031500a0780f05502c100401c0c42d09822250600b0510a09860701c4055101503400a000619146060001400280707400b800c0428501a030350f6440d56010001d0b101180c1c0ca400c400c0041841003c54858011110348900d8101ea02502010200e5150700010b48000c0c0207030701c10062054503486a40100c5584d8038041c00455440c03603844a101c12194603400768540084d030940d00c61016402900130340b4282c1c2d4100c04503c3c41e014420301c101400101848030704c10b0b941c81c62401600a5920043c01c2d1000b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 411948003 1250 411946753 411946819
    0x90b0c060907061809050714031608090706020307112e0206070c030c0b1e1003030314010f0b07110301020d0207020102011404031407051005150a080604030518 70
    0x505051441c1402c01d2140d400c00310421580021454849680c5111072085416010002901c1d032100c002c11034400358002160a0030030b80001c10f1240340b81d45000124500000d27944d8010880d01c64440d01a02d4440901c50240180d02c24401140032807414002ca08540400900d106140801401c8030882c0c1061480300040d42e01428040007010b640512605d03900402c2882d2106c140001940c01a000d00c840f0700c4080d10010240c000175070805d08014900001040b07104040c14503140a09005500740c01d6404102e00180c14011500444a4402d40550694048a1000e50045d00308901407025400080007683c0401c0114880300e82c60f00d00307100810078400c2c00d03007000d65181e4070790002a00356600360403611030178145d8008000102e944001110b1251070f01d4090b003a43d0f50103130b00f889442c04040740c240e01c00705c80c50301c0240b040356020398020014100064400d840c80d542d803982090340b90481108d0140c0031850070003640241c090010725913040840b004015032000a45c01480c201520000101210 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 411949253 1250 411948003 411948013
    0x306020a090603050103020303070f0204090c090b2d0d02190b091c0b0f0903130b0c01140c0712050f0d09020a05040b0114070f140105040c0e070c12090b0c 68
    0xc0020740c0700c032504002d840c29040504c45545507a0110340d41c0e102c1d80320b003d4002014101500c1c02c55981e0f0f000594119044245038100075110380800c03006180300c00c042ca1182c09240115146160003c4d10481a554140c10f882c0c2c00184c01003e100048007201c00407030f80903001c10760a495101c0780000b01c402800d02c480003d9140e42d46203003401040c0241000101c0708003c1c111601c000a50715601403540080300a82c00d402540f0390280e0145580500242d8014000c460749001c81c0e110780b148040e204541c125402070010010040018800c4107080d202d00c00803902c10800c050116002d00a0389810a15500d0010300d003440c0300c00070202680140300191446512003820806601c0c20703841e0b0300080c100880e01003041490178400a0150182c00c4c184040082c00170481006100001443d1084075402444024081001d61110790007080d08480441c1c0f6a1400e40740801c2c42c0301650b18203031060b590ac0d01e070780d1b0805a4a441d042404d0450500c5802000724004020a01c20b07202d0380503018007040d01d03000304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 411950503 1250 411949253 411949267
    0x403110405060604030b160e0a080c2107060e1908060403121506140d0203090f061501050306060c010e03041d01050d3219021c02090a0e1006030602 65
    0x2081c1c500c06000c25204810a020a001060750030071002e800108481c04902001d00030f04050b64482d81c01d800c401e030301107081500001c0505000c103401006140c22601140180b5082d10340410340300da03010780904698406d400c01d1000034002d030741030315800c00002c08494000d18002c02a40103c51103402c600c0c02da800100c03d01c400c054011401508107100d00d88188011020b1071180f200c40000da21565041001d44840001e403141d414085800d00c180d4040b06641e607143c038050081c1d440307011100f01c01c204c4c030030f100001c0d13400d0f0340018000d00c604205070346d001d1564aa030f400b044110303044407000303103900d540c0d410b40204000e208100410040801c54100c1044c1903817003e9036440100164030090094060849117000280440544030701c112617040c4c030000c14002090301d038810b070521030041140c9200740491010304811074000003a59901c00c46000c001320300d090000c0b0060407403900000750000d58110110300100d020390881c14050941e41d003103400c4152441c580c0e034213031440c9900550308240c5c005084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 411951753 1250 411950503 411950509
    0xa11030406030606110109050c040b0f03010c0305100807050a090f0e0109050c04060902090a030305130308120f0a0207020f010509034912020901051b01060509070e1c0512040311 78
    0x2001c0e9421741040200182100340d15680d0b140e800200c030f0148900e65801000c035a40c0e8507c2c4011116030b0340640200240e4040c0d4001400030b00081c1c41c000d070024210407000070780c0580040e4100a842d005800290310034540744d600005823140d0101030101e65281d01c040d1a60b140244580307200280944002c122800c4002e0901040714616084030114074010402e03240c03140c45044c1041b00301ca5040c54100d946403050070306110100101d030001001a1400500200e028901420f414040c02045442a40c02e48455031074200b24451080c000750003641c6411074500a600450160200070806402d542c00c44801c082c1020020040c49000007040080c44554880c100420012501e01803034004040c4810100d800c000d0080424450400046600040c10010a034420403e0b82c1d11100641d80481e544185408600d001e014140100e0b80074111000007d60740740d2040041c2000702402600c0e11820344c54050407040d0319445080152800c0c481c1d81c0d49082040d6001001304000c500850240603d00c4100e410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 411953003 1250 411951753 411951767
    0x304150b041a090a020c12091323090c03030705010f1a061e1b0f0d0201110904051e04080309010b062704112712120a11030406030606 59
    0x40d20740902e00e4090002c0360285100010845000100c072016496591038122802070300c40c11080c03103101c0c042c80c030200300e02038031002c090320000800302c541d85010602c90006408070341410031002c540ca515048884002c403144000103402c41c02d114141c0e418003c0c0c260101e80756900407a0100c4c4c2c541e5603004d0349891807070240703e2444212598405002c0c194400c200203600c600a01850f0f198444607003041d100350340b5600703044800c5101e02c8003a001e94641003a9455403141500409012140294401d1131000703841849259420a203e0b02401d0a007003041091000401e001008826010f4500b0030085018100062035486a84948004d0341d403464480e0381c4501b50741d00118018014074080c44488456000515a01c500c1e0b102000d0300084142c6600015010300900e0078404490f4000086031402c0050004208018007028110142c00300c1820f024442c0e40c2180b0003103090765070001284141d40501c03110040000c2100d40c0f0b499407100603440700140c20b69000b507101d02c0109036503071010011150040c00d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 411954253 1250 411953003 411953021
    0x150106020312090f0703140c0a2c0c0a030f06030206040b07020a080109030e04020c0c09040c14030f0d1115010b0316020313050103181703010608011502190c030602030415 75
    0x800760804010840c0001e80d11100343c04001c7c0b01361000c03129800c0c4800100a44c2c06d42c020700500c001f10a035030b031b40000032007444c501c0d04210740251130f035800c60074141c001c141071743c000d0310440485840d000120000324010400076031150032240e11200c0000250f81c2c1c240190000c0c4c007800d000c0d143c1d14062481041003120751341c3d00c03147c1980d0428000d140482c0d04560800165070341a607000d030f5504124843c02d4104800061000d500580c14070170f010034010340c3c040c2030007070b2110b044516030748040c640d0416503a103c0510070f0310040e61000c1002d00d417981c45003d1396030400e00d001088591508041070b80210710079098000081111001c07003004204c40c0c4003555200c0580c118000f0314540044940000c1c42d403400c0b400713580c1c1815110380713600c0e0300601701d0549091641d4100310300c0c1e604081510301503003603640207214150004810000200f10f420b90550405402c1a464004089200034011401800030843c84141c813918426500080410b02e14001944200d00c00c6440060595044071158200c4003101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 411955503 1250 411954253 411954271
    0x1407051c1e021b0a0819050c031203040609060b0d03020c0102070b0301050d061e0e030c0d080106050d0b04021c0e070b030613020d0e011d0c012d02150106020312 71
    0x549000c0415030082143e001071090460280f002a154a0101e014526180c1c4102294420948600026940c19251888051040055400346100c000826588804e841c49041c0701c1e8004202050018280e50310440505110300c901066000d40100000d0700100c200f00154056045018a04040d40e07060103000040e00d030a6003202e08550400b00800c105002c11200100059a41c001c040401d801107240c2c06d080c0f00603058180007040b58040b001c1c4d240c0c2c1024104010a00c5458000041d090281c18440d0503036202d503030b80c40d00301124458800c0c05003881c0320066811680c00c00080a038031610068048119004040220300340d040341038007500d40b02160340284640745040c01880f045560700c030030070f030020809508003580307032841c0c000c0b100b008218145d601c908641c41c190310680f10059804030000744228010580349421002401076443c103080303418840e140b0b402c16000c0040c3e810651900c04062002e0f104803000400028051610362100fa0030400c003580c804140034001c1c003081c804c0503078494615 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 411956753 1250 411955503 411955547
    0x6051201060219020103020705010e030a0306030209181f110406032306010509062101080d0f05180d080702090f090c0607050c1017070c0317060306071407051c 70
    0x20210843e035019204800070704050700080c8200a00a00b50004018440002d042e07a944100480001d0000c00081c88120702480c050400640b43c0c1080c40802e12864070f40201401c41e01d04800100c5510b1801070300f03041146a6903940082440c074499001d040604469100017445150020102c02965010100c5200030100c230000c000d41a47d1010a465001c3c00c191480743d00c81800c2c1c82c4c10b00d540e8104000000040f1180400042d010500141d144021030309500d9200e10b00000e900d0171030720b41c4120010401c82c5500146003050a040c51542d407110f1500400f54903042843c0c5500064804a00fa503201130840c80203801c0c400d5221042c0900c114140c011a149440c1003029034030141c450b0100000c0750710a00e0401c1c4216000e030700941041020f8050300d0412065860f2000014060482c682800d40000e561044074443d5103008480007806184001e005001e80ea94040c02101d0390440c0d002d409002c05802d103e1030000460401011075140d55003070181c3c00d104080d0074024112030049401c0348480c135079 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 411958003 1250 411956753 411956773
    0x4080d0f082206110d1a040501120b010e070c05100b0405060f090109050903042c0a060e0f090f0706080f06010932090a020702010905030d0210051f060512010602 71
    0x70b81014040700c02d0b808071001c102d81d000341e1101003442c0144015104241d08262071082e05a100040f640e004140c00c45042225036250784801e0111040c9200080061040c800181f00114118140f00d5120300d0610b050b0a107821380b591494281522880014a22603c40000000302d292a0280a80c44681030700e99122200204000071000c80323040c440c0030056036845000c900048010700c1203802806640364881c0341082d203800e80441c465100b07012204038441c4500800c140340014014081281c2c0000750403049600c03140ba205a0b51080608000510300c542c5d400b4100f5004184004c0d4001c190340c1d1100f002614040580e00b50400c0b001748001d0400c5002d40c414000302d01030b04440b03421851402c030500b4440c2203680c40001071146081840303600203081020401e0011090300180304040c405e0740c0e0190610f60f56024580c3e900103c021900250300403806800076240c41e0f500840e0710900c5403810840d035103111350b41c00c08079801580000000440000d00c0a001007060f10380140102121b100074048008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 411959253 1250 411958003 411958051
    0xb18030f0c15070606050306041a010608060f130906050c1b0303040209130c0504140a0b0f09070c0303020910030209090f060d080705031308060603010b150a050f04080d0f08 76
    0x259070b03001071281440424003c0910125038031070f4020300030150446040d400c00d4141070064201070102c10340300a4880303001040b0944a16100c0c0d00900f005040d00801a02110800c001111101d5000451039038a11494006c20600d01805003d40b040046081d034500311004440e40780207207089808642c0c0d00070030074040140c950b07540d01540700300c1d4030070501d01002e45032034006a40700d00b5a106541c402c4c05e054500342c0800f40380a0140c003480814104010301a40c003410302010040c20152240d2040b040400100341a0180700340d100c0d654807074940145044801d500141d4011800004100002e5010840034518184200529007003090745050010520300100003500308064010024031030500450300320b08126040080e03c0d00540c410b4407002e0403d45400d900c2e5969641203590503c02e41c201006a01c85042c9540e00e554442201e820351498503961050996995101d5580140ca004040000040c000170034000c0d00045281c0d50b07150300d051849070310000d01e0310102500342c50301d03080b034802000700b446 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 411960503 1250 411959253 411959269
    0xf050d0605100815160f27180504060c08010806011203030e061819051e0c0d0521121302120a050f01060b0301080d05070c0b18030f0c 59
    0x990005011505564030368507805a8a041d0f0700c118410303c16040c40c2d40b40c014154808078442c048201d05c0d1103220750b140a040302c2118448940c28080780f24001c4841e45a0034a281056200d0510710215102a54400180c2d074100301c401c070009522642e034000d02003007103014014006441c4851610038019410980c13441d032114018440d024100c0c9102040f501014025040240207a03a9003056641c0c5242c4000314824806014505d004030f4007032005c0f41d65603a000721031090b5540c1e41042c010f28135503504d001041942c0819050082c600e1003521015500c070707516000000c03280c03486100a4141558a005610403ea401a0900c41c0b501010702c01c25525084024000703511034a000c40f4407a0240321400030600e000c42c0c5001da12654000d01c0c070204144000080d65403480000c441c020403a0540c2c602003406540420b0050101a40090301c00b44459480b8501034003040b405081c0c1d22144a81c2e5426188866001000c00000013032100316030340c038526043c401c0720300c2030111002400858020000240c400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 411961753 1250 411960503 411960529
    0x1a0307090213050405010b0a03051b0a110c0a0b13120f03080703090c060f141206061309150303120501080705360612010c0807080a02130f0602070f05 66
    0x21075021581c2c0b40c00d090b61554260040101070003c111950b1691800c03a200c0e40440c1a01003c00e04050100701603410a40c0720a421009a2081c2e9003400080741c0211000001c02c0b082940358410300400c0809559045020401088103950751a5a094001c0030400c00c19195440815001d4084c91380710003003102044200511039142c645501e55548940c015401880c46650190082200080214405800015801d0005901d407600c440d01d401e0080301c01018818078008103a58440540480d0160070301401410f00030311503c6403220360980b0780c40e040c0704075130480111080d44181c8040400903d6080f02c89280d011000304001e228960400007166a5004030744101c41c0100c0503544080451600c5822900c1c016111210840700803240d4220180006130941d54188503040c800654445c0080c14071520b0a516500e4503512142e9075144000e5403030303640040000340c9194003040004064003241c01f403100540b40140604011506002c4000d01e440190740042080c20180079052005d69200705d041c0e041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 411963003 1250 411961753 411961769
    0x152a050601170a050d05040501030b04050c09091308120f06030a0507051207051503040c1205190f0b13061109130c02160611010507030b060d0c090f080106091a0307 72
    0x28480d050050b185000d401c00d6000e00a8082e009803100001e40c807000410445800360303014480c0341514010401100c005030f4810080050420031042d490030440c20a41d84800c0a4190340c058500c242c0340c0b1222a8012207040362424031050802c102043d140140c030f90061819001404a268a46c0c2d915503284080e00640303108141358162044101020801c07003001d0400680104c00c002048000301140340c005903421540c2100aa00101b0b03610654040081c0c059045001003070700c50070b004c41c05c9800c0300e101c4200352001c0c2040804140030400d040030850190045501419048aa905040c0101c510074040a022a80308200080c599a03450600c1c5805442c44180011540501803050385001d02403100c45010140c4410005143c6800c40b021402e1100844001e01a50343e640c034085045544050416030700c00b0050280301140c507045d07886500c0000c254203000035404e4480c00000440a084d91103105669104c4070b0500402280b405410506400c14071007030326041c1058000f07921003115000c0d2202c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 411964253 1250 411963003 411963029
    0x6030c0f0307090603110f010c050304030308130f08120703060f06140d0c1e030213031b0f08252402070e010303030e15061e010306152a050601 63
    0x318550707041c003101004040070282040640d5a0f03152074080100314080083c41418683d00d541c50030f5025802c601130f2507520001030f524207801c55405a4540e54090015202c44c1c04003492800011a4020a214410b00407201d15440b4019018850342088000703080c0000c150521008100701c3d405020709400341da04a051241131801401005600c0e0301614800380b5119080060303440205402040c07004110403024207110000c0c040d034205606a12a10715103540d40e4018460400c0031640e4007280ca080016a001c0320000581d0328002540000483e42098a081d0085580d8515400b5000c4007180002c206d814502c0185203003443d41354664118a00d1011102c602050119126100b03200301c070302915500a404000d540c603820014000c00501003020028400c1208050300040f03c079051601c684001492140b5000c00741803103010341c2006140d41c506043c2c841c0030204807400d1101002d100c1007580d07914040b803034110780340d291419442c00c42209001c0c0c0c0d14241c503202054012451a06460020350340c21 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 411965503 1250 411964253 411964279
    0x18030a050f071a0f09030a080a09080d05040c050a050d0203031e190207052b02010e04020906030f0624191b05060403080117070e0403021501080309040c0806030c 71
    0x800340b840303002c00007040030204820420080c60101d00d03150080c80200f1a840d8990f407000d60340d0b5580c6c401c0d44161400300301d000b0b0015420301060741204228a01c40d4a080d401c0c48541980e2006031001030f2800c0310a00c0f092903091001d402e1403450a402040222080800ea4a03681c0100381c99110b00c032104881700040d604105084042c600488110000c41800d10210b00441c40009403a0099405250b1040302c030049410120301c5592801000c140d81c2d6848080302c40000e0f0b005541a551090350183c0082c0c0034484003500c2c0d900c6401441c03013448080c1a046091900604111041100010f82c0a03100f8185500d00001a9104152101440700250f25401c142c071140040d54a40c8000ba1100c650f81d40d20111b02081040c0410383d14090f030f1094407001140c1e41c8a010503401c01070400b004a440b540050020020942c0c00300e00343d60440c0c000c0c0140c03050851140099503450400f40c0042845600000303c0c0b05243c1800e1040601100740703454024020b080040010751a0014a00c103948502c26201d801 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 411966753 1250 411965503 411965527
    0xf07030302041503051f031a090f030f041509060507110a030b04240c0e1e091003030f0507020a180e100e0105180715050c1b030618030a05 61
    0x54003d481d60044000c1000703000300000307010b020202e840c4183c401c60000e03189240c1250040d010300f030b44d038000702c0c20400c002c0e40e0761440b10540c001003014500c0d11a24200c0e02e0200c0301403009020303200980720220b50303441c144400c20031102000c61015080181c00001009a15400401e403249154452101ca00000401001071016600e9420213403031240300c002800100804039015404002094480d0078905901400f0f54003140c944804110104046000085c0d5510740150044070200c545480c81010781002c001081491400300d5142180600c00e903414418540c11610500705d59596142980ca0300544c4c1d4041184658140700702c0d60b20803001407900b4801c40d403d8100300d80d14400d2501f01d6051680c1ca00d5a000030f0240102131003450351814021600701290004040400d01846001b00400c1d0f19151003681c507000d01c202168100b06040c811498009414403c0c2c016038039806d4034400c03240070310130101410000013070140e14000c1115004146001c1c0003000f0354184a400e03040203a1182c58a00031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 411968003 1250 411966753 411966757
    0x60921080c0f040b0f0715090b0603010e0304050f0307031208040212030414130219050316020705030307290703150509060a030305030601090b0f0c06130b1315091208060d02060f07030302 82
    0xa02c240d03c07c6c5610030448a590b84400851401400343c11104e46921060500b03c40c05845140455041007005200900300b55640056588000c0c04441c0f110343d517a12402552000650f900e00040d501034240070561416401110580560101175440c0c280360513001207101020150303141c0100d40780070308a000c881c40f9a05403000550070280c41001220340d01d00003001a8821940a20019881c10503080300038030005000c0709031000036004618194054131a0750440d98840c07011440d01007980c02d144070104508a17000c1c09080162404500c13601000e005145c11041c0d038000317030f005984100400413103546a444040032a40c0605055a69464134001202d10841c6900200b1030504005003618094a0389401000d0412a03038050300c04a44625000071a46900c2d414080e0581c403d0b40007003100d011000c400f5100c454070603100305104090014288094a005880545504448409403421160007080050b40610101da000881d10029800150b9034020724459071402c420104a000405010b981 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 411969253 1250 411968003 411968017
    0x402060705012a0315030605090106150309030f08040f02040518070f0311030102030606041701140906040b010501081b09060c010e03030702010b0a031707060921080c0f040b0f 77
    0x3800b08141e03195040800b04011941c46101d2115211080e80f40c91007442020812100c0c00001c00e2214030350f464400107004080d0202d9515540d40c1800512a4804400b02c08074214980303000c80c0440160602510b01141c0034460418006030008000c00242e078a282c0045403541280c000955403144c0d00d1880c1001600604e04100340300d07184001c502e0b210b0291020080303d20402000d01c40c00c00314400d15081c0e02007541e020390080014481484030740711007024030803541c4100000240450214200c840c2d500c4041d101044960840003e00040c807012182440c0546070a09024a440c01c00c01c0fa42203102c020000070601a440104550f00b0b42d41c2c8a41c2181ca40c020400000d000c0b003002082c034542c4952040c0c841e00d02640c07814820728030a08250103134104036a0000503901901c1607000e182810350348140c8080302c419558003066000a000c0380710082e05d200161114959106a0b4032021b030040d80c1c054514044890240712000f005800003040301c040c0c1c0c1e481c500503074444000180d0b000702030207010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 411970503 1250 411969253 411969263
    0xc050301110904051f030f080f030c0c2a1002070e0906010806011208070303090807020a0b09120a021f020f0708012a0f0e0604030203100f2a0804020607 67
    0x252840140c2071001800045804a0307041043e919605504111030794101e401d0840c0f041039000420100c0c15858041090070b004180c22854071400b80c42006007039200712428404500003041d50303240104201700d0441c1c4840421a41000000d01c1c9021001113200028414822030349180d203182828404d1200600400c60f250000d8550b0401c41076540c2c4415090217034500905c1007000020703000314544000300c2c2082c3c0003000903103004040e4808a0103050340ca0300c16100c510041100c140141c81d51507801d80189100b00301c03903880d82c561004008111610380d113558115030001e22580007513943ca810301214006a601c140344c103403012180c10f0342421504140544e46000365000010215010b40000b81d0210409040588070600011032080c80441007001381c001030405a1030942c45ea0041071403d04899005000d00e040964035030019203060368041c119032410361149140316008000307004003c0e030300c514089213203180003c2940032407113010880c000b0810460101c010030705640300c2c02e044901035074002c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 411971753 1250 411970503 411970511
    0x41104030c030f060e0a0f021e030f010f0e16090207020f10080a1508030d0b21010933090821040b0601050a0905130b12070f0e0f010509040c050301 65
    0x3814000d0a5042d9103a0036030b1650300305241d45c040d48030003107954400d040e84207825240a46040d02807041e44101042c03140d6000541840d51203032560100070f0855148841000452400e03031001d0102e01b5190a40b0403440c03142c0c400c1e0080501511086045c1c2c054614142d40127071035203900c6c0001000c220310020060b8003d16801d2401d103400b40d00c11001c51280c07029060900c10301d00b81100e044c2c60b4141c4ea1090039000c2d0030070721507a101c20040b0740011180e140010b1441c1241c000c22402d05c4004c1c0020880d4180c184c0d520265a410048a00c0a0041628084100c656228030001c104d12408080c2c3e140303180655580d1180701c08205a000540c0c1440340e00c1c2c03600c0005804014400d86031640c0548059030301010b4200015050761150b4202c580e21101a529002094a0002031007028515a460948165100e0104906944070841d20100c0072001100908503d0301e01801c0b221003c3d1f40e0b42000703800e11044010010841d4941d102241198070a880100240c2d039036041640b214249038020036415420 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 411973003 1250 411971753 411971759
    0x40f0618050d0c03060c0504180b2b03030b150f1e0d050612060c0d0908040e07200f0307030806010512010b0901030c08010311010e01050d0507050409060b0901090302041104030c 78
    0x400780482c00713491203208200803660402c1020384442c000d9210b800c1a518079901d400c4030403a0036070481c8e8400b04015051402c810b0424000210502140a01f18100e400c4810400c052641c50700410304482001e9844828141c800140344000b4480c04d042c000701c1c0c10000a8070202022080d013440c0c9480780110307900740c1b125400e038510380c0504410741d0400c3c13203040441d640403040600131514900a511155805250148408050010380420340003503e0380071052100098008400380840c0c4144c09559802c150303482d22000641e1b10000354a01c41751658001841d03e0340444001046030f6007036403d424000b6880c8e842c40d00498540c45048048054210714000001d81420f201c0c02400803c0b9003620244481c1d8021001261008030900c0043d011460091070440ba650044054445441041c50441c0c41c000350401e80034103640b410344802000078000141040129940d11a401c041d00f0024820743c03402c1c0348180000d041001900010340315990352500322800307400c803004030b500465001812490a40e5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 411974253 1250 411973003 411973013
    0xa1802091825050a091a0f181e09030c0304030b100306090b1b090f0405070219050d18060203030a05072109110603010612020c013e040f0618050d 64
    0x2c618843c50780150445040031aa1030b0142c015512102801203da40e01001001d08100388240f80803041600020866004c4403502c0901c003429200305480101c540340e0407600580c0c096440001000700641d500f007440400c45010000c400c803800c59410042198050322134140181da5604150300041880d403a00440108000310140b2192181c1030089040e00c00124040a200c05480342058413079004280f40301034800792605510817900440144101c801013001d01e0584c400c01c3c1c0e20b01d0b405841036805010030388501a070003c0d0300d08059107032000a200161a11802a64902000e08400001ca40340c90001c1d104a2145c0c0124849800d5000642c1c01071100c1041d08000701841a03003039400407120030214042e4244981105d049514691b0781e541466502880e5400079046040c00c595507540700e180c9405814041c00c401c9901c2010344a182850380e88002829403840192046111030800901013041000006882c26040340d09605215181130b0000c0105082c42c005a0002c5510160000c1b1040c1884 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 411975503 1250 411974253 411974323
    0x618071d1f020c03030a0e0111011d06041401140103060c210218150301120807080a0509010305090a03090b0a02030d113004020409051006030b0a18020918 68
    0x1d0340980a9840b540030010074192a07215948400001c504042413041455124240c004c100c0c29515000107140d0003401407071800c28441400c0e1039a0ba9114009001c10301c00008410074030380100300000c21102203208010100070505110107010503a41d0800c0b0310015000d8160384400c072891410001580c0400c00b410802034000800b10008445000001c40c05c5080131109014242844241d190840c1e00c0c01104031466080c02e54120703500d010a010f100f000885100c0601041481c1d42c40b201d40710400c5a00040c120f0b84000c0454910764001e50f000c401080d00f0017a50f03801d035580303c480359070384843c4500b099240d8840c0410204600345001c1d488001d40f00c1c00b401510841000400c0e203c2d4007903d2206407103c1d2801681d441c100c0d004000082401450594000140c551054081c0d17100c00c0b151640001c02c65596500a80b5050341110410005201d944150b031101c45002c116111040c050b500498908a0001e0a41440b0941c4025400850307400700410301400007240d10f648050070b021600f00e01c041c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 411976753 1250 411975503 411975559
    0x14010c0905060301080616050f0f0306040b041b1115011202010207050a150c020a03080c1623090c040f120b0114010203092e0c05060618071d 62
    0x1880c0e200e0045018a4a44116812100c92000600c52500c800a08418a00210800205002c810480100c44141241c082c00001e81030100403522440c1040074401950321600e8924841c5180003002c2c04a51107194981e00f02d54844d2805a02c034003602001c951900903603c21043c2100c0c0c0b014000a0f007201c00f075480f00b51a5200780d0035142070a0b0344005001407146503003d04aa0506e424078662247c5100e9100003080a000030103800d2041c0c0d50b42c84101c03c2c0d0f4000780300c1c4145034206040d48145080c030118110f0040c000012020109404070b05218540030007003034400d1080001c2c0000c50a01c0001c2c2040d100500301d050359044089a80d020090609503a1070b0003142c1c44002200001201e2221034032203804040c0680240d4136001c165020401480e42690b0450409451004810050701580c82590303048610b50311a40031013001800c042c0c0c40c0500080609100b460700104d05045480c5190800742c000d10981003003084409811300460180e2420507840f80c00003002d55088414022000b880710725 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 411978003 1250 411976753 411976757
    0x21f0204050301110c0a111306060f0f0504080318040603021c03140703080f06130509030a090509010b04061409030a031e080402060306060d06050604090b120105240d14010c 76
    0x401c502203034084e0640120030704107403260054191540801c501c1c0440140c0c40d28010300e00c06c481080d000060381168001c0d080b0000141c06042407154454000c102e1403c5080e10341010b504052a00c2070560340da104254880704800d031580040780b407645031908094069513004006210180203a00409400d003012403007500041e00c80c4160102d0000113008684000d5007680e0b03800b90540c0e8a550814140001901c500e410001d20341100d9600c1030980f203054041c1d101e00004d955030300c800d90001800c5000c81c0c0c1016210328101c0004012100d0881d0882d4120f0300d01d810003465403c00f034440402c5900036009400d8050103548005010158803115090111005400c044100c1c44955012122114201d030001c5d0001c8080011484915148020f032601400042020a650b500c80c00811540d40103613220b1100c840d169860010759140c684021b510b01260040200b0080c5020b176160005181ca40003404044140c42801c0030294a0b4400e034805800e4000e960344541c0c40040090341c1c0244002945900 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 411979253 1250 411978003 411978011
    0x402010f0e0315071e0806030c04050118050903160c0303030608011415030c12030912030a020c15040306050709090b010504030812100e0711060610120903021f0204050301 75
    0x3046000d0207105044640c0a00202a03400c8455104640f0071800b8002609101e03c0c901685001c0c814021030a845080c2030341c07091601d041080502d0324007144885103500c5107050000511030213500c4694440a614035a1021456449200c0700b542144228014002518001401082402a044551401c0300d12aa6041081382c0c1d40c1c1740110700702c4440920b0408110310038408210003c03400380c45050350000003020380705040c80762000100907814000e042d124a42011030441070900c0d001c90746030004003113038014500d0160642002500d4244441080e4810081403880320b941c1c2c200381e41514041d581c040310810003410451400341000b0414815080000c0c204051781d01d15501c07038025141204e9002559604041e44003005100c041c07802059a48003600c075400005040f1040101640219215120503c103806c05045190030282d0003000135000b000e05104a841440e80b10301c4502140d4136a440028040d07120345402c80c2441c680010324020007050445804107414194000c00440700d007100208 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 411980503 1250 411979253 411979277
    0x3060d0305090a032a050d03141306020f0115030b0f1914090d09080c06030a09050a080c163b09010c02011b050702090702100510210c180e0304030b040201 68
    0x25170404000c3c02926042182524001c1c0000d01410b0031a191005000c64541080d0a07580e41101d4194280d002c03000580c0401c6900300c610078284104d0b22003000b0f4141d0460242e042d5150401c040781c0141009020051101c00508440200d8500c01c034507140ca04418040401c10b03200e2101e00c40800e4910300d2003405450040c00c115030241c5100d02c01c40d03c4c2440074140c80f4012004010340c1e03400c02402480310507219400200028401d0050741c0d0703024402d030000350f1540c008e980c0d09417918000302c0088031141c0c40107109008098581c405520701000383e2030441d440e0202c0c1c0300c0071145c46010704146182200c0b001c06200f510394040d00300042c0905164020055954901c0d40c0303032710040140000381e020540c100503010150500403c032541c044581c1c011152810424007400017266411956408229410b000074440e00745220800c0008031407100061200311419250b0826030300d405e1082c0c205d0700381800c0c440700c1640b655412059884051b481a2900e5130b0352b900f0900c0348480300300c03002ca000132101c480c14 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 411981753 1250 411980503 411980573
    0x915050402180114010e011403010b1c090312020304110301060e06040e010b0a0b090109030503120421080c091207030606030309361d07030303061202010503060d0305090a03 76
    0x681241c02c0c0c01c0540c50800400130040d1400495081101d041000039a07800820302c40c0307003000318000c01c4503442050391540301e503404203140304100c1030300c510301810300c0003401c00b10303601c11100d00c0c41182d6020016501d403160328000203441303205a40540c05500304100095000c002e0841d0030301c500c20696051040e5681d103580d603400ca405034000d0030b0f84030000101c107201000004014050069043c1000c0c560180c5070707190186180c00c02d000d509000307900d4004220401c00b14103c0703039a034520044509480c01600c05809400c00c9001001d0740d00e902408200041170382d03175214141e22200b11724415241038603140c0c1003482c090b002c580021303804120200340025840717500031800a03c1c040107001d010507003011100c0c95590801030702a5850307086c2c2c88010550416605840380c505c111711240007090103a02d0340c034024040d02c145603c01c0140c081a0710000300983d03004022260301c10004c803031102203d0400d280950301400340c124000d80018288001004100344c07450b0900003e40d02c14400d003020b488500321 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 411983003 1250 411981753 411981799
    0x11b080a090f0b0403090e010f08240f041707030305060f0d0b04030c08040504020d0b03160617220302060a0506090c0403030302090a2301030513020303070b0a0915050402 75
    0x4010b081500111228022401d00304009130440d11a19000e004260b544042c801070900a0b080041c424210035410030105500300520100100305125000303c99620213022106610014241c07446240c40000050410203040b034410b201e51505000d00b5265001400c4c01802080c045410f540111b1516080104a103407c20b035801c059940018015046e603141c0d5000c60750450100c0084070707801010b2101150542e950f001a100021828134002000001c0d002014070304240044800e80d04c00389020203001c4640c1c4400903452000300818400f946454418103d128030401e000001c100300e000b00c0440d0700f00b41c1c1c08182240038280100382405a52036000c1040311566040d6100390303803503008100801c0024003a40180450040080c4040c0140e580c40c0c064030805403030b4180414031481142c529104540e094415560010319021240c5003c3e059680170130b40c0c0f449035800141c507404840c4006040c44400741c05c030f8042d00707900459080b030b00394841c0c0500c809400241d0b8100c0c0300d501031281c00c2900590f00c140c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 411984253 1250 411983003 411983021
    0x50406080c030c13090c033509060a09090501060503100e070f0e01030e0a0507060219080406050705070b0712030518060a150302030312010503010b1905040203070e03011b080a 77
    0x1504644400c90104283d50802000da20700c3e49440e9172110003c1403400034840c1c010740c01070820303221400c0f5450746003920700043c1801200f854442c01ca01d4040711159804d5070b44c00401a541140d071030721882d03030607204402258001300e60700d4108800407074102c0d84880910b0065502c9908110301c0c40d103070030b82c1a814043c1140d0b14000204120281010284118440656841d041c100000e400c0b03181881c00341802d4010b10141c6443c4c1c4056400c010480c0e040060000030281455600801e245596419070f042c441c501c02c04080000202d00c00c03003400010b0024100600e00c14030b28030750350706107131400c0210040440d00b014082850f000024082030300d5491030954940307030030018146035a224080c080042440e900d00710001d2100070700c04001a01d0402c010000300e6144038004000398584400c1500b07403000c000080e8050704410340b001201400d413446c0401031301c6041390050f869644040c0225117110285507000d07410360a00b1070142c50400c0d038804400c0e0200304c5503601445982c1301000a004e03210010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 411985503 1250 411984253 411984259
    0x613091a010f17060d060e010902010801120f0f03020c03060106030e070509040b06041d030a051e0a09061b06180309060503010f180b03030406090f0e0c120925050406080c 75
    0xc0d00c0c0d40a00c035031a02c590350344581c1c0289940e18207500da444020491f0b5810701c5880c1c0c02d81d0f40381004c006660300110b4840c01030a44800c07104095415590f006801203141c070b001003c81c3e00703030243e4000b090300a200f01c440d4800040d040702c5080d0303543c0c10b004015040c40680e0000c030f8020445c1c0801e0034108a214184a160405a0004191201310a203c000c010b81a00380e95a0351107401c444407000f00602c0240700c100f00a540d1161943c11f03807008240310484200303910f000307540d041000b01c0741c2c5500200c002e0220b5642d4106004121142c410b0a0040034004600400e50340c5031500c51540c900b4580b0760901d009000750307100461192030f110165800d10081c0902c5031002d14007041008500c0b180d20100c24141c01004000c0707001d014a00120786182c00680044020440111090251002000584000700000a003d0500b41010b00304200244110f8600100ca4415a000140051010408031000301580d00380303400795100220a107018035119004083c03003036040080002b0300c4200010310909500c001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 411986753 1250 411985503 411985517
    0x80f060604030f030306150509030606030105150904051c080405011803091403030919030b13080703271509080a05060a23070e091617060613091a010f 66
    0x56100d0f490600c103000801c07010503403a40d1000c203d0310001050030b9540f00c41e030f46038242c0761034000d010076003059001400240640c1c5084100300e254021300302d080c0030b80e042c1513035507510b992500c1c202103041c0201c08441204040340300045040309a441642c49104900a000800410099040c01072884041030f40280024401010500500205543c100b2010900030101c910781101c4c07401042803510003610144110f4034100042050001e84903940341e200c003651260040c031048079079824101d8050714030040c0c10040e0440e03042d03202d500c2007008009010103040480042a6585250000103013034601c401c0b000901c0100000f9020000240200c4c2140e80074015110701ea45187d015070013401d414a021026090309411041d0403009105035501800305031b80d0b680000c04d01d40c0c044c440d1060001d0903901c07030a00301917443c1c2c4030b80340e0004c6c1070040303400203003c4c0400644500b0b002804030302071010b0780c854102010304009520078140d88400c01604040307c4501e0010120401500e250014144a5000c5060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 411988003 1250 411986753 411986759
    0xe070f030515270907030b0708190c0e0303280918020f13080303091e0c0d0819020106030c0f0b0a0302071718010e0906060406050f04080a030c03080f060604 69
    0x1000012051100c20480c204440c0504500c141c20319a0050313419031496040050f00303001340211403000c540c1c44a901c0c00e000300c075814144c600e84082d0111107200c50007144d4840114201e86e21442408040d80c2d07004044a480c3c072210440c8885082500f030301801a0305511204450b090700a0380340c44121241351040010314004261039102079070102d01c118103405010403580c0c03080c0c8805501ca8000d0101040255100d03c0e050145070310b04030308110a0416003d1400704640703072213000511030024810503102c5e000680702500e48501d05006e0101401c1880c9014002c0f0524968158842c3c0c044a002d0448290740c0b603a600d41b0602c0103015805600da640d403041000b0b11807a8007070f8009082c824402c202960442d00030602d10070710341d08090041e00000e000c030f4034518810f40c5c2c0004681c2c42c0c94000c59508240e0b0a100002503460301c15441031006000e00494400401c3e0705003010341e03004102007410754240301a030740340040c01c00c1e04103a021804035000102140714580403045044c03295002818142c50b20741 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 411989253 1250 411988003 411988009
    0x1002071211030703021801060909020f0406051e0d02090a05041103060907020f0a03031b03060f060c030507020a0308090102060702030c15041b080c040b01020f10050402130203010e070f030515 84
    0x16550001c0d050f110340c00740000162910707400b031441e2891019030a641e950420310002c02d50700c803a50207c840140140442048600310380200d40464095040c500e5607102981254040d03400d80c00e1144081c620b003c5600c2d8220103944d001800c468a0807110700c1c1a00d5100c60070041200e15a14031b0310940d20040c00021841d0900b00081504500280111a5010a48d405842c6000d12600d801c5001a85603150591000804105070000c40304c142001d00100381020720380310621040b8440c40e0208030201c801e0038141809042250302154019251130300b072940301e00780100c25520a00360a0f0040c810300700003070310b01440481a200b200384848041c0540a49840c98a001d03083c1c0a070098904101280720b0428070700c40700f62110000d2450b00c01a200d1110b032103007044112030b480440c090554002c0485c650f201200030410104012203584005126141c600108002c0c000c04a01d03076400321310020004c116802c2420303d51340704961070b035205508000180d004a080d03c41c15228056240301070041c10901749 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 411990503 1250 411989253 411989273
    0x31611010c05100b0a05010f0f03020a1b060c021501030c03060903030b030f0106030311030703140a1106040804051e090a1d07030b090f01060b0301120305070b1510020712 75
    0x824149401e401d00152510303402e080c11600e0700303079907007165485400b50710702e0404203220343c020802400c0a201500e403109014100519401903901015400118040210701640c03260b035600400c802c1e09182d040007854800001c08402040c10003510032031900c46246c811229980341a60340c0000c04001e01031841d5901c501505c03010104030240764403101c80d00c25a840420403043e0b80c0c9802c03000420300c00e10754100903080b0801c0c0c410300b01c215041009003a0202e80c004055261820032030f030ba520b50700c91010302d0417101005000440001c50040c1c00501c0140304109018105464044400e00d0102d84a1495030f08010140c01c2100d4011082200007024038440c0e0f4026803038100ea5031481c407074895200c3d8082d810401030350801c446006807603003400300e0000c0401c82208000503600c02009464204440030f0080c2c04144a4070819403e46900c030003c05100d00e040d1849580d02400344841d40c02c0c08903245044c6404040180c1c060118881c0e05a10780e413002031000100c441401910300d410010342c482d61441 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 411991753 1250 411990503 411990533
    0x50d0222090b39120903040b0318070b1603080411090c18040608070314010f021216080103030906120e03070506090d090302030c06220801020c0f0316 66
    0x501e948040980229400c03a085038810a100180b0b07188004a0583c0348242000d40101c11048402c00c82070700484148042c01c4801840c062040400c042d6102d080291851246800001c0c00d9040802445100c01c1d8115489200c0c2c0020816500c01a444030203640140c022041100079028140d099103010a0041c4007080d000360150034041e00105182e40402c184160a4400f00102c03100007a041d02003058141c03564450240c121402d2001038074142c0c90a687d107850780000741050007003030a680c0200e182544401260104c5020070354172032100d00c03080b0103901c404035081d4200782f5681c2c0c50107a10a1151350200d0680764107489580b915400c000f0122680c0b800c1040d18400f5030b0359030906201c030500400c003510450b4815002800e40c0c1c070300602e01e00c0c02c2620940c6001d0038409060001e02c01a0380c04603140c1c83d202e009441150b101c00c68640c0006407141c000851400c000614035000c140500107400422202d916202110106080420b08940c0c0303116a035040c00c0c100303078042440310001d16420794070350314 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 411993003 1250 411991753 411991819
    0x2030c060a0e25081b0904060b0d0614010e1f06050c010e06010308071e080306090c09040c0207080714030a15020f04140414091c030e030406050d0501050d02 69
    0xc42c56007561003c3c2c1c18200402c898510b141002c40402007070f2020021180038480e101e20040b00c186002c0302241d4407a1002d0b10082c04a41c0343d103c0010141c844011006141d0341124007480b03485100b4003a0084141e080c052000320002000c000fa281c04131684200b000784011410902d4810320b4014112910741041c40a103003955200d40070000c030950304010b0030b40614000d005842d40c80c1c626103012801d0391207047c8400e02c079403400c04e501ca001c2a040c50907a40d2180c1d05a45a000c20758503114a41040d2140d40c17000780d80039207860800400701d5400034105060b02e050f081100d001e2900da0b07040000305409040c0b16a07065000380300007000103402d004446040c5029810160070842d01c0001c1840b03036006a0131030b003401784c40580003041c0d0789407a028541283c142031000c910b03503062030310005403250420380898581d00442c861150540d07204e41d0040071040d40000c1565250754880310010410760144003581c0c44c07281450000300d20303443d0040c06000255402402c140814608050303000ca0905042d68441c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 411994253 1250 411993003 411993013
    0x106121505091011220e04260301031a09010510050d0204060e01060831200901170606030d091a0c06070c150603030e0609030a0f03030603020a0602030c060a0e 70
    0x243ca5640e0060440c0420100d142d19203c6151541603002916241c06000601c00ca41804010280070030b03006a4025401001941030b0518604220b10742000100c042e81201e5000000002440301600111041e00058580d010141d262100c0e00d03420380340306581d1005400e0038a03404004500c1e00b010016505840a40003284031035a664001c078800100360b100c0030200364003a08100d07044122507280380e46400144142240b5603144074500c090070380c00304401000ca50692140702c010f10b00c01e10a42102d40b10080017072110b9a1200b49154080845040c0b540d01c030300c602c10100c0e2403894049504402c03508596190300010313203000028070721100c840c5510788802c4070400c8150030070318043c81480c0c49a030480c1c403080101c03c0c003031910704000e00107807009030300c8035151500600000383d1220700032502190803110701ea00c601c0d480d80020308107041602c00921461100007440105034158003d9401c0b42d001701d82441c1a40d80e144c00603607e85c40b40c41100020f030f03006400007a40500b80380d40f0844801c280f08080321 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 411995503 1250 411994253 411994273
    0xc0302010f0e0a050d0f022d010903020d090801060b090d030c06091a011d06060a050d24050102071404090f080c011a010f0207030b1b12040302010612150509 69
    0x20102e54081501c58260f800c1079805605200003005500e0400e2a6440e1174070712603c080304004d4450010554021210381080342e40303096600310103c058110328100008000520161802035942d520700c40000f004508411000204a2810f00c01c1c0303012940103100da24500b61750f40e010070a09040c6030304114140031a9403648008540c04c1d100b64041284250a440301c43c01030300ca0440a4602d0580c0b20900444032000c4490300ca8501d00c02a50f00a60145c80c81d54981c010301c44240c0380d0340600c000d88141c1900c1c10b8000c08480c0b04100d000c0020700c0d80c01181c1c00d00603444100491311205c26009001109041d0081500d15007080d0f440f0032100e0780144200b1001d0303081c665480703a69903c4202078020300d030744906540f40581150040c0c0541340c1424203102002c0f01c00a81c019488079034612000c0d042000f01c10000c0c1c280c031500e0303944c0c074034000810000565420544440d600da000e03003550300350010740c603086001c201501d0741e49040d41019004034042c0e90505a601158003d400010302170016802450011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 411996753 1250 411995503 411995531
    0xb06070c0e0402150304030e010c0c080f0606190803120c0702060d0f0b0319081c11120105011b1509050f280f080c010b180a051b0a0c030201 62
    0x210340908054940100709050500412420450340c003880e450119003003041c000041d8200c504034a0135142800c103481c9440090902e04c1480400d03038440b110500400400c0030507001c02003151446010100d81c6070500c0440001c003103507040c88500a9020581c400c2000400120108800c0c6170700c1000c040510346800260b60114074203420030400b1441c07068070707410100342401d0240641910071500b074000300301c01c41460804156001c208100905800000207010700e04808903201440c0c003074045d22085c0710201c1c5007031030300d170300da82c4031520002c1000e203d00e002103495071041e0380002c11401001034030203964086454603801c6040c16543c0d5012542e0310074035080020001d00c28840c80d0000382005d89510303c0710641e5000c4010400b03803003542a500b000c0c030070000105642840703014a80c00c400203648440152445070700605050350215405085040d00324414001d00424921404000c0d000340704640f9140716684e90034008040182d01c0381c40901c02c0c0c0b90002d10401c810080079020388004107283c83c10880d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 411998003 1250 411996753 411996773
    0xc090f080a081606020c0129030f0606040c030b120705030601060504050108070e0102160f080f01020717070219030b07110109030906030203070207050a0305060105100206040c050405061f181202010503010302040b0607 95
    0x15a4000c4000c8c0131036805e0340745843c100b001094044c0d024202c200c2c440220079880d804014002c511036566540d8280b200d81c0310341c2c8954000b00300548504e40740155040a10794a030340c180704280c072038440c800000c10103901c1901030314219107040e12824030b2900c0740c803002c5d160484800300042c110310a8103d00c01110ba6001c248100400b803800540c6407150070f10281c103041011050000c0000d0f8010441000002c403110400c2c6040c07604494001d484400c01c1c070026820205082e034003074051009400210a01c800084100d007d001107464035011060101300c80b60036180211005804290b141104201c6075002e03030001e503484a014415243c2103501d13900020300303c0219410545407940064010b103d00e052142880d100100c8070b0004017440d15065880b13000c042414080c0601607925000408c1c4aa294074100c0c1e002079460000c0624440070680c03005042003042420454490301d500350000e045014448030002c581d4040c0d645501e036030b09507001c0c40041c0185d40c82860700280100460700101c0c02e4084 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 411999253 1250 411998003 411998021
    0x7030809180f012303070b0c011d0c0405070f1b140703050a02040b010302120c0d060b0705030a0801060912030809030405190e010b09100f120c090f080a081606020c01 73
    0x182c107401c507504000d025907481451451103c07802800b80c00d8001140d40005604080b19086000141e407400c05941407405010303000040c450f0a002003866440080f00400c2081180b5001d890800296032911400c4440e030071511403900200300020243e50790070701e01c00a400034240c024110952074050b041003c0785017511030f6006550720703080b00444800314603050040d40038100007481c09600b4080119000d0451a0340904a5240d0550014100c0008001b503003001c0000c100d484180780d11020315003805500c0b075014200b4000025032840010a08c140a407154005035908924144e20010840c1d4043d40e0720040039000e04e2080c0f200307000c0040c0503590b14410000800010b003001182c0da10b400500c0d00c1d05031040c1c0010041100621840d00d8940300e00c61030b03150800c613910309000700140c1031409075026041005074204003030600c0e000d1003149401c031101c0c80845100c12080c1004950721a8100d84440c00140002d05140c0308000744404940d070700d4410107481d030080c10010324094500b4001804c64070351170 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 412000503 1250 411999253 411999271
    0x2180a17060108060f160c0203030a0905031005040503030a02091f090806092404020f130204181a10091508010509060f0109030206180306131704080703080918 70
    0x500c844540d59420320030309004020300300013030a442c2407071100448203800082c4070300940c0341c90072504d41145e0300c00e000f46880c0580103001e0300d90f00e001c1d01c0e01c002c004841e00e005140c068402c0087c00010b4001900c1078620030b9800c00055030864030766a100c81c1c0039500c061081070380180140c1c50402c0f8400c0005a00020b2615511440303842442c04001a00b8400c00602c50b5000b03800110100030090001e204400703c01c2816440f01c013080d40c40e48005510241440e1304190080008080c90024150941c001c0c026034054002d10031001d10744000c80740584611b03280c0086081a00c80001403241170601c11071180d82800c2c20003c0c031a5403220b0304070a00c0210b20f100680010f40010041015082840207250810b0342907945111004000c400a841200240300090007200009420803000c0d01d400d001e1512030b0401401d80304a400c1043c0100d4000d40e07861000e480c80303407000d03100c5038402d41140708032411030b5100e2000d001841d1960312507111a402c54210250003049402c0c800c00100c40c00c00c8020320a01543d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 412001753 1250 412000503 412000529
    0xa1e0f0e0a0e12090904030512041b051e06070804030b04060b100504060f081b21010b12040308090a0c0611210d0906020c0604031205091c0302180a 65
    0x70a00d5001030b81c50684040d00c0c2d40e0040341a15401c84040030483c0c09060003510f4540181c2c54610b0211181d1107140303034085d04000740d90240410807842e07604c446181010f424201d0079640d26401004824400c0c02c40061441c0301c4010000f0380c50801d4009410041d00640b5020b0626603662145440d1640c126001c41d00705a41d14100f130303800d07d841042e400d01201e44ac94428101410000050a85030314083d1880500460200282900300511504800e000300b00e1411900d071540c05421000c1407480002c0000d0b0041e00400103e11404500d06454103445440d114144580701c98030103545401001e0001d160074000e92204002003010241a0350007403860b9607400313941401a54580f803d100c02c92203400d040b01e001c90740025000150000b940e4984101c1540026409450b15185000b881900c4010074503015180410060640142d420451b134041e5110038007244d030360b80c0079a41e2501c14004801c400b44490007200d00600e842070b80607010091581045030550b0076440c0000700d40002c1d0f6449a40a8400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 412003003 1250 412001753 412001761
    0xc09030614070c0206031026010e03070c0509070212040b0a030507030506030c0424030c060f02281a1005010e04020c0604020121020c1b030604020a1e0f0e 68
    0xa00d114450307031000da00300708a010b03081551004000819a8a0280c884c402c04000300d00280b1000002000411801c86040c803c0c2c501d01c009500c0d0b00c06a100d41c014154a0308010619a403c00305c201c5d080e02ea40028003071004c070704040030401c07895400340500c0c04511034882d0002c500700280c8005e202425001240503200c0b81030400c020300780c4d64000c109208240c02c0206000311505c00080c1440c11807422200410040c6d0042c9005024070101c0b48142802d40704190f0000a101ca44140e820650300785a942d1300b15400c1044060b0781e41c002011904030010030400b5500d02c682404c802140190740300781e00401c0340f101c50842d950703002c41040c1c9503680c000184c40c0c8100915070b009210320401d920140c4080d400d01001c008d500f034940d90014806411f00a03a203ca604007920003041c0d0707042c0791803d880115140d031101040c1c2035440b680340c41c00c2200807a103081260340d0382c58009500c43c400c5500500110380141003c40200030340c8c9909005d010240001c04c1c000c41e8190036035400d5005010441c0a048507450 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 412004253 1250 412003003 412003013
    0x51b031804270b09190602030601020c0307030305040e06040b040c030501051026060117010807031a091b030c0d080d11040302060304060506010228050f0105011401030e100c0903 78
    0x10a1074042c80c90340510420200c2c1c842504401220340d036040b0203c044a903a07080d0780c040c10407030704000704034201c10f40040440403c2039642c0a10f01410382a4215841e8015030424180ea1b2501404082c000c032310148010484540035040440e48160701600120760b0401071030200d000c3da000400a240441e48400061001d81030160380b0100b001294a00900c05c40038051801054002a10201e10709510760000191581d000f40c5038505241c1d800c8500030142e6039620541c0762520403501044841e08103c000d444942e20203405400d0055001002800d149000300c90954074084501c0006a054050b09880c400c1c21303500d0301020320b10a8011b4400d50b80c1c65103200b1000303084400128030110716a9003408140056103c203010303030394410b52180340013540c0e44a91006030f20f00b040361840d8069200c2540810380300310307204020210300c852140b02291101a103600c0c90f64240e4209003e20041c484182e0b01c0c010240d803281e0014030301e0171191410358002e040760308201d1090350b2401e01c03d200840e06400c02082009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 412005503 1250 412004253 412004261
    0x180a0c0201060b040b0d060302181603050408190207231212041e03020402040303030209010e04050906070c0807082b09050703020423191a0a030201051b031804 70
    0x805603200030031925003069042c4100340254004c00a90f20400725500c0d0300b0306103540c00b403000b0716001444a450715100c40c1c1c1c403035885c40045070a605108807201c2d40c2c12209019000301030007203511800306030400b0070b01c524240c2203d00b0040b080d801c501c9950000586040c0183d04400203014a18604080c11103420900688081c5500d41c0440ea40c0101814511a07070803c05450540d01c403000c08069409100c5003428000c08581c002961241c40000c1c004205a01540207101c6044207890303c030701d401c401100300b100b03d034030403666a14a50000700003d40154410800084010f10450702d46042005c551500a41c0e034011542c012034494150140c041813140858034454014060901071169103071907900c03103851380c0755480024000ca464500c20f03841403002c0103800110140a0750003143c2032030030030320942c201c40d4001d021030005840e00d1041180b1007002d000c548200b07180508a94100c1d0325503401110564082c0e152401d0302012042005444c48c0b040c001004001c410209800f241400b1100b04411a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 412006753 1250 412005503 412005521
    0x621090d090b0f130315020306040515090406020c1518060f2e030f061d01020406090308070c120c0303020d0f020d121112010305010e01050106050d020a0905180a 71
    0x111000c0c5a040142c600103000700e541d03440140b4100c94654400203240c2202440a4100070035243c040b5904001005883d4099880382d101120180300d40c1c0c954070803200381106010081600b24bd900c1000030081102c0b500201890072000c000c45406008a0302070f41c60f048420740c3d28601800d6480d44d4290303521400c01286410000600724101d450603c9412588a00604200403210001c42c101c210311500524250a0055070440740b425910718943c50014010a1a203402c42c0c0d00011955402c455180144240d5099401e19228a2101819900c403000d1342d400a1200711050480000003007414207003150503041d440d209d803910842407030a628010b07040c104600500010403044130039402e074a690001d101b89080d4014100f543c001e000006480006d0469115502801600040d02c01c2c0502180fa6126048a02440007000395458120032182a40c0b428030552000480c140051807106502d540108000f07002d90411a003900da480020030a6210090070200c4049504010420014003038003411901c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 412008003 1250 412006753 412006757
    0x7020301050c2713050403021c1805040b0f060c0604031202030601090b03060103270c08071a0c03041a1c0b0a091509020c010207150612110621090d 65
    0x1803058241c02c5442901560120000c000c4814402688980b07951030710044101c014413042c0100d20345401d0207940d8030b8900e080c2142d2020002e031903c140728485d0b501c10074031440ca2014401010314090421000e4200d0004140d4000507500c040b9040740c0e103507401841e2414200020700700c0d500d01401c02400d14104000340b4541c45004104000c4c03e82c3e84402d090050b2148821050380701d8940c40d0040b0300400d03085e03124040a4040240e10350540c6046441c100c2d0355841005500e00003525081a41e0322203006200340c5142d01041c80740f030240b010707181010300480c0c00600100d90500b07544100c00c1ca040d10003401118411440010f52040010603611040420742c0115418003500a039980800c0c500d58a87c81141d03800c2c0da81d00502040c8101c80350809004200b034600940d00c0d200c2e80f114a5000b50b00200c41240c05082e45c65003030300040080d014000c11125090321407080c0d00015211501c89100500b038050b4825410807406030031500c2c4800100808069926100039460070040061501680c40d41c1402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 412009253 1250 412008003 412008007
    0x15070212090d060509010906060e010f0b0f041703120c04030606090504110103050601112506020708030301050112140406061505040503120a030b1c05070509060609040908090a03060207020301050c 86
    0x2158480080300c805081d0701c0b038000600b5940d17107171240340100140c05d0000c0002d07042010010b080c4000c172602030305803075070700324194641513035a403900b042d92240104e121103048080c4005c00c400041091007451001c55182601c2c6840c4c00d26450203000003044070703070054840001c04c05200340402d40c865000900916101008582000d8072003c07071a035200c4204a040540340c0c000aa81d42e4400c3d1620340700c0c00640002c458600c007168040400301c07845e544041c3c060759461000040c03042d2000803a1811a00c1c030902940c5035900700401114140200614901e1940e1110301c5401c507001c100d070020b03115502480000426500780310039a8601c03184805040200a400c0c0700a00c07842e41e01003038102c0f44143c08010140d8800f0b00d0300301a0302500f00d00007120707400b0034a5180d02ea035402d03207280001d0003a0700c0380060780c0030240c07598208034042c441505e449801070418840025a41007503442400858002c0b900d1038200404000000c01e03c000c1c94004a2300250046054030841c1000d00038980c0010300c5503803480c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 412010503 1250 412009253 412009267
    0x3010603050c04120b0c0f0d020301030b0603060103030f0e010c0b0703050405070f0807090e01060f03030234060f030f0608150c0301061403040303020c1b01020d0918020a1115070212 80
    0x981e07134001c2400050644146007011640b80300c43d4100301d908494003403c3c4e05071204044c0c4122070080d00b00744819100c40505d100040c13110310380407940714103032549034480c082c2c6904105000c03991501510000c906200c82d545001e40441d21201425204440c1580c002c12a86041d14003036003802c50691049051604000e0705010040d400301d14a000d0b0f400d042c00000d80c00e40281c2080340235061030780c402070245040300404801d01d0350208101c040b80311613000c0d16464145015000f0704108184120308501d2007440e109201c120b1140019003980601803502080201060002208498250344070b40010342c0459500c50a01d100340810507400030700940d02c0340c119803401c1c101508030300d0442a5525042000030000d400c06000b5030554880a050000b140c020300d6503402d00402200114294030b002d842108107600e0458410f0114405a03540280841c102601d4110120081d400040001080c080a54801c41c00d0200c200710340c0841c543c1d042c1040403d8184404068145000103007100745001c4104004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 412011753 1250 412010503 412010519
    0x2405041101030e0d05090301110304062c030906030c090916023901180323010209100f0c050a0501020301090b010c0c0b0306060409090f0213090f0219031703010603050c04 75
    0x100706800103170625a5030b4540c0720700003a00402c04c04050150740e000100a000a200e40c40d80304018050602c1784148820700e05030202c42c2c40c1014644a241968010000c41c0e0003402e000700550b80143c4070255060030030383c040b0001100020122000380d25860745186800340d1681c104500d0100c0000340400609480e07824405940380c251542c4e0450a02c0d07256a41c180290740310b440f51407070800000c0040c0c40801e4880c07818421524034100f030f2404803c00354081c440c0300c3c0418400c030340649078001c14034200c0da01012019158560307110b01e200700340424443d10f540803e0060140d808440e21520006070707a9818001c200007100d5041c90020704202d049502e8a000450810020003035132032080b01140c903a5141c8000034070034429a0841700f010f60400b106030b0100301d40444854280c0340300721404034603039401070100310403611100c0011302120300e039511403005424104c074401d0000f400844107020305507c0741c4130750094412490030205c0c4c16000000411445905100b0304c2d40180c100400146024903090707031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 412013003 1250 412011753 412011763
    0x81f0608010b070f0803011e1a1219020408010912030c0207120507050a06050d050a3303080c070801050708061f02010b0a080c0f0415060503042405041101030e 70
    0x40c9020890002420f0000e200442010301919940300804580d21b60711100442d50002d0061500310140c00c00030804a01c0d0342018905001004203590034500345117181000c000c00800150042d40c8125004010024244990000b0310203084180300200b0200280e01c1e243d0000300c4076003000c8040500c1d00031100250383d4041205d804490b001144403107060344a00b4641c0c18120150b100943c0240d41c0c680000f80c0301c0d0010060480c01c80e140100b04a596250048401035402da80a0000e850358000c3d0058642108000d2030240c10205241c074007503080d01da5869100c540c3c44604403044a03030000200b084019000d00689a12058514003881142898400310f101c0c0c1c945c0303903914501d948000424540c1c06100354441d82880b100106001061691032480c0f540750400c006a45000e069101e503842c4160411380503800011954554013400d007854010220313006c0c1c0000e4400c03103c00080d008a031890910140c4000c240034800c11300000c8908092500306107a10454640a040c141403105c4001c0702280464 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 412014253 1250 412013003 412013009
    0x901030c12110901060e010816020601090c1107090b09090c010c080702010c1a0108010f050115030b011407060b0109060e09061207030c08060601020106060203040e161b03081f060801 80
    0x241d90818100381c500361482400c03030325100350018600000020060303800b13524114940401c0c3c9a00b1120345405590f5403c410340c5890550140c0c1c410801082821415404000c140d10545072080400c0800c207100ca0401c0195440704500390780b1080142510319203140440d42111f1007030000c1517000c0c0d442001800c0480781c060007174829800441c0e1503055900516040850b20307442041042e032a040c10342054601202806000200d6207004000346250b4417902c0790906860041001e40401503090f10128003034800c850580303042011340460451034054245c041c20704203208003000300e1048911000101180300d00d5105408229034828840c0450f16107505803900607201740c81c109103113591058501e1030301100341d00042501c0d05c07508000500a4010500c107004040990003844419036514007266a1b00850082c0a054010240411120000c58002d02000c11032400c019018850041c50b03401d6801c8171030380503004903146008100300000f07000c3c2c11060304107a00120090300d83c03c002c002001244140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 412015503 1250 412014253 412014269
    0x906030203040f0f12030506030c0102120304030e1009031205090612040303180302030405041d0601060806010c080c03070308100b040308090d12170f0f0a0207030c0501050c040e060901030c 83
    0xc01c00303010307802c000c01c10f0b559003001c1c0100f403050203850440b2800c02c20a00329400a407822010030340614010038403036040e0605034000c1c00d01c9014004040c490ba070000c0c008606000c0344180030a200d8903041021010309001340c50f1407516070b203035061a00100c8080c2d09a03c00700103040101d590f1a80c4c4031404d0342c800e02c40f10804880141e54030318040d4014062030661141c01c110f10034204003003550001c005c00c1618000e541c00d00c01c414546240e1005404006400c9866030402001400020301c03450035550b00041c14034002140000c5070b203407050103900c040980459608006411002c0c107800030f1040750404504601c0940c0e8501d040030b000342d01c0c02035020040c491040002c3c050b4441d81ca4181c40a605600003e096103041c80d11800a003500c12481c0900a405180c02c0000314501d0707001007110300c1055282420481075450310044002540400310850510180b03c9850002c15403d205151140600303407070301c959070741c100750f00c136843c480000b0a2544a420580014000680201c001404680042c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 412016753 1250 412015503 412015507
    0x5010f0b0d1d100914070303080c2104080d0507020a111504091803110604030e3106080c0316030b070c0b0c0909071d1504090e0703111009060302 64
    0x111074040b0340500141940c038103106940c407000f4407403029401244240d108010b100d0805803944051a1031300d015110183c0401c80c458002070310320300410010401e10b28001404245d02d28221504c8065a800341c4003594030300c8020a81c9501d8040d544035194100001d0300081a0040c2180d484240f04520010240d021b48400c0c220380034840440c10640e80030341007820040c00514016141c1c0031280006d240203400140072500b94400c1b4005c08500d13a030160750155036001d011340041d824405030458008400d201541903c58444400c1d600c1c202c4600c4210b68401c0101d41c4c1031415080318035203440ca01105101c0c0c1c10800400840000c800310240480c1d9202210720b40ea03030f46030f00c41a900c0c04000742024142d240c12104008030641c0c080c0080c41c0c40c83c004c0310019160b0700c4455046072855000f0032401281d51180411a42d2481c10b46a010142c0d0301246000c0d16040d151131038501076030340c200782d0040280d0004070309000b00b00d269400c00c4403200060380d40c04014408000c00511030002403180006250740 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 412018003 1250 412016753 412016771
    0x90906100302150d0513060b010f05030a090c33020c01020307060b03030c0708062703090d21020604110105070309150507060507082e170a0b041505010f0b0d 69
    0x10602a10500c0c580641c003000b043c071b000070406401e0311300c0520803500f0034907141500100358001c2c0111803001c152990b40c203045664800c1400000c1501400071b6482c1060030300d0005280107407601891000001c5013800d50415030503000390981c1e000584001080d0342041c010f00a050341c1c00026a0921078001d039000c1005505c00c8007180c21807041403503140290140040118510f54000382e00c9010388858803403100c085190703140d120042c1c00307441001c00c166003040115807610316102d52841015400389001c0340c4074000c3c0710b1804000c16107400d100c1b000340e04000300304014447c00518100380c0780d8080c2029494080541d03001441c02ca001d000f201c034114602c0200000841c403c405450202d548900700b0001c80c10300316005000b090080f80c030100f482178602844000040409461007003204600312800e070b66800c01d0b41c00c10b0300d01042d01c000b40c69440380c0111030b000f08800c82c1180340114000c0020003945051040f00c0420382c1c0c3c058229000301c00d12000200310280c0184100da001403c19440040c2c9588 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 412019253 1250 412018003 412018039
    0xc090303070f111504080c040b0d12030605120c151602150c0d09080607031a0f060f04090b10020303010303020a020d1a070909060914070e030307080403050606090906100302 76
    0x89101c44180c1101c01141c0040404d14080010800e807400c1200310b0340400c075024100001c1d141312500517034102e03201d9a81c45000131310f02001c0065071724141c02d02080341c079211000304002003401e103215401944020b241c482141400c00894a540740c40400c42c620b007060110700c083c00380c121290002d00a036194116842d1004115003a54441d480300826101a4940400300500c8280d8034024484070b0700401011540290280c4158943c0c5011202c80300e1102c2c0c421810003001c82282e89a00344c01a004008194070360300100c009001074400a00006051200704003070082030700c410304545040d54010801480802d8002441409860f411a24603010700031519000356100007114004d4080300b110300900c0841504518a001030359190f900030401c8696511704102580c4030014000a045c0400000c00d41d441c0c0b04401e400503282d00501224985806a568414281d000e680706031100d80000040c41611b2070801c1038182c20100d648000c0c04c071170030580300708000351007030b8400288140c20f0694406d078040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 412020503 1250 412019253 412019273
    0x30c07030903170703030e03030906190209060c030304050c0a0b030c0708092d0d2001140d0f0609020c100e0705041e05090303010e0412020106051302120c090303070f 73
    0x2d0342c0000440319020844481c2c0c44640c102c14400c80100b42800da0b415100c420000580340f040c11a00000d20840d01c40c00c60311040c050b8600c48404c0103503002c0108240c591100c8000f00288120107000799503d2510342403250030b01c419000c401344205141c4104020301114030b4141c0b60880c4581c80034543c2c034007061400342ca03a0b02c078804680380c0051205840101c1000480064035000b07400700070b0056080d0320710f810071030f49842d507134801081a00684101c0c410145100500342c0050b17818180007440042d00350150070650840080012005e13154150030141050500400000307010149095060030607181d03982c2e031122000260109800d41c0d6104100c0001d0080100340c004081c01380c400c000c00503e050014055003548078a2160340381c02c0001103413425000104590484610038040b29003a140d940e45c42e00c1007000c80f941030b42159200c040c0404c0756034603c20031030a0a01050030050760799401000350303251a00010a400203c400074040c00e10b254802008407120a613014004030810100c4e0714101c0186 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 412021753 1250 412020503 412020509
    0x30507080d0c06020d2a120c05071704050301110d0b060403030f121e0c14040e2d010b0301080d020d0210020912010614180411090403021005070230030c070309 70
    0x11b00310a0000d02e1442da5040080d6464200341e5480301c410b03160302c10380f03a41560408510744c80021001c010142c04611042a040000c01100e0b2200386003640e6040081d081d900300410a41014600081c882d0743c400300340c4188990104252009400c10b8030310388001d400d80c00000842001c2c0600d0700c50400410005a0003052400100b07080300d200100700900410003045c0006d6010301090b0802c48070038240c4100815101100e4030083d0121b41c81d500d00501c81222036480c1e0412800d101e91000d034907040311258840354082c016100b60b0540f40d601d840b034200d107481140041d900075500101c1040103401da01290700d801d071008440026179070b041c200c00442c0c500941014105501d518207040403a003030300081182d02daa0b0741d007291b4400001001c0c1900040101d4182c030002c3c04101d007036900000c0e030f0400003581da5101e40240140d950b8070701561704420550324102c440300300681040b0300792141102d02e8017441c0c05504d05900d0464000442c03001590044c4809800ca2412070300c0460341e07504140c4a0084070340a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 412023003 1250 412021753 412021781
    0x240a0b010201180b06011202030f0c0702010239041509020a050903030d0c110f0a0f02040b040c110106060f0219050c180108070b09011b140f0601030507080d0c06020d 73
    0x90f50120f41425114040c041e02c01c01d00085143c0c0b10603a611101e8002d0f28003a50b4801d114003803d8640540b941c413680c7c4075031022410360240d61b0b66801c650b0308290030428180c1300c00e034042c45042c00400301104001a410980e5204a14040b10302c0c0c00030810303241290540340504401669425a5030b0b00362458064031007000e0b4980300005a800c2031442c00d030000070b601c1c0005e803911400d0180c4558540d03100d03280d03080e2800055005401e0180801c21010217030b1082d078009400001c4034122080410103517110540001c001c02d00502d041d4400307040911501c0700a002c40e1502154032440c01e04029241c039007402502004003111201007003844005d00440a424000a01100e10548002c5a007202c0882c2480741c2c880c3c034042c00e48001210000c10048440c03005059540f0140002c2c2d841d44440301c41924403042e070300c5901c0082ca44040704000c200c400c201d00482d9000785820b41c503620300342d40307031120030b420004d216000300003160401500016110009a441a80581c56005100310760004201709a52060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 412024253 1250 412023003 412023041
    0x603030c010608010b1f021c03140a1409071208031f06120b010206190e0a1e060506031209280f15020a030801140105071a0702240a0b010201 62
    0x5107141e055000314004003055846c94182c0030010800d01e02180206401c001503001414039521b900140c2180d24568492401c0005856407200c0351001d9182003200c1c0d100003a562458403a503409003404042d41d1003d06003006100703050402040401a403104c0000400480010000c9100c010100b5a0945030f01c1020a01302c8071a95a004020800f4000d4203900304450f02c1c00300b0701e8105500c0070418134072482c2e81d00c29050100840d100c440780284619038103a04e45004414044001880d016647c0f1040344200101d003a0540380d90400c44216680580307018403d52101041c0c60301130300000203807581110111400010207141d202d441e441c003c54064141c1c800c854028001c0b8180408400769029119a2505000c0007a5003807000d80c2d44080044015002c1000040104804074803030f40400300850040c58010b04101407a900d203000c141e4010740c100110410f26007000082030341001541001701d1714001c12601750004103c01c4240c801c0180c000765401e41c031501c2c540d445074000d4100c96041c292511907a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 412025503 1250 412024253 412024259
    0x3190501050106080c040b0912030712051c060e010e060105040f0608040b07020f06011e210501051e06010e18040b1906030c0504090c0308030a09021819050603030c0106 74
    0x15000700720074041d11010644c030001240545042d1402d42e4180c8503070341200d41c94128800100043c030705000014a00602c8108a500002400c903032080072902c4440c0ca0710360300c0d01c042104805880c0c0c0d031f010f2000c42c03041c5040d0341006000000c9050604440100702200e046454000040703030244140d0300150310040041c00d0001d03505d5070090090740302c5c40c092140000700c0c0d00d80e854100d8480038550808003640d40035400510140c0c200c8821281441100d040703d0701560f90300c40c810f842d04001c0300ea46a0b0400c0030340005805005081c0078507a400310291649400e03032418030070b80b0290504094113007410804003c04500c040d03114200e240103e04204e142002d03840c5418030f071005174002c08848c41440d003042c001c120f2401c44290f0090405407a4400c074411441420710b81408020000072406aa8204080b040000810411001903004001c0800041014040750040c0941091311102006031140660704011003603280380b40c817000c0a00c1c082400701b101d0b03e80310700284c903501486003241829442e01c1000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 412026753 1250 412025503 412025513
    0x270303090a030210180b10150203090f0111060106050f0409020706020c010e0105130803041719031109060405040e010e01050703060524120a060f060806091f0605090319 74
    0x250740034429822504803520030b103102420f960340c40843e1100090a03484130400104041d0411b07900c802c100c0c0c2c154035031030390314069032078525031a07001000960000520385920b402c004072510221502824000701504a4101c1646da914051089000f080004140c5543c445c1d42e82045900030080c1540a40d252041800c1c014000e41c840220028079601c0e00d150f4204142040c060203200c1c045e0510801a400b0454070303109130a0380024400c81d0640d02521048510302d00c0c4101400900d1030203425401e501c0440d8001900b216400303c00c814401c0300911013450300d561814121029a20181d501054200d1300100362070160003002c44605440d4204010020115410750025080f50401c035502001001c59034101c06200900e0244082c42c110204502403108400c8440e19810110003907000070115502d0347d014502c107441d601700da00015281e00a02400385040f114840e0412030950654100301c02411492120700140d1094509000c004504500d1a98090203c0e10300d042050b0020000e03a0308030301d01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 412028003 1250 412026753 412026763
    0x3270819020c0d081c0501030506013506180309030307140109060c1211280c1e11100906140d0e1006061b030c022101061a07030827030309 61
    0x500c00d6205e030061000e00001400f9007030403a40c00030b0107449140d080c111140145c200c2e5150b101c486040e0703417000c81c02040c0c0707900810340b100402c0d0300606514104424403555010080d07459680d2503006000400c6a07580c040101c03010a85d024845040c0f561800c1901c0e40540443c07080580074030b1401d10001500b40d08000c400140c84007010082003010203240080b051030040300b100e14800b03201d081c0c001907002121030114203081c0d142d044c11800b006040c2c2e106c0000398280300c0f0310080d50030a100c1c010700304403800c0050300c4540d6044443d0381c1c14101d103e40c0105950b010303211341010000404080300651107068102d45407040f44080a005064954030596030307c0350004a001003c5252000011703803035204146a00f040d006000f01800365803541c3e1421907511114200a0fa40b00e201e11040c0c404508440704070880f00d0080c9400458001e10f880600030800141c8110481e00c06000c1002c100000d81c0170001590181020104a403070001100c11490100c1100c1495225440000b0a105d040000011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 412029253 1250 412028003 412028017
    0xa05071412190611040f03020d08072310050712050a02090310140105013b120105152403090102160f0c0b3c0a03270819020c0d08 57
    0x71050003034030114013014081c0e00c103c0c0310b20810002e01060a20041c40c200080318840f6020f240780c0c508140458850300c2a4a64948110044100f41d9101c0281482c0500041e590711001e40f40c10042407414030006000039200f0303d640c0a985948000007080400341c1ea0603900000c0015044a00b2841545195002040c3e02c4000b001005144400012650321444400c40ca0704180d00c19039181c1c2c0800c2e8465803410b0356102a9050280000c020302e00682c03140b4003030175420401c00d0008242c038100905a11266214140301501603211140840c50305002801c1f088111b001251050b40e813507031500b0a03e402801540500c604a0400301032030340521500e603e842d03200b40c3c01907c002080d140d07109540340080c446d0003609841102c000a4404100c68858007004640b9000d070111807014030540000080c43e4002803190700469900d100b80c0c03401000b000c404400c030070080c1103c2078108410b80c80c3c0403614003680c08030900d0903600d41d502d801701d14402e02c000c1070383d441c003d810f08050070380c03500d000d240a403c051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 412030503 1250 412029253 412029263
    0x170c0a090203060109031e0506070504152f07030b090f0601080106120609061e0c030b0402030f010e0612030c0d03050a0b0a0e070c0f0803060907020a0507141219 71
    0x100040344598032407085034011a0141c48102040d495a0b441484404803200302e09a04911010044003107003003405424404d182580c1c1d1305aa0327900340000c40c1d40000ca0031364110b0800000c01254180c1800d80151440440381e40e80303141440303200360409203141141a4100170424079240c814450145400580d901e0031f404c0304030948a85a0700c3d21030710307801c81e81e034ad10500e4001c180303c001c42c1d0041000e0740c0c0304290b400c2c0500c1000c03520000e0380002c20680d04000d0000c500c5070b0754844603070201d10b6051042540c80007080b80d040d861400d000e50200e40d25075060041035241502c50012512a03030f900c0a00c00050070b0000242c0391210307440c00082c0c0d1207150340107451010030704000020b200c6104600c2200c10009005203124035a40c2440500240080c004006030180f2844200a402084501d261071610360701c2401711a03074a00c0c0c42010b11103695400b0f041c420a55020900300b6001035030108008081d1400186024040c0c190440001d21513414600686540e02500302806894003001c86103451301e5000d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 412031753 1250 412030503 412030519
    0xf12020c100e1c021f183507020616050f030408011424030709061223030d020702040f090303090320030a051c020a050a0e090717060a170c 61
    0x34030f059110f514100007001c401a0008200d103258025082c4154250012000b800a010381d11510034008001d40044103960845441c400784403030140c01c6011032964001c44640c8a0440c408400b050380b1409001c01c001c0c4111404102d01400c00300e00c14a0b90f404503008811101485a801d17074551b1264002e00403401603500f442e080750381c1c0c0307800342c0c0c040390080b600320300152103502c0b50640601c0c2145a030700c1003d5160051040008000300d03035000364000380800c070b000d80d82608190b10f0202d100044204100c449e5100c10112040101404820394903040c030000390151f40c9595510005005052410a00c8042454141440d081c5980756006040d00741c483c0d00c803503d02c0c044040241981e5031800001c03034010b50007003084000140c8203c01810702a01035850902080d80e00341c90010a98020400040004101054a208041e403007429241c812005035500446400d040340010640440e0806203051090164086407641d01c40881100003008400c01c0012090341c0c5016480e180d000d9035001034812044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 412033003 1250 412031753 412031773
    0x506091c030b04140907080c0f01020a030807030207061e0b03011a041109030d0206101703031302060d14090d030506030c0108060a030b0a060314010c0f12020c100e 72
    0x50401200400620310400201881021030140452154068005032a21945200561601e45450240c40341c01d025180c240e041c24079140c036042565070303400e201d51400d02e642161641c007c1200030003030b07805190003001503840a0054019106401c4010501460010340100d896071214102c44050200e190a01c402060201010b00342c40d40351151341c04030000b61001990620745a0f1040c0030440e45100c07010700b08000000028285000c00801502503040301e030411102c4400020643d02800c1000c140c00c180f2480d5000d404da4074000140080f580b03680c00e0354600305660f11007041c2c2d1001203003a0b000b40510042e581c401d51000d081501d124010384039001215000f1070090264502c12207014004249400504004545041016180c25000a50114040040b94018401c50302c104941070010a144d403a40c6000034003403400203080d01c82039142286920080d82d0144210f00520160b16061007050120300d134410083c8240b1818402ea4480d507000210103841540150700000140c2c0181c65491034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 412034253 1250 412033003 412033021
    0x40c030b0702010b090f06030c03012309070303020307030f050c16030501050a0908030609060d0f05010c140301031104051902181f020d080405031204030c0c0801021602010c02030c040203130506 85
    0x1360701c001175001070444005800000100003a6501c58002021903c10b04c000c18003080c01c65004c05040300003050b203000c014203d01c0c1a10095600501920014256940313582c4009441c1d0113080302c02000c00c40d1000f1200c680601c54030070380b403030100000282d50b8801c511040c80c0e030717122a240c40101c1c1c00d9401d040001d00c03041ea4a100b00c00b46d003500105a285555200e8042200ea051b00400540e030040c442c200950101d111018a001c81500c02d000005401010800140c03c00050800412035010200010f00c00540744d4070482e02589010350700400c090b112103034003400143d8141416054144040ba4160202d80542071100c2e200c0070a4032295001c0340352040c907510007401e0345c440c0e40141e40200310050415201e604c810b64818020f1040c0c03410300c6188028106404401d41e003c0c0c000580d440d6000c0244118a1151002000c1c400021464040d581041000400d11010081e061120600303444055440c184029006031340010404c550700c0c6032404801c8150300c0014415501c0c1e1245d5000500302034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 412035503 1250 412034253 412034261
    0x40e0a0b0301020a0c03140f0408071409100e040c0b03090c040b15030c03070e0603071205150f0111011b0c05120403150506061c020a2c010f0512040c030b070201 71
    0x10559a44400c0c0702c5034140c0b01540d03209039903c90300806a800700143c0140300c007210060405442c44501403c1840d02d08a140480e00d10515443351181012030107120703160010080d039004036915100d070500703503540b1070401d40c00844665100540d2860b0010405c801554041145195280100c5041120034403400c1802408485801184445202040820718035004000a142d01070254035001e10181c1a0b08003140b00c503013060301e140e00494882c3c0201440c40d1100c0c000d16502400c0c0c02110380341e0441100004d200c1c1140c0740352140c1881001908104074850079000710040310490068040c44100003e0300610b42202c081003a10140280641107200540010840e0202c80d0405511174111840d183d585009100c017030b20303040d801001005480e0801c0d0790448150b2610703886060040e119030307c2c3c420242075a400b9107008900030001116055040307981501e108181c80c4280f03810120300c0d142c80000e98040c81413001c0841d503100d4240401082111048111041c0c0344240800c601ca81c03a00c5005900342c1e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 412036753 1250 412035503 412035517
    0x8121005030124090e0f010606030c080c0c0703151401030506010806070c150203130519021e0904110d1a01050117150f03073203070305031c0b06040e0a0b030102 71
    0xe0f0300c0c01c0080002c00c0700b98000700125141082540c01040c4000005401c40c0c066500810100b911801d00141c01e58000c00c0c42e0340c2c803030b4840318014548040d81e00f002e07483d4049408010303c040c00e608a0401c68100715130028000805101d0140300a503102c0c10880c0d641c010921410050344107680002d614141b0070b4600e80d4025034842c500114441002c07201742c0c043d400040c08601010550032a64000c16010840394000f40080d1a85921070402c9005002a13000003100740004007094a44050a80e201c0103611503100340c103c2c4400041040160001d0807903445c01001521080460b01040e104c181402e0300541220801d0f00d03100c000d6610030041c0c0d440c0e107d0807204400d811440d10f05812850070085055000b240004042c2c6d03100b162103410980014000c80d01c41c00103904c000d80598101644c800320703180c1c3d19900303c00400344149160f449554911895094505200450030b50001c843d115420001d40e41a005000646840e154402d01100003003c90700014460f081409400d0141018821a144 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 412038003 1250 412036753 412036811
    0x606090f090302071a09060711211504020a030206030f0f070305060904081b0303180106090207380705070204050601090e16091a0c0601060203040b040909081210050301 74
    0x2d0035181c05c0c940d81c55201140021000c10104200c41440c50b44c4180007010070b01d11a140030042e68500d0014004410501008104e80f6000c140d6100320202002070b00d00880c085144841145175181c6c404140300c21107582c0000d4000340301205004540344482d0341c0c144504160303540c68040f076a4021088080c1c032000e89200d900300d6102c10200700070441d00030082900c0315444103640d1200240c0003043c2d2450340115541200501e8403600004840300070301941c0d008041c0000d0550800960f5102d005085102000c00c5002c64030301400c00f030042d130341c242440768410313741d201c02489031402c0c4801801e0381d401300703d080340700c0c524107000035007503601038169003081c4d03041d60b02e10032407a50f140500302910340c10704074560050152010b0700040f05d001c0403020400c0980e0704080c1c1368032000c80782a141d25000043c2c00600a6400501040c401c04541100741c3c1e0482d06104c00c0420700c0f001908003050948604514070f6112041242040112140c51f2448022100150002c00a1540006c80250b8a13113035008090300c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 412039253 1250 412038003 412038013
    0x1031e0b04020904060b130606090501170c0a14030703060f1d0601052203050304050a230d0f02040c080f0c09010c0f050c101d0103060815150d0606090f090302 70
    0xb40c18603800c1c040e84a80310710000168500280c000030300a00b88052000c1155850348024458035500414a0000301006e0070304500420b5501450286550000c180060341d690226041c50382500c00d1083d44c0d00c0d5100000060707138a082400008000e01058000c0d40300110302031400103421603003441c81041c0b0308241c0d6101811621020011070300c2d9030040e400d050343d000382c075107403e90102280b4400ba03000303500c00d00044d99542d150a040c040c4041c3d05502c000000a8212002c020500c0001004c0b010006d0440c1c00d00c804250314588a07440c1480d1000c080e401c2464456910209500901d4080c007540419910314032643e0740004004242c807403011560300207000d0008010000310781134213008a551141050310310303d1140b8000f2030041c2e404c0c005080000b40c079014200010003403030b183d084240b40c820718040c4121814035544a44d0b514980507182d0b048212240022035007580540000e0034203100401f01c450010f9141000b41c06414907018403809641f6100e07141810100070f10540c45907560640142c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 412040503 1250 412039253 412039261
    0x81005030a0318050315040b090309100f0201020706021605070801050c073c0b01050a031e060b100509040f090c05100c151a010212040b09010c020301060e01031e0b 72
    0x2101c0e00b25902900d03c400701c1803400425140e03030070300003001c3d80524945141524a03207401c207140c0c05800a400141c2a40007000104519100c44203107032035801540c00c0940c5403080d82e0000f20b009114682e03025025500c080f492810700c00117555112200d40c09881214030050712020703454201c07102603913010001d040801c00d12b000600301030100031310703440840c0c40d038240b0340b00403140c03c0c05620445900e42595480c80b8604404c014494000501402003601d00c00045404c595854582c0030018181c281007641c5806620304001040c0c201845050010b0a10404500460720180c05500403503415403165083c694a00b5580303905218041c0d039641c101d50f414140614200511081e07132a0841000c0800103d50100c10208080d160001000340700480c0000703804040001d20036030342165128060454021803140701c04c4448131000d580070f0b2406131340c080e81e442480c04016100b01c0000c100003501942410000641f1801690400c0d0482e401124200765007800c506c80200c054002020041c00c0102d200081 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 412041753 1250 412040503 412040507
    0x60907150909020c010501051c030801050d0609020a142e0c050f01061202040501061b060b0f0910080706050f1e0706290d052109091501081005030a03 66
    0x408454603039420222542500c0300e2080c0140d070310503494802c032a1344070b5004001a0170322070342c0e0084101c4004028004401c2c50744c0c0051a940061090520645580703544909100c4140c0c4019420780d030040c01c0710700345662000c444403080c4035202111702c10780c0c0c0b0781c14103000700b902421070004603000c000c1e40a0321140c0f83c26096a2044500e4019140c0380b24000172102407840074400c80000d0210b1001c8034070045c44c0c0d80304000c1591016004482081a5a01c8003281c0c0d518002d04481620781c0007001040b14040780307002c142210424088554480080002d0050f101c21949446c0b041da00c000050b940f0150301c4070000d9895108002d0f54110540e010000b07014a40d440c0e51007108c40300b014020f000d29010281d1030703040c191040300034070701e4486801d204d011144001c1c00d03070510040d01c01074522081c24a02603c03403d840b1603103504240448507101d10702c203040c203080d00102d540c0c19000410803612810701d00c03141e003400c030600c0314414081104200451a03030b01050040d4022a40700030000d01c14621542c1c0e007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 412043003 1250 412041753 412041779
    0x5010303020f070f0b0c21040312030204030201120e032b050709061227200406120204020310030624120803072d12052203210515030c03060907 63
    0x54030b0250098580c1c3c16503151a010310300740c8901f820604030b80c80b64194144081d08070304585040d002e0510420003000142d810504071002000310810008802d9001c007503490944c0b2441d114090381048082c3d11559120305282c5580020881e02d00801c9282d48150040e15214940e00900c030206160101c0c200300c1c480c0640007285000c90300c13012030302c0c941303041e95401840401c8a4011aa00281c025000f907094032641404038132900700f100d0501c0002d16000901034800d242d0030010380215000400a07240c0000044200011540075504111074030106079044660315880182d400303258100c0800103403001000e11081c2c81641c00800c01886c60701c680b8030540e40004044201c41029111842840c1185c142c507114080000250301c507251801c42080c1c5000844500a00125106080e0000460202c02a00044c0061949810130140c12035000d0f09002410491200c84091300381840104007910307942c0082e1000b1580306908171150b070030000e020075449144c00c858207010b540c04030004000c40c60110003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 412044253 1250 412043003 412043017
    0x1003021908010c0f02010e010c0503150a0e040f050d0305070806010c050a151a030303011401050f0d090606140d050c010305070c050609030c060115080f06150d05010303020f070f0b 79
    0x2040202180e0769000c1c0c070b080d910350030b440d080491221441c0c2d80444d0740a01505480b41d000c0300082161100307042001c0c01c0c500014003000c250281422a9107071545035525400b000d050034164030070440c58076240218654041c2d020855050241200300c500e240d01030302801e8080c2c4e9503034844140903070364580111881c1c0758940080e07a5900c22100408082080e00c04048500c5050388800314422800d000c0a45c1c951050f075800900030f6000300300402201090b001800e60550702440d1031941e07a40d901012803501e0052400102200c1d1a111101003005845c1d030080d0200c482d4010754482e502c1d03145081100d000c0f268200603000e034010036130b82045e6600c01c2e8051070b0b212095041c00e500203c101e488a510b0102c0c100c4a0043c1030748001900c0211480400c41a80103141c1941c80ca06800c44604005203900c8001e040c080c01076900c8004100a0b0b511740300701c48200f60303d4410641c0c4502c0d1800c80d0402901c000c0c40160094000c00940030300390000490f95001307880d502d605907800c0900d0400b0840c62540b1840c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 412045503 1250 412044253 412044289
    0x13030206030406050f060a08190c0e070c0c05010314060d140d0c021f02030f13091b090902090a030f02060c01021207080603010c20010e031c14100302 66
    0x100040e680c40c00a9402103026240000d40342c9000040001210000390030b10340708140703e8608000d00080051420300b0748000d00c43c00e55500c03075980b4015001202c0d0790406190b01a58404002440c0c2d803098007010243d0043c60300110481d035940c01502110101c0f084a0004100180001c1140c1071048541103210b202e01008008500070940c01030920301c440703d0b03a100040e90001c1072810b41c64000c1644144680d00c020300e0355102e044080c00303035403885010b081506409010601c06044004072811000400c0760080601207049042506012001e01c6107003080400d03540c4502098031180fa10980d00b54110150000d202c00703095450361040310fa400b607c200c0e44020b0800c00417107034082c203001402c104d4103c0100d015160907c00b902401d130f190010b1046000342e00d0036038010440c0794071090070b000e0050f814810145000c811390a8502400d242c00d0b88040724032000541c0221652440021081510895010848031000c080d00d0744c0944400c1e52405040e00700254180050303e030103104c40761011159 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 412046753 1250 412045503 412045537
    0xa0605060f1c230c0406020c090403090f0608010e09060103150b0316090c0207090c05070b09101b02190b0402042a0c02040c111b0a08030d0b041b0507020105 69
    0x2c4000c4803d540025180ca050284603080c64410003a5180c40b00341c120601e61419801c007130804c44025502c9881402c0d842c0b00c1c5481101060603d400740401001400f607400c2e0b4845010f84400c2d01600d600c80c02e219040036000804001030010340d0100346181600d622030500980c1d0400000c00b031000d04144401140d05001ea46002d0700410b101000b000000d00000c0f2010802011003040a810f0004660000524074104010109080d901c1000c40d245264414400403482c2c9520141901d42043c1d4400700117032901d0f104409085003024080c290384030303241c0e03800c40e10248580140b400b181c14184400520b00c041c114081001490180c1004807103000704545409100005914841c00705080c03041540450b60840d10340f4250f00f424010311800010904180300c000c082e40d55625600c5041c030101c444414a40c04500e2015a034031014400201441011240c41d51210400c503001440c040d500140308a28103005101c800c0107100c10174640c3d501e6901c03905e0402e4030a400644030380d40404e4640d4181503070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 412048003 1250 412046753 412046797
    0x103051005063001030b1f03081b060601111e01090516050306150306070f031b1706090c0a050c010209100f0e190501030f0b0409030c030201050a0605060f 68
    0x103100050708180710b1003c1558140c0b041900504140c0c120420380301503480400c401407012414240039150400003c0344003c5034019080300300e669482098100800d0000000750030b5141064445032440c040740e0300c40a40e8995241c1500540d07040075101d10b03043c0c10350002580041015100e220f5000d80250710710011684820b10303564142403500400f10704200300b140f91001c1c4058102000195446040c000c0d07446a988051800281e407518010710080811403c2e0602c0310082d4400d0300302e813108a1400c071916081046580d00030708501c0407481c1c0c0805c074081c4100051003d01d001c0d400240940c00340800702e4900111070030112074076400014140859902000084010380701c01900000003a080d070303528110002031040042500000d5030840740300d4100c2c41080c01c03501400b40300e00707421203c017400e0005040c50110019809080c14619040d07100d85045040b805040e003140c098005130384607600030001ba0703454548003022200f541c000c0301c0d0003110911041c40510f041c0c2d0300404a80411004d0b002101c04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 412049253 1250 412048003 412048009
    0x90114030a14090d080a050105010516110406090b0f060f070b0c0f03040c080d11060105011b3207030f0308040501090c0f060306090506090c0714070902070b01060c050c0103051005 79
    0x5029520340402c2e611003210080005d600c580c20542141e0102820b1015514002c00202a4040e11800340c00c07590042e00c500c410085c00040c15480c0d0700b0b0140081c04900d90364481030300103120354114140a10840082c03401c2c9803500c207045034204d03902400381c00d041c89400d4580b000341d50310090a0680d090410091b1041100204d4080c5124512500c0c2c000c440505120086040c5070100070168103002c040f01c0d05d0502d811700824402d05445081ca4103050350801c42c0d40c604104580c2141c05040748940d0807040c020100120b00c610402d0107503100e11180554003c3d60251b039242a440084c1810f11a41e01c2080000e21981805412501440010480d910744e0b440d0403000905551040302640c0001d1410410301c2d0305402290002d10a40c1d0007000300d45400d8010075003412005001803441ca500040c15801c126070528101000d040c040304803080e541d214000c0c0d00c02540501d60a6032242c81541c00010014480e140c04d0504c1c913070117400f03007050402100040d000742002520810046003039203800b14040d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 412050359 1106 412049253 412049291
    0x80303060904060f02040909210c080f28020a021201020c030f0d060e010806071b0503071203060801110403020a090501150c051014060307050105090114030a 69
    0x3284c281c1402441950084d4424500e06170302d20f014082c40729070380070440700964407991109159100903103890020303140007842c1600030480c81c9d84030f1145034007410184011100381c0c5060341d01d14010b466051040036018006900113600c900551070700c41c10099024009100840c507240104c020309480388540c01c40a0b84090700020001140036166020718010074101081e2082943c403242042e480d254180c6080001880b24640c5001c005000030800c05580c0e40040107502e8a411980c0300d41001d8074480182040c556503400003d49090b0a01079190b444c800408419500e0382075104010100c8050782064101929003030060008d4440629400e14080c0c2e0350911505403550307490302d6490803140d030714644000750425200300d00d0890b82c2d21b040c601402c000c0b010740d40c0e029128001100c050091408240c000303010120f000e014585003030010b40d0840181c1a001c02c5601c14081e000b0345031 = true := by decide +kernel

theorem cover : BRFrame.Cov 411870503 412050359 := by
  have h0 := BRFrame.cov_init 411870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 411870503 ≤ n) (h2 : n < 412050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
