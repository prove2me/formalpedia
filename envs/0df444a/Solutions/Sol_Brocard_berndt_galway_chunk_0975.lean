-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0975
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:36:06.476476+00:00
-- url     : https://prove2.me/submissions/7a06572f-8e15-4aed-a1f2-1b38880a7f1e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 175179856 ≤ n < 175359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 175181106 1250 175179856 175179869
    0x150f050c06010b0c0a020a06030501091808070b091c0302030a0b27130b0a0603060507110a030309082701080604060b030411060c070b0a08063102040902040f090b010801 74
    0x510242e00306000078084e48005004840741c1c0d07003940d400b207111905141e01600100703a442c001008000914061424003900c284242c03410580e059584e0007584c0900c50000d03048084110004003003100c00c00101048081100140c41040701d00d5800502039407003100d006188506050101e8124201580c40d2546121540d2a80211b2904009031176049840244800c0b0046014804800800c00907111f0078002c90a0340c40100340e80c0d00754201072068035400b81c010410051801000880c0100116004000355458540400d19a26a080102c018065500d200201c6140c030b03050b450981c0142003da0090000030b8940c42d440359182000c110448000388502d5268560400003d4001018246941e030030043c0202954109454200351529040c1c282c0c00040c01010006200b0b1800e9800c00640d0745d0048044601c00c1d0890303c8440c041c22015507100030b00c0d1102c480c2c251304644800541d01039a0150104160840d20746a8445811342072603120f01c1141c030514a40040401c10754411b13481030b4161103c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 175182356 1250 175181106 175181113
    0xb180a0905011214120c0307060b09040206070b0703060506190801141503090709060f0810180b040201140c01060e010803181311040303080f0a0606020705060c1501150f050c 76
    0x43c41d03102e40d0210728072084d40010742d00075005142c52041c00107014003101c042140045850300c1c00381c0b4082049a0402c0005c038802e039108020000107039104422074003900d50100c58251561100d1806a000d40400c0d000598000c1c0082030324242c0c00b42960074400914410380e10f5042c546d90700e16120304000388204505403c100b03018118082054031078000c5070002000d50031174070016a10303880541212929040b41001c0340303c10310b00f0809100200100a20900300300070410550715150704440450300b1840009183c011101c002030150385c0210149180c0d8000303043e4040d91049030b1100d240c0203001034080c03041548502400815180c500006407007080c2c208004500348222000204480400104c0d100d00e20551600301e00d001c00341ea01e102501c01140300c0c2c0c8071640103044c00301485880f41c2d4010f10065105207005010402541d0004a00003281d0060b5002c0e80d8030041481c0d0f0034200101260801c0c040200c0000004035002094070b10180c0d01903540d00d12410b90050034040b9400d1003290750a181035031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 175183606 1250 175182356 175182389
    0x40b0a0c110f0f06090a0b2101060810120809090405010e070806040f020d022d130207050c040b0a030c030f03181406031003061811010201020403020117100b180a090501 74
    0x24000010107103c0300040c404d03400169038500700c01c9a580074140c5408c1001c0e1a07144807094004407810305000d08214207240e419032624600281444500e0310451900c2524000e4010170301500400b183c0742d06d00080c200031810314041c01c08034080c0c401c1c000ca08029100f007520015100b2000b10352940615848452105074504a400701700b0400111780090740d100a43da02c81c000070311249114514641502469902d104034990704000c007004e040800005c00f1401000004005400898044034030b95046900044590228011554240481d000100b0710800250044140001c0f00410402d1034400d0b503d03001c011185007514040c003200f81c4100c0035414100d60210038180b621a0296a01004114030000800e98980b28001a100113030b81211203a030041030004207108000001c441c03414000e0000f540781524550000b040b030b1183e200142c00c45842a00464004e1460780a41e80041502804281c0c07918212510003041d50f0440049600c50f1001070b5000404800e0703405094100c0d252441d8080c070a5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 175184856 1250 175183606 175183609
    0x140904090c050607051c172403010c03060509010f050d080706111603020f010203090712050f01091a060405061507020a050418050f070e041403040b0a0c110f0f 70
    0x3098240c40c101c07120001074074049420744420002d0440c0501030001400000003528650004541c4450180100a030400c6508a1038802d0020540c0004840c9000e502213480351a1a8691690700d00d50700781e06500705122503140340e40c0341e0030100a40ba4200c464841d280d07602c1c43d0b00c0c0d81d440b107207104164101c8510030000c40410b240d0001b815805008800100f07a010088030f40142d903500294003070074404484130000c414154100554070500303891b00300840c0345081c0004030303580e25200361248140d49500342e408901040700078091b007140510000000c2c04101c6803031401d10800ca0f004100101da501c00540000d07598a0107010300d1b806004041c240101c220b00c81000c01c0d0295101c0d600c140c1c2c00c0450b03560002081e859501c1950340c840d041c22a03038000040140b604508150000c1860032650f0f000c3c20041c810a0b00301b0302c10035009075211304480240a0740d80403060450143d5030068401c00c40120704a601c0641003500142080c1c0f1500319031080c0b0013102e08001c41d560b40c07241801d401010f0410b00e044607 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 175186106 1250 175184856 175184861
    0x81903050315090c03011404090803060d03020f01020c0609160b030610170f0912030114060c0709060603060f0918060213030506010909030f020f0303040201050d02190c05070501140904 81
    0xc4a40321441c1942c025200c045010204142c42400b801c01000004200d05000249510b061a00480341404040901e4036038014034000a40102d120301c480e230012104050003005500403403011807009540303803c0c41c00d12031501d41d0030841d5144c800303000303441419240022140d201740a4444854895085496000c1480400442c0c0c407120010320071410b1160151a0012031007034030403001344501c249140b42a004242c2480381000008132807000c280010712594140c0740c41c4080c841c40a070740c26031703e5182c2c1d628a18030b001a0ba41c00340c0b00e4186007000100f0b246074560411815580c403e00c00c00e401c1540c68203401c00322005005003100300a007030781403c0001107141d0003c000d040024040700c004981ca903158242040750070382c4500306142e03840c80030408050b04214450340d0000c42e13001800341100703150485a12480000d1000b8100503000441001c02000741d410380e11555450741c05900094500c2c40054074070740034030205070392512580d900069079611506459070b03603020403044030f4200030f00b61050202 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 175187356 1250 175186106 175186111
    0x3030b01090801140402031b090402060702010c0c03060608060711060703092303031b0915030402130509030702031203010503031c090b0c071203090b0f041109010605040f0819030503 80
    0x410040704400102c10b0000d0081c1d0b03106060100110001d400c0030300c10180380c0492a03013001c0400007454a00c906503a590f202c55a4440d406460302552580980f004a401d04c0c036802004091b1191020007000780682075000e0401c0d52841c8040301c00c42d40300c40c0c1d42503a40b403500044007a820782c014800100024402e070842c0c5070951041940b86120782040300c80104010300001030a44560001c410861020300c8a440115102c03040c807805c5151441d240c0c08201105100d00600b8903039040040480c045440d4002c030050b140250b00c0d420031641c04e01071803e0341c031781e070006400b64031900c2411400c030300e0a1a032004032030488000400941ca481d00c0c1130040c41c1c11611804011000503600c0c008180451034640ca134500c0b6001d08440d090f901c4105140c018180e406920740301c410140b03031001c050002031085081541210000d020480715039210310b0010621040030001070780140b1074500014049402a0190013582c04005a089001c0c2d00c44600503501c24032000408541d01c228023101700840c0c0500c00958 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 175188606 1250 175187356 175187359
    0x309060403030f0c0b0c0d0f090203030f250b01050f030c03060114030102071b08070b0304030806090405010b03101d0111030a022a0304030317070e131e0218060f0703030b 75
    0x940d55135846294641c24219000c1c00e00407000240701a2084c16071140486a43c6c030040300300200c03501074001c00c0c1e590040c00658076260030b0020300c3e0b10110002009648c400b003001d5501a07040195440e0007551000288a5a0b0040008081c0c003212407401103102d00810700003a000b031110b80e00e014113282ca0781d00c3c180e03d6185c140d54200f2034038021034800042d9140c100600c40290000d10b1410710716a10308803045e40300201c280000c4c400c0c44002640020a150441002c4602800b5903e032800c0290060421500b00c0da8148202046c5584207042c680110010280041030890324604204443d402c2e201c8910307900d42402d0b8100001411038242d81d0190403419400c1e214a95070720606500c060014510003003d00740c075807001c5020010560b00c000102401120a1003110031414013141c068894240b40c0100c030300c01c501580d40d07560810519400410031391011512120303064019490b40000358458145150045102c101c10190ae08210007110300c00c51085080c94907201c41c0d610110002e15800c55003d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 175189856 1250 175188606 175188617
    0x11011202131410021f09021309050105040c1d240a0807231e04020f0711100804150b04060e01031b0e1303030e07030c030c0305010e0309060403030f 65
    0x465414507008206405000342c854044941e5141c002003110442c414980501154010000d20f0814100c0581d2000c851044810100d40c100f2107200003065487c0302c01013244058038000408007441415000340d4012409058500c540d9901e807540154040c0310804888903c992020102d041a0006004442d58000402504c0190340c01c1e0000100d9072862a0721140351540840014801030944070300f8402503070549460b50f40c2c00a2407001080b211691410a40c0c1416410b2401130b0840d240e03501120030f83c0e2007046115650f0b50f0301703240050001c4010002103010b01c004403044000345008941c4a8010303a0020741c0b91100c01c480701c404c4c80c00f5041650700a070b0001d03100d1100141c440c0c4800e4246002e54419680b42012417020450406031460744e41c01003a003511544280900b640000d1130107006640c05140c08200b4040540d400e42c40c02c100c1c0e030b2000f0224103076a0300010500c211150f440094a20850007840f0903003e084141d030b40c0e030103002d44155004e8070802c0108002409208003407600300711030821 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 175191106 1250 175189856 175189867
    0xf14060d02030103080703080705040f05060306040906050a091a010303090509090a050d0e090a14010b0705070b0a0e1201021305090717270304080a0605070507050d0f0e010c11011202 80
    0x1181070ba0402e03401114410320209109007015041000540c0c011b007149041d44c207143c503042242141c07000034452140910000400710307202c1d494942100d90100e0300800140020b0601000040040c602c0381400e44206200d91013801c06048040b4001d4122505591200015810300e02005034940019200007031922a072040d04001403010700c80140c0b400e16035115020403221440034003101708002449405400e1030990340700584540e4051a40c19035003804500e44d21481d07580380092a0242503000003007260b0020541d90300007540208680300c03003c1d0039160203d443c0c0c1c00b1030b0014280e018500e00400c10440201051102e41481c20069070f00102518080102045041c2600c4480c1c80580300040d404a02c072900741d282480901180c014109008029880e00e850300301502c0d2115002c610050641d501c0300c020400e0b5a10800990310b05030b030010305680d4007040017800900304000b500c001e5000714512610f07054640d80280340c1c0740c0070b003504030311200101c011038001100c800c5264541840c100da0300f88070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 175192356 1250 175191106 175191127
    0xf051c050601052811010506010c061d15010603140112020112060b03071d0d02130c0e09180c0607030c12120f050109180c092d02030a050a060f1406 65
    0x400302c9404503085034092508019030024200124401d60b10580d82c106018400d0590340541d012b4440340d0052400a0104c0c07451070490003c100b0345000d612648140c2440c03000752040d50800e44e0484005031410072a4441400d5001c0d0307004070900c15070540c060760348140d9003d5402600b91414000d9010380014040761034401c1020950019110080000c000d036104100d4030311072040003019031100300c0e150000d1802d19030000d82c4d00907000407a04445a1902020901076010340360f4105007000080c00110b451514034083c20450880110301040d1b84581c101080c01c5041050460301c81c235400d030303940040c0000252074211640100c40341c07010030800400c05c0c42e8804515840340c1001000407060118a03035152240f00016030328281072003c2070130b90010100000a580034080c004460429a021900c50102c61a22002c000f4002c640c9100e4481e8030081024400c0340da0065100b8003181d1810811926007440d120115001750003440401b050030340091100000202e00c0d1840503800620651428a0b19030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 175193606 1250 175192356 175192387
    0x207051e130f0b13060b0a11010605060a0c2d02060c0f0118020f0603071e030e010c050301062303070e0609060d0c0f110a020f01020c0d050d0f051c05060105 69
    0x103501071411961000c80b0500f0740b4152180700c0c04d1541001041c8107182c00c0a01c0c0715150b1141e00c1c0070784180240c085010505042c203400001c003d100080489403105000d40c0050842540d12074111034032200d0100e081d20303c482c0024000c0c06c0240554030b403040320b2440c0d42400190b80c0030880f8000544a803c8006031007003024001c624a40c8641c0301e04100601152050020500580070a684075001c103000300a1610ba002c0302401240ea2905202c04480044010550082000a41c3c00c13800d5401c20186014141d00320000354104c40f81e45c0d07206042c841c0d10f990700051400c10f5400107082d09a0400200f81e4142c46002440c1d16280001c201c0b5181c80300d000c0000781190f01405402200d503031940050900d00703030400c40102ca20a19400e062011008540c5100c0e214440180021300c60030081d207103480c0c1a482002569585d8902428501407020142000d03540c603100004414000380c201050307070264a01c2001540d0100c1e032008070007500101d1408021001d072600a00702070401c2000c1c8110600c411904 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 175194856 1250 175193606 175193621
    0x303070c03020a1430030a0216201302070f0209090f0304030c0303020607140703030504170d05010e01060507020603010504050711030f04060201061a0702010e0f100305090c010207051e13 82
    0x4000403c918400014030815010080c550206580d0041414400170f88004045030b0344110400c8005031b41e61064015180781c0c82c002407018000340746012039880424072108c0c5600c1340c9201100c0389034a0181620f01c1c4010707440f90003402444042d020781100c0050605009540c2c02c0040c020960340e55440d03900d04645143c02c03a500039905c840103440704009154060000e55003200c40c500d0710886400503180d6440c80c0b0310982000030101550b480014090015002c003840480e030520b00202d54407040241617801403c0300b03000e0403004101480c00024014001c001700e50500b640075051a046030b18100c03c1000030080103042200348081180c0040420b07000340024509038030005000d81c0c589080400c003c0c00c4076402c1d00100c1451100c21007043c098000c2c2410350780b506909203004e0002c001c00501050300c0c00a000c84890700b0442503a800d18015406800c814880d00e40c2c4405ca681d0004041c004aa4424040c85400c2d080b0310440303243c48251101c0701e03140208410180494080380041c030341940842d0b091 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 175196106 1250 175194856 175194893
    0x2041b021c08011212020c06040603091203150905181606030b0307031502130b1902010b0612190b060d09031b030e0d1103070f0f090c020303070c03020a 67
    0x481e4108010751004101e54000119518003075005604040c0c080c40d600e442d100000d40f000c1d0782c010044422030710070041a49078220152140c1c4c1c440d83c1c0c9a07030140140008880071900341030060000a1004d1085c401c00703900c0c61a010480c08000e2420350f10301e0050001078030440040c80d810383d000c41c4114007007040b0141c05040401592040e13150840c020102c0d410251014802d0300061410004941d0380181c0002508003d400180e50301d4003080107030300405c00c95001c0d249070308002c40d0500c00e541000d803000361103044c0f5800030f03c1280003c40410100c0c0c4948805920401c007042c010641c40748058400408a900a00c000240c0d40e050b42d0000e81d103600401c103441c44180c0c0350501c00d402c0603407201819030030b40c0d01030950708c0520b084c55401901c00c204e00d201c0b40340202408060300c02031042c00c5450461a0a0142c03e40d4601c98981046045449140c081c030715017446140c000180411041c450b0403040d00e469800b40d421611202c40c102e500c1c69407500150308501c03400c900c0c400461051041324054066 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 175197356 1250 175196106 175196113
    0x5071106030f0405100902030a02040c0309050607120e03070203030a030c090f030c03120c02030a031103120408190513121a070809010b01050405010e0f1206070c0203010b0402030118050402041b02 86
    0x200381c60035500d0690310341c820b05d084034148820440140c0b00001c00000c0c0c00c0e41100c0104070140200403c03001800249800307030162041d00c040c01110b80e000303500c1120703401c18050309001c1301c01c00144880e034030b01c50180f000350194000c020003400c07140700364030119088a813440c05410031503076aa5501078200d603035001030350b080c0c1450070708008003c5c3c40b49240450a801d8100240840400c0d00040e03203440c2e14a00c090706120034403a20a17410201402220705440010310115800d007068104401c45401c442c1c107403000090b001c61780002c40e5004005403046c440f26940c1c680030796428901800d020740c660000440d555905804000050b080d2003c0f1a841004c01d681d800c1445e2400d203154609403103401003a281403280800c024000d991340030058002000301500c0c0041c0b10900c1d4004030b005544003141000d803038002d0030300380081c07141e00c00d200d004000d00032802800844200410403040344001e104061040c94429480c1c0300385421034000c1580b203400200300062100102c1c0c0000d818400d0404001c00580 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 175198606 1250 175197356 175197361
    0x9120304060846090503040302120a05100f0902061810050c121b0f06090c01080c09040f0b03011802040510060206060603040c090c0504060f11060705071106030f 71
    0x642c071031192640001c001030302003041440c0100440004a0010680ca0b041d1260040702c082d0300702d43e00c14052101d040c9082003001c2c01d01410155240d030050b00080b80700c0c4512541e643d0749581d00081501c03140e9080b40c06440e2080c1e406089038010b044140010301196228035041d00542d48a00107003620391b030b2000c40304112001e83c20030041c1040c2070713811240034403505001c62020400b0000c1c0340360314041d0510840f81e84140c80450703240c5141d14031300480703041d1244480904e050000420801c2c0070b400b01804441c00240c40000544243c401269126603841050061841624140d00005c1c5240c591071000074000034010b0109003035a107906001c106135007100540344114100782c8212684150000c00020545003003960007901d03508098403c41c481c01d8084041400c0c002c044454200030000b4840030440c04111090281c02504180b10300c5002c170b015102c18001480c0122000178024100701d016042541d5015401d075540c6c0c20100c0b00b40d880c008082c94690302a00e82400442c00b031620351f500c105251 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 175199856 1250 175198606 175198619
    0x207050d031116080403021e0102070801020306100c110d0533010e0408041d0105040e0115030311070b04080c0301060503070614030606071e030809120409020c010209120304 76
    0x20048800031810540341501d07000704101008107440c4078100345101d440c3d0804040c18407010900407030308060740c002c03086042c3c9030200800f265000c0490b00c081c1c080c3d58601f90740e148690300305d0000312041038010b419490f010710003500c5660b5907101c0d43e00c00c80c00382075483c100001103088680b80e034108803100e038001c02e441b043d4041ca0781c140150308914041440350132007520382414207102040c0305070105090300300302050820040b1015200a003001c20104aa51505c500c6095003001c001c1c4103080c03b90f450000024048074060007070005403c485280c0d444100d155550846a0074411000c1e2010381c0500103000c6001c0301c2e100018001884404001c00c19a40f683c01014211440c645c800c030300c0b0b0f90180d4003c01010b90010345410030303178240584650300ca523681d9020a000d0b100b01031000304101c2a40012a550703034054968406d405000e07584a001e10780c0c070f603404640d407250200c1d180c20140710180001c01008800d500217000c0c04000c0303400981401100804122044150b00f0b80c60000d800108051161 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 175201106 1250 175199856 175199863
    0x304030905151e0c010605030a0305030f0112081911030d0608070807210510050c0a0305062b060609061511030a080402040c020f10061a040e060d170d020705 69
    0x15240d011142031900100480d985401c2c03188500c0e250f04680003141d416180c190a40c0504003c12015040c0e6603ea0708915006156500850f90b5580d641d80341c1c0d002003107900c40000b058002a40c0181c61501d050904100c4206c03900c2014801e40400c0004241054130342824000b51078400f41041c000f103040c0342405002d038207290b01c0e07400c8500d99500c041c0c81000032000e582d0300140c00340c0340c0c0301d0224078140030340c24087d0615982283d1450100d041c0800c2c403041050403402450400a00e0f58200803a440354000c020800900034501d012480718688200c01ea4080160304000191080e10002050750351406c02c0c2054030758580c00280800031052030680b1268008042e00486107441c1c0c0a1b503c0c0424002d0040d100007406480a802159511000b4001c14000c028400318155550100e41308100e481e5150303c00303441e040c040c144035a00b00c07808045030118904140c1b02035402e05060b92105903205420b01c4419100400d05541c0e1204003840c03004810200303c0100320481c1204005a80c03100d03203003801c928 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 175202356 1250 175201106 175201129
    0xc060903070305070209150406030c050f0d0b060105180a06030506120f0d080a021c06060f0201060308030c0c0a080301150e030f0c060c010b15070606052416080304030905 75
    0x2290020085400001d602c4021600495030441d42541c003a01da813544000c03030b0803d10105035009031030510080244040000700000725001100c6074801a1018003e10a0080d08a6401030040100d140400c2481d8042e60192805010005110741040c0f15080019a140980d500c0140030030765a81c14402903007032810301c5041c211070300c1006104591982c9659a038840741121510200300c00303036010600b06100e0b50100c0e60300c0c42d00e003500c00c001907813001c0d803880060a91744584008100000303050442603006000704000c40c0c5d00112481e041d030f59094109025076102ca610100c0034002c24070810002030b828400703507000e45500c00c0041c213083e0700c03a0f4021f060313507203c01c242130711130303842015a80061000082c0b106c81000d0b083e40c80e40e45a02004080fa805041620045580100490950a50440d14a0160004030300981060245944c0c0b80c062125403c0c0c50b00c034036a03148035a0108070000e160034400410f0f05a05103914095034400c00d40f0b0b0351406400070764048000540f0390348100040e11703200f12400c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 175203606 1250 175202356 175202371
    0x910050a1404121a0f040609170307020f0601091505040c0903050708030702090c040b0307030b04060f0e04020406060e030d1d09040303051803030105221104081e03031006030e0c0a0b0c06 82
    0x41c550401c0f0300c560042d19401407001f0442d03511040380000b00400074964030021000f2040254984c140040c019480707111000708080c0c51310541e800021504414002c142e410203002903902d03115401c0600344406080c01000d07400a000ba0214004001542004040004d107031040145032503050902c10805403400c050504020480140404d010710706d00502200d03001841410001400070141011801410180d4421a81d22889580c001841505040440e21880c800c94080082d0354070358405036600c806880c869038065103c00b00800e88540250500f62280c50b008000c45444003203070300001c088907412102140002c1e100c2c0309201500032051602100302816401860843d81041c01041ea131300740c00c40080d400f05241d0742ca00ca00341e000b203600443e0300990070b0a03040d5071161030b822000e640d10070b50280d0b08001f01903a481ca0884080100580b0700608502c881c2c03d03040c9191034001c60203018001b1952034180140214080c955513074001040040c01602d01e0a52100741241034507003800402401e02 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 175204856 1250 175203606 175203653
    0x300305130f0b0a0c0c030512041d070f050a09031e030e4e06070909060e060405040501020c0a031119020d080c0708030706050a0e030910050a140412 65
    0x28080702c41003800b0354944000368a80054850824105039451681c0c5500251a502403084000d0440080c80e00600580d8442034070103584080302e1581d418001c10880708880022108170301c01c2205840341009003143c50080c5070449003240c594594481410413121020381c0e551a1302c0d40702003051f800c4044100d62000844100044200000140b400340288040c44101c49030000c0840508500c04200580750441e000340000d40d0b101d02008a07981d85000f0b65131400030808404000a060480e401030781d054482c00841418a074495005020252201500480e0155003c0c810400387d280100721031044c1500903500c64001011030100ca60034041c1c3d082d0000c4440b51407119240151300c440119149a40d070092100c0d03500c10b1000c0c541c03401c0c189160032850840c000091b8004c14005a03402c80381c000c02510350104160042071462035a0b81c4249002d040d00080100158440c01c1e000e0405031400000740d00f41013008480500d00b2100640c00340d0082c0d074400540380000c00502145085440b804040410360 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 175206106 1250 175204856 175204859
    0x5250b09030c0d03020c011805150c041508040f0515100602070602060412020c090103030c110603070c020906030106050d2102190b09070f0905060f03010b0109300305130f 75
    0xa2070b0b00c3d0249964a001450307000998242c550109502c00c030000150503c1d984060300d0360f86895510b074a1101d481400e500a1140841c502d03404079800c03a000c5440001403d5652100d1090a40d58004000c00a6070441407410b2036030003113101800b141801c0d0441c04141c699510f401c42e98009000c4168029034110741c04004280240c68001a540342c01c0303030f000141240c600e0580343c401c0745401c10072403405401c00440e0000008041d0410b680c200400c0c0f00b020640d02c0030002901b40007d1b13000440b841000a061808200007509003000c01541180c1c0150000c10f03000c0e1610041a400d00c000f210441d089201003a80c1011480e503102d441d000c510040c4003612009104400d645051219820064900080c00000c03400c0368600f04501c0d001006058080300ca940d84d0b0b59208002040d0403500c0d07600513440352010120605c1c0610401d41140c805864624444d070034130601000d0080c141c503401c40f103130700d207205095902d9110341d00000e8181e12a0f512981c1d2124000e80c4180300001c2c81c4c0c000500103800c03110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 175207356 1250 175206106 175206127
    0xc0a0c03120207081201061d090f190513050105010f050f010f021504031706030d08160201140a05010501021c0203030103141603120e06030103020f0409020105250b0903 74
    0x44550140d805180c4503408550003401c00000384a8010010031002000030752060041355004403504940460312000000b580c40b400c90b41c219081e0300502c6078007003001d40c00214402d01c0c1010715034024408240e003e0811040740007581c11034030140c50710086503081810350020003400740502c50261051000d41b01609180401190102c83c0e103c1d4010b0501c5460580c9900d814420072115035a543d41d090341410301d08003810701030102004094403502d40b684801c001291800e0019002c1c2c208011507442e034119946948090241c050030352180011952114603101654110b00c0c80b00c1d010b5170180c100003609525060019240201e011840c581d1a482c402d20030608a40200583c0d04413600720101c5120400101000c40c03c1c0324010072247c20b05e00d0340d201d020061001050000310000859110507270380340502010026903000c2440002e41c032a20703214201250782040d811550a6070300c1814850f08051084141840b0704034104400c07402c42260403841c20030302044c20380c1980c1200c2d452001c1c0d07103000c0e01d44a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 175208606 1250 175207356 175207367
    0x40f140a03030c030215070c020907031503140115030c0e1003030c020904170a0201050a0f15090906060b03011202150a050d11040b04030c0806010902090d061109180a050c0a 76
    0x700140c2401140b60036502414000d1000540320000740310390500d245800040030f050040725071000d0307018005810001d07003280d010b03120720700301203d0f000c141c100d8007440d503a60070380c40840342242683c0f81c0d503c80482c81d03510760540074a58040c1d4855140c0d601c0141c1880b20b00c00c10441e004160f84c030000101310f010408079401c1081085600d4061b84c504040303980d182454814400300240034544400005216022558190300c0140034144420b421b2110a00d21a003400903100f009145800c802040a010401602c10354020918a0300c640303008294903540300a801c03e660800d170705c1005945904610b003400c40c944000c0746081095036000b41400c00480260003082d07400b41da40b110f5182950707000c149109001c02c4080d90010700301165082e40d03c584901d0007400c0001188103040306446014000b040ca2205070003540c00468019201003070060050712040068039140005220b40e000401c50a004e81e00c0324100302049400d400018000b0b03080c003452003400c40d2401407031212400f405204400710280d210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 175209856 1250 175208606 175208609
    0xb250309111507030e0a0f060c02030106170d1d0901060c1a01030f0b040302070b0a0201090501050105150f0307050d150513051009020c0312070305010e010b070b0c031806040305040f140a 82
    0x52030b10007032664105c1c000c244c038140701e50403004819001031030010f503841e407107050385403028400d4000303000c281e66a14015400c0d4405008401c1c0780c1d017000500d030340721602c15114545003a0102c203110403a0709110001c074005010030781002c0c3c001410b400030002030049408d814008184c00c0300d5540d0f0f080d8995151004c50301805040209940e2050340842c0c2814401c00070702003e01004450b03241d4039410341e500640208003c0008842c0d070350811000140e245010010103ca00d900d000185281c072092804006443c0d100401d013105000381442400091031691003040d000002811310781041038204010001784d02c007000c208138061400c1c10200070040100c148490200c03561aa000340c0c5800400b11040e040d03000340800141101c11000410140303550503003115040354a40c0d40905034591b201c40382c0d1400b510400c2d101409500e0940007146040507002e00440d88422701d013001c1180070301c0500409040c01410f83c5d00740d00042021800b4091900341d00c540200a10000c0c101c540088024400300f07556140c4e5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 175211106 1250 175209856 175209863
    0x6030a1410110409060605040806060607020a0e07030c03051f0504180b1302150304051b1c03020c010e040204080601090f090f060f0b040b0306040b250309111507 71
    0x402840c1440c4541040414071800c16401d040c080c0d071802108495041d00603210710050142801c500046060140342101d0a440500f006440315503103902c103200c0603610160040740c100b0300e03c0c41e00042d00c501e006411405000942d030082400b0760302c0b100003025940d0252898a813480d545d0000c160f003480180c1c0780030484600b6200070502c190400c40c006c80b080441100506034070000001c025014005441850301184200da840a18242d01d9071b0048131404119030041c0241e02414018518440c0c0b1b25160102103002007495240001401002100803085001103004d648140842c80302582c0141d54009070304402d403811814a0725140310103544500601c18010001e540308000001c03003001340c100d5030400760496481d011101c0186040c1000340310510f01b0318281d82c0303031420100280c5058003c0404c2d4440c01070040806450b0798803001c2c01020054408444001d101e10305620b51038030a07850341d8004080d618005990f41082c1030a105004000c070441e1703c0b5480e1400c0c41d90510f080c110a88502d03030b81 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 175212356 1250 175211106 175211123
    0x90a031d010c02280b19090302010c060b0609060703030b031209010c030e060c1e0124060f0e04051807150813030302091503010518070207051903060501060503010602060c0306030a 79
    0x10b59a613001000034103050300d80d00c460b5580c00105001c41c203403004107111003824600300c100130320801c8110381401040c00002e00082d0040c16100105000741c120141e45074009010a240c1880240081e6032507110250442c042503d910f81c080349880e00b40000041c07682d440c090301d03240900790000240761952420004052008030703601104540c43d90400d840501082d00120746241c6000d000c4144101c00e9440d2020f190b60a02d1802030506041e04d150000344000c03058414942420044140d80401d0f004281d81c00700204100460344680d194081c207405810b50180d0f4bc1e100040c4811100c1c10004950051a0500d0003262074900390341e03005190301d512259000980300b00c0d040038502240684581d040860b804411501140c00e81d40e4840000c60403200115071100440895015002c0096022200e042c05a00010340402c19800c107968034040130500001c0f803c5c4d515840303a841500300c543c2078122000203040480144031507038041044982002c940700c400fa003503150002c0040e64409044100800410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 175213606 1250 175212356 175212379
    0x501180201020c01230412050f01061422060b0409110c15090a0b0708010608061e06090a030804080319020604050c1c0510050403030f020a120e0c0603090a031d010c02 73
    0x400280648000154864100741d40c0c6c0d9961408600c0d4285a0106030307080d0040342d17044560000d052041c038040710303d000c1d92201100b04032030400060b44800100c00ca04129020040300100c0020710030f810180080800712500d0720304280c090022585024200418407e080001c5503004400081c90007024030040c0c10141690355013180e850030011094070040250104030f091002040d0003841440c1618401ea0307440116036101000c2150740400e045002030441e440d001034400714203000c3d005184021024010504007941d90780c0381505513000790302500440c2c0010400803a1400c040c2410608540a44001e21450a01d5160705441d1004403013089e21901080003030b140c0500c6000308012940f41c0000c2a0382038044014410320142c00300300c4080700040e24058140c0e00030200d074400e0380c21001c4542e40b441c00c400f400303a0204000b04103440f80003003c0e1003156011485a5140c03001148129000b03c00380ca800c0040f4580609042403000d0310501148217520030062071b9a01c10720410541d07404950070123003403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 175214856 1250 175213606 175213637
    0xa1707020f0d02060f0c160b07030e0f03041401030e0712060b09090d0f021b09090a0f030906030e06011202011b140c03060a0b03120a03020405100306030501180201020c01 75
    0x4031100e078000752a0181d4084003001d290082400303841407414500003005580c449403030340000c3c401d03544007080c07c40850801c040422244556203905c03501e107050004900382c010f000c072071038030941b2040c44403160b0002509001e14441e540c2c0748150503c2c2800c05004481007050150740700d89090080d4410107401016000c10300400c3c0c0c0065144503c081c0110042e0b0802c104a2904d60380c5c00c031141c0d000310740020740e0000b0791440002c8002c000230304031240b078803104148000c01003410320280040c1e0080c0b00e0715161102040d80000e00c01c000034840d844510166162280c050143d031031401c483d51664100400401248090360f1214808950901e030800040707280c0c0582880c24106000064003203000600e0003000210001880205000c1c100c4c12145030f6900d0319140760960308811582078068124008641c0721244070b801800d561041814050700346a2900c010890003141035411000181c0c50318010414440280b0804050f1410840d00c00881c03240754001075501d20781448524100701e0281c640308041c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 175216106 1250 175214856 175214863
    0x30809061e131502150105121c05040807060306030213111c270f02011103040e07030f0c02010b0a03080d060506070807030908060f060d110d120e04020a170702 70
    0x1c005102a0035120a216032030091081d146000d4281c00b540c50481401c01c01d400001e46600804600fa6000d11903804c0c8010f01004d04404603000f80284180b80d81c0caa010f40b014420920044030b1991141d0715035107410065803420780b0a40c0904185441d048003800540c4440f490204c90310403c1f803000c100811400c4c00000203220303901d00400c1c0d0525404000903081599042401140d8515408101a09900451201201101d18014080e40303800c07649400650242c880c680c804072258080d00e0800707941c2c08800040f130908640041c00a50f03a854003140e03117525481841d40001903440200550a1002d01041c45001c0c240400b03803140b030b800f01d007961a00143e504a030020740b001a241c69100c00b040e103044840c0c4d030443c4038102c01203800350341c01041400000483c544558024042d640c81515844140f0850751000c000540e102004400702c00c1940e2550000b640c0c0451041c100c041003074010303600003006891005d10462045004004807000c46038404460092184041c030005843d03207a4440a900c1e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 175217356 1250 175216106 175216147
    0x6010b030c04180e06073009230d03020a1b020f040c0801140609011d01030902100e0102150c0a11010e0d0908060604061d10030b09031b030403080906 66
    0x20fa1542464000c035031190790b80040c20303e1514003040315000e803500300c802c1d5a000c005851004c480ca80b1060715400c442d2000004403e80c0400000010b103c0890382c40b0b0340c520402c01d11403048980d0210740303a41d5444400b08030810b41900c00346411270818010400c01002d00e100c2c071301c4031032401140311065410340d2744003a42000080350040080001802e5114050601d02d024401d41d580c2090f80740b00503036030341405012600054016907c90b14110702c03180400c804229003903404d0703040503036402c0b203640161540c51082c01005000d0f181e450a0b190640002840c020301c4400380001c2805580c140410f828500d819614803e00714146002c0080c0141075080c01444840105003e03489034a901c0503017542c12411000c180c40d0700c01e0580e840c5036070740b02c284000e94030240704079140d141803541d00c000e051349590301300d03a040b01c0d9220002c0c648a9072915401c0540340181c038030401c1e54100142c1d4091440506041c4100b842509000d11f0400d0703d59183c0300c000b4000c41070103d000d070703000007040303200517601119110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 175218606 1250 175217356 175217369
    0xd0f020112020a0e0f030a020114070804090501030804090e010e06280204090204170601030206030c0f071406090c0a0e040b07091815051c060f0207080715110c06010b030c04 76
    0x15103035040000001e00324011210351500035503c01006417410308002c00c21800070340e0107840300780d00c1605480c59601c20b83d200704025900e1130418000440c0300002c48c01560300850140c440c0c84c4d01c1d2070806400d001100c1c00540c01680e5030b072410300c1d520305400c40407170740ca58006101801120030b003490580c9012140307504002e20065520005001c1055041a805002a80e503020300b5240054008038446940790001c1c0004dd61045062001a8042d04110010415820000c58690a0841507aa0030550201311403e5045075001542088030403079041242664506003160400c1c4914a003080c0042003c401030800b4240c820b901e400601c90300c0c000c050580007041144e031100161110305c01c600005000006012020300000740001502d4600b02445811041d94207181000c9544075640304001006070310040c120301902489500081100e000161441c103004640e0046010000c81d0288100c55010500000c2041c050240002d400800149141555000e01c0643d0342d94a90180700a0b490007140c3c40403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 175219856 1250 175218606 175218611
    0x306010306091713121a0a091e02150f120708061e0627060a050304050d08010303080f06040b09010b0c072301050715050906160e0d0f020112 62
    0x1041049940c404400c560188400c0c00105160100c0c41d48144100143c80300e40b1320b110282485400000014500c4180c450542c0c810460030700a405982207108480c68208140d4488058040c000d502000140508610742e03590113841c955030000b09560110501800700c914082800c80a2101e050100d80340c0945e001e02d81305403440c28000040c0350b10412290a400303221200025000b070001c42000090141c0001e01c4103090a14500001001071924000352042001e500000603441e100c0c500202581032203a55070070354901c3d0500b00685840740c0205060f01700a10b400040011a90155105402002002e1108480d0300c03075000040c05050707000c80050703028aa0800000d6803400100040440c1c005401c151010655590541360348486000c501002105400a10020300c1d03225000801c00c09216801c04012410f05031140002c9507c01c032610542ca5001c4000e012440452000703968941c801460b141c01841412400715032250030b1180001e104402c90b400d90400c40e80070302e4150921800b0300f03208 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 175221106 1250 175219856 175219859
    0x60f0907080d0810080610090b0103050709030813030b16110d020a020603100305030d020711010216300501020403020108150f100c050607080601090f05090c1b0f100c031a0405060f030601 82
    0x501d079124440c8d100d40010245028200c0410b03502900881e0701c10300f001d403540c003800c9140d5144c0c0081c40d4403050310243d000403012000702c0024000c0c00c01d503000e83c1d248850100c0c00310011401514407420104249a03a620507605103010300d600045001740319a059689a40700e86030351203500305106144d000200346000108208402070181c0d4003400003540a07000300b10486a20310016625034030494042d031002841c80a040c007412081382c1c0401e0b01051084041514488082103000c0000d0090100f1a1755940016007041507607807100b2a2904144100300e4407141c00310980c00112580315025803e4020482480c680400e0f60254071100c03074a581000036507905241c039030790003440010100d50182c00314081c41008900503290410b41400d031280a41544125150800030340c096401c2401030b14000c10a4000001e0000401d000300071103c00540d00800400d55032080d144203461462100348201407500e480c074990250701c0c4e8040c0e2500101a5000140e584440703000c10040c0124152094051141200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 175222356 1250 175221106 175221121
    0xd0512090109050d03020a0b130204050f06012304060f0903020603040f02030f0307020904060e01150b04180504030c02040b0114120a050a140708090c1002060f0907080d08100806 78
    0x500300035509aa40c041502e44400c100030001c052480050010303400a241c60000404031102182c121809080c2410000740641c006019a4000c0f1604954500c010040c40600d507080079004c00207650442da00300103a049a550b44d00f150190348506410400141d0890b1505402446690051500a080290340345000d09220a02d00c00d00303441203000f44101c4100720300e54240441680c02030344c1d0042034408251902d45682025000c4004003c5143d581c1d460040c240d0380c4200c4800004000034040d542d00c0e58030308100c1c06000b801c0b2503609a99141000c0c20403000950100441280a5048400007500d00409004840c0b580b00d8814542072040700050b4600d41118071201d19101d107500c10f030b09000650710b8992500580300b00c6405501030741030080206a4071030040080641c0015607001300c036002001240011710f2008804014005600880c0601580b0300f01c4c000355560041c440b0008089103464410160341d10030404441c98208020000403903508401002400000d050000c22a0001e007007058 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 175223606 1250 175222356 175222393
    0x71403030402131503020d02120105010602060403020c010e010503131109010801020903061b04150c0b0a0212070f02030d0c1809020903070f0e160309060510060908070b0301140d05 79
    0x21801d0384650700000004000f011180121101c1a0900c030400000e1441c55003444035260814104983c0b00085403c0103020b400309104550090920341c2c01400309060908010b820a21420040360401500c125060540d0760403400310707034001007030105031481c209107420b182030702030818030303000750f00000e000000981c40105402410b90a0300c110142c0e0265114018000c05607407600d000c0c4a0402402d05c0304000134172000300f80c0d980141490030401311078042a900c1c0c1000807000c840228500744c0c08248540d000e02c200c0c0400b64880c0c43ca041058440c0780b5084040c0da00d014407e00440d0b2140c6407a4074181c45403280404070000d51074080080222601c0e03035241c1340a9004440c0d2580280705402c1c0c005403180e201c0740290120781d4040d4081d80a80c54080f440a26045185002014140c890140e20001011840ba40d8440c40c400d8040c0f8100c18244080103107410b01e503520400d03942d4085002400410702401c01c4a0445c0c0b20200c5ca80314070314804000c2600205c1d415000b800354041c452003c2440b0201d40e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 175224856 1250 175223606 175223611
    0xb0a0f1d0106080304080a030c08040906060306030c050f01080c0315060d0e12130608041a040c06030606030902010527030313050a061707120e1006030203010b03062a07140303 77
    0x30b204154072061001e5070b900461186080691280d01643c001ca4000c120583c40c0790b0040200c180340c070303031100181c0d001d13540d080d8403190001f6955542001406003440c42603029204c100c552404428089000030402d04000c0c100e80001c110020100c0c2244489080300500c1a07030181503c2d0307d8528010001000b4840414250007902415a000d02c3d213807007a0040b6034107100348901b0111031504014003160080e0009108548002d4401e51b1241c29821b449100c6120358415054101801e00b0311708000c3c10364485a010780300341802c251130000182e13002015588088243c90024003129120440c40360310744020400981c16000c002a403060711010f1901c110282c500c15211981c3c415030b04c134070803220000c4c42c004030102c1c071403960041149144622000081046074404c0462101074400c803a42c00c250350441503010840ea41e03141001141401e0140392448041180681000d1074180c4160000382d4100d420304807401d02d041100840318143c602030f229243c0d000110187c411400c038449941e80d0303009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 175226106 1250 175224856 175224911
    0x30c040903080f0a050402010f05130e01080109022827110301090e0607122a0504030623220c030b0103140109030e01050c03040306020a0c031b020306040b0a0f 70
    0x40f0740c000b86051a0742c0c003895001c4d0358103035120f901c0e980342c445044070303680c10400348919001d10a07240000c022b40d1a01503076010300310140c0005002c103110701c104502054080d01c2c0103240005240c80958044c0e494920304110b400302010f0340130301c0e03c141865820323000486d201640c0403403030102c40302c2d203400c00c4102450584020300303403c1000f0b10354101c0c2d4039601e00c3c040f500322001407000310114606003055009000700c55800508440343d402c00e14014a840c0307140e10f5110380003400c040380400038080303280641a09425000800c3c850f4000c1c42c21031903504074008001e18481160015501c04080080200c80c46c4c440d08451401038081e1a85883c0486000030700c4140c0f00320501c00d6182040c100d061282100150b0304d6141d60114003801e04c015602e80c1c01c0200c04520303a01040c000000840c403140001c0c0900c076901e983d40c02c155940c519010b481806c41d5001600310303031b01081c00c03980103880001d441d9400680000000301c42d070361003030b020401800100c0201072646040c1403501c60305c121441080c4503c10fa4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 175227356 1250 175226106 175226131
    0x50d08090d06021e07080d020a1b060c02070605031b03060112090605040b0c090108011406130e060103110724090f03020721020901030f080403080f1305010908030703030b030c04090308 81
    0x8040c0d01811045c0215100605001c00c100441c80a0450710380c000c104000b400d08114000a949101c150b68030455000f0540e181611030654000c003907410702c10740000d4003240c1041421818840d481c50080f985002465100c0400080840c1140e03000b403040140c00c00002c0030a01a8500c3e0749004d002900c400e8808664106021b008125030711418030540e0619481030751130740c031141c0c41c14a0591041084000054206204201e440d101c40301c11500d50002d40041100d41d4510f04055000404486400110100c40c0c2d509000303800019115181d008600c520540c03c10009a554020711001040c480000800803200c80358800304054002c19150111182c40740e00500400e02c00318207030a001c017940402507003e54280d00510008441d0f400021003c4c2c01094028102a240d558031201c84d40220f1648104801c085110304443c4070580c2901d029240030328050000324a0688490340e07138050702c9001414180c0b590850708150310204100042040c005000348900e22007420301414500085d504601ca08a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 175228606 1250 175227356 175227397
    0xe12270306012d0b030a0b0a090c09030c0b1c020c190510050a02040506070b0405190506010e010603090b0606030718120b0901050405070b0703020c030111030906100e01050d08090d0602 81
    0x80601c3c8030b14003200c000300101c0f891551500c036040014901c4050281d404129042d01003001c4105105040404c1c0c01a101c640889040d41010380b07a8ad0030b00d074460014280d040010441001e160001c45403444100880540c650700c0c404030413400c001398807460903101032009100006100700000d010b4011402c10380c040010b500c90800850591180e4012241c20150070051040003c4d0790300303e002c0c0d210340070720103681c0c4040c0c0c0c0c00f410360100100b400c02600c8540c00040180050100d041c1294014445400d04000018040e2b0f5001c00449004000300d1140e04040009a20f560283d40a40c02d0240c50103031f10071015403038034101c1c903a02c131508406880c0c291000000408801c0c0500c01c0f203006076017140003000340c0d516040d44a083c1d584190401c804500504402440d140c4090140c00394041e00800c5a0383c07a803614000703003486d02c20000c01d03e40f048196004100407103000f410301c41e41501c80989246500b080c082c1014615842903880440d000703005c03488014180107c42d8003a1040c0c1c0c01c160700070364059 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 175229856 1250 175228606 175228679
    0x40609053702100c020f0603250305091b240a0207080102071a1b030901020405040c0806181003210e060415031d0109150e1227030601 59
    0x184100000290018140c003e124816405000780044032480140041318582e101d4020810a400944454480304c032000050440d41103a00350354611480c152804004503d00454031950300c8501e491031709401440d08240e40360341c1e100e8001d150002035044010a081e41c03400031544501ea8481c030018030050242d9130000c200008103008a450041c1c0201400517110503c520001d0400400703000200b0180700c01c41f40445030050300d4051445071078210f00058132185004c00740425940401090360400204804206880e594552691010301891002603400e1740c83d40c00e107900e150401e0b00050f04542000410132130785090314071900000129a0390722282d45000c4000d004160103140503039419200c2d5941c1c104d581c0c92180d030040240d40100e2182c4035901803400303661030848485503815100302251140440000307140d4011a20003a560f400100008000c0c1042110140540f03482d6000d85550310500901c040f0401c004410350340c0c1e000701600c00c0c03540c2d070b124481c076802520315903d000c002c821000703060807 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 175231106 1250 175229856 175229953
    0x105150102120c03130305070509060d0b0f0402210618030a1202071118040b09070807030305030a14010f03050706020115050f0d05010f02040e0f0603030a0804060905 73
    0x180181c008000801040d0400e20071a046070f4001106440b05005d444c0b09200307040890002140564050312100d82404180b01000500410550188101c4162040050f601c0c505050b0310405292150005444501c0011b440c12010b24500c2c240b0010340703400c05401e1700d0216503c3e02607c1c00506c1401411100403580d82c407801480c03140d1010480403031490300c2d6194503030020300e0480d01c0b03144880e22400c0384400080020711140a10282c181d2490104410010525080b60700000b100d00140100c03840c0425540d51003075140401010410084041030050140e500f21032800c0102d40200059903071546a03d4005504a00c002d0381d417841001c81c0014224010311420b9034600e030306000c0c500e282d030401c0c05010044003901c50040d0030148080740000030900078441c2c040c0030881541e0150f507652804803a00b201150141039680400405400c0c0403459070000212410b0403414100204240e550341450001400866000b4020340a0654050709081b403980c408003000050004c0d4152101000c42c69044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 175232356 1250 175231106 175231141
    0x306090c0f110f060f07030c090308030115120e0f0d03020310060c141608070807050a0905060a0b1204060f14180102090409080409050603030a090302040b060405030105070f020105 79
    0x4a81c4091054008034070401d00c08840c2d030544001c03250110f401c1d5000324038140d02118403800c11910103003400071041d4580a81c10080c01c1528142d1416415504d030b0040c0e42c801880795030601480300d0f8041c807180b4084e0304d2400e002d04040c0c83c20852004103448a94890040c0191482d9074000c0c0110f02120364042c0c07095a000b5854001c1c0040700f503050903c15550302c04240d8080d100d42c080701d514108212070030404400ba4142104000f4400c500d4200801e2401c00213030000c0800d0303000a1320910240c2c4800360308400716500c20f00301141d0703a19114003040c10307081503400030080e0450005165075101e0100e82024011440b540c2c00300110382c1c855800c00304881502070106001c1c159840460f01c031091502d202d4564500c050001446c1c0060500020200c1da08114101c889141c0031800700012207483c03044544c480c40541c0034500d1b100c1841c0005040b1215400001d100d41c1d51006805000e880305001c0d0b40c06880003074000c01490600ca0000381080d004142502e005600340000a02c400b80c00c00543ca1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 175233606 1250 175232356 175232381
    0x3030601020c011d01050702041409010902030705040207030203091005070b04030806090c0901021e010f0c170a02092b080a120e1b01030f0b0a060f030606021b04050405010b060316030609 82
    0x1c444d02c68203004455a41c40007100b60303400740d1145494401c030f602c001c0c10240501c0da0340000040950861040c0350400c0e510307a00941c0b28510611010000c81d4010044455a42048442c96515031000038103130749501030000080d1070551006d08100400d0f03085410240203400c2182c40010130b50310911025110f11998030305e203006030880030500c80034406080040004181681c00452400120b11070601103454013261180026400341c401d201c0c00d0310b9040c0c3c1c641c21254400c8154075000c604008200500c49203081c0e00840400d40b80b001da91920340c0503c0d03021385039004000380d0381e4440c40c88001700308038118400000000c0c031340070a03846010000079040204040303d9030b010000c0030405006500404507446904200d9864000740358050b55603500f0013003c4c28141c0c07031f03020360000c0a087c014100e03140350300003101f03550240b0a83d0408201c905101030201004840204403541c45190041c058501c0c0389841d60002c2010050240520b070fa64a45e1036503610903138003040000e0b50340468109a4800c0031011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 175234856 1250 175233606 175233647
    0xb0a051005132d0b09060d0b041e05010f0504020f04060e0105040b03030f0c0f0d0908060f0718030602091005030f0402151204050115050f0a0b0c1e03030601020c01 72
    0x1051030812a0021200d001200c0c40d0990320061850f00001600d0300144403002840c0c0ea0540650180f174804d00998000742d0070b9a51351940a400c0e5603010b00c04002078409055140c01c5100c2c2c40c0190900005805902e82c031200a000312041820000e01a10040d03404a2040945004546050405102c2e00701200e045080c1109946d02e880f061200401802989542500007000841c15107581c040084c141070b0a1680200702140700a1103d60400104584c028208140e042d000c00800000042030b82c0c01044a40d4110f1840d1a1448160303264403a4403018444620015000800c0c8032550380500340004042c1d03254100c0500d0242e00b210380b840102c035413440100e8500b000ca03025003441c60100c010f0703041e0155040e26092060322003143c000300450f0100d0301e81c2e4642d60b00e603891101d44420100180800e07103440744000c0c540000134089003418003035411405d1000c119504100410844203110104050b6405a01000004a1501d82e40120b071850301502c83c03a01c00009070b51190000340003458421100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 175236106 1250 175234856 175234879
    0x41104020904060308210c12060103151d01030c06181505040b03100302031005010305030304020409050c102006070507120c02120a020306070f09061407050106030b0a051005 76
    0x802000303410400000e50807690710880132001035240c0f00141004011614035403018140d40d035020b02800b00003850a0b000030014071541c00c130051340701070064002000b400c002c941a01300012445400c0d015070b20000f80710020580381d00c41c00c1c0c469040141660f010b150b01d00142611044140d52103056400000b20031882c0c00d10402503400303641d03808608209a032503c24a0700303540300d491040341e800c2542c1c00101082d40311000c0007145001c00252410a009650038802503246813903058030303800000d001a004075100c04503902004802c0c04141b1000b00c004041015166031520010264120303c615804018034000c40d04904510001d1518411340c1c183c0d03103140c6004100d955500d41400500090070502c642c020304400103035945112141d800048000520540a09004051403c480904020b05010b88003032030100c02c0c5e6005c0006015624181008503070b2088210308054144540c220140c115482c1a1000c030800409003409809643e004000313111030349071034030717840c8821815105d883c0d444440c00360b2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 175237356 1250 175236106 175236109
    0x90302010e04090804170c0a0b0d0b0f0915031605030a1403121806070f08011e030203060a09120504120b180a03080601030612050d0305180d0905180411 67
    0x8400303075a01409440840d041c1141e0756030300c490750403c0d0403020740201d8801009000160822035095101c03000c0b1481c2c00007902c0c00e04400701034481c01c000c500d1034a858100002094813510203280c41e103400581105071604d0310f000386103030a250301d1080c8bd2203402029080341c1200c2d005510401500d0009002c3d00f2110032a640b12000c01c1741c0c180304101c1601080c802d070742d9102c814020142c4645404060a030200011000483c00c03d03078000e00039010310508000700c201c165804003103e0b0560391107039a440b0130b00410b15840b0600c6840c2e5030000303606100b601c0801c000405941c0100c0300092040042c41c0221500c04010303216405140503034901186a49115800308250303002c419084007580064002c0c0d0b01040c8101ca041420758a02075001c64840800e000c0c580d649449040d0040040008604400141d60354040c0c6a0b0200b0301407200b01341d10f0707501142214180a0414074801107031800c40300c15440007200500421060f100d91403041c0c078500c085014003103440122612603070348030343c04010f003002d881c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 175238606 1250 175237356 175237367
    0x5040b090a090f0512040611160303050915030c040f050306010e13140d0315080102160204020a140d0509060a02031501030c090812180d050a06050402040b06040603020a020f010c09030201 82
    0x44143c4440c00d1504406000c2141840308010300c1c1d00da0600b15035950704048002d8a90300c01040b40c51115407141c500030103280c4050011200f40c9516103032040c0d0b00e481a60000304010700c610141c0c0c040034000401d00030060400001081100c844264500c0702554903401c044e100d040920442c0d6001010030001103522000105401000b44524030322500b6030a801c04061070300041c0100000400d0340c403078941100e400201c5981004010120080d854a41c00400b1001d441d816588001e0003039401051046006002c0d20030a254003a642d000307262103a860880319409020141d238024038038000c200100d40c80058900880748580c400c41241c4c04003840701c10044005014603c9a90104805000003003200702040c072a1245070a200308840c0d4031280c103400482042d80755184450300c1204001c5640c40003440206105101d0358104070300040036a51400420b0140000b19030b480c2e44680c0004020500541640c05000c100c402c41d0700b10742000601200e0702d42202c0e480882d80c404180001420070041d071040c1d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 175239856 1250 175238606 175238621
    0x3070b1e030c0409020304030509010e0a0503030d050c040e04050703030806031603080c0f0105070c17070b011802071b061808070b0a03020d05130308070201020a050406080703090b09100605040b090a 87
    0x20b049840c10b80d4581d941c0c8101e800940f0200c1c0000c0d4000f4600c40650f83c8048000800d00c0e08403015a1a07500d018002940c9118440e9116140307500e400c001658480f000041c2c40080154001940311440c081c81d00036100c0d18140011004034480b240840c0f201d040c009440f0400c2e413100d0081c08401c07410b50b1504000d50708207401c1005d00e031140f801a005001000e0044900528071074650042c240c00b130380703800d02880104643d240c400c08014002400490005000e0a0440b00d5103e60b00203a01c16007040c5101070304c0340510140c84082c40c1c9408550101c10b03055a4011500596900d8200702000d8a98016040b141d1047cac08481c0e102400a0101d10761145c0140302d020001c1c00c1c010b1500051961700001d4600844107010040c500a84440500d81c1154046a10a0082c0b00841c90482d40280152107400b8034000c4e0b1040007040c4002840f1640241e2045030040c8c5c00415403d0903150621380d1650fa1041000b1403082281450400034660800e4044c0c200d400341e00411031105a541c0c00918001000794 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 175241106 1250 175239856 175239871
    0x30b04020d0c081b070f1101090f150f020f1b0105090d080c071703030106030917070501060609060309020618010327120c050c0d0312140603070b1e03 66
    0x2042400524551407058140e82d6840d0340f200c4001e4940000400c02605800c218031060348000c101c1e28000840b00c0d464092a10f0380a0481e5100c42d60520048943c0740c86904045040d201200c0c01060641e412041c02120316495a40c1c081041364100301240ca5510240c0741c40380d0b55010300140520551058689450303510180f40c880d00b00202e102c00140113a882420035a1041d0001445002c0d2103c14000d8001811100b0001501c4689410066a40c3c1c80140b0602c0c04140d0340d104040300b0052090140c00300c00c501c09400c1c503107521840c10054000e181d80d220b008003140307081c1e0b1300044641c0280070322899039400038601420160011602c0090204564805041503078400345030300080a803d824049100d040800170303800303149130b103001c007a008803035564070082c01080503440f00004c00000368103046440968603c10641540c2c0f4085ea14861500d00040000b414001880311059070b10103075a1181c50110b0823105e04507503601d42a0400d00c28140c400455203040c0c43c0080280300d0110042d5085103c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 175242356 1250 175241106 175241111
    0x6020c06060f10122c010c052106011209200f01050d110c0f0a061104140409030e0604090902031005040305090108090316030c060e061014010509030601030b041202120a030b04 77
    0x30749101c0f01c040c0701c62440301d0380050303804100c1805d11900300b4071030030700450154181240f5201031042d00d0003150324081c0d00761003110180c000103440c0307910580303070042e00442c0385409010514071450030810080c03a8401d19800b0301045022420710f41f409003040e130055841a103c517445d10a000c0900070190103c901e810030004001c000070030b071070702c410000403015414410140c0f440004901d0004152603800c424046000c2041c8070070b0007408004480c01c075400b90200e4000035801050716003580e154144510321584420b000c01c1c0000c0ca0491a0040c4100d01c3c4203d0665230003a1100740b204044410903640940055010301000c44a54040c4203071940046050b0222400c00e5040400324081d0a2000000c500080508104100b000f0542c0504048203081801608082c5844121404210504e100b07000728400500e082c80010390049040700e01c1d041014041c0c0d02150303100d08000e4800c81e02500c084a1582a420b600c840340c1c1e06c0454104002c1c16051b105d00d20744600c0f00c904801406010006581c03007507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 175243606 1250 175242356 175242371
    0x130b0d0b040303050108150702030910170c090f0d0f02010305040c030503030103080a0807051204031209050105090d0206060102030712080a0e100902010f0507080f0c01140406020c06060f1012 84
    0x1425016030520030340c030039940030460b503040c52000e504052002c0041c016049100b020b0000c01703600441030b125081d00644846a1040c06171070100c4010070201c00b12406e0346226424046c10031000f20080041040980300c41d100d1035003071014801c45100030752001c0c2049010b0380b42c0900541c42034100e507801a0280c0381000f4400d0322030322014110f600aa02c211440310b40082e6003190320382c0110f5055030040c43c60601c0c42c01d103180d02000c03407510b13440140000d0400242800c010b0f04510030b03a110780802900140200000d281c035034003103913940321040c4035100580300f2140081d11942c03001048442042d4451440c80e441540440c05440c103080180010303110603107a40b43d0040302001007005a0b02d40b64032000218100c0344500002d0302c0321400c0c1d00003c1c00c1100403c40741c0082600c0908031000d14a03918445030f0780d11600140c1a00400011840b03640460042041c001449115006400c41201c0141030ba485c2e41c0320303030003000b49c15040d048806410084084100c0d00050040074031203040c0361507000c04100c51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 175244856 1250 175243606 175243613
    0xa032a0b060a050306180c0108072003040b0d050a0f0605030a0605190f0c0e12030f030405010e010c090906051c020d05010b0406082b0e1207031a0406051005130b0d 72
    0x240044500030340d022081c0144107a001c204007c0d92a8806080c2080d141d6030074007200041c04005c0084500b28026003507030441410403010002c0324000e100c032500103500c0d000504540d40c060030081d50708100160500a14000c030036600c4c810001145c0d0000c0003010541866510f02018140c020010164113115040c1544d030140c007030061110700e082d81040000c22509510b00980cc1c0d422034000b150040b41108690807003140008112240c0710301c0e12230029181d9031140b610034091f01a2048044c01d40d400e00d0340c02a07895800c980d514041c0e507200d00c0c0602945440d070041c41780e0010804042a0b0700303580c1d00030203070160610341e06014065000c1c000105a1511a01c080b8007902e010780d01050240d03000c50764846030740c5070318120803c9131250b0040740c0030055003040380105562032440c0d00511484141d002a20031003002c00c02d1400550b4401c4450b25080402c10751001d00b8a170480d0141e0340c0c0c07403c00c00081d119680703a4a0400c00e540000305039180310301c0000c8150b0001c050b00740341da51700a9005a07980d00070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 175246106 1250 175244856 175244863
    0x90d120f060f06030f0509030d150f060f0206070203090303032d01060906030f0603050c0105030601090e13030905010503070212160c090207060b1c150609020c0a032a0b060a0503 78
    0x5000c00d845400d402e5464201c004045030309014241d0602403802080c0000c40741d01008035030725420341c1c100108004074903120340c158034015680f03c034940e040c085000081403904415013203201500394080c1c0e9103d9888510036170b00c82c442c1510703050b4182c2040000036801c000322881c4a42d1a0000300a4603000184412010328a410a0b0411030101d034407100c0405c42540e03d801a2800300c0e030b450750140300c030900d0b5a4032550350303008442065041c4540400001c002e03034856030b080c00041a100c100c420482c00c0c40900030103103c0c8014419800601000008100d950003501102d01405069004100c001089481008507030401555007403500c40078613003540030807a08450b000140040f0741c2c006039569054503102c0c0440342c810b403046000b100d24000001039102a03c00c6e0003521a00f26910030000000303094014020507480e04000700152000c80c60b400e02040c001000c1c3c052500c42e03207030003110842c1c00c4060510282c50702c1c070f00c01001e4410038500d40020003c00c130b0705810181c064100b0308000c0c0c955000a0a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 175247356 1250 175246106 175246109
    0x123040c02010902041a03190807020a030b01050118180e0304120b061201060302031c0504120b0412020102090a0512011b17100308090108100b03070908010e0105090d120f06 76
    0x5030f4440c0d48602c1903140511500391100c1d0044141e800c0040002c0110381c03642003d2200400c84040181d0384000d0000c1081210400703907009141c800102c0c0c41b8500b030083d00300280074640c00100601e24044107040c07807900940503a4142e101c86140b0001581e1080c0190011142130907460005201c00038840302400180302c0c3c098441c0c030801900389490810301c4405007800070002c4480c0e051210800141c1c401062030391501c003614402d094108000e0405032420701c50780d8070502e15125100d01d0320060024102010340911310481d0f501c1d1014191480072401d1f402844200b95000c03444060401440c0381104c0c8114a0100e00300011a6603820000405404201d688c0c0c1103003c00c00c2c011000e02000e01e0319102c0c03544041440d40d2001e40d10b003946c88001e401d0150b0040705043c4030142c0c0108119000a510120040031302010860b030324503000100404800041c45481c05942c202243d203e8405018000d00d485403020000800b02160003a40442ea284840c6081c00c804d1a610540084807050310f006290 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 175248606 1250 175247356 175247381
    0x4090212011a0102101103041b120602091801030215092b050d1b0206090409050a110a06170a0c172401030506010804081c020d060503150906012304 65
    0x1c1c0b601141d400003900380700039400e100e007140f0700d0007a000c3c0c4280c0441e000d90780c115400c2458143c440040c16410001d801103600300d4035412031f4814214040101a40080012090507610444000c0d000480d9502f00842070000943c04015200081ca0241d0f10101a0158150041107003101c0700064035440300d80101c0b503074100801c2c1520301c01103040c810108600d040c401c0592824000c8400c01c88041d6002c440a403c0080c420701c0d0001b40240140e6682d0010000702e50800e0503115862024945602114a1044554059012140001291381c050600440e8511065070001495940c084c21200100581a00e403420b00c04014804002c0071501d202061091111614030201d405643d803442000088078580c1504142c03d15040000f5030340d03c004490340003075002d441c0545425500b1445d60501030141c0b80c030018540f001c00d130420024000e401000458074254141c50160040c09580301c40d50804490418040e03124000400c400350181103032190210814244205080c159400981600c1040d003602 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 175249856 1250 175248606 175248641
    0x405070203120f0f0105011d010309060609020c01290114030c04030c030c18020c03090f040204080307081803030906070311010b0d0605090609031303020103020904020d020301081e030f07020409021201 88
    0x110310301421346003070144c0000d007811120a50b40300c6101c500400117940c810704050301d8800300400c024032a00854090a00c500c02035443d09110a1541e008041103810b079001c000344506ca004800348040c012600c016010b031740b92240881d8800d00b04045510290150315044c1007003100101007a00030450070302441c45807072140804c91814010010304080d2800d42d000b86481004001e00601c0c000003260350150050310005c200c0c4008800140081c042da60040159020004065042240c140020280304420b01d0601d1001d440d50701c00d065403070041c651300c141c20841c200308180c08a0300400324404140c1d510300020501100707d070080756070605686030895900d6290020b00079020401e1040c55030004020005508019010403020000702d03035031201905066002900072480d46458045504000c1c222070259039a5a481c0c4c045a9985510075008004a0801e580c482c0c01d0000132044580e044e00404040307080100f95000c0000034981c0c1c400c2243c0c05400904001a4020280982140c202240b080c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 175251106 1250 175249856 175249861
    0x111c030207150201020a0c240204080f160f0531020d0b0301050402150c010605040912080f01050105030a05090f010906060918020a061b060e101109030a020405070203120f 75
    0x31049100b511540840569006000340d448160b40701d00581c90700c40e0071010142440154030000b416020380000c4003141d043c000100800c241d18001200c0039140796080880d070540c0c41c444a00010b00d40c5901408040900c1e02d541000145820580348100380013801460941584408040e03616500807041440025008520711040c0701d0f091250615088095009200ca8501640002d2a540ca040c3c0621080e01000c103120b50400e0b0b00358810f5014010140c02080348000ea4101107000c0f03240c24000700c0011343c181c03000600015510898504a03881a158107046850303007400070014002c000c01c40d0005210707804038188030b00801d0080ca070344980142c0e1b00084250030001d0803401d5450a00c1410b003480c440500b040e0058892200403c121849131a112032a0f20244007440719040031144050502400c00304116014100810440346d61100035a0030030801901001c00c104e2405920040703580f41c2c004010703040260401da0403440e031040e80351050360b191144502030403000d40c900340c802c03d090344800c804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 175252356 1250 175251106 175251119
    0x90f030e19031e0c080c040c02030f0706020703050702100e2110020904060509010e01060f0309081803030d0207140712080417101d0d031503111c030207 67
    0x100122518400e0719064040303480c90303100384900c649500c002040b0a4540310702e9601c1140044050060550103103046102680e2107441550b1101d1480c000c0e0b05c0b81e85400b0f41e50200702d000104490714401e00e41c2d80d581c00e140003500c61400a4010040603810f20504101903401a07071000c07010203401e0266184e0a108a050b0000c0c80b0072850309500352908d04140d00d070340100c944400038800f1090029a000540d903000e80c4008140646019807109421894150010034001d01100059040e100195164018410594070850942c1c0340034001400440d000c02ca041003200c03071051182c071001d00190440e443e050012401900f01c1c0e0050b00c0c10b440e04554082e0160803060300f4081c4c880106400495160802c00540300c0c000d8038030541c4a441c040e211080d8240010700070511080c10708001c0043c2c204100c0541504500350710480c1074082410b03006184c01d5500c10780c0684941403400030b000309040203660960391000030702c0d8070b0b180c2000c2e0f10800d5039031030f0020000403030080c402c041d00c2503000d41041881c3c0354 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 175253606 1250 175252356 175252367
    0xd0905030606010c062309030d0f060f030305070c0816050a090b220b1306060305070f02070b090f03010f02041d01080c04020a03020d051006201504030210090f03 71
    0x4010500c240c1061050040030380c2e0124548a0b2940c208400280080e50390195484503200d07031094a024030200030411000d1076020000d014804841181070110098080c0d02da400c03601140101e00f194a8081014400b00b4403030405008400d1140c0005e9401a40316203500e0f1411140452180e03286500d00d0041c805414002c03c9900201200b040a11401741503c000504894180040301c00449004911205030052500041003041016100300341c0009810042c4000c0e00c041d010300b102103403c00e03000c50205407140c50065402600350b409800a1814222460180e60015200341d40c044010058808039a40a12030341049210300e26005989628000840c1d000c00d6a060303049501a00b0700c401009010004120180f200d0070450700166038040c2d404044d4020f00441c10050360181c0f81c0002c22100301011440601940d0941c2ca84000f07211002800c983d00b00b840d2004030501390001042942501e134980907c54000784280140c58a042c40f56440b902101c030800d00584880d42d80703444110074150000f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 175254856 1250 175253606 175253609
    0xc03010c031b0c05160b09041406090c0901020f070b1902030301060c0f2a1a13050d0807080a0810050604030506070c0602090a080106090b09040c060f031d0d09 70
    0x1401c00b40076900d034072900c084005401c0041c280c140300304041900d0821809000300c0c061380b9060221038085c40d490f06082012a0040e4401c503005a2402080d0400c00c0a002042c522070403008101c6083e070b6072490301c03c1610741c01200340726065100c0c04800b0004050305000c0d0b400640789000800c3e80300e07030071800204c4248021051080940d0030400c014000f095022441e44c0c502c5800c003036206040140c51030200e080072078060001c500503000325a01c00c214072905c0d070050112692400846200304050212003400d00c00c039a805460146003078010840303420000d02140405001d501d07100d04001d2941c40f031a04a50180d08031000180c030b84020003188074180101b0300c003e000c095484909290442c0c1c0d9080d40e404010744010103010044c45008108070319070f0111401020041c00100f01581e54942d000d000e0920350040c040c0950801130100d2681c1401800381e03124903008001e10301c60b585032840a40c0d10310001c5154104040e154103a540c5901240c038461600400244010500900340f110f0040c11800e29 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 175256106 1250 175254856 175254881
    0x80a0506011e15020c0d050d0e0604060905040b04090813060201050702030f04090b0a1a0703031a2115010e010510110c040b01180303050301030c080109020a060804110a080c0301 78
    0x10104031041c8200500030000070f0721081810184480600d034410781c41c140003082d1650340070350f01018440400c00085140b850641045d1210b200a9030f1142c204080d500650089900180d090382c0104201d28154102d40380c900310180000071a03c14a0319074043d9907200000c0000c0070001c210382005099030920543d5400f500500c080c42c14104400c0030741e0954400d604c42d69803010b48881085910b55030300d0040c040207180c1012032030008110103800003d41d802541c0190080b0380341c0100c03c408031000392440d80003078400601101c810810f4101a030036680c214004001c1d01c4c400c1070580480701c0d05640019000c0c140400c1244140e614002c10015401250300c141c2c400c0210380c2001510b14140001c0001480108a0f808030b00b48000a0040703507400019441401c41222060b0b001050581010046060b203000380d03d41d038060b03525000740600341c2d0051078000350021920300e403c00c43c4502c032780c081a0308035106500035480032591100190a5079041c0c0c1081c100c60308803080841c00c6240910814032030f03018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 175257356 1250 175256106 175256129
    0x2030f01172a03101a0d0203032d070f11030a0f06230118060605040609031e050312010501020d0f170406140f04062009131104080a050601 61
    0x40c10381c1c050303103039000110644900040c281d892640014101c82e140c9034004040c085461540704400c006010f8101e44104120071040014030298030305000c0e482021072030700a0f00035450008042d0a146034405200a0440801203a01c2401000d4404c030b4003c1c03855070f014138205041200e80e410030070b52280141c1012480313584070482d00300c005141072030b00e0403000e508800009003482c1202d520b44400c641441000c41c43d0708000001242c0000e80380d1703c002c61103100403810007900344c54441c10740b080d210301d0040e08040342c0401c408100080d140340110780d8409020250003880e6906960b814030f5600214569400e1091887c0184115641000301d2800b080c15440e050320010080702d409802c155000c01081c0c10052000c0029048c00502d412115040740001101e044ac1e16280602900400341601c0494220303003480201058086003000b210101504c5c4d4800c6850b007881d00007000380e282041089148285e4032038208000c00103800c00038000070804c02c8090281c0000514100d0708080058011030442c0b00b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 175258606 1250 175257356 175257389
    0x40f06030e10050708060d0201020102160f051608030706051005060c010c031104211109011d07020d051204030c050706020a020f04053d140102010e070e15010c0804030602030f01 78
    0x70381c17022440c0d42140b019601400ca916090004078064410120000c0d01c80410305940810400002a030100081c040d0060307840c0c0c0410495503202c1709000e84620105c540c420b020391b0001c1021544015003000f41c403207010901503038031004114650081c40701d031441c59544131034140030550180102071140d45086040c91405041c240c00c0c8842c04601d140641d15041280111001c100c01c0b0080088441001001e144040d0394464552440384c1480841d03848078448a80031483d07182c0000b900303d0035525180c03291410f00c44008100325080c00d00800640420036031200c50008500d051050030098101a40582285211401030045103191942101c2c001c601d02400c1100702d0300c0c0429003421039000002c07087c401060600c80c0024407614001356117498402c1d9800090300d070342da00204000580007a0000c0c020303584040301041d119601c40c0728007410401030400040e00c0c500022100705a02c0b00c141801c1d290780c001a101c1002640041d041102c0b81a800003d205034036002c3d40d18280180481c0c2c96045071076 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 175259856 1250 175258606 175258621
    0xc031b0c0a090f1b0210020c0102121f240309020102030d0c08010603061d0a0c05040f12020909060708150105040305120d0e060408040302010302030c04120b0601090812040b030c040f06030e1005 85
    0x6c0819526102c644c6902040030029040290100e4076000500d42c46005907040002c0f00351a8030504580c101c48031405032000040701c0c0b0b280c01c43c40c01e40c66805000502035501919096003c2c004400040741103020400c20541070303580380d2203804d4403035182c0d50312a2055810310401408948054100000304420000c20152249900b169240d00000024006c900307240f034524241c1e6a805250840b40c545c900941300880e2a0940e000c1154600c0c1c002c56102c80540ca030024019164402a201c00d40010800000100d4000481c500303151100d406250852800c0d41e0380e100d8504198440034040031b52040003420b00903000c07490041d031110181201c05013035a800d065540380d42c54401c3d480000c1c1410f80100c001902c40e440070081d500100929000100305440510b00f090007414106ca40d0341c0441c0d040300c80428006000111801507409030455545070901f0035203a4070f041d4000401e0704181701810000400c4610782a20740c0402405141c4021440f90704641030303c1e0520a18007551410249003208100f1341 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 175261106 1250 175259856 175259863
    0x105090c040302061b01060302121f09021c15140f100f1406071e0606090e0304050402090a031704031a07090603020c0106080d0e090604020c031b0c0a090f1b02 70
    0x640c0030210409003a17844070740180c00f41426a001940c0b01e0b0200c07411100d00000403c082c002003a4400c44102a80e4511445404550403244003941100c0740c44c054003516094007105a8004d802a000c108200724050070181c1a50b9003000032002c41800d060a10680441c403580898000e004a5018454241054440810100d240c440c3d048171a0b0030b000129101d4480300300701d400d89500b00507082480011840c1c880a00030350307a00300703c0b0454944130001075100c803c1d200e100c0c1c0f001c800c200510b01d49131401c0b0420003c3d42001162540c40418001c00200160058060b50170b44980410328035140c40c81c43c1031207014500d2070f2500e60b03040380711101000340c904c0e8001a203005480050400580310001021014010400c17904001d00510645441510280d004420b5000307220084406a1855840005000507801650f5002c6690342c0700340f14410710350b4074800c40c8142c08540d10b42200c814000032800a90451010792105140d02c0d03940018a8032a41d1900403514006413843d02d240d00e89103080d000959 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 175262356 1250 175261106 175261117
    0x13602011413060512070e010807030c1701030309030b070c0203191a0702010f0c020f03030411121212010806070c1212060305031305010804081c090602120105090c04030206 76
    0x1089500581c0412100001040d110300c52400d05210180700d48a08000d0020751003940c40d0551003800000080364140300b04c040140805040c0d485c1030441c2c44901041d13014050221118082c8001840702040d614084007140c5e008501a590700707218149103040040e40c50201814003030801c0403c444500c09a1400242c00d100d401403050b4401801d040e40c100304034440340c5000034849040c2d90070188a40a035054100c0910120310460030800001019000da0740c5d58040790104036590424400140400c00d10104c058501d200601105207004404600d141003001005c45c5410344840400c281807814141091a409040c244004041c20308040d0406091015020f034010b0840c4100106001118401d20100c038507460000424002c81e506c0385040d80d203039089500c0c01d550103170b208140010b55611400465001d59040f1208620f04806520700c80c03500c0700c4400020040549030b001c0140042c0b090300c020041d00e1540d00300000e07554142800c00c14440c1025002c1011103900340300501c0580d079003404a80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 175263606 1250 175262356 175262359
    0xc03040803192312041a040606360e0f030f030a1118151e070203060f240103060b04030b040209010510020c0402070c0e0408070b0c07030f23030108013602 68
    0x1101507449160594140c101c401e6070101c203242d91b0083c0401c0014035044113080d02c250308411a0b8007903642c1850000c003031403803100c185410180d0315640e00304925580500400010700b4207842000500c0c5684d1880c4d548050034980400c0700c008204031403400701d84074000c0c140c959400c8003880d04040e00001c942e110416034806100c0c060405407200300321001011984224041d00c44040584080c005140403600300900a078040e000d02c0000600964405c1c4c000c910540000421902e007415007091544806c980c0740c103040c107041c0c0c0d8550101cbc4081c3c0e2407010b08021803142e040900d5500d0f0a02c14401c183d207069118900540364214624442900410207074240c0c1e20070344005803207040d507003004d1200c2c0c500ca034402800003681200f80024400d038503004065140c02650a2041d40d210910f01180c98450174101800251070380c0b204082c003e21540740803c04146207080340452100340d0490040f01d62081c1d00040850307669213080041c801c181c0c01c0d4521458907403601c07850034044111008054514412000707 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 175264856 1250 175263606 175263637
    0x7230a200102011e0f0e0d020d1103030f160c0b010e150307380f03040309060906050729150a060e130b120a060c090806090a03050c030408031923 64
    0x1d03036000d429580901c582100e01b1003268000152514040d4940000e0b500050010f46406070ba0003081c0030000480f8040c82c0c1142d141412071307a42e80c070b000c842c01140c401203000b04002c00070450301003050342c0c2c0e03283e0180041840900307542c20000024101201d45140da14006d4002440401c03440314080103001e03048000000c0a001010511160041260f98021100d0804000308104004000603000b0f548198401c0d1038101013140c441c80300355601c551900c07810000031020851075002440c90312050052a1024031f001200780e02050f079081c041030301120301200ca02a200d011821314030709401030700000c0031241886514000c2da500403c0d000a010b9490804032911b17080e00344e80d00d880300c0c01304814401042080e529861094035010010741981609140041c41d80c450218040d003012801c24050743d44040100042c002640c0e041d02c4607005040d4004080c00b090100051140d002c3c4010280702100c0200850a501c071b4100c00b4000b0b8004020000188200000c4080120b40c2e52040f61580740311100348 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 175266106 1250 175264856 175264871
    0xc1203050c070b0a06030b0606121933090e0303011a04050a0b0c010f05130f020114040b040f0b0406090e060a03060e060901050108010203090307230a200102011e 71
    0x40900601c00c0c074200500b042c0c04401003040c8540c81351720082c1681d1042c0820300d4a07444541c1044101d01444200d04c10340350b5810b0200342041c040b6685c0c0300d61800d1083c03010540c403000b2003080348280422a030008404240500340016420090800000742c00d038100d0401140c6660300116070349000500450440a0114070030668551811050310011b0000070141000b813900c64075491560380000001400035820b01c1d4100c0203550301030040fa4401e45140740706c1c41a1031040c3d02e5041a10110355000da040c40f40b1f0068032120450080c000380080c01300040040e030794600d01800b012402e62035600c100c503910300600060240d1031307024214504844e0007080084258a82e0800070780c5514440e4001084140b602c414040c00200211340c1c1e03485500b0040003002540e030f03140550342c03d038030084680702c185810802013440040d004031540080c3c410500c0103100340541e00902c140c54409846400d50f02042940b808506500403007444400040d0207100a200219042003d2004241d15003013603004aa160f052 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 175267356 1250 175266106 175266121
    0x61b02061201060207030c050103050f0402130e1c0810060203070f03020708010906090201030e0d091703160b0f1509010303211401060906050304080a14160302010b0f010c120305 78
    0x40d41d103a2103000302211140e59589002940d1034850f480210b8084028260000f4550300902c6103520515000000c00c0142d40c0d06c0c0d00300081404110081003c8541d20003184440913420000000303980b030180030703241c41403c3c01007000c3c5c041c3c5001019401c1c90012030400344a61540070003034551540d405506001100e201340303026030030b140d0207412801c140e40c80d0480b402c0034040185c10a820082c000c2c0c03010001c11094051058680c0110410f070301c04142611020400d001c3c1000c800d000510105060340d0a00714803054148207900302240a5814150301e200f800504019441c10980140340b030100010f41d01c0d02c1c440071402c122014840501070240c4400d401d441c4000010020450f02c01d40c420030088220994040405071380c013070091900003941c0d5000401d810380540c048138011a00030344403e0400c0c1000d4822030721b060103c0c0c00f04480580c2070140a6400f42e484882c8041c207803180c0c00224030b44505000740100307412000c800504000e40c074994000401c090489107000e003946850003280359032310490b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 175268606 1250 175267356 175267369
    0x130902030c1204030c1a060a061b06021606060e090a02040207031403090d0305070306081c05130801051b030712110c0d05030109050106090b0307030222030302030a031104061b02 78
    0x1070304050000891081008040d40150b044241c0d44c49003003106c09004c901c0d20b8038000c008044070001d40015001c4803d2118500805c2c100300348103c02e08000505140c3c0d65030314000d0380c1001044280030640545800c081200c0340c00740502501c03681000c1481803400c084980e64131070462502a02499002582034249403240c0c0160404890b59003502e86d42e82000080550f075111807030301a000003407074100403c0d050b921a00403042250183c0c1c0040c0040f07034585500e0043c51680000034018001c080017042c03040d40b840d800d070400502e40c1400005081ca4550131054411b040401c6042014100704100701c80f05070031010205000424410001d000100c0007094040b9114100f540d0040d4032855503080b0302198000001e44c141ca07101da50520031642c1e03613001a1901c0001d402032411040c000c0c03001441e514801c0c1e01802c401d020200c40c5403040041c88145000b0369902e82c0065005810000d1460707500e98150040840e241d51608400d0700e428681440181000010741074031b100107000302034038015550b605 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 175269856 1250 175268606 175268617
    0xd05030c1810050703030b01030b06070602131a0403060b0307050904060b01141305030c09040c2106060b030f060915010f11060703051b03010b0406120f060801020a0e0303130902030c 80
    0x1d4154005055034801c0a003031600134802c100c0001342403040343e0f4201d5200307000788005918080c103054144181c076074404020f50408204080c01d0100c085001500c803041119001c1101500401103a581c1e041d0308068007503803403440303031107000350300014042000da21240314583d8801c1d00f01c3c0f0300180c10508031004888191040000300358845010030032a882ca0882d641480c1211001c0301220100c1c54008180000420100c0e406000400071103000c0140a0b60b14125080c16103103030038691071603d50707a6900002c648158016092030708010041021841d8088101a004102111010480e1505860220481400b4022a8100000e022042145900408001c4803c0201b2420748450f460004d074010300400c1304444051440e17190040040d0074540b0013044078107845038880000c0c80c10342001c000b41c4030100e0984501c28110340d81e00c2c41e00c50950184c414a8043c00708a40056591010b91800600c10b0304104640d1340710360020070154030501c0c09080c00c07000320345481c0e0300036882e50b56029281d103050088 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 175271106 1250 175269856 175269859
    0x20f030604150c140f03060111030d1505040e1b0310050c090a0506191d030607020c100216030620070f0201021006062001021c0912020d05030c18 64
    0x1610140000c100784030881c41240c4205801c104480000d48008a80c4c0c5941e048045a8203082006075102da800520010355020b10103041c26085911032400f8186076031b200c128400c8101d0741e120990802c03000c0100c0c0c01401000111805e0001844840c1483d0711410f20160302c0c1c194013400c0800c0e08003901c00b4420b6503c41250389004002d280f803c6942d40c2401d80c042281d02c4e1041e40c0321070b008107035131801d44107840e5141001200300382c5461001c1c0c07040c2c0b0381e85c2400d4041d1402e84c4190940384c603140d81c00c0044510880181d4081c0c03514004000a100003940300ca44103409540050119081102c03406502c036003101e41142010a07082d0124440c01c66405290310b82c1c1c0c0080c41d000940105110300d082c06051128400c1c3c0c2128170519041c04903508030f0340580224800510390460040712000ca40340070b6804496050300051409040c0c4410790491005045084039480c0c03141c0e85001440560790040001c2c40041c000f420094450002c001d081c3e1000030511101048003044101189090b2030103015540ca0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 175272356 1250 175271106 175271113
    0x3020708240601030504080f030402060706020318010c0e03280602040b0a0e1e04020d0b13060f0506030903030c0703170a1e0603030504060f0e1009061d100507020f03 73
    0x4524600503040c038204000090001295002c1203095100f842540d1003150070803503081c101980802c110310113900192003030b07910000c00d00003003010500c07520041d40203007104a190280000c0314010f4600b0344000640c0c904c140000307501c407040c1d41c0e1404104440d88010340046082049a6602186454916100050003a40c404140400c240503000018078942c0e045488201c1241600e80400c550000749500c03c0c000349000722700104180c102500034040021040c500412002c1004008c92a40c808844039a01c00d50f03200d21040002031114000503001e070130261855855450a40c1841d6903a22006d40155003000000400400b4140b00340300c0498a1041d1507070100440c1007140c1c03000c01404c01080912038a170140d10015914805a20507601180d030300d500d0b10750030301d4030b0241c0940f400030000304014207000c203400d1a040e40d81d0b2034400040ba5491151940b601c803c2c203052000f07007102803a12842e40300c500180d00003901d07039441105000081101d850040e944003010b1020940300406502015014071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 175273606 1250 175272356 175272373
    0xd060308041d0906150d020303221703121302030a06020309030306090702010c090e070504080102040909110307120f06060312110c1c02040e0a050307030e030d09080c010c03020708 79
    0x40c4040710b4824400460080a80251100403107552641000d88030501c00b4a2104003404040c01d19000c1641268002000e0300d08250090303400300c3c3d44200c10301075900401820402800f803485000504003140d20a08011400d1903d1000d4500c000700c00501481450b42000c08a24210343e02000703203031003e9901090640d01e83c20021415a03894005458852080300c2540c00a05114030500c5000e00b4010955101000b6905c1d00c1c42210154201520305403c01070708120100312102c00f40010001021900000030340e00009007029140c0d03c90f080c0070b1034443c0d00480c404001e02516050120740b410b40000030302603203919074075201c001007a10f940011b1900d814040b42241c0305401409121040400c1c005560040703401c0001c010340c0c4020000340c00301c41444460300e034002d400d146c0c1c40014200f01d0b940c215004000203407201d51564101d808101c000400704840704489090a205030101c02109043c817440700f0342000e9101d0784400b044221581003000150f0418145807003000180014500c0000741c40004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 175274856 1250 175273606 175273619
    0xf0611070503090306011a0d0c0504090e0a02040b04110a030f15060e01080f072a02091f0e0103030e040b0f040501060207030605010b0c070302121507050d05060301050c030c0d06030804 81
    0x20f8221a118911a0184200024541c0c85011301c03440700c42d910042c45850210600c4508004050760701e905c10821030188000302d040c0a803031082600076048100102000c0c4640d104000680382c804071a14001c0d42083d03060b200032200081910303166000d504003c42d0303451302500440001c0020161451620803001c1d00001c0e070f50342000700d15100f01420ba8a03004140e85803010303200b43d0340c0c050b541e0800107040e5450382c003070400b680010034103a0441707516403105150082d0001120b6600584045000ca41c84400410f0500c0b615510301c00100511907007600f166146032400741558000f988014000c0362140600c01460b6a804594a1404e00040c410442940c552400039a07450361400201c03101c9151000100b4002c0c02402511011030841004201041c110343c01c1c402200c0c040c1c2c8002c0c08a02c206482e1002c0800c40800c4544180304550302e03181c03141865601c401c2034860181c4414000e03490039003401101e00340e40b41100d038131031040800ba9550305c040480400c000d00951740050310b1a040440e010412 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 175276106 1250 175274856 175274863
    0x62a080405011b0308180c040906020a0807020106030c09020d0905010501030c080c0f030d050715020a02030304031b120e030c06030c090901080f0c100509100c0311010b06070f06110705 81
    0xe0700c600380e803014500500035070b0428140d4158903020b000308140a0004210400c0100c1401622500d401612189888030780070a041c0c4003400401c0f80c800350003240c10b0f5246540710300080d502a4407403000307225086c65078648181d980c01d280201c5299a40010300220382a08981000c485140d01c03100030440ca6030f4a041118554015014510785401040205030302460006503905900d0b200070094240110145010354107540800822121071064107140700b6001c038144003810309100d641e0043c507035924240c44c00400c0c030348002d941c842c420107a00d0a81070202d1343e0700c0c5899003041842e040801c0103002400010f443c1028100e80180d0010002080004000346030000c0c189008058414240fa80d0b2105030301c6490300500c400304000daa0244e03048007002e190007107071041020030600b0700501e40001d04010807050310480c001c0c00040303864050910100740d4814450840400510002c1145210038070000d00244a0340b08050981a0308111000600600380c2c859004a0302440c005503a603004c0d490480e44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 175277356 1250 175276106 175276109
    0x302010c0e0406030b0c0901030b06180f04020403110405070525020906060a020d0503150414071107080c12011404031e03140601080405010b060a03020c060c0403020307062a0804 78
    0x2841180805401d04050040f1804c3e40d902051a0f400c0741c3ea60f400d5140c9903000208000d04142e11400e900701c46464078401020b045031024010060440c00302d00344a084040140498000c40c41040b0420103d9002d15408180600407a404a0030380c89a92003200d01d4060740540c3c2c0841c030a02e00c24280c0010109540210030b5200f56003400c4155102c2d4200040740c0103800440c40986c02000ca2103000324440c0c001190f108142d0a40b18941c83c0154003c141106c1c941c825400320300049a0902000b01d130080c5411503040031740002090407606041c1c1d0161640320542a240c000c402c82e80c1c40380801c82c03080d0059440c4000c448500c0c0d007a4505401d008120011040035240702c02d1542405480c6281b10b402080c4920020100c40b5800780ca4107401107441c10300040080c0d2f501e56803011016080d540321170090403401003079580541c83c0c10441c01d91509188015102e014450307810441000140c03804520142241c0d964108150786011141915178044080e00f50708070140c81416080041017940c401420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 175278606 1250 175277356 175277381
    0x170105061c020d060f02030c04030b1014060c0703060f060518101202060c0d020d09090b03070b07080c06011e080102130b0f0c24090a0f080f16030201 66
    0x51610342009111011410014000c441002160048090304010aa500c000380c8288800940083c62800b40d00c00c90b0020744000d411480001801c200f40b150700700304160030412043e02c820940d40340c03024510300014001e0a0703038001d00000c1084240b10b44103004117401160411405c0c421421204042002031a1a001c6d180c81603031031648500e2240305060882c1d00c15400703a900e0b84906400d004c051240d40c0a0007808a074040000c00a60100000038021404118429002850340740c0204802074410240c2c0e41200349882d00e0b0030410100c03a40c00140071422100b03040c100c55520006403e100400c0e1040c4590032a152082800004d01c241c440680c548560340c003014101c000d1600e4210417030030303886010340c16100c50341e40e520244016010540100542d40005411510385000000058241000600520442d0b12000d40304030070948041c070566402040c0030060010101c050351955148a00080094001c0b41c0200c0c0004c454060102125400101044c6007584107201e894002d0181c014440c424 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 175279856 1250 175278606 175278611
    0x103140f030c070e0f010303080a02030c07050d0806040f0c020a0f030e03070b090102070f12021003021c02030103060c0804030f230408030a0306060e0f040203100306060305060708061e010c050f01061701 89
    0x80301c6240326507289058aa25032740e0181d45403690300684003e5007000d421605110020801003001900400c9840984802c1c2e0700e41100b84c1c5011820402180c1c0098602d100050400400107241036010442c640f90b151f120b13410485605050800720785004150a00d141c052140c48404104a0351017805820002400da007101d0348552118525805c1402a114142180300401805030044c40e291214802c860107500e801820200801e10313903c09107a45d641c8988200e68004010b00078466107019003400308206003050800d074103050390b0084c241b041d006c444a0800807108040a00300c030a4000e168032a2a003411000d072669110503000b82c40380c0c04804001c020034236200000070306901a00380714800c202e0091510201e0001070f170501003c5d51008005902142201c10040002034152007000082c5003d00002d04540c40e096501508164019104034402d60009100c030102c2420741c000d0120120003840d05407250728039460100e02c3c182800162210550a000020404583d50302ea03500c00f002c3c0c004000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 175281106 1250 175279856 175279861
    0x60309250609030b1801062c01060905060d02090307061e020607020606040c0509040c111203010f03021c14030a0306050d02090c03070c0f0506011d06090103140f030c070e 75
    0x41010391010344140750119402a82c1000440d020441150344050400d29003020182240e4000d400c4981541100107000040359480074403000c8620701c0404040d003012004001e504103a400f405209151040f07611031000020035441310700c2c098040e614134840140482c2d401030340301c2c4d8000e08400310060a203a2048256065400701c2807000685901404079074014003401e860308401d1002802c6440500001d0010420030102651503610a11803403445aa4926001c4c3c0c0d031044003541070244020042c030440b40244018003600388800d50304d0307080341e074102d41c00d218010318007a40499040ca49440a050703142c0c4100000d541c0000800103281124041e6000c110711358803042000414a1ba18502075040081b0100103802c02100324015900074800e400c00c4412082d880d035071107070500a8008221000d42040740100500304107002e000c1410205040c8110300c03481c0c08804038000000501c07019181c5000b459142003504010700a80742001c0000c002d8070b68030030300c3d03042d200c6d0b40741c043d071194a407903002f490300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 175282356 1250 175281106 175281163
    0xc0613031b12030b18130303050f070219030e0303071b05010507171e0301080d090b03090d080601141206030f010c020d030b13020d0b090a1104030b040809060309 71
    0x12001d0850351100c4510801c62900714220002e0025a03100d54000880040c140f2104d02440e92042c4500c0101c1e0102c80d85880c02e2030010142c0300080c128141c40040082032100c0309401180c01d00d8280410440d41c1000465401c1c1203440d5264136408036014000003e51000784922545041090034030703a0358640e074240c1e41d040111543d20458002420321750b6007e40c04480001154002c1c000514100894440c03514501200e04283c1d1003a805241282c3c0a00e21544840d90000448030052404000050544c60a56007458560702c2d210300b03c4041281180000390142e011304d01440c15400f072100c0b0305032a44400881051384820a460702c81c428407506076030715401c80c014011210741780344603806060398100152056000d016080c28265002c0c0311844a4240700d0058405886050302507540402d00a4140d801c0c0701e203001b0080e0210010b1401c0c138100300c600a81c0c04c0100c0701140d80c400488201992141440d02860042c080a00d80c420000030a0004540000440365014002c00341c0034103176000040ca = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 175283606 1250 175282356 175282397
    0x50601090503210705030c0303011d01050906060406050a140a02010b0a0927061b030b1002070303020319031104080102070510060f0902070f02040509062a03150102030c061303 77
    0x4050b40c540f8510500701602c3ca0503c4050b148652003007080741d00b0048801c07001c60542d00f007600480c500d02d182c50148c400c02d048038060725005100035107504145051403000304581c1c0c0f00e607008240038000002641c000051080075800301c3c0114030313810a41c41c0c52144000034060496280b001c1c0c40342401c2e07140410100018440d00103800007141c40c0c0c1d06005410400d03e100d002c0d400c0c4040c0e514640c3c0d01d452403a01130301e0a00785580c02c4015580003541c1c2e056502001748202d20b08400d01c045601200303040c0002038000088407404035610703078984c00782e070201d5008501515510145100d07400c008030380002e1a060540207895168420016500c003140c003201400102c4140d0701c02c0444144420b10300300100002039000b000080d00958041c0511b82080c1c0101d03041d10000d840c600c01310b5000c441000003100c00e818010024001856080301c50a4080803511803074000500364105944810291488a0b0b00070022284055040c0d401d9580514060b90749202d00320018400b40c0204291441c5c209903030700183c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 175284856 1250 175283606 175283623
    0x6030c1203090a03112d19080d03090606081b04050a0b12030d200a05090d060e06010602060a0c12230c09041b12090213060801020d0e0109031707050d020a03050601090503 75
    0x1a0003480c0e41c0c0d001c400401411247d00c01142e10186e0341d13400d02007010070f030030310031886108042d03180442c06005918060081300e40560007140182c0100c40203c0c12402401405590359004683c041065140d14a07503800a003151001c06610081600b90f510b050a00480038005c0301c07a2007201001104c8441c5000003034910704890f0580700b44410005900100c4c042e1025020525015008400104803a82c411045418028001129600c801d0040290075070401146521002c403072000d1120600140c0003405020300e041882c40180e40340c02c1100030860140241d5180c580840d07c11b1006810b05c0c03030000e02c09a014801c8140141c1c01c03e0110005040045000001c6071035030b0307a818106000c111581c40040920b440c00704e9100c20301d4094422055824011040500a048001030355991551000c40c200d86155880703c1c85641050040d0020030707000a405040034803d03400c0e002e280e96442d101150715120707000340b00304c1c02c0d88045419424941c3c1075000307a2140c5400c0e00d80302200c0303441c3c504040d5104c006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 175286106 1250 175284856 175284919
    0x2010b030307031101020d11070c080706050d0908070b0c03040b0f04150b04110a02030c1902090f0a020f04141002120a0c0201110303040b041a06030c1203090a0311 72
    0x2c1140c080024030405029000e200d0341c3c0001800c0140106640058500041c0071041c0f01c0d02c041201010702601070038038801000004024002c1500e4084090400d0040c0100e8000641d81c0ea0800380074040030000701c40c50f13141d00a00440e00c1e446c1c68075054420341c00a441c152607070340790f4800103034140400d145c000d4003031a0041001c0d0400c0300c01e04c44d02d00251040c541c07550b800c03580740c001c5003014542c40805042c1449182c1c0195403100a060101444c010304441740e00c0c0c80c440122046800340e00c410031000d40104024800c590b0540c0c03081c2149000c2e02c0f52050030300380864005000908001c071040c58119154040703804181119810b18101d17941e440241022003000400c1010034503250082100c0040c90344181844015011030152250860300105d8060b201181680c00b0041084024131944019040d11092004581001004a952210025400e90050076a460301104c21101001942c01000c0300138680d40c106612807404282c0c00c0d070b40c0480503001c0d034000840c14032102e545002104800a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 175287356 1250 175286106 175286113
    0x606170c030a020609010219031e14042903090a060f05060f09060d06110409061508060d0309050d121404120f0303060807080a051504020906150409230702010b03 71
    0x902d90208003980c1d109410b2203065201d00f4002d0034080410209503224107010391205c1c240c20f90038260803148040007000c0b1204000d0207a0b00c500112440070180d409071501004488903401c02c01190f4a40d40046065099079a00040108040701e040000c1045205204040c14410b070740d452414842a101c05a075010391103042c1008401c1c640c10329400280d0300c01e0004264481500c000e40781c0e90f045a0180c2020495081c0001e0309102c100b0050042c0c200800d507010210300840728411000f04695009054584030f603240c080007106042c41140000c0c00340000812182a1520030700d0640401103588456002080c03004100804001d500c50a94040b14280d4484565095041c0e44131415280461012824165514004540c0310700400940c4040c0c04036500030f01015409081851400a00c0d8100c50901084282000016142d5010144e00300f44150307001004001c0e0b83d000418203000d0383e081041c1c000c0c07130b2150098095020b00c4142d410091900340320b81e00f54503144070480c02d907614099010b40690 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 175288606 1250 175287356 175287373
    0xf03090f0c010e0f0f060f16140f030a0807140a020a11060c0a020603060310090f0c0902040f090509010603150204050901050a060206130f05010504030503071701080d0309050a0209040606170c03 85
    0xf40050a150302c54401410751f468010f040c03000451503004140000300000c100d0981000308080021294480c00c5040e00800600d00070300c503002c0d40c03803027104150010403034154041245d4601031200d21003084200407a5a442d45801d81000f5030301c0c0e99402050f50b08044040080583e41480000c49980c1e06d5004094100e150b80b035000e0000c00c2d84041e001c540c05101e850300100e841c11203841040c0c101c40c8541e0581080b41c400f402c105522307070b6098110720500b0b80704000070070030a001240c4620883d0b101c1d02c00440d8a655844500c3d004041d2036002614242001880110b5440c8550040c0290b440c01c581e01050f503600c9100740f000c2a549800b40760013592011000c1081540d00301c0c0382807003842c0300c0c142c0c075520007401c0d5884509450307042d40c084011070f2000c400c2c0141240c12014401d0380915030040320303816600d0190a640d6400300701494100703050b07848603100207010007805090203003900606a920b1a080600c2d203a0010311151003000243c580c51001610b19007408544121040c000900800003203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 175289856 1250 175288606 175288609
    0x10501020c061602060c06010509010b0909070c08120109051609030f0201032a050414030f1b01050708030907050a2309062d041d03030f0a020f03090f0c010e0f 70
    0x283d102c0b00c66a50495039800051005940b580010941c10080e180903182c6540b400342809002c64068210710204001400700f4403154480c0e0040707c0c0e2080c00741c600644101c900b400c282c180741c03040101d40c9400b0208600013203005810364024900401c0f00214051310005196000c0b921030140d400010600c0048444041c05980700307030030542005441c1000760900d0700890803101c0c0100e500301261400326102040c1002130101510180e144a00d00360301a144c0d140250840c0ca44a40002c80805440c0482240d542d00c02c1e403007030081d22803031540b001490381c1d40d003042c1c00129902d0100307100341d51040800010120301000300700c03c9400000c40e241c0d00f14035500ca2031002c0080d40c3c0c1c0e00030440c5070400c4581c484080d1300c00d0b4000c102c019112212030010a5054040b00740000e0f5840e000c0000c2410a100c2a81d210041000044950100304001480360f540c175078408600291203020b14403100d200000c02408408180031500404d84941d200442e1742c03200070301c0019a403085149031556031010010900500d40e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 175291106 1250 175289856 175289869
    0x603010308091c03080402011803050a2a1d011205060c0901021501030303051b0f0405040b0d0c060809060f060a060c111509040b0d08072a0b071a010501020c 69
    0xb0100140100c0000c011407801804030602103038140d0010b50a20300f0300c015942c120740c42522445c100c1c4002c80c1c4450658413507a83c3d400c840d0000808081306580614440f070000d146407004d0b00f0420804440c12a070f1352803070a01406007515180002d42651000140f00c401d02e14155141c0c0f07500c0005888260780d542ca030912140c200031703000c6041d401400110300c45100c0444c2207601a612a072400a40c90510341079111032408000403040c080001040380903481e0717440c1c800359400c031070341240c002c00c415502d0f0300402c1400080e441d0080c801b6115100c0465031a410604140c03003090142c0450301a5503c58001180b824425143e05402c943e180005003c1c0074840c69a03440d201d0b000301c102c2e541c01000c4501189e81101c03042c00441c80000080f41d5400c141c5854050f491400100b101e20307000340c0c425921448014800c540e03000b803514600c0c0c066080104642c4006003840c1514682c1c0004036a170f00c0d40140c141c0e1307001c09000c440865048070029064140c40751014140d95060f0300911014102405000c42c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 175292356 1250 175291106 175291117
    0xf011710030203030a032c100b04020d020a0804120c1709041d0106060f0206040209060405130f0f0c210b0705040513020705150c0706020703090819050c010e0603010308 74
    0x1425038410110141c1c07001c000410302c045680ea4002082c0764070b5500031528070710042800401550048032a64800d500103400300c1c40d42030f40c1c2c40000e40c4c85008000030700240700e1f020103000d201d800800c22225594010900c2407045005100000038070070440c80c2103889180c0c100c802441c45003114071751340e4580c101c00c003d4044c80030080d100003041459000700358060070095009003466034440303509000c040d40c800c910206071180c43c00104072314241980000c0344220010504d070b018940d00c0002a234251494140d111040b60800d16150442c18103017000e0482e020401e406907a050200e44001450141d0290420b44040c8640598242d905541c0d0f100241028050010820000700b480b01051a550f055400e85074180b94107801070365094186440360030080c1504440b8520a0101d0030043c1c500220422038541552080b80180d03a0740300c501c0c0c10381307000100d030700041030502c5807082c54a04d00c285800c03a041014062001c0b212a10f04040044891b81000010b1680003c0140010000503455401911 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 175293606 1250 175292356 175292371
    0xf0904020f130501020715021c0905090103050a0c050a0605070f0813080601030b0c03010501120b040603080a0c2d02040e010b150301060e0f0a0b030709030c0803090102010b0f0117 79
    0x6240401000c0562210741000d00307141c4460b8074a80c0304000d5507804120260091050900c000c008203030204002e1340300e04504021400d0001d240031400210340c45103442ca009050024401c42c003650310f07030801c0741e502c0c0f4101004480186807100045101d160080c01c11b0b0898440d03603240d900d091300c5a942e540220400b03a4084480b00c0041c080c00d034400c02d030200d082c00078148400040400e5031441c144a0380840c00680b01c9000c0b00010030050001d42d0b8490b00905c2c03e45005e80d0045203070303100e500100d401441d2982c806004c4c00008601c1e1004075a1007024108814003c1c60f00c0c5d040ac110704558144050f05200d4140300703000c40e0740b180c0001402c4c0303074004017200b4800c0000091801d0754400880e1042112240c1c01500c00400401802419008103c118420070240d40e0029202c0390203000c00d032821203a00804000c40004000203180074881c24411003c0c662009139400a6680d920a00d581c0360880c448940c055420b18141d80a5414a000341103100302050b074507016140d81c48010340500040c0a403100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 175294856 1250 175293606 175293611
    0x606180e0703110409030c020a0b072001090b220b07030f020c0105031504060f03030503090f06070903030c1103070320060f030103020405060111120d0e0309010c03110109050f0c040c0903080f0904 86
    0x11f0025a840d2420702d0002d0283d10a500d030317a0056447d020f1104140000000b10010405480b008180d03848007182082e00c26100b407043e510030038038401c0307401d660800a807004a4154210049603906e16034014010491203510795040701e0305403801c180d23140d116402c0b0181c0000c00610000e43c2c0000204c1205403180000b038800035945440d8400602d4a815941003a0007040c000814443c011300f0030441440c4685c0c02c103020f40540e0410f010000c1251069210103000c20031030558003024032129540410340741000408503002190f4034501b9980300340310a182d50801c080004440ca4040c24500c08550400c048054081d18603802c542c200001040301410090403c000100d50600200040010410180185244c2c0d034480301013680c0807090b1025001040f8941d04180042969a40c10408113280c0b02d51505252400d1466400c2250040c040384034050021b00c2258461030201d200864400d504010903a42804880c4500505031855041480024401340003041901001c164010242c400310350020000b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 175296106 1250 175294856 175294877
    0x131a0a0603141509030406091203030e0a0308060102100b13020c070e0c03060a050d02011d01143403020a060b03010b04051503071e03110d0606180e070311040903 71
    0x100b01c00d40e0008007250100e544030345800f500d41402e800c003895011100c84000c0d0714182c00d010000b4440c2c5204d215101002c08240c40b900105402074204800018a81044403211001402c00a00c2e2810584007103025020300b01109901c1c80d49406000051840940b034404c010450030341110096100b11a40d030b40718001c003140442c41f000e034036804901500c840c1400d19102d062120070011044490390140b0b03c603092401c2d40d01e0043c2d030890b00704500e10754140c620300c1c4101c0c074020045e10042000c5030280b08003074001a1401079900c0c80c0f4003408100100f0304038a201d60201603a80c01103060803843c040c015030300480c081d5000403811341104159004c0035001142c2c840d41040800d0551300705854480c00c800311002c0c8804a4202000b0850003403020b408220400d102c012070340100030b4514000600040000d80140c4d01c00e032910b8005444640d80103800300302d00da030713560f85c19441d03070070b1804804802a04040c0962904a00000c4580691790460079140310300e16010200002048200c50071030501811901c07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 175297356 1250 175296106 175296113
    0xb0d02060702131805070806071d210f010b0306010303140a020f070f0504140601120905031e070c06050301150e131d010b04021206010e01171e131a0a0603 68
    0x68181a24800004041150b44c9450540c0c10300e42c0641207400075074000c10400c6000c0c4c0e0700c0380d40000d01811070500d42002441410100e40404ca2402c0840b03100c101018a2a0680900203041c400f05030110008002c000d5810041540340c0303100380310140c005006881c10811b403c1a03040246851743c0c0c070b401117078003c96074611401e04150080d440580c9400140204200900f45805004105c11200004180d1031070502c0021704541c0c1c001c404541125a285c0c000780401104104454110380d00020702104441101c000942d01da003c0302c022030752000d49006c0016028021019a4145c41c0700f1503002d1080c1000d00d0b000c0702e5094aa81c46158040d0081c6414442014988a107403400221038000840249000c3c5100c0c1c20b5422418440d40501e1040285d01c600400c100c1c1c1d0540c00240034a03010ba007015020004031014405aa441d040e000200001e10400d034560840120328018000c680114030b5880050452291002c04800307040c0c10300c8004109210346066031100d178422404c020008540744c8a4070b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 175298606 1250 175297356 175297361
    0x3150f1703040f0303050306040606051c0b0102070503121e040e0a0506220f0e030423030307080d09030f08040503091002160e010e010b1303060c050702062a010b0d0206070213 77
    0x14011760201d90000140440c4e401d1501450001c2c041500b06986058109035880f0756143c0c0240409900315580c88000b07215071310a03c400002028000e088810a501c820000411944258803010034161500e41d2380020310400000e5a00311010142066495614665140c000c1c2c10010702070b56210103802d40c58440268411a01e9802e84656600091961603a140701011941d4a4001042c0f83d031061104008294204103e20441d82101c0b00d000c8000c14001c0c0428514010518020600381001c5005592404994400402c0170b00035581c48100b50946002070b10249410fa9002e030154000f00b151103405c0c10981201084000c1c10303c104c419010b5400f04443c2c404005400015034054004010000000c50701d62644c00740551a0301d482c51b1802d400b04e2076103500c5280c440100080e8960202040450160f000c0d1010300390003900140d85d5064008248241c3d2824022000c010b81c0482d6020003010310502c903040078400c0180840104500c950200308140e040030000302d902107260b002003040c1141030f0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 175299856 1250 175298606 175298609
    0x14010f0e01020a0e0316050d0501110403150507080c0d020c0705061306030b1c0311010e01060308041511030405010c1e050a030207060215010504020702060c070b03060103150f1703040f 81
    0x10030005807503030075000c0000d10161106101d50311a40c0851442207200740d11381d03000411100200d507040b20305460380c5011805484914000580075401140c00401c0c020443c9482c1084015608104020303035404c2415260b51100380c680d00b00641060048400c0310031682e00a00c00c07500f69400b201c000ca070340c1d000000d0142d80f1104801000582002e001c004a40c6c0500a4803082202100c070182414114200c02c00510324001c006407c01106460302c501040080d48401c40840d0000000c0c0600754aa04020b19103134018411004940d0b0307200c0c25031480500c40c0c0c0c1403240f031610120117035180a00d00801100c28041ba060143d516a400c203480940343e501d000f0001c0040380c41000640302c203000e50b0501034103241641c0e1100080d034201101868450144086145c1510b400719001a150003181c00800c5250090568205a500c218076010441042d000051413042009036418095006405088162019984603249480c140d2990901100c07009801003442003501c4811a0704050340d07030b45a00501000ca = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 175301106 1250 175299856 175299881
    0x50702010302090d0606080d020304050f06130b070302150601020d09090c0e060720190603150e180c0102031e031305060f0a0b01030509062a0c1609140414010f 70
    0xc42c0d0302081f01800c1404155070002d075034005103003042c1c900700208050a1a0240891140e000002c06840b64940d01c040c490150084014017038490140e468065540c02c0c51070038000300d1040d400d00090096200140800304103005680b0320041ca494044100042d200c01d0414806010382c00c0302440ca41d4035084040e044080c001d15984040910803c0301c150121013001f0264040c1c10700d10f0300d034100307000340d007072110100d448a240000d41b14204840d9010784c01031541012880155901c244030702c07142c02c2d8040c8074082c0d040d1011f0362a090030980069989101d011581181c610a0204005000c01f048000d1030340005c0c1408080010307610303aa42d0b2030030000100c0312240707880c061005001115690344140010341c102170804201c1810101005650381800402106115641c84a00c400c462400102c8a007080100a1041d0f00e90741e0301f000b000d854005001110415280c070100000c3c05640b42c0c001d00006a0350046171580c00d0711691503984000c001d072800d030b9800350740300d846c0901b81c07613a10301c6a001e0030200c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 175302356 1250 175301106 175301111
    0x818010e0a0b0603070308040b07020a03020d05010c080601050a020d081f0602030319020310030b0411060a02010b01081e0f09010603080d0b010e03010509031b0114070c050d03020c06010501050702010302090d06 92
    0x2181c5007402c06100c0c042c100c54080d0744205001c1c40001c8541d0101d500741c0d03020603206915007015100083c1d4500c0c15420007500032052841a078108001500000710581541e2282040c0e030ba00c141c0110fa10307015070b03c001780c01a800354003012582d80c0030700c0c2c002d9000b003503181a045280800c924100d0340c0e0b0a1982c131410040e03000108002c89240c81d461020300020000c4801c0d80b031401e1500101042d030f8030501016140c1c215403004642040303000000304101ba2405020280c44242d0000080e000f01500c0f07840f075000c86c90305c600040e500549403051210100e10302242d84020380b28071025190804c4002c040c003109641c0d5144c080041540903000c0c0682150414001c40c0340d200010004207009910300c0c11a000f80c1c104000d00c140c00b10040281c4101510302d41e1030b42900142840744a0240501c0543e2002c4000304a00b40040b031075202640e105501d00030411100e6440000f00300310200e01c0380f00781d05c2c0819009400140a90741c4648000d080040c014580035040c070900b040017900280c19084c00319186035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 175303606 1250 175302356 175302373
    0xc0301030c140d060c1b0b011d090601091d030c0d030c050c0a1104110d0b0907020d08010b07021206190e01060b12060316060302070c0f14010818010e 66
    0x40c80750421001e445490801c0450498880100300e0072500f075036004255648540400300090320514907400001425580e00c09207044030b04000d14406005c0c001c0400e61001017082581c0c0134804580d450042e4800740c0200300c5a0f2804850708020500008000c1078041100d030342c0040407504002424041e400400940b03a44100090301030200d07190b5001200510000744819420700307201080c0c0114254225000300c0303400c0c0d402d0002078000c0100d021450000f03580455102644c1400b5841880d03115400d9076415143d4888c0102a80e840004200101c00100f500005001514200e030151441605c00fa00c114042c440641c0b03038034100300003141d45a03140b855a2000b0030380d2402074021022076400702c0000f002070604113050a18107103c0c100101495035140d0740820440d8804100856080d4a40c1c0b0301540040c2c0c4400e0300074040c2d401003000741c07041c003101e41c404101e640e150700c0e503002180c0161615445c1c6069684c01920000e5004148030302a40c009450708034440006e0143c400301102c0c003c00b030182c94 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 175304856 1250 175303606 175303613
    0x604140604181a010915030b040605040c0203030a11030402090103030c02041b0f090e150402090d02040e060403140307050307030c09080613020108150321070503040e0f07020a02130207031103030c030103 89
    0x108000c03c1050410050b1401080a2000740360384100c0e10f040c5e071801013956240c0d80c000ca000f0b040140d0082c1c3e00070340740610210701540d0220240d030040c0c21000d82440404007060b0001b45a0200b0354002e94030603040c05c01000000d01400000c1e403101d1000e000401e00b0100040c405981000402e40c140100360485070b0a2106076220060001609100ba400b080d40e080c01482c4404000304d00d044070340641d40c000307550304190380d42c1c89803400899030051081c000e80c200407444648518041d00d00f00c0200d4000348403c042f00c5035800990f44580c01660301c450850750342c51130481c05860102001c0f0b0600480e580c0100d0030400c18840c1074401c407220441200d05d0085440018040700d4018481c0e0b480e124002c4e03c140c0e00d65000314803280d281c0c0300d007460050405030101304454188901c2034000c042d8400081c0c002030705a14600ea143c0310750008040505980d4645d5010381c0c0310300071000c000b98800c1074403d24004540155028021060080c9440310701d15001c444004d240d64015251103c90703030808401001003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 175306106 1250 175304856 175304891
    0x60b1602030f061005040c050705030408010204051e0d0b0c07120306150207030f0311030c0615040b0f01080604051f03080346020d090f0b06030c060414060418 70
    0x6941102c401000c0510b003d0260707910080d2a030050710b12458503090078a504500c02d200380d580c0f00d0b07080815250b85540d2000304138001e40c4a4822907000303c401d0540b1404030051614858400040a8401030740f0304030a03564440e021070001e06c3c00e031014100303004d124003003082d4500c1c0041e041d01e503407070015942e070800c686064181c20b80c111060855019103c00d0001807510014901d0040d40b50906500c000813186084e400d5004280d00a4541c0c07091000b0007408114440404450042c00da5041107500d103c4e405000450007200c5a46020900c1c01d004a403950400e54456580418040a10b00449406200d0844001c2c43c1d90700c282d03410f00380802030100c540240484000c1f109420a09541c0c0d60b801c0c42c42445070b104a9030040b00c4462140e185105402049404444100c4681241008904010320388501c024011100a492041c0507a00080243c100045d0014003404010485810170f480c00724a011515000080a0f81001c014000044c3c0d51062180d04495100e600b00e02042000c01240340409 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 175307356 1250 175306106 175306123
    0x20c101a0d08070204021b060708010902071a0c16030309060f051009090201030207140a060c02030405013903111005060603150a08032b02040b120a060b160203 70
    0x904404100c10080c040e6030303045402207455803161449480b441c050000030001e004d96121504604400343c19205600c202013005840f8a903143c07a104145d989481c501012030103a403000500410f0313901c850514540000075a80d600190031042146007030714070000c51000c204102c0c012000b20307446084010811031940149650b201e03e00c402005586011403003c107401c07083c0d1248040080d9540107503c19644260102c501c003030b1304140514102104081a69559040d2003810756511385400c003da810141301000300c804450341603480f5407440740020780d01400c50300b19a1400b42c0304507200c420003040342648450b00240c0350180d01e4400c0d000300e02a454608040380c440040e01c4030f614100400c001c65480a045ea500180700c01c4100701d61000c0d14010030365810954116101034440890a800300c1540c400d1441c00340daa01040110304400c01c0e60844007079014601844d45494001e10041109e156030342002c95001c103032000301003143d9548129021140e03101506850300c00541401d9001136080070000c82c41c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 175308606 1250 175307356 175307381
    0xd050d020106170a03020a0201120b030303071d0103060e060613091505010210020f03010308031f141201050415052205030a0905010804030e0909070305011418070312030c0c06020c10 80
    0xc42e40784c50b43c0c000d465071540e602c000d0510455407144900c1400b41e0307000c403079a5071010301243d03030700c5c2042c99001d010b4081c000c60784035402c004c00040c0c1115521078001d2108482d00e1500540a40c4c54110810005801c51110781000070000880014164840e01911405241c40850504501e050000080c02c2500b031f1b42e00c40d04180d00401c1003e10b83c640341030440c2d0449820414481e2280ca40801d240c5480a01040704102c02055003008034458003030010940007814112954140c0150880322030b42601c5080b00c000d0702600a001d4882c80f0703035010350400d907807052455505544103a6461034990754140c04001c2502d0390707071010801c54a000d0300050884090702e07007428410060314256800900000300d800507a40118040e8005c1103045a0803c08600690392001c001d102104001490307841c004403c1700e40b1640e4522003040d560070440042001026641c2055601c480c58003502000e6014080000c40c280c2007000d4840e00c6008510b061002d030881c01465406404980e51002d400801c5e1000c40100a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 175309856 1250 175308606 175308613
    0x30313150c0804050105030403030212040b100f030b0406110c0f0601030b0a0605130908040b0a03020705070e010b0a0503130b2406030601020a0303050604060e0f04050f0d120b0d050d02010617 84
    0x1020405440994086130000d18002c2e80c3d80c0e440d8030342240603009107003c91060808100c1070008002082c1c210710702c565120141503e034181d5600e42040049128030015042c40d800c5001300340441c07826040540d524586404451910385a100c440e4680455000400015044080181308000308214001c0c0c020803401c0e0b051111a0800000072070030248402e1100345a96600c90b80d81c1081140f5050310000c091104443d40c5800d61110060040d5010460454403806450310204440a80c0140b080c1a1042210141e00304903c03000300369078036403018000440b400321b46d043c010000703049044214810090928020f041c1207208001601c40c801d840b04241c400c82052040205590340020640310454040c6000b045c203883d00c82c0410020001c941000664085600802860109943c002405035110340308403040f0100c10395402e6110391000c0e0034071000034031100d60380c1040304454101810001000b043c2c250098100d0fa40c0c245030521117415400980d4440b0b004100c00d80b43d04041800740011607025 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 175311106 1250 175309856 175309877
    0xd020c0d200a08060a0b04060b03150d0c0306061d130209070c0809090c0a0801060201090c03080d0f0e0106150503190509070f0f050915130e030903031315 68
    0x7055000d418001640c140c0004a211010700c0341c0d604284400185001d405903042030500d008807030098840a203500380141d007030113000140107291000f1a0300c6880752900000340121884100043c140b07035040290b03280c45460002101241071442a01d00030500d000b0366011003120701c10305441005006040c40480100302c044480562606011301c2e41c042c44a1400790301222013480d25030403601070425031a0701f06414500b0808108003d00007000400050f44500000f60b0760782d80204e00344c1e0040d40e0300401d103002c03a600420000d90700c03001030705200b008203001040c420b00c0c0441d040304654401200203251381d10750901f00700c60798081c103401041c80a00e2806525500c2c01c01c909044000340840c84441040d900c80004408203014031600c8044e000001c92100b0540d550390000020322000d0284500c0303441300b18007040013910343c441070048810000d0300c9401014071101521300203200c100601d2000d40070400c0b02c9829607030148000c15180c1111282030003030038284000c10104c800502002810310140030f50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 175312356 1250 175311106 175311113
    0x412080d0c0e13020903070e180f0c0a0e0106020d0c080409052806030201050f0304020103060b04181401150804110a09141303021b180403020102030603010e0d12020711030601080d020c0d 82
    0x70340030140c5503481c81c1001300e910740b031481e0100500003074198a09d9018925140b9140c1c0c0c004035001c00b1600c41190400c0c0d42988441007801030050a108071405079024400b9003410300d002d00c0c0c0700884a4050304035103080ad69551580400e9450031900c00031081008520358003180d40407504413a01503006441080700c6400e50b800a8080d02c01c030911664448004030002c5c08580c4a9000140541000b46800351983d6450041000611400034921401410301030703880350000030410840d0403246100ba00317254804c10094140c17072490008e0015a5032070001c0c1c3c81c000158a902c201c44006024504001034403a0102c071800c0003160000d4201d01428142d8000b242c080b9600041c40e00120610a0303542c4008108640012600b410107000c03003221016103000c000c145501075010358031580003a8020710104214030301f596220f41c80749840d04049140480d1a0b20b1083c3da03640540301e140d100300ea040380080e042c08002031130004240d1000e07445030310030058480c0310f81d8107000c504041d840c00d071502070f144031441d603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 175313606 1250 175312356 175312363
    0x3030c05030c04061b0203010c0c0606060e0607081e04060f1103030f01150e03100905061302011418032e0e070902070809040e06011e03080412080d0c0e13020903 71
    0x460f1504000c4952526803207208948845e8681c40d0b4020001c000d1103017000c8000c2c04010b9100c00031380d4410301e0100d00103100d50041940103202e0400520103483c100f00d41c1c1c1c1d00030702900888020801c001d86401d44268601c0540000d002410683d1580d0204c160183d030f0062040200030030242990b001401400098040d5600090544004000b004d206040020ac02c903001e8a10b030302141c0d80b620032800c1038004191154030141d007450181068032400d075140f00444490130390000c002400503614408402d10107200714050444001e00001e140803101b00031001902d01410385008ae0b00c6850304804522401c8862071104100382074501c0c02b8490001000c0c541138a41d20a4860103041680000e00b410070040003104a61011100030001c1117010307410301096035510005d0141403907030481c11840540a0440200c140100d070b41c082ca016240a0401c09a10001d46500008036441c1d071007880007040c4048a40540c044041907a9203610030800c00d202002001458103600440301d510400856a403502c3c0031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 175314856 1250 175313606 175313609
    0xf0212010504020c03130b0301050406050105120612010b030f0d081605040504090c03150903110a0b0103170c0f030a030f02090d0f0201050f0f19080906040f03050403120c03030c05030c04 82
    0x302c40c0140c4950006000c40d095102e0090300501c42c460504000c00d0084114010390306a44042d1010012251078800548161042400d0013860842a400042d03a900d030140c942600da0002c0c10010075100001004a032818090070b020100c10b401201c07190841d07540c00804160711085648115062540035980607044e84038a0044e039020329203030701d81101401245040140219440901802540071803030580b001000ca44034120002240c6c8401520b501c3d000081d00160a50049103110a59195542e0840101e8404042e095036400600054441c08810b0040c0a000303420030700a140d4800542100070225084170512800e064414001c82401d92905a031007140203070310100188041c0b40c02d0005944174040c1400c2c07032010803000900108031b812450b0103000d071024050141c183d00400000252102a42114184400e030b0004000078049101c0200340317429140603081042c5080c1d200c2d202c09501c0b00741e4100710004107010340012000c0680c1031107a842c0d030846900c0c1c202d0940c181a159400316100b00d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 175316106 1250 175314856 175314859
    0x71104060506031b161103100606140c0a06090803010815040f030e03011b091d010305030307051606020406030509060a0504030503070c020112020c240606041a09030d050903010f02120105 82
    0x11128484c10582591044032640780c400f8000c80030022680c81c0c13807200c4002c41e0141d00d00901880d000d403413500a071402000152502c5444030380580b60036101da0040c03900306007038401c018441d448034080032809602c80c81404500a4103821350320760518130300ca40b4100202100708520062202008042221588600300c240d606203010b001d0284624006400341c600304850310520781004000111f03141d00100d84030b007201d0410381140018a51952001d1300c1c6542448043d203d50020000540c459101d18020f02c00866100881110781c0096120041240c0042d008600800e0340c60090000c00f110030458140e00c9212548240310b24a4160340040881c08080c14100510070144200c804580c00341d1055049003403803001c02c548072261140032aa403220014482600703440d02c1d0740d80481661004c1c485e80e2040c1805010f240c40c2910b00349000500309140301c20300c0112181400512703500e88c3c2c00d20004164802c1540c4003901c81103464101421940b80664000100c0d01c1081300e91030100513092400d044810 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 175317356 1250 175316106 175316131
    0x30203060409020a06021b1203041419030b040209010801290315090c010e190303050f1620030d0818030705070603050a0b010318021219050307110406050603 69
    0x4448001c200502215400254042040d5001007040d55001407248001500c07100d00542d40000310080c401004009a40c24131140c0003084240319614210007004d0042d9005820003080400c4d200e038a80b80d24a058200f240c0014082080c80150f250a0b032019024000350307802040380e0b4002d01e4181d20404030303841903500c0803040c1080211095a0522050910704401c01c1c464281c3c1c0707003000c03005d40c581503090602800705100000602607404c0c01040c031801180c0450038402e1050843d06c05440c1600000c0c0741000c080c0302040140c800200c41200d1001d0203200b031740703440034041e8444441e1910203c2001800c0c000e500921f409005564400c041a401802d681068800082c080110074194450130302d000d040382c42429070019060780d1540c4450b10404082c0010041e04042170011010b9690080c801030038100403142c500094908a10341301200035181c0100c58200c400c00340d103809041c40c07043d0b050303c244e0408901c940c248505050302d00c01c051000c840800500e8200b0b80080e009000103401ca181011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 175318606 1250 175317356 175317361
    0x1050c0f0904110d14090d05031b0c01020f04031103060708090c090606090301020301031a060402072121020403060b120601060f05091507030f111b0301020d0f060f0611030a030203 79
    0x76210401c84d4140400310303e0912031205110408004850191240c181c6071162984c2c0000c0c0038480d2003640e01480b590a141202c0c10640c8c243d100307a80d00110b490b21000d55003004150180ca458a00400c0114031410011801c207449600300341c2088c0005140784184410401080804440420400d440300c0d000c441034852a00d420011410a00070008941d0b0191320000c00481801a007007a485a102104419080a070f40c541082c00103a000da40002858030480f00c1004074061500c0c00d8002c049030981c0b07071081039030f418078002d0580000008112080c09600003020b1017488100e004565044900790f40c0c44080c510001001541c0340814807606007008055254290030520130421152040c50007000c49107460400c0c80d607480203a0140f10101c000c205186c4402141e14000d88007000e00842085c050044400e4200b00307103c17145103880250394503541c20410080c002c1180d118806507400030044c0001d110341860480b180b8414980c1040c801c0c0100c03501e08106040d0300004803551032503d03180158994 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 175319856 1250 175318606 175318631
    0x8010506121c02210910030c020d030b180411040608120708030c120f060913050703240501080a0507051e060904020405130c0f030606140a02161701050c0f0904 70
    0x845015408407400007040b03210704c0484d9061019014101e01100c0150440c0c6500c1c01c140c0c02c440702030f1130500158010500102d401c07030090307003c100d102e040505a501d0040c0c1d4110040701880c812607049542c40301910304541141020312680025000080050a200807a052441a44d002c1c00074010400b41340040001d5507407010405440001c0d0903422600e5060400800c603d00c1c0d2103045035000c0c003a180c10030004007103078102d46500c2d503a40d41080103084007500b582c9031a85450310207043c3e0307482005d40b0301400140034502d1040303c0c02000540041c107410300162400c1c07805c0030390381d92041d44900d240d0428801094010700c00210042800c80311250703650703034200124010f401a83c0c407040e400710b045800000010341c0383e000045504d60036541c544641494401c04e40c00c82d0f03081c0c0110310004000301c10781480303290400700074003600000c0d0044540401149600c07101340281a0401e03400b103007412040310022102405110780210829450500700030b800403039403c2c98028100100d03c115102e50799218074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 175321106 1250 175319856 175319863
    0x40809010309050a06020408120f0a1d03031b0c030303040b07050c0c0d0602070c0e010602100e011b2c0d06181e0b01050a0501051204170a0908010506121c02 69
    0x3030340d000c1d0a60345130780c0060414000942091040c2d004501443c940206084131001c2120b0b85100364044850515140c034004480d170129054900c5412029401c1d03066603079500b080581001c10000180000d00801c000c5503500300115a11040c2c000d030b1051050ac40007400700012035034810320b680b0305113031644615625186020200c3c0750494122001c040c1110600500360014081280500040c9c660035540d0034203103400300002d2088400607000f2004a0780c6100395034110b41c6150030604004110200401d40c0e031454030750807002d1800801c01e0304006e001c804540c03282100c1015414031000311000e0041c40842c00c0361146850003040f0f50b585a040701c20350750f05040d80c007082540007402c0702c1d01300c060b100350540d95407844802aa621035003c0000a45881c00f2561001a503006235a503a06006c841c0006520f5030001500c01c40c3c94642c80d0031000d02c08124500a0600392045903a80b4852601d0300002a0031100e002d42014002c1c81c5189042c00500700c0050000c0c1821b4001c040c0944225100404904 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 175322356 1250 175321106 175321121
    0x4030c0c0b030403030c0806031b0411120c09030f0303040c060c050a0b10090609050103020f0111070b0c0d0e030f0606060a051318050702060112020904060902090a05090c0d08030408090103 83
    0x1c0400200c207110a165141c0e200329095042912a00030316110306c001c142e524080c03403070001a0100040c103040700380d080030381000301c0944000d902c030383c203101e90300d400b100342c6000444980c00c60620100c0e5011540c41c00300807072412400c0002c00b861450034552100894420700b4020703102880785070419075040010400440740d41a0b0040c0c442140c600317150703a1141a54105203d080c600900f04680814281a01c0c80b41c5812654000c000c802c9101c0a4401507400b41259041c032405030080b24000140e0707824502c002d0198035845005003e402020003409001c0405100074039000c0d40c009281305c51a15400038015800100440c0c0042c0c4030421480c08039035510840c4400790050820040008e103081003041000d00d904060041409590340c0c200e4200d070b840c0003d1007082c00b2103800b8820b4201504024901300e070014000d050200e84103003d5000309042481c00c0e18400000c583d01c004000d5450401d10400300c001a0031181280042055240c031842800050005881c9a5002850081d260701941c000130 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 175323606 1250 175322356 175322369
    0x70c0306051909030e030c04060f1401091509060816081906170304030203120a0c0321021b100b030309361902040303210f0e031b0105070804030c0c 65
    0x3010381500e15004060034107080501b80070780b280d13030100840c5241c140143d078242d68040d0000c244143c0f8044018040d001c125142074103016110002055401c20000741d0002c000e05c2d9101c0c0d840d550701d0400b004010080003040c040c900100e02021220641d400200d6541110303401e0501d8403445103000401c4001d01760781d40034402c0320702c0c4001c06248108010003c1c20460f4021820744000803c2029200e01521070822032000196400e4201e0b40003a0007503410903544000e01c1302440341010074542080881e0710003014407051014040c00e06441c55010031011a0440c0e80304805d2000c90240700200760b581c050440300302c1c41000950700382a0000344125454000c87c05035a20103c84100d0700300000312007602602c6260036850401100406000c0c03c1c0222070032243d0654800c441101e1400800c1401c00d90302100401c0d10b42c0f601c0350b04400d2031150141c206640241805159144099655003450b1407070f84814070704990510041241090b044080c0940c45900740c00c0c9020310f03068034a84450041c0301c6400aa = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 175324856 1250 175323606 175323611
    0xf0909010603170403120c0510060b0403050c0a0503060a2007030c150b100804062022050a05060a1101090803040b061918020705070b09040b06070c03060519 69
    0x28200405400400841e4001d900041c03001000000d880428403c40c08054886071042120512861060341503400c014003440a98104d20981400c500c04d8602c6035010315802d98022506000380030091200c1405400d0803201001094a0140030984659000342440861941c400490807085151200140c3c0701c2e030710a503065503d008a20340a006202e2010301640ca0a0321802051a404107511510944400045c41d6220345280654100c9904800410403a103840c1c0f14241d544c40e8003943c2404046120781d0560b12a00c0340708640d258529010780702e12010360786491140404c45074a0300c0401c1c00503503205407205a48c950b07001c0c40540340b9a207655201d0810b5072825030318401780030045000e58019449425480459181c0c4403c10a5007440100601040307110101e080100700210800807080981011000d400c04840e40c65071400c09085a0011445040009030095039107880e02c104944a40c04840c2c5c5414211951211810041c40d40001498956150081403a021a03d03429221035846080103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 175326106 1250 175324856 175324861
    0x40305010906140c031005090601030e0a0f0311031204060906060302060304030306080c0109030816170a0207080c030a050a0f0303090b1504050601030513021e040204320a030b060f09 80
    0x2070b00080c902c41c49260307081c004401c00300304018088400c503030103070410068502c005400c04040184400300a042181450756424005411a03c240180c01000d8010502100c0030305407801d000d010351501403404a41034100b000b29005e1030000091054015070007450002e4515a2494148020215508040d600c4403011041104150b4542c0210b000e880d1660161444244108015100c4107614000105101410b00100c2c0f8980d42111030f0405140c01001000b507040404c2103d0708503940702e441c242d00160464041802409010030000128000a400034840c4401945a00e0784500e03121030010050a43d034126074040c10320a400054806810211102e26030a10201c4116007401d1205039074007960809001800075070207440759a201d861120700d101c0100b803035503080202c41010350801d09100c042c4c01128142c1d40d125072014102600a2840c0c00001160f10714a200e403c103d2200301e0b88008e420314802134419110307220a1812241e0003c1014009e0705e81c50300248c0c00c601007240054010036500d04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 175327356 1250 175326106 175326113
    0xa0f1b17010e1203072f0109020321030103170409180501050703060b040506070204091403040e0c0403020a090b040906090b10050114040311120703060501050906060a0f050309030403050109 83
    0x36882a50300380640204906901c0800c180e403109a0928403000c02c0320f0910028068a010341c20002d42d08002074204180003c6242802900000907005180540c4d595807000341181000c101d03404442d0090a28485104004908030900e0b120500006201e08640050240040e1045003030350058209041c0600007000c10310502507504680401c10342d191740c00e000c0898480b030f010780b150344191408540741c0d0707140c18188008d11890b0340c014034041f03030050b5075080d20714081040c81e00c000c4800000840034542e51450044c90102d11100603203915800c8004020400041e0748041900c0c08844400202044480b6004000707002880c0d01da0b000b8140a04200c5104100038031400094810000c2580b034141c0584c0300c1c00111a5031011072400700346083c0410061002c2801c81c0c0005c1d440d07440081c82c003800c0c0801030040c0380c03d000480d84111406a1518014420303480e0103401151700c80b038150340450400021a000030320381070a10346024244540000401d142c4003041c0129409590440024400000180b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 175328606 1250 175327356 175327379
    0x4020f061e0a1e0c020f01021002030a0b0a1a0d09230a120509060403081e0408070303020601061b0204051b040b04210515060a0f03030804020103150501020a0f1b 71
    0x400c00001420803a8450000343c400052421494840d50f6090420b001c95090003090780c1c0001c0c1d800c0c10742c404e44c0700c0d080260301140015482401c800d180419803160705001d01000c4030258008403c01e4990540b0146500e0307140302074480924071041e01180c107400078207082d00c420320480c40840d040c0410b0348003040e0441000a2644006d07208100403810300c00000f004031240e001d81c0d5012544030100704800c0010038042e00140080700c5001c9901b442e820b00320710f41340f1500c1d030140e80b0200031313500103a2080040c0364041c0042c0780142071904204050084007541c41e118039000d03102c0284119aa000401e03c0c0c4100480740511100c1e0000605a0f1070780c07034145000160f0070900c0b9141802c0d00080310111842201c071040702003154000700a049200d03070064040381c8a0740051140d034016000040c005030700181091400021402500d0311005424031f0b00005003911803580d00110008190101046166030019034082c255402c8035080602c0d040c945010100c07540f098400d4034813400b101c0d9000c41c4118258 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 175329856 1250 175328606 175328617
    0x902090f06090601080709030b10171c0201331502010b120a0206270409060b010f0305040512160c03050c0307060f02030d020313060510091d030304020f061e 69
    0x110b5205006035502c8004454603072045803000b00003810103908000040803180690340000012401702c1074070351070301d4011078410004000f0316400e5100a9511840d401ea0801000c0e40000303a100034441c50084140541000c02d40c051024080040319035281a4890b0914619025141012011600c02c240001c024064141c010007684580480b207010542d6081c002445210301c0d07030191001e03060a52001d000e441c0e070134480001000d90440c0c840c0c011810f603690721407501c039142b0030400001c441005400040141c403051b002071051500e0f07c0240300110f5000640d444983c0403c0541c207a80f5840240340342c0c807100390382c0c400603d9900502c0c5e001c420400c3c003181e0074125240a07001c85410941e1070038216460440c0c83e84c0c542c0582c004120032042c120182c0c004503408222141090708000c003035606c070002c88004a6084c803405080319800d2001ca44d41e80074101c441c0142c8a4154140d0b6000c188094480c400038000a00c91944007180055540702e80b01650505080d429400c4100d0003e201c20b0b03100755119 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 175331106 1250 175329856 175329859
    0xc03070b0d180f0803040201170c03010e0a0504151518050f13080d0b010903050a0b06090c0406050909040606170106080606010f0c0308090304090204121a01080604060b040902090f06 80
    0x340b0300414030403480a0480c0c0041500324450094000507611003107000d40c4058001c0e030410006d102c11304c482c8002e250145001c0c0102010307040d0f90350f15003484280c02c00c0300a8001203c4505000511000c00d64440040c103549014a000050040c02c2d40119004a240c0d80d000c03121044181c088241e0014040c2e0180d4441d030004050074105541c0c00042000181d0700c800300602200707080c450a8510051648502c403443d1040c1045890030780c0304e031683c510b0708500354011500d51060710b040012905000901c00c2e0401d10549280c0c1c103090074480003074070502034418082d0191401c03400250070b202258100380002d081001c0c800d00c2c0030920318000f50180050340181c0c5039510420011a0b055441040c02c10900919a0765004148003107580444440b2005007206000e0701c010b02012a18550307900c0200014450310480d0007a40c455807601e00c1142e0310726a8041c0245d816000104441c000200e0010b030300643c0080005a480144000a402019501c02c040d4026111034200403101c08080c1000e4020300c030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 175332356 1250 175331106 175331111
    0xb0709080115180203060904060b0103110309060a11030c07060b04090f0c030303150b04090209030c031c11010203220f0b0a06090b0312190203040806040b04021905010f0f020c03070b0d 81
    0x40321043c801d0784010344400e0b0304031800c0000200800c181d9404607a80b2801450041a0382c0c8040103844c0703030354000b80e4200a681c1c0200c01800542842e40c0314140c0c0e4050340a810302e00794506641c624526002d500405801d1544407000c0c0d081580d00c503072240502d00e80c004044000c1c1e001d1030401705510301c1640401c4000c646003001c2d030390000a40141c0c48c411210044200c030700d01070500310345801a40241561a030036102d00b0704800c0580d603003844076032503c40d0289007186a4680c1e000000746040f0500c0c186c0c2642d0f0748108244000d100c180d52130706241000380001051003044601e41194103ca407058040d040005490920192140541118048810060003440b00710004400c05845450b0305071424071000d400c2010381001030180140e035140103030600503070381010b0380c50343c85038100182103600701c403180760203001c00c4110300d00885a250803900c528480c49240f420400086d1001c40703450100c4040c0981d102514406a20811546011040140c1512401075942c03041403095001403a41001d021f0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 175333606 1250 175332356 175332389
    0x30e12070f03021005060d02060d09060f0b0307170c0418060c02030418020a09060e0415090e0607090305070b030c07080c011b02010b150c0a0506040302160e010608040b0709080115 79
    0x30128060b0b03d0103460000c0c101701c0011048e600300715069006a03400c13542d50f520740000d100800c4c0540300c0c00c1c690303109404012a00c0345c0d0303010070103050454035007040c0b101d007401203040c405810001400c0b104031141601c0000f006481803651050504400d000244030600386205a0034407070703022001e00100c0705000511840300c049240400264080c44414000143d404002000001d03c120100a403122025000044006542c20041034100194124182c030644030700c1d05800e02d40040040d15032002d00f031316050180b14159620380d03849400341d104d40c21000b103000c4003144019450704112040d555000c0c9940f03a44079042814940600380743c0d004030034514460070040641c1070040c001e041c0c40110042c11024403036502141540c250700b000612805610910800100087d02001164000d84c0250000c00109441c50309180816a15030801101a410302d0010003480750407000d03903a0170551124240c04640c0d240c907402c079140000b0383d00104607503003096240010407014101032000d03114000070034103009 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 175334856 1250 175333606 175333633
    0xd150b0a051c020c1005060a0f0806151c0302010902010e091012050102130f1e03170714071517070503071d06030a0218040b030d030e12070f0302 64
    0x103000340c200c620302080d020440300552140b0341251006041a90a005003040740025282c1d00d4440106014407615544000703208580c40c100c00000024441d03219041c2c8128101203132151a0000030f40504108501038445c80e01e140d882c88021150f400c2049100000700d00d103820300070b01815420200342c0c04511104080a06e078180040c02a01c00e0018a2090f170000740707421039090f030fa101244011b0340d07207550078061217003950451000b8400420101031002d2542c0e0421240410088244a1300200002e2070402000022214204d0514101a03015565125070181c240245070b25a201c1c00c4503014010540046070705903c4e10001e82005c07507039a07103491041100e012000000c41c001d54107070012400500001740d265100e21402c828542c0c255499030400209500455005d42068030400d080701d4010401c3c101003064501814101c0c08100d81c107110a81400c8007094503201b500302d6800801d501e40c2030301c140b540401c203c11202c000c0e0100c0e155540d91003508000d04070b0414000c2c00c8005005041c0408001c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 175336106 1250 175334856 175334879
    0x7030f030b010516022706010906020a03020a0f1b090608010e07030b0f04020a03060227010201140a0b06040308070503070c2702130e041101090b07110409020f060d15 73
    0x206501078543d03900e813414800c4802410b8504502c201d92001007096910200201c1d2a2030703901081c03c10036000032504101c130000d0840030301900a481158001d401c00d20100c0da001a15403a259000742d0029040c100500303240c0380e007400259405006001300c0c1c10001e2014035030f40c020411202e21800070003010030000c41c2591960752a04c0042d00455080d0007203032050440e85469501310b407004000d03c100d80e1340c07a902d120982c0c1141140d042e0b001116aa04442d40540101840000009200070080c204117070794202c001c120080c000d00d0010342e44025070241c648502c0200e602554003c09100e0310742665140aa42d82e83c030082c1300315500003904100045440c4444d100310701d030f5685c104440c01101c81c98a5581c0081d000180200003c0751607500c001481125243d460340940d001d0805659052400310001d402e12400340c0c4400c0c02160100400c0b000f054551507010140d0500700c3d4042a0020540001010307114540489580940000f0712a0320314181680308a1480c1c5403001103c8115554422174501c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 175337356 1250 175336106 175336121
    0xc1234080426030c03060303160302010507090501032708040504021201050a0f030302150702071214060f01080a020609040e0304180c0203040b0706090309080607020703050f06060105040608071b0807030f03 90
    0x30724a41400410b5004840c4009503602c4032007e0101c0b03041404019841e01a85107804c03091380580d5480e0b003841041ea6024038083c1c064a028242840a800f20451103154091249554800d8a2141e50300004004507001190005c002c0200255202c00d00320746030101c0200e0170304c1043c0c03103481e20085c0003403074100381c82d02442220f4042c0c014104034004c1190b03030344013150300412060440c0035028010400900084e012030030580a4210244296680c00314507150440180c00d6801d0000c5080c010070000d00c001400021041e41034494039210480071001c54003401c1e0000580d141400f0205002c00c01c00724181402d07032900d1107880f080c0012001550309030303141d120b180140301c0174460420105020943c142c20034180c6a100b460b002080707907079682e4080d050107800e45d9002c0058024000800074070204000b07001420420102030400c504280c0000b0784907118a200782014410f0000006801f5401422420003214030550401d18070140f80c40d1000c041c0e80000000c41c003040207513030801d450b503109224280 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 175338606 1250 175337356 175337423
    0x20307080d1e0503060910090903050a0206151e0102031c05060315060f06180d150e0c061209190c030c0815010308030907120b010602060c12340804 65
    0x6141da11090148840c1440c028a0000d0481b4118800121080c172303132142c410914020f0b61401c2d100c0501a400074101207002c0c2c070300440da041c0b801301c449480d903c00100c240300c0f04009401d04040c0b1607a100517411801600c0101048058650710740300720000641280c0d224030412419101c0380300805113034001f03800041e03500c507801800e12240c01c2c0d404d0505130018226118440720070050903c40ca40010141040854200c0c2c05c0c8260310000e54641c02180202240307100300c40041d000a01001c0c010900c21f0003410702100e812111040840c3c1020f0702400f00f1860400385200c00140c00c04039041ca41e9044500744006c86255410b484009015040400d204906903030b42000c0740c00030b03440e680701c1140c00d0700060810400350003050400074203c12441041a0700314403a202141d607c1d8982800603041c41c500900c140811401045810400d050943c100e07036026031841d4100c000c00c480c8039141d56256400c0d00261141807038040001740310640214020344114810043c0703440b000d106420955418800c0307418013 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 175339856 1250 175338606 175338617
    0x40512040b040b0304030c0807030215010902040501080411040b09041101140a1b03260f0603031218120a023405060904090f12080c090a0e1003020307080d1e 69
    0x30b1003e0041c0740011500103000e80303024008001e845d1914812603101c5903044025a1103014829601c1d2210190680104184078045003060303d0800080d1503048000d200602e1908000700c00315182c4c0c1c80340d100c41d2380110302038545060352401d4500070410444080b08107000c51558524825500b2801040b0750280203aa40c41034122014034070b258110320401d000842c20721620907808041c5048080341c103120401d40b804403014a0800d071703c1208039010090b0ad024041c0d0000c02c0340d00000510210016000401e0101882881d4420990142400714000c48a695407800045101c0c1166000078080c09000d4801c140d0554102c80500c03104c044100c4034100d280c91045040f0030001e6186c1031028060404010384003003004215a0b49031000360300066022180c480001087c10a82640001401c0e84003040c00c20803440c0c201240c0003d800401c07540f00b00e40103003032801c0018049811404400008507400340c1202e080d180c176094450b4481d004a002800000c2403640613440c14070755a03420320440d000e90b0b11078 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 175341106 1250 175339856 175339859
    0x22407030201050c0a17090106090507120e0109030225030503030708040302060f06010e0111010f05011e060507150504020607150e251509080a08030f010b0c07090b120a0b040512040b04 81
    0x2021b40380d100a00040181d56a40030004200300c00d405858440d0341c503a47e0307007075091240e50500d504403110040d8040c0140e14140491000035000101d20070188907c600c2c0c850030304140b840800011040380c0000b02203001c00300c28840503d82110160f40120310079025120a80d48034050032211090496080f400135940c0b40c460001c550003070800d504114805000441d041e4600301d014400e5034001c0e841105000c1c43c1505a95a08268003503c80182280d07103480f40c03404140e900c0b1003408009030306440070704641d00d1002c1411582c996003120f1105921008610000c0c0c1c008200c0c0000b4500949040c5c124080c40d660030810303e6502003105c0c5401e42c0c08040406450800725007900115140d80001d090100900c00803c2c8680f0420284103100d100e0714025940340361000c6d800b84c00d60703410381c0000d0401e2001c0c4a03070032800e0004141541550b042c1c07400000d08900760000550f030710190b0611011301d402540410002e114000f104c0c907205e40d0149007112000e00f07801c001040944260320400c01d010f03006000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 175342356 1250 175341106 175341137
    0x6090b2b06020a020c031b0a150503041e050d03060306061401021506040e151b03040201020c090a110c03090f090f160c0206040905090f0d0e010507022407030201050c0a 74
    0x2400d03103d1101d104403001402e5407400710b40307001c9000200903c9841140c0750040c03146095802403000d80501800501c01c8804000c002d0201d00000d0402040c1c0c484290b01d1817410141261440c0030583c0001c1142d454500c0c3d802c3c007034011b0007240020341c0e1075400c1c41c0002c15102c10b161604002680107900800c05000d080207018000480905100ea015484584d6045c42e29000c100c0c0000004405a9202440c242034800301994407080010043c0c42a047c010000940e03004104041f03406800d0303034036440d19901c1100c9400103101000e620074900e80c02040c44171441da00000030b44034808040d55004c1094200307108010050108948200007444103000090344c0941103c00040030021500b09440e4092950f400503610381c106800407003800b55124100a4242410489031071048190405040748089018000b040445002c0b005814007000003002c80131911140d042220005091148424000c0c0002d40f280c500e03806004150300541c02d02e000b06402072903c004032540d85101d070712090702e1140d0031103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 175343606 1250 175342356 175342361
    0x70f03170705070308030702150403050d1a03010c050703030612320a151802060a031107080409020a09060306120f03110109050c030706140a05030405070906090b2b06 73
    0x2185400d1100d0520400e00002c400f004248095446445a580c80786002c103c000d24204400000c0285201c1100070300012030780007400c507079600c2d40320328001c1040703103019480c130341980049010160590319105840c4100c0e0361090161000758481c7d03400303025a035a19a611a20a080b85d003000d04280136140550b110904004007000003080c038102508080080d50103418180b03103154209072001036121506070705208841c4241410625040034007071a010310b5070003250f150b0203200308410615640301c1c012204501d892081e168295442059240d03656110300039203001e500512040d80c04540b0003100883d100340680690341c1a1000d0700a941e04002003071301c0300661000324038001d405000744005043c01c2d40c002030242540090088008003940c24071441814034004040e03000c042000200e4000c0307006040d848049a69141c00313403500f61b80342d40359424100d007846100c3d03010107030fa54600000060b00d220b80d81c002da244450112211141802822040540110190b0300202e413540480400c000061196 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 175344856 1250 175343606 175343633
    0x6110d080907090e1501030c1a072a120606030309080a0510200c06090c03010b0109050904020f0618130603030804060507031503032703031e1206090507020c03070f03 73
    0x4d4112282d007020100b404203440b40c20707041944c550705500360503c104000c3c0030908088000c0310560515107c196100c40003854482414246480d0340700100301d0140d425009900050100340d03200c18080d040d42d2416400a201c2440200c012030105c1030300140c003007804a030000407542c01c107018220900d40308003240c000b000c000c0221b100585001a5000c120803201c0040d11513520340d0302c0205241d040505030140791403503c1a240c0e100b03a0402e100ea8010b81d80c00710b18602111400d070348003841c6e030f29644000707003a20484e254500d03042140401d080c0d4041c4009422000403150a03582a101841117511100c103452039030102401255107000403400190301caa020030b40c08072092400140c00103480d400f041800b0340c240d100380c00090b40e41c41101110380051171048000c203140d580035002c00b49140c1d00907180c20505040da000030b08401c4c000804080c0910f181c0c4240805110702004100c1c3c54403881d100800c0e05803017000052080005071003050400195a1050f5a405407070a4442c61441e510802481c440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 175346106 1250 175344856 175344881
    0xb0304060f0f02040308070501060905061c02060f2d070804180605030d0306030606141507050c0402030703061409011809080912060414060f040b0a0e0706110d08090709 74
    0x3511401007042c419840540051072080c4056541c407a600d08103c1d080d00c01c260000400c0a02e00818010a96100d00c00d00308012035000d0294003400482c00018414021400003203101c2000203640040035054001c640361078060745d40030015207600241140c10901404ac2c0c0106110b1040000740045200d804507001804940440803400c907407200c0c0440e00b4030a0325034116000c41c1e122001441003051601440002c7d1030b440010501c42c03c0316500041100c84c1900b064882450001030a2050040c18020b80b545514040c1c0155a02e06205d00002d0003440203210311741103120525500c0045103000401541250610180c09170710a8019003448010003407032200716040d241c108420301180d243d000e01c880c13940d103128000d09007a00d8a420040e8403800c0c07103842e0b24065045042003009200c650801c1d1608160440c0c10000d00ba1348940485000f80403c1c130042003603100e004c01c002047e43e40324903413041c100f4218040d900d088508413000d59460b0010744000c01c080d0040041840010025406140003000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 175347356 1250 175346106 175346111
    0xf01031707110d080307031a06090f01090b07150b09090d1404030b010b0d0606140a0302071a09010b040b04020702030601120503120106030e190f150f1a12070b0304060f 74
    0x6810b0001024140800001c8812040200410080e150580701e00c1070200500488120001c41101c0012994415a19050f200e10005901f050031070f485520040058414082d00544d07407940ea0600004081e0304900241005042200c080402c0c1048805c40d4015030703154000b080c0c0c0d00861b2100b603c18008103c901c4004070401d210020110300003c41450086c20301c80300f070650b150207517034202041d10341c01c0e0884000c0c42282c06110341204601d800b01c5600325118900141c030ba6446162000c00a9a4400c040f1640c000d1102803010049040d030000340c0070101245c040040f01110810301c4140c2c064508080d5140d00450010060181360a244003642c40c450826649000c0d41360071002070003602038100c5030010760307980741d001121507003004852903501454804440710550f0366074030312007543c1100c07000700701c5225810040b10a2000f1307013116440000f02c0006001000e1900c00d009003210101d000544070b00191181d840055a0200d225030507030b8003d025140c03555030703591200c82c040c0c860011444101e45d03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 175348606 1250 175347356 175347383
    0xb0d020d050111070b0412090b0d0b0d2f0f100302030411090f010315060b0301181b020d090e010503190503160305300105150f0f030f0f01031707 64
    0x229900041013064801c240489003818181403411f80581d10381545010b1008092090000f407410038140c81d010160003101080c4c91034000301150318184d800c04018100701010130644425062080600c2d0301c10142e260a20580c6100020400560084801142c01c4010080400c0107240300f50025503002e401807030349480203030010001c01c16486c0c1c1107076a011806483c0d0011b000304008807020101d0029100c106114490529903600158481031141840c1503080c10032150170010076070003c4001c10466062030400341180c04c0040c0d01c502c0f036244030200040304408041403991403180c216043c2c0344007400819800c148039000c4550200b060038290340b107110a00c0b01d142a50781100c0c0e04d02c101e901c6a528240c4034588600f00c4c10344170b04164038003241c0102c1c0b20781e411400903c07480a01e0449500311801d0b514400d5000300d80400d0b04c00d2002401521400060503002c00340c214000f1400b400351282c032034002d0741c1c0d54114400502000c1c00f0003011080561001c6020a0b4804042c0c00924002d0b1000a81403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 175349856 1250 175348606 175348631
    0x2100e031504060203041202030304110d051504122613020607050f0c04050604140412091e030c050102071a030c0409020d0515030c1809030c0610080c040b0d020d0501 73
    0x142000c650845043d0303000420001000504440d285460100c0d000a500b1810107030366103c11514000c080b00d004d410320041110030f10408000244540750031040000c800d043c079050000a00d80038500c00c601086500c200300c4000311090354103055803003c8a131903c4050300e03a1482c1c400c0714049040107a900c0302c824000c01e808104140a2a40d180c80c9080080a0483c00c0f6414081910401080103100e00d10f00704420020200d1305078800e600a5106040824004881d0000d4550b801c0c4c2d6044400554643c81010301c4030902e10500c03c051304d000d20490f001040e95a80126a1440300f4051480142103056401001c0c0000380060b41d000b0b80000705180c1003a8555800c40c003280c0091550b80b480c1c98561050007155a01c81c00d4503694440c00b80e001d0030f400f01800000ca00e2003803011010081c1c0341a04000180a40710500c00e48a04044190540b103c0382006d02d88041100710500600380701e400740c40c10301d40081c83e00e881001d240a4000e450320006c00300c10740800071010500c0d03800b40d54654943c2040e1004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 175351106 1250 175349856 175349893
    0x90c020f100c020118081602040e070303180e04150506041e150504020f040e0901090204090b090f030406200106080627151f0509070f020d0206010302100e03 69
    0x16241d8034200010745889218009081d590048000e4401103140b070700c4040483ca845044501d5440901116101c260061000c10010401e0b01d0307021310140500c440c00b00c101070b480201d0400115405a50a130803648449400404240c1034500610000a07401001800000380e0001c3e50b0081004000244080d501900030380154038041d049030115642703141803880800081e5800001e0102138808606000070192040c44a21a50180b08403d04900000134500c04003500030f000c2c1a075024105004401091515494850007522491654085c0402031072239440000113a80448485135502101814449403420111080c09183d403030554aa40011840d01410000540619450110a45c00c0d2042d0b0a40320303084000d03000e00e04010b40100900b01c0701c40815110060b0403501c2d0019103905202c5801c0101580b0b0303002c1c1e014a0300720440004001009401802d1640448841d03025251007481c0f86c40c0490700d410090100039484a20b18110301d000c42c0c4100f8101003000d0025040f5446114902c2c442440c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 175352356 1250 175351106 175351123
    0xe040203040b071101140604021b0307030c03080a020a020a11011e020d030e0a020a092403051b2205180109060b100906090e10031b1a070804090c020f 66
    0x450081c10003d1080781980b1540d400c040400c040001c121010400c890140e44001c0074019500c02d03500442c02e07032000d140c0c030300042c0a440b5041044aa40d28001c2c6805400c078081c030b0b14250082444040013a100040d00d00848000081c0340d030250100614954400b03000c0c00c02030064030304000c8000307281e03512802600c115043c0c00c4000c0d00204525150408024140d9401800480154203c0d401d40001a224070104000761600d140c404160304100600e000074482c1047c0140d81c04074a40c0c1e1000052007404915240822100740310b61550705c10381c9040c0611520103007440045c41000903412807031014581d100c03a03006070f006686080c0d10b03038030804480c1c01d4410729031050300c0045d544c0760891480d252030b0720010721300801d90030b064041d03070700c1c01502801307901d164401d03c1c03400e00d52100002c40c101e005840d218095948840035088481e1f00705440b2030200346038000c000105084402c20100303407084005035401c80f603101503249c0c40d250038102c95001400b03081a401d000d41c481c02c00e0014a002c070a00079581c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 175353606 1250 175352356 175352363
    0x12030902060d050f06030a2003010b1c06050f13020f010504090617010f06060f1101021201030b060a08120d153201090f030b15130204060801080d090e070e04020304 72
    0x15079013020261490604000741001d84247d200751004000518240c2c02d003041002804d9280d4180c0701810042409041e0b40703026507500164502c406112900c0d40040b054a81c2c2c001d48040105a80340010201a54001d85142c403e6840c202c03011401440c14031000340c01c200d03040c941282819901c5007960141d8046800c640d540b22400e00d42814407500921513405600713070b858014014a880d000380034010210243e803c05c10009041243c0b282c0c3d010940403120792901241540c0d1181d0780d241002d4003a0702082d150140304052194000542c040001040c3e00f95080b004030b000e141410b1074660703078020032444241070202c0171075803800a40d400d401c1c03400078a802441c0a8810706c02c0d42103203d04007c1441c01d0b11a5040c00803110f070500603051091400c03000d880d40011062015103031131001c01255031144035560750150b40000f9403001200250054000c50360580c0ba518101d0740c8410074192184003240c202c42c0000c443d030004100110140f5034080d0011151300b0120169248507011400381e90086034146e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 175354856 1250 175353606 175353611
    0x201120612061a010801030803070201060f0e01080d030b1005071a04050d020f06190228050405010e010c02062d0c03070b0c03040b0f0a1d10200712030902060d 70
    0x6003800420700600c0d440107420b280075400f4800003030000c1c00c440e1041c003000d80a20004000106503d000f540100081d150001039991890b903610a111001300703090043c40702078041d0369040101a4064050405120300091554002141d081c904440b50741020790f05540300c80b00700e00507480320700d900c070f205a00135402400944814041d82c90064075001a002c54281d40b58402400c01206007046c0203a030000c10002d13080903a9445a4106450902908107020a460032034410241d003415006070041045550a2322020740e00000300d0019202d6541011010350060000c1085120016074044000e11410507540c1c03102d117100100100c44200d802c08001542e56610004040c406e201003442034650203407000e003800303103585415550140421405849010004140000701d1119413041c0c1119070014007104600942080010115507204888070440014a2521b515541c5c09a12002c0c1c00c40f4407184201040c2c0303400481c0d50384030302040380301554104040c0d54808500050b950807006058008000501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 175356106 1250 175354856 175354889
    0x1b1d1305040c0b070b04020105071a09070e0c13090207060e03070305030f0a0603030e0108060f130f05070c120806060f0c1e0c03100b12030f03070e100806040902011206 74
    0x300c1c49180060f0840460b00fa01030210f5000200c02a000da940f250742842c2c02c0b51501803074608092207030004445040518241070801490074400580720703017150b02c85581070700c10303413100100d0880c10300c0b90340720850308030356030020a10042c4495002083c820b0b200d2440058001c1c00780b8210750071900700e014103c00080000003401440e0000d511103c0c0c1082890348104039162071568090b02a070185000309040c0540200000d400d0307034402c898440340080180c90300325407105402c901c000030b040350380802280c2494100850700d030600c202c2064a0310796000c104107641c94090030301aa134600c002000709510000c20040384440e03940f124043d080410028004104000d03e1030f051240d900301300c58002c0c00c1d41c1d000b00418a0603540000d03030380101000000c0002039000001c0081409040c1ca407900d8269803000164100c41d0460390802140b24821603030354145240300c4107040020302011545140b000070708136070100b5481e162a51125110b41e02c14140130780100301100d10001603a50030741c00b0304400080d0440 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 175357356 1250 175356106 175356113
    0x70e0c04060306090b01200a02090112060f090c05010c050f0a03030e010506191404020702060c0703050f0705061b0c030d03061d040507031101050c01050f01060f031b1d130504 77
    0xf501000d020044014030111044c400000d0407400c0840d036002c400d50440c18100c0b04038206128920346550050403200d541d40e100d0240f4142001c61550440d481407401c07850700100d450a02c03070030084540c00101c0840035803404004480e0850100f4040d00d460141903c89005018104146810a40300343c41c0410300380304100c03c050860b00010000c41c0140c40780444240b80c1c610810010081d0381c01d15691200c50840b00f4003080081c0941e050094100e54000382406c44010002144400c9a105904603072000300300c0e10510b034682d002c82c85961303000071050001c0a0302a1642d00e6075140d100000003120500188400001d161007035094440300800d0b621130090042e410680c11145c1c14a0030090030307a030306007850366034159148091b100241ca00cc42c1740d01e0300f45003a8440c10444502c0860480240114101a501040c0d8030f1428400d001c0415901c40d20036942c039019001d039012414004481259111840317201703640420108442000100281030036a51742d0b82d51641c1103442100901c000901e81c40c042c075 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 175358606 1250 175357356 175357361
    0xb0708071809020a030605040501030b060901061d01081e04061b0c02060417071701020a020c121005041407181104030506011a040b0f03040204050705031605070203070e0c040603 78
    0x804203030800800d84220901072900911820032102208001681c40c440b43c04220000c00d034640100c0d0744641400e00000500088100c11030007000100d032507003c3e40e40d0790b000c240c2c2c00c8402c00c00c00c0c480307950707006540b8001c540c01001e186a01c006100c1c0118500341030301395110285801110101c9a19a960342546014000002070044d000c04504000c1007403201c032740001d100c03409240300d00031100720030001c10000f001080c8141b000401c4c0c080075080d00840c80c2c81004c0c1c040c0d0402c1262030018401c4c500c3d1510203141100498501d8040c10015168a0584450240c05024002c0c816140189500514515040100f0241c40280382c00d02ca0360b141c023448180d100b02600c40401d40120200e005110610108401045c01030465031002d03010700081d1030b104171031165401103911050804038081800900c000204000303510551080380c08104603a9401c40598180c0010707a02090304200300008456032902640040041c0d900003021120301c10360b101e004110300e104c200c0b4a100308072000b060400c00d07d074150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 175359712 1106 175358606 175358611
    0x1103040504020c031603110114010501090308030714030c0403050601050f10050a110102070b07022e0e030d0e0a021005030408121e0a0204170106050a030b060a080a0b0708 75
    0x901b00680580c003071400300d0314654200000c1e07490901e00c403103640f41a40c01c1616040007a50568813070030307080d8200070611401e00484c00b101e0000c140000c00910320404080e440166502d0441c40c00900708281a444103008010980038044150b46450b0200101c103494509030ba02e42500100455014982003004241540700190000901071030140030b030300c60314050302101c1c480b1035400c0c22541c0804550806114444044140081c2851290001c8514a0307500c000c40c1d080c100c403549020103c404d0544088000d500901c540c41c11030170400016151015242821802c5150075240c505003445034084507000c1218000008824641c094270f05485c2514441880c5518601302c0b00da08001d40c898007482d04660024400b07990a075405001e01000d554003d456502c580c0d24664581c89030490240c134039644103450041c0826452010080c0480d40c5001d41582e03c11410710350700c00340c4400c0c000b = true := by decide +kernel

theorem cover : BRFrame.Cov 175179856 175359712 := by
  have h0 := BRFrame.cov_init 175179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 175179856 ≤ n) (h2 : n < 175359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
