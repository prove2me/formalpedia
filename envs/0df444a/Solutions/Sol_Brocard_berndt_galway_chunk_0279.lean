-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0279
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:56:50.738848+00:00
-- url     : https://prove2.me/submissions/66f1ecf8-0f78-4f36-aadd-28fe9ea871ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 50000004 ≤ n < 50179860 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 50001254 1250 50000004 50000017
    0x90309031b1e06030c05070206090108150d081308010509030d0c14030112140d0905040e1507051801020309010c0308070e0a0f0302011403060901120807020301050703140a050f1302060d02 82
    0xc55200c2c0b035240841c003905480c41007041a060003810b00c08040503031107540c2141c9901d182443d1124050340c800585480d51781c0b01044075504003e41c0c7c1c4082d400c1241c290002c20441c40d0310181180a84e9503194041d0990320300721403060164100388403848400b2000e800602800003a406c0c80211003001d440d042019400c260720251a0350700d000007840500c03118010b0407030985004409081030032450300015020044600c41e4030b0041d40e49008140703100703006010b00e0490b2031300850260f9040c107000500520a804c441703580c0303400e107940300400c15496000004444d1024810b8454408002207030301d09403204400101048180800003503001440d82e01d00e180a17001d4076400400c840018218000104081d1843c11442c08502c0c0800901c000c1c5d03503841c4a1241104c04000c24051120000e01d0071012078054002c00075010360030a1b084c40902501a0030410990080c50f205441c90359841a0031000d668050b136921000c42d00c0b18021a43e841104080da50325580090001c6241107400081d402c100e92061 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 50002504 1250 50001254 50001299
    0x806032d01090f23010c05091003240305070902030106020c0126040c060f0503060f12070317090108070c0b1b0c0604111011030a0c02010e19050f04090309031b 70
    0xd04902c8100005841d201c01d4000131318002c0204280e001400b802c5441032100300c92003000840030b240c02142c400d81000c1e9036403d501114051841c03c0c605403050b00f100f01e000440e150b0048500203e08030081d4070a80c0e04a0701144e0003031140107900001510701c0800d81d00454442c1600c16010104c500703440c48814080d51250104c6503e041c41c0480003800e00006044035010080c2c2013040c4090303690b07a02c0d0301c124041c80440301a0040c1d0700c2c2802103071500000d40e200500b954280d007001075140400c50060300541c00283c954291568488008071429a2081401060000640c0110341b0748038482012a440f100340d022841d10b03090f8000340705132409200700c604840b440b003248901c004500f030503000921035001d41d00708410b041d5000c04c0000d45a00a200c1504100016522100c0c1568807c8201404119026087c4000d980b680310100804912034007a082c0541200290600326041030b20a40b91207a801d070350b9003842181542c0d0345d0703200480c00c49544050340c160b020002c610b903850140c40941c20401c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 50003754 1250 50002504 50002523
    0x1305030a050a0f231501060c1127070203040305070905040b190605060706060f05011e0f02010b060703020109060b060c070308091201052d040309050103020a11010203160806032d01090f 81
    0x220324117840300c41050704203004201049001c4000508110005c012130327070301144c01d114803070203c032076400603064013081002c0c40202d0282484096038011008100780c038000c5d015180310075201c4041e801550001c0d6030040510b05040001004c5003281103074a200303854640004549140d40d84c0c00103080f40c0000c901503c3d03459807a0313020082508440101c4000b49800e0034214244102c644200181d92030641891060120210981403d24802c0d8009030b011640100115154811420001d0082954100844000d0324020300c904141ca40002a100d059580a00600c2c1aa080d0b641d0480b03240c010444d00381d004844502c0100da039080a0040307e10035100c0e00d024038203000911204d010801400c20420320b4010032402440003203a4010f1800c2d003510000e00f0056900e510358402141c400c00c24501c0702505510100034401514528070380030003c0d071195601c1ea162074488104052701c981580d42506031075650a4442020020310303c1014044030100d10000401d0500c5817664464407500040c1110100030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 50005004 1250 50003754 50003773
    0x31e0f061a120115020307080703020c0a09020d0e0f030f16060906020304030f0507020604050405060d0c03030305010f06030b2808031602010305070804021806060c01111305030a050a0f23 82
    0x40450000d4014242000411380d100ca002102035243c0c843c0d0310f8054200200002c44805041c02048506207083d009001c0f03003016603880e19804002d4100e189280a0b15003020611803000200040c1905550310038000355181c10000d0340041d0242d880320400d2818810304210440c08205a0300c6441021402000d000d1390302d1030540340090109075148080001d00c038040c010b500250b03e8800035241031390b40940300080c00382c0314400022440e03a04041c0042c098130b204c00010040550581000d4100c2e0b5262500f48842c03900d8080039030964509040381d03500001c484c009840910307038000c8a2600b855164025507111603e910403c0e00315800145011210740c4414840b6046590621455a010a55152050705410301e9400918400d6001c820300680c001c698000c14220f54441007241c01c03040e1200c000b0008004e4020058025801403070b10b01d290f41c002c4590024840c02c000c1a810a43ca80c00009400040240d60358200300805021013502c006900403852101c0e050056480c44040940c5002402c0a11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 50006254 1250 50005004 50005027
    0xe190501020c0a061d011b1a06030d050d02030c19020304050a09050405100b06130f15090303090e0c09100206100503120a050d1b050712031e0f061a 65
    0x8610b42c2d81e015585014080150a82c0660107040c5c101c010b43da0150355600303030b40049038a4441031001410f01503544180d00100601d00303e220002d15036030540e200c0f0a50f5103404141c0c448000c10b40700000324504104a003e24140c0b0b6001710fa1040d01c920329541803440012000c21025020400300c000345c0c0c4002400c0c0143d20386039035803c0c014107821005028523307013903881c9074035851040b19500e0515110041b46110f41e03104010391740d607900e04004400450390703074000403000c40345144503400110390003c006d04589e61040055000b60307a0151108407007107180001d2540d03900310042c81c1d0241d0b204240104101551260310790003251400c0d80c000c01c141e08044440c03400700c45490707102511907484074007596000c007000d00c00c3c0d4900c0e01c1c282c1042500d41450441d040042c2c8901104003c5c2084c0c9442c02010740c50b009809010030307501501e101442c0d00400344055007203a0080e056a49800c1d07480b10010785080241d0003e80310349100f54804601240c3e50100940720040401000d8520b91000ca4201c3c501e9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 50007504 1250 50006254 50006263
    0x1e01050f0d15060f0f14030c010509040e0a02060309160509070e100203041503060503010e16090b01050403050102031e092805160f080c0102120406030b03190f0c0806070e0405070e19050102 83
    0x1b9004c5014046000e05100081c6c114803c2e20b8a1034000e94907100c0c003040c419400e202c1300320041c0e006000240d491a14800550b02d6000b0407006040345204180c0100b002d06008810b248a00c4041d00e420520854a60030480d0070300b1641502c1d82144003c20010404403c4110b00c2a070081d1591400b040881c1420201803e5900810400d812035110101c090681424040000c017115884039000070b04c070302500e0048810780718540000c2c0071980000184020250281d440344c100c2e643c90b101c00c00481c0c40320000c06403690741078070005503181032201ea031111800ba0710201003802840741040f10038469000d1201c01c903041041d0700c030100c03008990208000b000018000c00c0c030b403007400744081c00c0c0e00044c031400d555260085000700c80030141c0c3c2d03440c805020f84042001810000342c001e0404112221881c0500258895003002c0b280a03045c554002035609000850364002c4815031104000d03441ca4405000c01424010a003500704a060343c02d21030aa00c90141482c84a907003240d284413210304010019241 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 50008754 1250 50007504 50007539
    0x507090501021609020306010504090e0f0d0503010b07061e050907150f0914040e030d09030e0f13050a0b180a1b020607030908121e01050f0d15060f0f 66
    0x1950031011800c01100050b500540c180c40010303400503183e0315154012501d5001702e07007140103101c1c33400010902e40d5200080c90410407110720102c613210500c2280444440c0428411320a420300c0030701012000441c4d80e0080640c0c0c5428600c00b405928000c01020b007900c005503035080054100750000c2c002c910300e46514800c03080390b5051940300e500a444008000c41c1d0f140c40f80c1c00e284860784588049130384c1c1e95005007448807034090072251147c0b82a9000390080c5910103040b000f19150f4083d900040c28901078000d0461001080302e45401c3c0040303100c2010f04001081d1005841d41e611007401d040d551140c0040c00d494510b803150001c0c0c0340100203003084843c1d00900d0101841e6aa403501b400d658002003080d4000502e127408501441035241030203050040c03002d46080d09543e1002c020921b6001640f02803002010800341c2050390342e880034030100c1c031005030b09290420320044031381010905024488448184010002541c91703958000e8803540003030703604440018000c00004001c04400b41101208 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 50010004 1250 50008754 50008757
    0x6090105100e060a0f0f09050105010215070509040e10020705010e072103020a15020306180702061b04090509060609090c01020a03320406020106060c0c0311120a060507090501 77
    0x180c1400105800a81e006114580c10300e65074100041c5030b9103c041c1200002d200503001c070841d4036103801d072440355400c043c01080e6006103440000070b1749610000f0b007181040c07220201554075480d13150044030740b0317030005107240c3d0407546a60b07400d18804020021700030042002480140c940080380b62040c25030b900c481400f40d00c0e40c40013405010007004104a044000158400304880040500e0143e05007845180050040c0307200041030020456203400847c4105e50403104a2100c566005804142e40350030348404d401640079100140700c00b440c03d580079041c20410828030781000e1341c4010f201c05488045844805641020b02030020310b00b0248407440c2c01c540300300060180000c45d90700003952200038480103001c01c01c1200d48582d80c1c10300030b010f913110384003035180745200c0710784001440c0300325840ba04c2030800540ca081c2d80010741c1480741c4048450719900c580342c110842c1c03450300d03448220700401403a00e9105210345c0c1030501f06001003211242c482e02c5200d0114941c0380099026001e1400b9038031450 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 50011254 1250 50010004 50010011
    0x3021b0610120803070e0315010e060a081614040e01051003110604030503090f063001061b02060f160309030204060504020a020a06051803070b040b07030c1409010302070b010308030702060901 84
    0x2c0004000a0541394484024070f003d0400010b0000001c2c6001c102e40030a881000390b0000209030300010042c000c0c8541015540e160b0303001d41e10802c036583c800905400b030300401a4204140706070040203140c000000001800841e5081b40140e1990031035005031581c1c4a600d820080400070494032001e403003500d003012944541460b145454007510b84c407582a040b40f06880316040d04007282c2d0703450250385003131076899510b4040340b500105010300850703031070400c01d41c052081000141c035510039031680e4030b102c00003034907030001b80c50640c2130003455003015950900400c4c060104400c405c00c0407080c17000444c02a5221001c1c00d103180140000c6907441d4003c40e020314010840700c8040b5400091506549500c01710004a45e1f441c03485084050b0944403411040340800202c1005000c4400002d5004600420401d101030b151050154111000a0b180310080307855044000307070f030460000c06010130700c1d8103040c00340c502a000c0c0e035000c0f42400d00743c008803044000401440401c5070304000407540f01d141c0714000c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 50012504 1250 50011254 50011289
    0x221b08060405040c09290105070b161202040801020909090106050a06111e030d06050607080306010804020d050f0102130e090606091b0301090e0c040b0906060a03060509090715090515030703021b0610 87
    0x315001d004061151001002f00d080c0e41451265400d083d518130400402c5444a480d81c00d1345000c0d40c0040c074101d06c944081000b0441c00c00041c801c010441d50000e01700c680441c43e208003170703030700c0400950300c0d90180c010703d421701d00740000e00ac00b0807800c0c140c0040555510305809180d40100c807882c1d08014082c2a05210000c00101da0004598010000b42031400782c5580c0da00c005110400c2403500140640030700a40b80c0205c03081500030303016515484044003001d545644020345103041c21a40f0302a59408030740032400606180904980240c034040c0d150340b03c01d80c0e2a030740d1032007640280d010200d095070b40c83c0d803243c0c9420103200c4101c0c401d50844040c040592042c0014600f403c002e000c4610900b070010b1820207440c081e611900003040090038001c1c2c10b15117845000c1e2a0b41c500e100311641072080c080074042d42803143d08601c003038450080c004081003040f6111080c5940000f490401815420000d010100100128501501049000510a91801014400034220a85d11801c85507800503d503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 50013754 1250 50012504 50012513
    0xc070e0f0a1b03050603030c1002130503010e030f0307020712080301030b0108060601300609050915130605070c08120907080304030807060515221b08060405040c0929010507 76
    0x8042c1d4420262030b02044039152940000e081d07100d4600801c02a216104140c40040c3c8e01d500544420400300315210440c507038072000e25023a00c03003040401c0300300d0700304000b4a00c24950345005103802848620494400548a502e4034031003440c0b01000303607218a07003c401001082600365109000d8483d60000c2c10706807c0200002e01102c0039400c007800303402c0030016011407407215080d080140c5240440c0a2000316039a9038250014403042c1c03102a40c60181040b105d10001120b020b00b03020740d101c4250102110681d0311100700908000e03140130300300440c1a6440001c0366502c800b07004500b01c0039914140506010345003515149032036124032842e400501c01000400d0010701a544180e40122011031f1682d2a80801d1810070050394200307500891180c0f0004a41c440c1c2c4407144421010300404115481e500e4601c503c002d2007150390240001d00000019881e802c00d0f401064203d8072445194910307580303c012540944a072440721170440c603100140c1e11040c00540f10400a440400e0034010320f03160341a1103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 50015004 1250 50013754 50013791
    0x30610050702030c101206300b0f090111191d01050f07051c1e0201050112020f010306030203030a020f060f010308030c130306150302011701180b01050c070e0f0a 71
    0x4400d01c05d00c03101c03503602150f50040e10741164034888928104039050700c401c200d4002d0f070f491441c07680c000c2c052444180328000e41d4200080c003194104400341441d81d20165507a6013810000c089060035500c55081c001e49054090191845090010114000c0482d040700200ba1808480500380c1c03a401c0c01c0040d40c0ca59803c08e08070703011200ca1480d000d5551005003485c501c0c00e40040e002008500d03807100000d18980c0d00c03455444403e82e010b12100a04441c09004900307981003030103901c01525906c880172005191880c0448075141c0c060401240c903aa50b40c0000b030840d04800c1042c000f50700040580000c05100307012456100c0c54408400701154190345400b901030100810403440e40d40c001940300c1c54000e031200000300444e8010424000000c401139031030702c104018402203000c21940c00d80645203100440c003040c141c9092892a801c281c61100c400c0000e040e02408440c1405010041010036580908c2070304060a8000000f2540382000241c41b105407400074840c802041c0b41081d504409500450f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 50016254 1250 50015004 50015023
    0x60105180301060519060807030c120b0d050a110f040e0604020d0c030f0f060605090402100e0d02120d0816020307031d0402190801080a21030204030b01030803061005070203 76
    0xa1030060300000940c0440d004200e5504500d9100303c035803c02000703201541e00041c05840450f0b075062080d4942507170030b074107880d50181d200010030403400c0e10f201131203020b0f40720001441004003810704030f10a584409061201442c000d0341d04000424102040e42000d00c03c800180c201030b41c0030030000c0c0304015607030348885000e00000d104000c5a204c0b50103000e2040c605030040c580007204003441413501e00d000b0110300d0038441d0449440d41050000629407400356109846550060030840c40b01c8803030b0f0011034825800080741a80003d124000d08003680750440c4841401d00ea1a00410000c1c41000001d01001001001c0c0c4200d1000c4203c40d03017034280e000c0150350b022541810800d8030b00c14201a4a841c40303042c1840180c0252000c140c01050005110160a02c3d103e162500d81150740c907040915190f180103072018003903c0c01902941c441d4001d200f0f0080c0703464828a401400c040e100c1c0d13110715030a4003e80c0240d50004000c8240a2a40340000e00b030008060103050051425a0395800f0946400114 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 50017504 1250 50016254 50016277
    0x304050612100302030712020307170307030c030201020c0307081803031611040617060a05010602030316050c03130e010807050609090f060102011508010c0206010e07080c030705090306010b0901080906060105 91
    0x202054241880c2c050150103940e004040c0c1d01d4142d03e43d0181c0004007010a016031191107074120004581111242e008041000100518034080203620269100f90801034118115076003081100b002401c1071001d0a4501d2080c2c0710507a40703880d20340d082490b50341c1035840203109400410042c800c8a00c048458000c440d4800d01011402d960007000900804843e03000b05028511101c0c0d0380401c0c20003003803091207000020b0040007070340d80301c0b203007240c1c0c0c1c0c00b04480e0800410050522806600d0042e40038180100b81c880490740b5000380b5054659405486600c030000c2200b0306001402541c8050003010080c00c07013655441d00781340070400011b5441401409650f0b064041c1c0002c80d8031a4400c1d08132444447c40240c990103050360704d4070b0304d40c028698a100307480103005070400842c1c010074031100300d8050001651004840e480b00546880030758130150041c42808810400384881d502c090110724020f16018145544400094001408185000b850a94641c20800c00c1100e06c4c0e0704407003a02d00441c0b07803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 50018754 1250 50017504 50017537
    0x10f1a0c0601090e0d0c0b070c0f0210080907090b0303070602160219050f0f030615060403060c120b030d020703060c090302030f0601140d05122b060501090803040506 73
    0x415004054820040d042105004880000c100e10807960404a002d000d840304035200e58400d080116900e00300d526008000303004450100e51280c0c0720341c4050003094009d00c6060401c03121a0700141c081c0000e0b41401e001b1070502ca0030428044002d104c02801040c240105002d124030080010703840303101d03e500c01001030b035020400c92441403d0071450b0a00d02d03400391600401e402c0e005070303e001c010468442c0501c943d80714040000942044490700420355000b80092410b51100c0d15100100145001c006400c04018080000492498000c20300410032035120300e0394402c41c441150050310021000240268044131480350741c0e941c00039140c0e044070b402c1038000818003c5e01d102155070b0030040d07001a62511401003040160386001c00d0090485081a5803544960702c58801e1004401d45c0040181a80e001f2850300f104030300030480101011501080740101081300000c001c9040d403100300c0061202e0340e0307a080502180d42c20981c030b10041d04800000314185071404000454600c02c0038030900c444104c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 50020004 1250 50018754 50018789
    0x3060b01031d0d0c15050901060302040c03110d0921180b090d0b0619090204050a12120804030309020d050a0c0504060b0405120703050111030f130309050111280b0906010f 75
    0x104684900c080c40d941702000d115904100e0381290113480320f800140e210324603001c03092154900034842d041c080f929400d405801d243c0c00c0b0b0040001084003400c140d9074955414484a5002d980c5450201107190946800e61b0b10640c6080366507514002d42c00521078a6230402241c2d03400d60340c003410480b0140e40802e00109942d52240402c2d01c03840403100c0c1c1e1000703806204002c02ea912681d00a0015a441600e40901c655924000481e07180c403500c001403d2207141c454110700341c40c4569010740c0d01c20b00900b408928103200e580840c4022803540e401341da441d0004e0402004010802282000508040700c0500101e0b08101d07443c0458803951007080e10400711162041041003081c401c200c0115001002080421158500c5c0035066204444180b984032401000a503c0e000c41c0c3d01d22aa5242c150b0340d0300b00d140303080100549802c81d80c031032800881d204134001e06200020b010030281241c81e585080040700da90618003a0004036026000f0f005070b4000c1e20040c4072410060440000300d401e100c0c1000709126 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 50021254 1250 50020004 50020013
    0x1a0703030605030303011203020c1c0b040f1a04060f05040803010618030516060206090304030812070509030703060e01110304020d030c170408071701090b0601050903011503060b01031d0d0c 83
    0x815400b03160580004400011955418240707440058029000d0322901100c039020014984101c180011103050302810030b0000c103041940099000d807081c040381e401c00c0c03040d48035a1428112805900d050206000410082052500583c0c1d03a00d001c02000340f10b1801e2030f60301c1c0c44060105021341c01c10443c203e00150350b1030490f040300b1001141c000040e03c44144011607602e01c4c0e00c62a000300d201510a001c041355548000008541c12281c100c44e0150905070203032050829100b014200c1802c0100a004006507940d040c01503800031446440700203148000540424203446005d100e07024002ea0074010800541c550110340c0001c1503051501542403804c074035004a0000d040d1180c60074101c00800d01140c41d440010f94001503e4208022032001c1c0d401440141c00e84a80e00001000403401f180803660341c0d4000d902030075812000030000305601200c039004010405950307101303560b01600c840d1390025a582603c03411145d0502e0303a2070300c1403600003021440d58600a040ca00e00820010010540038030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 50022504 1250 50021254 50021261
    0xb0901030f020705030304260403060507030902060c071401110303060907050708030106080f06060301031e050309220b0603040201140a020a0624061809090203030f030c1309061a070303 81
    0x14080700404644031030075400e007240c1da50000c4900305d41600d141c0d00307000c1c180c0b81401881003c4000340c49000389043c0c00c550740c403000741201404200605898800c0180140e03076690280030521810703002807621a1504404801c0001d028507520705014003d07521070720207403020007141e40c8140242c40345071190b22400310440d500e20503504040c05020000c400865441da10a07401d50040c0700c404810710064941000b000460700c020711000700300b4480591040e07000703644581c4020302c0501403030960782402441004030f00d0703403480041d0303a42c400400c2c0b0701d44141c840c4252180501c030311020f64085045180950001c2c0480c0141e00b00c11964030b201080d9010720b035100b000381c11041a4001414070002c060b600a00800d030428940e1404603103801c1a0208805d0711520881041030140e81c0c0711144585480d44201c01040040030680e0075000401c42c03000c0c461000d400642c0035690404030150b0741d21038001454080c0083d5001019094101002013000a14080242c4080c0c03126100c80c0c0d039034520038a002e5008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 50023754 1250 50022504 50022521
    0x50705030912060103060f11090405150301050705090102010e0106030302060606070804030f031110290a030c0608010816051806030c030604060b21060c0318030f0a090e100b090103 79
    0x402c0c1840c54031030704904003081040c103ea2088409208050201c03110406407041c029002000c1d80c410300c660902840d064000e40e4000200741000c450b50340008001c03074256034040b511040444c40000e41c03000d044d64240b0030340200b01c0061008001480c110780d8025116403001c0c0c285441110003292000a1080407800c480c01554041e007030008035240c40c41c0140c1030000f0003107030b4032440c080c02c00c45404007009402004691107090642c0c1c1e44680c0c2e0050b040407410360070030203142c111030030490200c00554400f00c3c0c007001c0e21042d00c0e001c4941d031602860924000c2170403404e81d2a01c19000d000c00040c0c4070402402211040145580c410380d4901000ca40f0703103c2c00022055051242e8424403041c00300c1c030707480b0a502c060155407044280d103881c44004011001c1e00d480031034581c010000111120908805140c100c4d440d9000a40c102e13160742400d610359041000d120a00d0480000c1140d810351b007107221000188504101c1d00300c02c3c03500f40407a03603041010348145400200d00142d240c1850780310f548003003807 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 50025004 1250 50023754 50023759
    0x2030709060206160f05310e0402090610020c03100605120304060f03050703090b070c02040501140105030f0402011e090e0a0c0c06091529060301030b041118070309150506060403030507050309 84
    0x20047c00401d0414170940c004a1f0b08040e1174444010611903035070282c00f032003241c0160100c000e0740c490f00c1c180f05140c06c80a003134070114080c000440b2090b075424070500080107060711012603414209020480c2d18403c03511007800c142d00400080000039001210f54840c800c40703040005541d42e44039000d0b00030703204d0b071000101601c40d04008c101c446074000764110002070082e502007005070380381d040b50403041024698860100f0300510000e0488074041401950181c410301d421004086c400e10b01001c151001071551010500304641030141044080506a002810a40034051118070050151144c04140300180031180c442580e00d0a00600c510307032003000203d01204021690715020b200003800c0b41400c01c280c01d0100c2c22440d034041d00d0001d003540e060381d400800702c040548940e6520a400b19560107226000708141a80000c0c419014120030301c00d03c0d654501040d5000c040c40e0070b4080320030900b80403401d42c0c40e00c03081c8034046d101e0300242d8003500c0d45420140d41d1010701e41005443c5001e08200c055 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 50026254 1250 50025004 50025037
    0x6010e06030f09010c03020414090a0e01050708090f07060801050d0c1509090b0307080c06030a0b03030f07060506010903050d050f04080105150a090c08040602070201050910020102030709060206160f05 88
    0xb00d5909445103119034052002000314000601013241648940d204000e0400500c401c3d20942c2e1400001eaa0b40254081c9000a43e088c12210400d00b91403049501c4000f0841c0082000402c10051265450b240001005408461304101c0081d10244040c000d41d4010461003a504003004400b284440241c0ac080000c01d054036201a8020101c20142c020003100701d041c41c80c001c10368180021001e040da0701000c094034619115034240300080c0c100030901031829403504d2440d881c548042c0f0060006a07651171800756200881c3c00e02401740d55014242c81e040040c00700b0b08201080e8049103419603e2200d252a9950ba88044040045405103401c02d0340c00d94640018442c041208080240c40c000e0141d0300e90500d907036562144c1048440c040055004502d920000600040c0668010b0003007a105041480c18100102c020901c019601c00710240580e50000900c545540c00500850040c001840109003a15110200340c0d08410000b0a10081c0803540040842660260081ea40d60001d000c13100c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 50027504 1250 50026254 50026261
    0x191115040b190b04060906051206011505030c0d060e01060305010b160210021e07030b180c0f1c0b0405160303140903070305120310060905011b150e0703050c01030b0a0e06010e0603 79
    0x100628548c814584540c0c20f00c0c1d80960f22900205007141241d0903512180d040d034a5020b01601d0359403008081c080c42803400c000c59641c2d4070302e43c4a900064070103140c01c40410360400394040d013101d0040e000300c2c05104040c0016020034010340c0c5280035555040c2d800c505138600742441607241c0f80400441c0107181c507500c0c446100c0508005110300071240030310168882c82c0c84a1103038905c211510741007180180c002c2c0220b031900c0d04042c1050307840b845d006814804034881104095020403000c5208451a10700300061201b40320003003107002489003282c00b0703180403503145079000307000d441e0405613a40321240c0101b442c2105075428004d94000310b07048008e4032041040180303240310341d44c0200c1d0f034400300702501c0c540401c032079110340c500a05681c01230315542208044984100c01c0503a03101d00445856800610380c29000c46180903680d440500d540081810390700318581036061402c800041c0d030403d403074803010311034559880807071600303e8003807002401042d124640125500803503198050340040e400008e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 50028754 1250 50027504 50027519
    0x100909020408060f06060901020d080915070503040203100b0d0b18010203160801090b10050c0106050a060207090609050c16080d050408030402010f020f030d11191115040b190b0406 79
    0x100384114041240503131540e46942c10000180039040740f581c0180d020780e414480c0c281c041d1840ca40c01c40084400c9a40856100740b91039500c10742152400300181c0b0100031b11046040801158501c03113503080d0140701031007408002c186c80142c0400050107021164000c6012400742c108000030041d1001c000f95a203241040e10042c0c1601169a48000aa41030000040300d0fa45031260121070703040140a4188880401c01c01c4030305420002642040d55a0340d48000b03a0b9582d121500d42c0102010b40141801314a81000c902c00c0f90810b9001034031301418502004450004002180d40c0506810b2022150a0503400c0c030f40d08a00440c05224940f43c5040144020b00c50b0b0503010b944118801d03a1240c1c145601c4140480e01d800d43c0381005640d5a10074840010003075040c2d0891684044440c0c129420080b81c1030101c1c1e141200c2c420460041400c0c2080d0f628004020310410a4454041040c4003140c2010340c0c400074003040c0100f4094604800c2c0c021010f00308142c0e00700402401380240184411519800f9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 50030004 1250 50028754 50028763
    0x60409090506041a0c0301051201020d06140310050105090c0c12030f060a050402090114090d08030a152304150b0315010801050102010c02033109050a0c0504030809100909020408 78
    0x50a89640f4807150065107444c107010121441360050610040c110f03460a000e1104001e80044448403554081c0000100480c1d40d03c1004010013441e0700004030f2000c118145414516804001c1803254101130041c0055105c90b43c0383c42e00003601110090380c5030754544800341001070110381407001010000c01e00c46605019a404c0340900c40807200008030303c0e91354007040128490300507014041540c0b12070201074040390101511840700060210f440c90300b5180c5d41c2d100704d940212650640d2179a100b0002ca100c1114a20041c041e0469a403c011144200100c0199404103441c486104a4a07007444501c541c1c44154900020f12003030150036140d08025001021020000d8903003800101c22000008035580305001d05100051550003849c5422003c00c160034105040c841801c5600b9150044100786000f42c1220b00002c0c100c2030743c001580d0510380001020b49000495680400c04144018000319041c50210380c500c40e4100ca116400c00c2014030147c8210070795034842103541c0d101150000f0107400126 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 50031254 1250 50030004 50030011
    0x902030a0b0105070b04020d050f01180b090115030b07020102090d12030506090c04050411070f12080906010605030a02090f060c030a0207090e0304032303070f0302150405100902060409090506 84
    0x18428520304600441d03c2d401025030140a202c082c10209015043c030a04000b02c1078016000c0c2d9452030600d0300c1c450b007500c010355441d202107600c0c0c00c02d6000b032041001c111500051000002d01c030441d461042c4049649407400050504102d200216800314001d40c121041d01d08080c014003041c001e28100701601004040f9198081303418580010341c203107040b5807140c1c4a1600800b100d4241404d003818080101a1101179a03541c0c41c04001107030201e26001403004140d84900c50800d01581c045500a06848018280381490360040c80148001d54120082e81da000000b04070050715250301e000003583c1c0a143e13030466600108009601d007850307000030004144c3c0420f1034003114a401d540300790714400c403400da0140d0a13142e04203000c1400003c0090b400703100f882d20178030201081ca14031504400c4c11a80108800c0304e140c0f1091400c4020103030184124040781e010282e40c2203151400307450f8551a80c45c035140d520b40305580c4881c60030071076682400ba90080c2100308402c2000c407101d45845666000d056 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 50032504 1250 50031254 50031271
    0x405030a0f0b2809030908120304140102071203091a071107050909030a030506061309020414060a080403270305010b010e0d080405090403090b0a03060e09072601060b0301090203 78
    0x11000510042c8003100c1416110b0401a101074503003000f42c18550007401c101c030040301000000040000c030302e0000c101e44d19420442510884e500c2c10203145c00000b0b1203c6104484190f4010700c560004507401030340741c580444c441c1c24082604041490085001e1009400003c07412030f0600c140f0410b03a51040605120300070700421600c840740c4803000c01c94104411a039040c20707030b4010400c0c0a0190f21079006103410050180a8904100c10329034881960030741900500c03111980420b08105144428519049840c8103441702072a007034400130001c210300c200400c0901404001d085144207483c80103010800c0d584d1083d03414031481d81301d00c1c00314040c08084034090700003491074600d81e50902e05401044869030f8840d0500f4034081c50310050003407000004000b5001c0c84021100019180818002481050b42c0d5550002d042410451102c40d08032024140c00301d2503124041c10b10444501c0011500784c01041c0ba00514141c1c880c000607809011640c00c1804008400b1000088400c802c0e0055402030858 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 50033754 1250 50032504 50032523
    0x30e01080a090f06020d11030a0e010b06040e0f0c09030a08030a050f01083f0d05010b16201c051911010503040c08061906090e031c020405030a0f 64
    0x241406401502c03080c54018080c541072110100000301154020050031140c1c60000c990f240c45600500100d403c100c41510609480c0e40a0002a4800384225580c56104465481c1024103203031103401d0b5004014240492115071f400402e220310152016104524002021100300c2c05041c139090006800640d04001c8803420113000c40e01c8031000001c001d060354080c00c000c02d0840e03940f15942c8180518007583c1c140340303011045c00c1000300354020f2800565028007440c0b40e60300e803410711800b41128816402000c182000b407000d600201c62481061689a821084408904828080f8513255a0382d01d400243e200800703000e6818032200c003200408041b4081d40c1646c0d0980c0c081050501074100300007005007000100700c01082603600034006035030498081c40c20301650302d0711014400e28040e070076101d6a00954010b88808280940f90040c83c0150625402c00e104180180c01100d98a00802100c1880900c101c0b03540029004d541e4181c070010000102162215140e50500d1003041d52501e50581c5d02c1c801 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 50035004 1250 50033754 50033761
    0x30a091e0305091003110301090c0e01020610050f010509090f0117030703050405090403020c030d020309041d03030a09240b100509030604030e0310020408072402100b060705010207030e0108 83
    0x880c8164424054058072070928140080b42004808a400800501890390b244106030410035004041d6000c0e0610401c0003c00c2d1181020117807801114043d29411035010008100d00500380c101030004465054030744540c0383c0d4950323005035002c0c020340138a07541082031041000080341c5860f010b141214080c908c0c603541e042c803100240c4d80f280726506003e408604104401c000c2420487d0b0f40b84ced4080d0207071054801c503001120001e0304280078a007000006900c041081d1016283c03a10420400030420003440e01024000f10303283c0e0f01c80c00024448201603039a54820300900610800c4100540c0c50b40e0390740441070b81071880702001003045031341c0d03c1d0040e4808a02e2141d4980124210b0f54465402001020075588a0f58111040f01c12502c195070540611030408401e0303a003d001070b101500722400504101420000404040c122100442000a440e510350041c0d01e03402150b4041349105000011421000360404103501d407103295002002e40d8400207a010515030300c181e0310b00183d1000d0340c61301c202e6113 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 50036254 1250 50035004 50035043
    0x100b18010912030c08030c09030613031b0302060103120e06042405030421030221060306060a0e0a11071707060e0f03120a0b0901030c0303081e01030f0f08030a09 71
    0x840b110030080200c2c810780681d40110358002e025507803001700080708501d04032a500209090000030783d41e00d9422707848500820700700b540056960381410346a4802c3c5200454a8070000c0d600c42c0180b2002d840b030b07a11080c2d03042c51a44143c888240c000d0028059584c3c1716a5044280300007641079404000b21b03c2c02c0da101c254503522a4044078080d41d042442a40880050a00500254009140e0700700b419801c0002003014880c4641da0103000100d04d10350f494030302c2c015041c14203025004000c2449940c190900b480003407800c0c194030b508100c0301440000d8241461011080c03038450344d0f40142101207940b07034030035030300044100906070984074403410b0000060f500d9070141c1e102c1c036480d60140319030010f102d00c0c04c00700ca0b00340c551548640c00c28008280c109601c030204036003200c02e0b0010346008031000c00c240145500b020801340c00401d071550011207a162a4101c0032019010f0100501c030012040c903540501003030340c03c00c2c0c0f85140c008008940c1c0e418040801d900800c4000f004482000f880c041ea14003d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 50037504 1250 50036254 50036279
    0x1080105010b210907030b1509150105031303020309130614010c0503090d03030b1215090601060f0c0201110f160f0302091b040e07050306010318110405100b180109 72
    0x2289019000744603004040360945a900106201051703c0703940c10000105e180e02070716600458000054082c40548581800b49000e802030090862038050300301c0c0381c11a640003089a6103e162080c1e004030311712441c41c040341107100e0a003040f544050803e0816690154550001c0119813a006c030000c0014130391001901c0100203104041d0240d08180031115550616000e08420540310346800180b804821f40003c081d401798500e410580c2c1d00200b405c4c60918800c0710803940200a0800401c0c070ba616104008044040e01c07040c1e1420041402c41413030441e4010610103240c00030701c0e0152503034107400d10b10700340c5c0c0c44004120308030710140310650015800070050210016a50090f20801d00c55440072100f91041c40004400345525108001c0001c0e900c003058482801040c255a80c269241480344c0011306890012502ea1200c0251507140d20020b102080c09003520303002034030f010406591381018190100426400204034140002e00b0b80c2034021040b24860400074242c070740d03e1200b5210030701c01020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 50038754 1250 50037504 50037517
    0x5070e01020d1d010c0618050c0d0f0f0201050c0f010506010f050a1d1210020a0306090203011404090503040f0308030603010e0610030f020f1008090d0f020a020622030b01080105010b 80
    0x219100e0818841d0a91440400c00d040c11010b051110701403206071346500c01c07114580724648550511f03007880c9041090a201116004a04941c1400c000c3e8945d140c441c4110b0744044010b1898149218190031a400341c8141c80400352400243c400e0301c4041c441c82c6010b0141210340134001110008455041c0b401381d816039020003050b540d030007061089008131641e44444000e2669105c523003892100c1c3c400710200940b00c50300484910150b103030003080c08081c00b9219150401901d2a0041c80144014000304140302c90108084a010651110500f0300900303507c9950065080d440b0750342c502005000010000b14000d240030390080003a11195001d072030710307080141d42080d5000940388c1d0420201706544a20740c1c0050005280307400c5201c0400c00160f0101f070b41e00d40b039400700d60a20100440072a082c000211035901e00d0400717455166010200945034604941c00034822600840c211a03240d0b0241c44000c0c0d031a84502d032540a0076100d0800c159010402d00c01d50b42d8644c2480d0000c5010340381c85081c0c130b90 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 50040004 1250 50038754 50038757
    0xb090f010615021009111215010602030a120c0c0b131704031e0c09060e070f140306220207050604050f01090c05090c09030109060b1801051e01110f0105070e01020d 72
    0x2404110344400c880030381784000f400e807400010a20031104695508000031414402d204c005c0c22141c411104825000c2e20580c8603030150740050000e01c40c0705800c03a95110f540104803900140441c0300103010340305c1414080300a00105c40300703410800d802d000ca994ac990f07a1402440c1c51910100c0d650380100e0a481580001040000f4810006166804010314082d41c1c5100305401c104007900d50300d1000442d6002d5000f40c1e4040191000c1c000c039150400300320941c030041072610700d66608902e40b9208107484041c0502c0c0c021400c0700d4481203403030000005640b031425140b00555680425013050741d0780301020f503800d441d00e000700c100aa03c414814414011741d1607101712400080c628203410010341c0040200300354160300c01044070811640d028420007040d140b0524001034140b2090003885a01d001020310380022600781e100501060b0b0701c240b41d0356090102030b4420b10915501c00b00407110800803c0b1109418840c3e030541d900002d0301908080e108207015910000041441c0c1d00490341c1c1c2443d10710100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 50041254 1250 50040004 50040013
    0x30f050c070809031014010e0702010903170601031404080406110d08010509040c0815010312030e07090b220b10090320190e0f09030304020127030b090f01061502 71
    0x4002030b2181000d03007003809004003940e9000c2038802d00681603e103020820302c05007043c0401400101c9005200a40040d9903100811030003906079000350034821206220303520625004006802a8441d400c0007e1001d00c0c01080141410140380c07602d542c0e0414054800480c4c50b41c1c1c450628108009014541a0010340e540081ca03444c010030320101e141c010380b0545c0c0c014203110300450314400401c400b03403c0f51002c032001c034a80c0d0716600341882c10a41d1801400e08050030400003480f1950300280400540750709107c000b030760001180000301110741500180e07520085000715540d00c3d284a502500e040c004c182c81000440d1800c0c20308603002246408000d01e000c1d003c41c000380b1201a8030801d96084200a420383c000c841f40d40c03d5620142040b030b0700000c1d14081c0d050400c1075050102c7c3c01d084e00103d100300110b040d41050ba0010f0850b50b5042c4a603152791508181c01e2102e290910564002035400041242590070183e00d915210307420220304202c258202131000a80d84180501d4031800d4500e94080c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 50042504 1250 50041254 50041267
    0x1308030903060106080709030f03120f0209030c0910090510030302010c3621020f0a050307030b0a0209040c0e0306060d1121030a030207020102060903160308130609050c01030f050c 79
    0x69a10316000b07003600d004c11287c0710700400040c0d680f501c60843c0702d0003a2603c0030300904810412003907500c02c4000c80c295600500c803122190b18000340c0007600d04000c4444ae0300580d50561400c2400c10554040c41085060500f44089000c5039421032040d04c0c000c1d8028080c030024030000351002001b225034604040c80c0001890801c60b050700c982c0070340e0707410401c082085982d03075030100c0c01d0a400312111802449001d41d841046181c02801528042030959001d1403491502000036107070000c5100c00742044000b840085e40c004019812281072850062080000042c19040102036035038042059009108103404900c1516107078070160601c560010b1110220b416400502846401c02000441400b82522003605030030b40c240042c2c160100d6a940c01616160755000081c6030110103400d00300316410800801c0902141e00c4142040340e5007509058105031204003011840c4c441010b80580b401c2d00e40760601c010040b011808504217202660103104a44001014101b1501d0076a100c52010108102c42c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 50043754 1250 50042504 50042507
    0x30b010506070305120a020319050910050415060b030109050a1418010f090609060b09071b140f060411060f04050f0d0206070b01030302060c090303030f06150a03021308030903060106 80
    0x2401c00d28844e2815600300401000020170240c4140e070507240442d004400c0212015000c050103802000802c0f0900c810300b4001906c43c0c990800c104a400080d845400150512450003c44410450310032401c0160030354500624945400a0040309000d904040100e1580c1200e80128048691070450320025600d0f4038500080e0315600300d885021954884020301e02400880c840c600c0c1e5030780942402314040009291041c200c4400003107091052407403d05218807182d101c0001c3c150b550f22120b0b664100d081d54284401d10050080e0803600d644281441103400200101d1118001e5100752410010710002808020107070041c00102c030030044061000300325501e41203142d0700660102815080000d41140c003c207940760300850060b65800c8030701c40104101a410403e082c0e022091074500c2c3d041c138a1507800240c41e44406000b8044191000c404201c0c1942d03484440c0100303603881c001066071168800340103800794002c58401406102e42c0c07140003502c8200441140c0c12003200501034250b0780e0a0400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 50045004 1250 50043754 50043757
    0x10c1a0403120c11010c0801030c03060e01110d14010801110f1c0924050c0403060e010e031b0714060f03101a040503010c0e030319030b03010507030507110304030b010506 75
    0x30980070885022120000104144204024458070390b558020007040d4190442c01d40b014210740300100505c1c40c0040001c1102c0006100580b58008030200e001804c00f401d0070302524200c1760000480400040d01d501e036140fa94004429920501410b141aa03a158801030883d55110001e400c0858208001103c40251500411607008a20b2401d10000f121821f0131048a50080d0116015401e04401d00668150403008144808a0100500062410104d81d4581d400341d48001800b482d00c0d0b080c040f108074029000f400d4401500022a81c0b035000265040040d4602007020901500a402021680382d00340c00340164280d001a2815180519503007960380035070b00041a40114148c1ea01c40462280391145204158201c1516526107503400c01e800c05003119040340c44c41091194102034000d05031000b0080c1da0070981b00148400d50029080410b0300503000d050040b9a0651070301d41080181600742d4001406200c080d42d4079000121010f400d02d07030720322a030300010300000300e9440104043e150610 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 50046254 1250 50045004 50045011
    0xc0e030105092e09050304060909020c10020904020c0d120c0201020702060315150a05030f010806040c030b070504050402041d01050d0f1101051c050109050903090d061a03030703050711010c1a 84
    0x300035800b030b40c8002c110001c903480c513241107645400c0003504119441d4004948005012a180c0461401203510012690348104072410144a038000c40d103030f41c599640d941600c10000e90395003074540000310446d0080800039140e0b2600440d92820000c0c3e170300301d441442941c803992f038081d1800d45141c0303608520319008090352200700d601c00c1e8014440c000054500740074001012060701c60303036207a00306494540c056042c1608032020340e600010801001c600c1b18840c01c403c480d0001c1303212082c3e8031844021506889076030840c0c0d8000d40005000640341801c580070b0901d410790545130701080d036210001c000b81e0b58804613001c1c007680302c58600807010680e01303140b0300e0014105040c800e14003241e00c02d5410300c411629070204685651003004010245284c0a2240d0007090000075600c1c01e014040005c41d00d844080026003003544d40e00d1820141d82582c03200b0413401c50010101e98540a2618000384180d0080e50100c0d130185513460041c0903035008081d2142c411303511942c900400782c00c3c0100d044800d40e008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 50047504 1250 50046254 50046313
    0x203070503030406030c08070809060a1a0d0c05030d05031b0307020325060e060106120b040207060e100c030203010f030303020a0c020a081e0609030909040c0305100c0e03010509 78
    0x480080c10341d40c100300900003131419440200b0006003035500600b11031402000002803044840c10003038000404100307168065410308000803600c048441c0500748101005096030011501c412860030309c42014400402c5403401c500312000d4a03000002203441d4041529020070079620540c134813400940c4440038690040117881200d05004c7c071b280c0304044032101e1018011114002c80c40e000144000d0780100181c0c986104c00410003545003540c004c02d000b11a0644143d01d569910030702c031103a41e40d6011183c617140c02c06410b012000103102e025845026240c00500c2c61880e24407030800d074500034000e60341207a44039140c25104901d15141a0040d41c0141c2aa00403c00c0031401c1e60b00680d201002000603142d140300422585000032047c40d00310031088044010740d40030000308600711500000700c03451098103841400c010746035480d1201d800001500b00500301e02031501c0816410090b0351160144078003540e194503200444c2428075088420588440c41140c00c02c2c810480c03441070700c2208081d4070880 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 50048754 1250 50047504 50047513
    0x3050a110a083007030207050a0506042d030c020d020f04050f0610020a0c030314070c030638010305070c02040203010311040b060301060c1b08060a05060406081203040206070203 78
    0x15601504280100d00100c0301488045059040394a0700c04540925650080503003c0300c2207400030030450844014100010940c00184550400c201840b0701c07403816a21804035840740c00c0500e042005055603008a54003c54807184000f1100440c1161140b40c0c0e806494090038130349281c00b8000400541e8401740e800c01d420380700561035074903144502c0d44515110281d5000504051003080040e0340920102c601310750080c03442e032020908a03840d000890f60b00d42000840c81c219070003042458040d480b40a022000301c81000002e01c80e042c0c0ac8140150200c404000c00300068403014814090440c0800d00f8060180300c084400c0e5000b6800a600005a0304080e100c4550a90000b41680d009030001c80d50000d1b8808030340300c10705107802400800b100480d0031a003598100140184a4020818050803c00b4000007580e145a2078600b1200074104000585155280c10014080a00415030700344e8001c5182c00c43c002449900810742044050200071443d2460302d1340d40030132109400400d030680c1e240c000e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 50050004 1250 50048754 50048777
    0x280c03080a09140d0f020105060109180c02120c010f060509070206070e03030c070906050f010503040f110d0204020403030e01080109020a02030a0e0a090c0206041e03090303050315090106020703020a080d0c03050a 93
    0x400c024808113000703503035240c5404910b080090940e0000390085040c8200201c040c0141d9180d69034200d00b00701c1c1c0c441c00041c18006000e0407442c0a92041d80c02c83c141000065004040784190001200c10140220911403aaaa20103000d1103001c1264540c0050f008100406e090500c00c3c02000b03c501030040450b8100b00b00d1007071007400c280381a40211900e0380d40c0c2d00c08000c07070b0030485116058400c2c00d082c03503800c616060300d9080545072741c4440105405181d00d1300310302564491305506803031a000360045403a16224074020b0032070720450041b2070110358448000251803406000b12940e88070b05501071802c00507075850035240d240502020361743c8403038401c1c0c001c6000c500078840d0f201510f041c2c1d401498182030900f0010580b03d4002403440040007040b07201d2010035000f00000040300d41c10701d40b00d80d8030760b50340800c294103469585c03055030b2001c501d03000050340b503034009107100503280200c41b0000c0c265910341c42169110390340c40f0352502041c404071081002c6030041016000d0109181000b10b075040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 50051254 1250 50050004 50050043
    0x10315080304060809030403030c0308091504060209040b040510090b0a081501060f050f1204080c070308030109110c0d0809030d020c07060e04020309100209040b0402280c03080a09 79
    0x1401600038141661010600300007995000d03a04a40000040b4091443c0a055840040814468850140a210100c80410310002c01001003540c1c110108040302102e050521305a4041d40c00000f000c1d00ca2802c0ca480181203141500c602401094605a08809249069012000343c07a4612a2540c80307404c5000014103080b05001050300300905049070451b43d8101a0701400c00042d4540c14000c011003030161403a0403020400300e503005801c91100110070741e51807030602801e02c200c1c0700407001401409000000c201c0440c000c6c41c1a54001d610903c035110203241500c00e58003841030004e83c1540b2007004060f1060013100d1092b000440c100a480c81c14100000b10740c00e070790080c2d1b55031030b0650100b94100026540f0001d0042c1a44d0112030961942c207141840b650744000c030703865540100768001030559580e034690b07210210300240070b802136442c2c0e40030051501d4603078a80443c45111004828504810b24810a24610141d0707050f2102da41c0d80c0c0740c0c800a00000c244440b000c640a407044c0180c0c46808 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 50052504 1250 50051254 50051291
    0x507050912060708010e1b0d020403050d08100902070b0f130b10060f0c08090f060d0603030e0405060a0608042901140a06090f03020d020a09021204110d030503070e0103 74
    0x10071190080800c0d092030f03c0c0c0107040040580c03010091a492034240039105890310038008a119520142a46403c41d00c80350400920490b40000e015205081c1c491345480c1d04642c007107100d510544100c6400303542d951000c400340d126121008091403201000070b0b05080c2100c4403d81c22a0154190300203405403903848001801003595080d81c0c54002c403004000c426848008100030410030320304800c81c0c0f5620750780e640c4140500a8800e1103020b00b1102c1341010303103440c41035603141c44468005000c4955642006030007141d0600d0b086010340d04000015105040c80c05c1e00b1000c6441300c0d62190f1081d548e6448004007494000e030600d654080d45c14900708601c2400c1d540f28041c00032000201c80ca51000810090b100c0001e40c840003d02c0242c030350402c2004540844442181c2e0155501c072201c0506100207041d8402c07a030407581d0750f54030100742d5080001924034210310440c03045000e50014a030800c10400503c099640040010344100001081303148202003000d40c144040c14003003252100803c800094 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 50053754 1250 50052504 50052529
    0x204050a080f0c01020a020d0f020111030a0905010212040503070303080408040510030606030506040605150c0f062805090d0518030d03020d0f060f12170403050106030b01080c1305070509 82
    0x1a41e2214520030b0810307000340044a080102400244900c80e202d501180c1032150003403028101c40680c203c50019640501d54514555002c00c0982e0765585c407494020348070742640e0081900500c9126090806001c0c00c001725001d40b5001002403002074a59030b011a02c00354010012100600c05000c00941600c503204044c0e950a20380d280851043e0500308014102e60009102c54880c50500070100616140d01c1e0800700d40c01d04007100203070340721040414103140203880a00309502c0c2c4984800c2000342201c881e0500119824542010f10b00141c0392042c900703444040d110105181c02184101111a002e5001050f1000e200310003107140c00141e200007410854127081e54804240c0018050f4451603540c1f10300d00500a00d00d20420043d030804281000310319050283d0140240610748490612806c1c404035103150031104680f80d6590303224585a8040c02181c80110b0b00c821031940003240b007140210341250642c0000d40701e030082400401d54007000d000b01030140000d0180400c102415501e6051740e0044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 50055004 1250 50053754 50053769
    0x190302180d08181513030b0609040f0809010311190216030309050d020103060302091314030a050d0903030e0a030905030d08010e071d15030f070c02180717010305060403031a0d060905010204050a 85
    0xe1340b807030743c10040104100201614400d0274100d0030000021400c008190003590440002c680319850700d40164001c0503903040d811201003010841d00040144240744c0c82c1d03541d0495091300c120703012900700b208000c2458000207012450b80c01043c400d0b0704040c3d00325070001d4014540410466600d40218005010035610040b00740005001101807040176540000d02ea51508002d520704282c2c0307103008145014200002004640315a05101410721a401400d40e070024038040d0f80b46004949005090900103200d402d0003801b0342039042c41a50300031400303d0704981c1c030030041c0c52155540c0c130b508998100800420f005100b62118070740c1519250060aa540c0000b0100b05c20399a00b40300700c172410007040080051042140c080c80080c0141c55418260418140d0142e61512039103540009494001002150003c002d40303803000001071210019046010301d0180c0c03400c0180620300480703010582c4140038200e42201d16000420002016580546c41c014001e0700010f050940b03420029000240c0c9a00040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 50056254 1250 50055004 50055037
    0x1e0e1e01020a110705130902130c0203040602190c03150e03040810060b0708041a0405090a0b0108090105060a060c170307030b01020715080411030102190302180d081815 74
    0xb10025003015080d0a9001500c0090445900c0d0034006200c041d00e090f00741116039200c8501d0000c5480780c0140d40d40c8950348000600111180318002980d0b60030900c24540103220f0b044545041d90a8112004122500022158121030440c0c80d50303210561014400720385250307904000d40c00e14a00744040c0018081c00700142c0b070081030f20000e12054540750f8000700542e500800881001803544021201101e84030f00149c1c000780c4010603c4515400380ea03006075040450302080241005050b402202c1d801400d03281c041041d00c0d018000b41c02c0711030450302c20340c0250114800b88543c9000c1d130140300700d1030301c02c400700320b400d10140115124941096400f0700100c0d85a54500d10250b070148146009004c0ea840303074500c2d81c07255600091072414003410290200007070444160641d2800c0d0101e132a07040d1342420484070074411140050003507118414102024600300120510740c0391980e52504003035045000c6030300b400006004442d1400c43c01961079071108440d01322140c0034020101074403d0061a0482c030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 50057504 1250 50056254 50056267
    0x61e090f16111b0d0819030f0b01020604170c0f070305120f04030615030b1503060a0212150f0a080d02100b010f0806011b08030907091e0e1e0102 64
    0x101c154000e50411401401a406161196041e00043e8402d442807584028000400b040012410480b443c0402a1100400250007030740500d040c24400300030f00a43d90104422030459044c40101d40c0d80070040c0740140c0104c2d02140c08104c20a070700d0f40075000ba24610300c0c9000f00c60070f5441d00e4a00302014142e40c0340c003c90020401d1010900422121008400809241110300d28850889200c0d900000304010ba40342c0400030080141040304c0d0180d81c1c4810200c3c00c0c0d007003800703400848048461065110f40300b000c00244080e20700d4000d60f05144100349180c600c0f07441d0075040c1650200a103002c1078104c036031100400300e44e5079040c2501c0002d0450001034410604001c0000341040702c040021001e0a0601e54007800d540d070b1101400300c0700155840d200c0f00d00c0d141c0c0d13030040750300010049c139400c1c1192000d04503905000d035003c004c60244510310101ca001640d21003d10b03060759456807261022403100312201c0902502d80e0808402180c0700d20075510706034910003006005c03094400702c22003243e40c00b1440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 50058754 1250 50057504 50057521
    0x10603061a0307080d05070302010621060c05160204020304080d050f0717060105040501080405010b060f0c060105090c03160306030b07050703030e072402010f020f120a0212061e090f 80
    0x84060355003080d0040c000300f90802c24405da88190030078a22042040000b441e070b0a05200394013450160184240a0305c00e1420340131400f0044030b240b841501c3d401c0c07800ea0b00440943c090070495903104182c0342c3c0b0100c07805103902004002c3d080203005660b001d070104902c9100321124860b0070f221f228601045462410003a000822142400055554800000042c0b201c540e80003015202110000d01e00300a4503501c074500540940300c6030920940010001c00c010043c140d07040c01034490007854004850300c503030fa00c1d0100302e5074003025104075807803000400119405140c0c1c80c01d141031810003070401050b1291349030340d00040d2080403245070b00041c0340441c0d030004041c0e140c064061070085c034000501165003410165182e0140100c20718481004000d90640e800c0d000b03410007400481c10f0b890441d100c3d0032810100e580e6500c05030503400e413140a04001a4629010710079a0089410070001190aa460070103100d202c1c400c1c1441041c404000c0044002e1507035038004210700c00c600608206d00580cc111a8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 50060004 1250 50058754 50058791
    0x5040908071406010609050d02180c0915041206090f0b01030b0f0604021c0536070807080a0209060a03140a1103030a0c1106040b0406020102180a2306040801060306 72
    0x11400c0143c22410040080d00c2e440b1881100390751303044403540d000700c400d840040c81142070043c1265014212a003000384e4503814001030144100180c0710b0010483d040d006100051043d809098081c10181280e4004690141d04c005256407003411060040303c1d06482e17000f0051400d81c0100c600f804002c0c20041d0b1202084103a641262040c0ca0a5091204282400ca8036840258401255550b03800001310384807070102e500648000a800201c900b9511050200500c440307602d40d22446215a10740044c0d50040001c0d4082291030500190001d074819a01700305641e10050580f6501c1284200044049003613103100b03c0e0718140d010014050405c46180100e620580c9016940c0700750001c1c410303240103030b40182003c1112540703d160140003941c1540012120b000790341100c410450040340110314a6015401005142800b2004102c100d04010030408001d58034014402034080340340100002c1c100203005c0003180d600050513542015103490290f800c40781c00360700503504681c880441d125003586922 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 50061254 1250 50060004 50060033
    0x6340c08060103061107050303060d0c0f080604060509060c0f1e0307030c030608010507050403260c03030108190c090f0f0e0c01030b0405010b1603140a0806030d020f061803040504090807 82
    0x5281000c0306d603281c030741e01ca020007010725004031000e01e4108200300903c0440341c050603010080c420801e84a0026544d6840e0896089603080d1070500840c459440024965115411000c00107240440300010007204c0e400c0040802e822124103440c406a05250301c01562286c21103540029180300541401010f0795a641c2c0500000c0c3d03d0300d8180012940e1080444050701c0c4c00085c41a681021084e12002e03a170049680e6102e208008552010788010100007103040f50100e50841e0030304000e045001c50810801080205404086c0d2410030040107130307410400340030540d0b00b400155000c0325a0042c05076850000d180074590005410f40c5000d6800d40f0035180391030400d94040080c0d604100c40a251417041c40681117a1104041001c010548240502600148912080354035080d040c0d502410b2007100307a41c081d10900807030035103605244c0f00242c441864604040201260b48410071104405890541203c410740010480424992031310f004581d5210704c26103001da580c20150401c20f10040381403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 50062504 1250 50061254 50061281
    0x7120b07081008030306060c071a03040c09060e061201090f1401060f050622090204031a0a09050606120a051b0a050a080c040513060c091406340c0806010306 69
    0x2078009003c1c06600000340c1383c0c8402c5c03c2c0c50543d0703601c85195034289844020740c824118a000030140b64180d007400d4000d94083c510691038014110344529000042d540b02c1d005204481c90610005007180c1340030360792404094445030001600c0c5600313803130f4400b61545514083d81d82084984407800d00c0d803001d20071000181000c55280c0d44c950b050200245071442204240124024401d5500040070702c03081d0042c004040d1503c00f195183d6030303850000d140c043c400d02041201d00c03900c0c0004040000500841089030361120180040c6d59072902003118079030001c0d5403014684034240506001610400000305010f17061ba043c2885400c0c0d040401044090720340009004003a0142c0800100c1070003e002d2100c4c0c94202c41c08107550b85c0d40200365600025001000d0551410581804019604900000240d44141141001c425050014440d0902c01e01c050031786507004000d5007034040daa130a22034a2985c000c171000c0103200d0025407118802c0d45016004424150030000c010070030406980320f00d00740280301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 50063754 1250 50062504 50062531
    0xa030c120c0203060604090602040f120b0c1602210318190e04030503130204022101050411040509060d06020a0809070806070f0f02101517191407120b0708 68
    0x41d603011940f20076010705454000c40d140c102031001c12040350140d0700581070525804608070340c1d40c4c2800b598810404025107082c8000710101ba010b6180c2d40494402480e52100d01c00200510750a000410f00c03d40d000e00d00e02001e04010000300300051004002641000c0c003940b95403440082002400303080201d810001840f0404104032500d480c483c2e85034015003500381152a540c2da4010240700240f10030000358400e00c0000c0741c150480d24030083c501400380f9241402c043c3d07078881080c4030440e0440d00c40c042410905000400142c40c1090085511510241c071940c000c40c0700355104026a0800c078007040208180c501001101d1200700580c80c000c120240c0100114207100102a10b851b022003c00c2081203560254000164000c100d04010002e9408003001076180030b107810354185403a402071340f481441c01d098115043d040061f030300303403500080003180c004028680d64400124134080400b0865000e00040000c0600194501350005030040d00604001d15209500a207100380040c481444281c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 50065004 1250 50063754 50063777
    0xa03060f12021509012703020d03120f06030203120c12030a05180307080301061103090907030203070e0a0509011e09090302010207020906010203070f11060408070807050f091320030a030c12 83
    0xa0200c41c0c54407416034807100340000300842241c41b2403500b4035040070f9040b4035a0700c50381013003540c00350134420340340100354080044071010407a20f82038811034880070354581d001c04100814010a100240504c08103181107072103250303056041e08416001121700319002690307041000100030182c000c5c0391005c030102c009107140c0520fa41d9501101d002c18000c3c00c1c200114241e1040d8a03201c04c000322081d0f030000800c10348507460183e00c010080e51003112008000341030007404200c01c4c2000e08028098900040c0380b1400351b803c2020840c511309180513075111195003044005034808e40c3e4032030300701114040e80c00540c1d0391115005201c00154080c10f004d0456204100b0030020403021800350240c00da0000c1c8001096580c00002100c0d4041d540040b1058000c0440001d0629000140c88040358004e447c3c0d0001c0210200800524600071203440030007041446150b000641c1c00a00141c03851240c0d40301e01100348801000c6031411059480c07c5010030384190b5003200b0b011f084003038540d008006207060f1241d0708 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 50066254 1250 50065004 50065007
    0xc040609061d0f0103060203100302180108011109010903080d060b07140d090305060402100210020406020f07090204031203020307140403060c120c2007030501050702060703050901020f09060a03060f1202150901 92
    0x31414417015022590203c0410351901403040510015038004000c150751090401c58284490400c1c450b4041c0e030f41c82d05240503a40c030600800d540702a081610307048900da245803100d04065000d01c501c5030301c20395208004a880c000e0600034003c014040d03840006515507030034000e80b4019400e8419014805540002c0001031310021305a0703481503040c2c5000702a0740c550a4280c1c036140c100b03505054100c1c008a03010031540c3d8009101e9801903d08012540400d5580c0c902d03c00700c1c822408041c141d0190183d0864809009400031a0050501e2411003115580020840003a03041904212805503c484040d10a03d600a045030304049000380d0401c040417256401410b144840d0312594015a0000711000c4000c4044c0455402103400400a010132300d0203031030003911040100d842002003442d14002c00c42c1004148241c6040b030702201314042c542144c1808200e086d4024456200c01c040e1030700c001090a5920342d00500061881100024450441d441002030140e10300522595031801480300f500f260303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 50067504 1250 50066254 50066281
    0xa060b070303020a03090209011401090e040201080402010807090e01030809040e121c0b090a05011d0402011d030a140105071202030402060405010305090f0d082d0106110c040609061d 80
    0x1590500b001a40c07041840740070f8018000607000650300c4000b030000003e00003003001c01c616174003e09a0310ba502864580c0c0300032806220a58019001540d03420010300154090030406410540604003500030641d5254100c0009900b42c1040702c0789078010805d01c0c002e0901e070142e072409160301d10203400c640107400e407520b019002d03000905022103401100b20804216591140451a001078040e2000307142c103d0340200607007000e104030241c0640111104900c6083c09140a0081ea8142c4d27a409050b50201c075500d040c050610403103540740c0502d00192000551a04010120403401000482c440c544010094642c019102e180c1c40c0d82801082001300583e50141181d094810900740080e0685818085600c0c0c0095a0101c401c140f180d40c11290a468001010302d1103181048182c40750881310000b00c8281d1a200120b4043c00d2594030018000f00d4061401c00200710464011580c41994800c001001e0315101c0e440815600c0d610b040c00d11042e80120004410b4031002c0354000d1141c1040652203148 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 50068754 1250 50067504 50067517
    0x60e04030212030a0e0106030c0821040b030c1918090c0824030f010b1e060d110d0c0c140706020307030c03050717090a0614071e08030903040e0a060b 66
    0x360382c0c0c00000610540322592120700c405040900070400d050b11307403420a12050441c0140143c0b88503007050b05894198003840c880c0d107a85564481d50501d840d0518120068001038401c000290041c081e402404030040f09150b2045401d55400c520100b82c0d45000c552013110b50400100765003004001c01740c03075811100c001d4101503240c0014581103102d158030030381c0d01c0c0b8000396160301d80111510080c03802815041800085022a0403d541d01f10300201103030500c104048040d040041030020b43ea03080ca640d40280c40c02506564800d2900c8000c5131400200d45088001c100815001e5914009006540c801c41c60314002e900b005004450908102a5581c000e03090020104100050520100b51045094440041d8401400c01041d08204e0804071303107401941401c0d000348125a000110b40c0d108103d20408400c90000700e03441d20001e40c8554812002075102d0010b80e0080c04600e00010701482e0013188501ca00d01c010310b40ba54248031288613040320103003d00003040e003804070600c01c001424007150f01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 50070004 1250 50068754 50068783
    0x307060b19051512040302070e06061602090604090602040b18030d080610020106030507060503060f01030507050307030b1507030c021305270c0a06020106050a08060f040209040c08010504080904060e040302 90
    0x10710300714050f5600b40352241c0700f4019003100411041c001015000100c2200703075410b040c500c11455031642c09219040c000c10b10881113200c0c10742c0d01b40c1c025040c80d40016400c4103016002080c0c0389000c0c0c8031002a64001e44c0f05224020000403098640c1c1030010500d074142c14200d010b004072110a1100611520b030140c0344038802c612030320885203124001d604c00700c01035900c6015508030f240d54201c00b40c016003044400b40e014069000340b4580e40e6100e031058520600c03503510f8241c11030321044800ca0017401a07104554100541042101011a401001d40b005603c40d0340c541040b164144180100b10034031040c601c2410713084c10305000100885e01400740045c48190008550039140081541c541034416103180c0c0c002c00b013004003003075035603064105405450060711740f1400140d0315100d403031740d51404031240000d0403440e10200e001032500742030480d0481e00440300d807a180b0f0303282d270301c182e007181c101340c1d02210401000944003101e0b06060090031300411040030020110310f419140a525920140780149 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 50071254 1250 50070004 50070019
    0x1030507021603030201090218090d0f020a0b010f0f150903080f071b17030a05040314030f03192d2007030210060902030610030209010e120307060b1905 67
    0x104414420400703a90300306103541d02c15103229501c0c04d000e8020300141c0c40980c00b460382d1600307004c0415210400302c2d000d1410300c4000c0001440c140c1084407080060740710f0008500404411002154402c81103502074407008210b8a8a2881c1440703c007a01c0074507520501c0c55520b8440180d900c42c1d00014034804503904942125a03540c200b81445295215840300140300101440103801140320b40310444007910343c81c02c807800b0500c0c00c074011160b403070007000f0302d000004070204003d10000e1465118841d603900190211380c24140c4100c500b04954100b101c62910807006c0164241d030402d514003a21040389000ca510a480f4200e0701d403441d5100c40c0c07040175690b0a0740c5503d504d030f0020f040c0c0c0d40c031a0060724107001081c1c2c84120b940307002911a4400c001e40300031103080c0580801ca00c140d91003128001c0a0003031908050a21220058010b90480901700303062000c16888074020362500e081000d1100c0d21200030f1580c0e80d006141200c00c03500504541809400350100100b0f913607003001c40c0ca070151802194840d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 50072504 1250 50071254 50071261
    0xc14040b090901050901050a0203280e06070c050d0c020108010608090705040c0f0909110307080a021c060303080f04080313050c060a0315060c020603011403010221070306050108011202010305 84
    0x250203459003100c82038005920310100202c0d42c1c410751090f03000e800f0400081c46641c0b549251503041e40001d540203c075050500410300313900301c610f9180c00c1c50b0448903400801e464100d41125401d100d41124914003152a9004080030040284148070a803a158100320240b4921030300020040349050192000303106128000c90601842004070600400004005100c04072860708010302c4030004000c100f010030000e94000c103510101d070040f0440303a90081d460b1803c0d03a694030400c64094001400200c4415804c00019a45021200d00c0805e00c461501d400b05849255140051014200905c8640854003020900c000100450100da800c11403548030042102c1c0310303040caa410480c44000055209400044001985425801c422030384005284407042996a5090030f40741c5041030140207601c11001c00050004440c01d48403809070140150006041403014050307407480300150b040c2d50b05411411400c0061040e414002d847c09400e0030701e040140c41d4585655880c01c4940d54078001d040c1034484000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 50073754 1250 50072504 50072509
    0x150b09010509030709020a030f0e060411010c0c030b07080a05060d08130b031f05120d051b0307030305010e06010309051906021204080306041b020a060507020309040207050f060901090c14 82
    0x998981c20b400030241c4a20035070b0b0b4140d00000f9841207a611020908000c4e0701c41b6406524880d20740000c414002411207551a55624401e50701001a030505002800c2e13200300104080e81e0109001d5403146030900340d582010f4102a104d10802454a84028149801c110840c0c4030040090381c0c0391b9000c501c8545a0b1700042c8002d40808081d003141d610101f01000f00011240b007015000041c07164141002c044985900910074141084001c4030115445400b443e04042d1080c0c0c014802e1210f201e03003804070307810071030740c81030855000c00415000a0340701d00050200c41000782c0204e0b0003a50034203040202c200b0566403545c44409800f80703080201c220f20307144421710145404540480b014500d07400180d152502d401012900240c811600591a1111000324050040c000c2140681290000c02e100241652000c000d06401441041180400e001980060720303180080d1079107500c0b500152480c120b4481483d4a802c4004049a07000c0e0305104000d408030390340c031010405031960755a2801003820000c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 50075004 1250 50073754 50073757
    0x1060e010e04020d18021002010b0607030503060a090603030210050f060307030605040804081e01050108060708011809020301150303031b05120702070b16051608100c0309050303100503060a150b090105 88
    0x104031340c1e985c201704213030340959400d14030950903504c01c40c0c2421041054070f6040f4200c034122a10590000020410b44008c04d0080d00503503840f02c0b004045118143c1c40c2c0d20518107691503a84100e000d43e128401481108006014540d40041e080c070160300d9500c0c02c0300c0003a0380d07084648805000c40d50340c0c0780071505005400d4212009042036038104d8580c022220340c03402220385c5190070000c070381d4030741000860340580210300e0328002c100c3e955407840c0300d0342003010b00c41d2244200000c51442c3c032b956035124030041e01d003800b8001c0c0098180c002e103240d5603e1810041c0544074802440d004108400401c041441c1e049403c0d6161141640c1c3c20030115501d09a0580c40e000a03034002c508140b80224500e0700c0c1a0b020000402200e100f5030035980455004000c10075603160f14050b800040d08415481c10300489a5800104401010710740440c800126496035030441e070080d03030040c403080c0c4546000e101904007007110300d0300403410207400c1112456200302c000100805006107048641c000070610042d030b200d01c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 50076254 1250 50075004 50075017
    0x2131806050903090a0806070e13090636050a060b1512010f0501020105070f0809070f0f0302030d02030c060a09080706050906060901090903020c0f0103090b0108060f0604020301060e010e0402 84
    0x12040100e07040c00202d40740d0f6500a044100e100721303044000403030395602c00304819003c3d00c20b0b51907000c01410701500700005964018440805565500f18000c08541c0310f01403a56001001c0201d104503c04904114070302d14940800180c2d43d440b40c440b980c0c0080c800062540070160046800980c1c3c032488000244150b610034620f000f03c00d00402d9052080350b1140d2454100d803088032005410541d5500160300341c490846114020030602522001d0b51401a441360b42c1c401c5401c0240d0f100251902001c04040390a034100d800c1603140c1c28010f000b18101000148103641039400218201100d0180c6141e40c0c002c000c1c4114601610b403011a810803078406c0030b5400c044d5210000344000d2908481a60303440b00200e035040c3c400c1408800014215815200d10b1141c1c03a00356016000690042c024800c50507164002c00e410156034070ba80700046120245000c1c0030f0b011003c0500510306201951030001c0e0400340c01b80303100390320400041200750b400c40d100c2040d41200b0300b003ea030421842000600240a0754 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 50077504 1250 50076254 50076263
    0x13030b0c19030e070e01050105030403030509070b0705030912010519020a0504090c030b011709070902031f030804030615050d0201031d060a060612061511160905060405060d021318 79
    0xc0701c0320075090350103401214080c481031044409103a5a0340700000000c001b0710646000c900c040000c2004240300c3e80040b644904d40d14129006990f0340c24820606a20800041d11250004103c510303551402d02140d038030745000d08002388000d0034042c220b002200c03101508659026800104581807900400c141d800410b031a180030441c3c40d000100250151130640901400107081c034481d10b05d0608010b040383d000e14074030401029441c1c24145904021b6001501000d25000810300d80d4030100b1030906034401070740c8207200558440b4078600d003030820b840a034690807401010030b43c02408a81c60751004685503a0302460b0103d0a0b100701c1914201183e459035843d40d603401044208946101075410243c1100d0041c0e03540d030204a1062604802c4400724020121500284884101030700c0c0310711900c1d000560161f090f2a40903116800712013170002d203076104203415900d40d402c00056190511505600c814242c9400480c0c821035400582c04504c50380c4014800b0380c0e1000045098009190f07030038411a1310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 50078754 1250 50077504 50077537
    0x90507090e0105130809010e01031121010609050609010309060f060f060f020c030604030c0507150f0305061207440c06040609030b06130c032013030b0c 67
    0x5405030140035103000015106035608020210710b810f034006000442c05900103001c5410204070780d0045800354900d01a03e0b0400d521481040c0c00e440d1b1610003850700720020385c8803001940300224581d04c07080050f030080c01440a194010030080c0c84820448400c48400d29000400c01290f01d4040c0090040708000e1070060700c0c0203008100300780c0b6020300308287e0300380e1f445040b5290170f0403004907901c0d001c02c04c02542581100c070210f000039014011510000748260180c3e000320380c41d450041b180c0d00307043c016100026030000342c03400401e40600c6002c1e0031120a44422400400310042240ea401031440f488889101a5045039400c43d03a254901d15020034464000e255450740622500b030050b000d03071000d03d150051840d00c44041c9000d10484003110b0f107d4841104031461500c4643d0f88400003080310740c0003119590050200703c8944600048158240c41c0012900403074110700410800074011114400030800921b000b8981d000704000c02c4907030106421016980740c0f402c42409000703640b1443c0d91071a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 50080004 1250 50078754 50078759
    0x80409020a23090a0504050703020f1c05011409041401060f0b03090111070c03080901120f0515121207060b04110406030f0203011d090c120c040e070609050112090507 73
    0x90049851103071480d180072110225401410b03120142c41003c1080d0340c031800d031300d40070007081c1040c0d0442c90b4014010b09005080c411072030324075140e640c00300500002da20806288584094018400c540c09010048006000d440d807400c0481c41c0c21101400141825811078280c0f90300e40425008040644840c521042c551030341d034440f14015801c103030340e01e000d25400c100c6d14101c40304200058035070b50307034208109a4506255464400355980300d0f05100341084000b6500ea60400c200d4040c0d9906c100c00200002600d1410074080040000094000751040041180031140c803030300003815410718070381d0010b02a40c8410f207250010040001e14005900941017814040000c02840054030860307610752818000d16410707000e03401c200e10090103080aa11007020b0109841c0494452032540004800c0456109160000004a220580054848540d40314607228071640c03c081c002c0c00b59091003d03004042050425001510a0495020309410400e046400e41100e249542084080c9a0401c0c01c0d80d4000b0f4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 50081254 1250 50080004 50080007
    0x20304020d031d15120105030d09050d080d020403080301031a040804090b0a05040e06010e09010c05040e041104090b01140d110904260306010905010c200406030506130507120506040f080409020a 85
    0x300601031100c131421045c80000307550305000c9854080b4104681d034030454a410036081001c420840403042c2c410050030300c18818510a41c2c8024000b0b0750099000d252030b507165142007141821118a030003038030032100b82804006403a202c00e88060701e00510700480c009629402043e000f0380194441c59001d400c00810080075107011a070681600d00c0014042520707642d4401d038600769099000346000003101007100f0041c0181005007560424071865008031549035100019080e2100d004e019219000400d0040040780c1031004040024103054800b0150403001d82c5446044401003140c0ca4000c0c1c40340000202044403010300702c0d0204c1a0034007032184424000585035225007040340c4180c00305601240110b401d45c01032802c0011140d209800c0703510500c0d00030140180600d0881c10a03006510303400088001403080c03280500c10359003070315444004007403030401e20f14008050b4060115034129408250110b4004245603500a4100717003214954030302440d10300c80b90b1245a100d031140500c04208190020b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 50082504 1250 50081254 50081257
    0x70e090406020711010512040809040204080d031a01032315030d0207030308010501110606040b120f030d050c090a15090f060e0301060902090d030e04020403050706120c03020304020d031d15 83
    0x80f13000c0d40b00b084410004000540c1c6504c11003002d010030740c95504c0024002420b107002005d0780e01000e040036051650f5450107034030704400400d001c800709440b0f10781c1c1c1d54403604040b00d01e1005042481c0900c0b12049104055280c0c9110b030110ba9448042c03100041d5542c01e20b121382c4e03c3d0b106006400c60311070702a4400001c0d128412404110000f0340c04500014040d80306a414170800d09214025184a803a1142000003d100b10101140c0213031101501d48442030041c81142e614111000265907101924a40c2808440c001091455100300a000c82d0305561500d46c030f0074050301c041d0f81a0041c061200c0c041a0b840720b81c19404480c1001c0d8020000c2a01984040c04490514054000b4488941c1b204050416402421203c580007000303a110040885d1042040c070300d281502501c01403801d500c0b81ca4050908d071403604100c002c0750301e205a41380c0e0095148100e0340760610514045082d41819800a01134107440794002d03003081202d480300e01c456044c3d20003a90400038001d00c0e4040848170185402c084c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 50083754 1250 50082504 50082517
    0x60b030a08160c050103050606040504090c1701060e1b0418060302040203070f12050103050c0d0c03080d0c0215010602070308030c0c070e100f0506092403070215070e1305070e09040602 81
    0xf80f42c444200141650007405218040c0200603c5903007020704140600000b0200d01c032041e078802d4101c0c0e07000203000943c2c034040002c0480d88400031600500381941c0c080c65450241245014030704900c42d6840d808041ca095070191045120000d00a2441000140141001e41c1000c0c1d40244004180113100da000404000e09c255142c44402c1600340100c01d02046a03000d1201400f503400100015103203251007402102018403c0603040c11716a101d446050654215030240ea41c250b03543c40c00740440b03603010000c810220710703207040d0b040103136040080080d03c0b4000c03131000078044940803010804842c030341030030380303264100a0040726103a030b503200700380ca201135010755403c0044080803001140440042004206850018000700c4c0340c0384030740090145000b103000e10140c05e0403d01c6028807900e10880d00450040c0750b186d00518500407240d108102e42c81020b0504018009032034a803038941c0d2109259a84103403038640d00000c55507102d0070f080ea90f400a503110940d01c43c880b1420801004940e501900c403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 50085004 1250 50083754 50083763
    0x190503040c0b0306030c0405061915140301030c0e130f06050a110403111203040f0b03040201020706091401030b0102030d060b0c060702010605010210051302090711010e01021303060b030a0816 84
    0x204241d65007102e0000380700644280ba0942c104020f0081942440c0d0889600581e01801d031007407404c44c140c0400d0040690b50400620050110480f0182941c08614a40b1081240d0030103442c6516564494951000c14441c2d50080c0441100050001050301264250581c220012446c601c1d03882c41c0450003028100d502d01c4007549051012025030500806840a0340e03440541100c08906c200d00300002c0300f541c00766544440c8400c010100e2881d1024201000820280b0b001d10b407641000c5c4006400e280c1c00750000810800c60a41c200308002d021407466800c0034082c200000d1032418140102d0444c401c4100c148078440c184003000070b403240e03c1802804a42c01c0c803025030b5403e40b038205c01203099450354071030b0300d005031b205190104030003074140c0c003942c0c21500c55564100b040040d50301192503481e0440d000000f103041b0403c2042c09103028042c2540d4801c425008514200e801004c845658085000c082e15441c0d0718800d94199403010001c20000755000030242d5120388031940c032025030044400781101c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 50086254 1250 50085004 50085023
    0xf0c060911120f030a0302030402270a2301051210060b0d06080706020304031403090429030a020901120303020f03010f0302130204120f021f02010e12091e0619050304 73
    0x611003600030600468009014004d14501080b56204401940000c3c006980c407449600c80345a0340d461421149403041650b031070400907898140181c000701d9400001c10144d40c11a41c80030850291000c44850548030101d4080b51400b01d1a03110710f140c20036030008624080c5c0b6258003c52080513202c003502002c02d5091003404038035140c0142c107450340c00c64400c41025a00070301040c400038100e59a41c2c18445ca1110440e424100300d40f00203025220718000000444802140042103c0031202e41c0d09510300c410750041c0034141c8154045108110705114001500018807046810036100390100c409210001e44015180d503103039a030401c080400c910040380b052246800d41c05c2c3c001030303d00a4504031801c00c00d40176240c1c0090b4a030700896840905040340e000030b000b49520091088050790211240140d0700010f221040c8006091414810500f05c03040b01005200440b19550303803900821a42c2d02c070122052030402c099022034060b01501c2c0000c02e03900880c5100b50829648a00618030840c020309821 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 50087504 1250 50086254 50086279
    0x3060f220b0631240b0403020a08010b10080601030b041a030d0f1d012f06010b04052107080a03020a030305070302090d02040507231e0a020303070f0c060911 69
    0x400120441c2c0301418160300020f100c003100201540c0507401011040501040b41c0d5071a01d40e12520349280d03003094202002c041014019030501059507800381c04680000c00c0488510b4000030403480c0101c01c02420080c9110025403240d10a070004540300001520030302c071a020844c081c001001903202e000d0b000c2e1041209800e011807048000210315a01a02c0d1201880a04d01d540946a90425100d5052095003039025200003402d80000c4000d44101c0e00c1c00185603000300560b8100070040e8441c3e260070100740018042c0e6961600d905c0d030b900c1550165400303602100c42e0400c0c208150381d400b8011a0191014400a141d00031620440c407034071982d8100542d070341e8100c0a0b0124054180c842e9080301c8162011001418030380c0c0941d4020380076007071403500d1010700c143e60b10340081c8240300311003040300c080f85039142e24110840d00088841c010340c0b000c2c105110380360000c3d0380303010041c0f071901040400003180500501945500c849107411a806000700140340c2000c6802d0300091401074011504c20416 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 50088754 1250 50087504 50087539
    0x60a030906050a05040314070611030a0506010f0519051c0c0206070201140f06090406110a05070323070f080d090f031b0b0a0c0219120f03050603060f220b06 69
    0x3c031841707198142c44041840c400d581c0720003465009580c084407029179a2404c0d962000000e8040e44c850000c001c00414503140c03e800040004491121040521209000344464050340680b10001d002d450314040381c882d031200080400c840755850918a89507d000d000200180c5c2c082022480350f40960000d1000310100d060081384c03060112014400c113995280840c0107442e01c544500c0e0400d0289030041800b0b800c00551016940c0500b41c0b04010403400030f883c80800d07070016020200300a5008500303ca180c4805884c085920811000070454200c9107000c9003046044425640b06c01d01417803081003000d2080c03401502d0700311001c2054010030803072a0010f15408040e0201035015511600781441c9448546030038010f00300b01000c500c1075020700000d0484a4000e552412107250050041921850170804041d080c0402440340c0c1040508040811815807000110944c120000b210040190b5031003091241d2000d802d0304a1412089140512200344285911054005d0508862050342126070703051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 50090004 1250 50088754 50088761
    0xe010b0117010807090513050607050a0f0509030a110a0b0403060203010f140f040209010306031a0403110307050a120c0f0f03020f0f06061e030706050d0c0302091e040b060a030906050a 81
    0xc1c070f01280e48454402d00190800f500700303035084039540c00b0707035000c0c2e4031555101c50901030111005c500240d4003282c454440e0f41d0150188450701000c0c180305150400040c0426180c0d250500b014000e80c01203502801c19444a240803002011142009502c4640341c1c0fa160000e0741c0280b24803140259511400304202e040c6180000180c5070080600314442c0d80201400b020390401d401e0281415541c42c4c0000100d10b5110744004640d07041d01c40003119103001e24002d0901c4408481905c91540b05210080014400099015903075810403141140c0ca10b2203c07048070f111205041c01801011810082820010701500130010b65100f40c00384c401030418041c802e9039601c003802960311950f00480c0032841600b001c40400c0d484e840303020940300301d141c111070100e803426405520030000942c0008098030100b01c0392240c01c407581c55500e02949003086070000113980f858888041e4041c0b085904d5001c00ca0390355940702d1094400f001d0401a1204941d00000c3e000340100401510403a0403e40002e0781c1926a20 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 50091254 1250 50090004 50090009
    0xf0607120c0816030e01060b0a0305040507060216270c1106010e06010c080d180b0924010303030c0908010606050a081302030a03210204030605090d0906120207020d060e010b011701 79
    0x20307001d00c1c3e03410030354000c0b005801d042402d00415540c544022a148619500500f262085514003068601341031820318a0848650301080454003c00d80f40d518904015030650100c803003e104009044d12024610b90400c85180c071038401262070184100541a0403e01984462003150103840c02603036540e5034144002411502d050002d25410a1080001c0402000d042c10340c105202c0003450740700c2e040c43d46190420419051b0307000c400260810a2800003000510324140b03c5d500c403010b403418100d51200302c603201804002d0038142c07200100a4020720502c0040c000f000c5920007032040f266984e134058034503801104140005010361000490161811034100c01c038680c00780080c42080f00b00c7d00d04859400c00046010b076040b1018564600902080c000391010b513008513000141c1d4140001d0031483c1a070300d882080c0501c0500081081b0041d000061120340c0c0c0264500941e0b2130010307200180280d4a190f038000c200c039181000403070301c612055110004120007a21080e0b03680103000408105613100340f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 50092504 1250 50091254 50091271
    0x608192102060c2107030b03060a020a0f1d030709050907050306040206040302062a030d0e06040209070807020f0a080a091d0109090807020303070308040201080a021e0a020f0607120c08 81
    0x11008a2007441280c0000e00ba40100703000ca80e131140b40c0c2c1140c1010300c031409807018000a92a0f031143d10701441c0a0000c1d030f41020b050401146085031200340541400d014041c01ea05100044491818524180001c071052036002001d9845640d1a400d803c401000181c81418861207041804256800c1c0051003e0040d074000740b40304e04140c0b40d0717400c100c407951092240245000d081c07441c44001e4202c010540c03840d64a0702d0040c58681d10f0403540e404c02c0f1039114020345440c5e8031060621002d80c4a4481040e003140c0c1701d00d0050f2107035036204c4080c0e140c4000350703900d06450b206660500080c058100090180c80029550380101280c0d00d1401c10340021a809140768207410300c6004000f4110386030300110705584a502c06c01d0902c0c0301c03500000d0071504500c109401281400003080708541c1d0241e003007544500714000c01c40c240800c00642004513803075100141d50f200400583d01c00c540b4000c1110a600d11014000c480039490556002004222010300541d146824078041806407030042c2c51652240015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 50093754 1250 50092504 50092513
    0xc060f0c0512040303061502030c010b0409020f040c02120703050705060705031b0a0912050a0303050c0309030405060906090402042301080408031906091814030405060f0d0608192102 80
    0x10b840d1488000201501c21070501d039a984000403103907288840f1540040003a000355840345994030b021801c0d120304403000c0e0b2055260503954001680d901010742c0600c4000d0318000f42c0300c81140816071510000e240d2a4031b007040049058801c0503405030041c040103100b1070070b540d01a120860305440b240801e541c0d803801028040580c40c21005880e001c0c0045c501186080d5040701e60b1120000f0305034150242c203864a0308080000c10615405000300c070b4006403030840040c80c0d031410b030341c0036616805a03000b075900c15900052041034a82e01d0b5419549401b00c018411540c2d65500c9011082d84a8010103002c01340341702c00c1444540f503000742c520611803500404100d01c0c5943d080350340c40784440080c40001403681e44c2c0703c2c0844c0281d8107110341080300400c0d03c82c0c01751800c0542040b441c003030401540c0404030340c420002800581c0f29081540c0034055071154950300c3e04c080c42034100103810160050085072040740c050310540b0794501c51031042d5030300840480740ca2503494500c2a50302c002c0b114507034015030301c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 50095004 1250 50093754 50093767
    0x406020a030815090403080a0c080103020f01050c0304050402030f071101020a0806040e0f010f06080c1f030203040f06020f0315100206010b09130e0609160e010509060a0b03070c060f0c05 82
    0x150080c240d008074205001601400510006413000c9000d58059000035220350400c003d00e031140c0b0400c41240c10754280384096600d958002941c07480c1000d0350320704100010900c51414081001640c01501c0000e10640d12460030295060045004035982400a007860040d20400301042c402c94411280950340c5070380c1303581e80f1014080644041d0040702070a215400721274050300c0d001e1007272009103c1c58580104945181241884c40d042c80c0300e40c40d5125101118250400d05000140b0303c80c032082c14100942c40390b8a80c200510a50441d01010741042e0000a0382c0002103039410096100b810700c5002c200406070805c00703106c00b008071311011303a0259005400610490380060081c1034808002404840c5001d100448001585c503022a000780c958005e9090210b1020103020300400b00c6088124031b004036151401d07000301450306102c6e20b8041c021500c0420710985503c0c181e1000b80101d44001540c0341440b0704010300301000f008060314000d18040801040300303114000d49400e8100399a84508200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 50096254 1250 50095004 50095007
    0x902010207061b0f0311030c010903020c0109050a03060b12030409090c140904020f060d02070308040b0109150902030405070b0f070605060906030c04020c010e01050f01030b0f06010507031206050a1e09020406020a03 94
    0x400c1c0700141d05000030386c204055050310800091403034001040010500324001d03d0040c0c900100590302d10b043c480d00d10028030107a111017035000c0403280c2041d1301107003540c0c190000c15800b611801210340b0601000030041034064003a005001054420401d10390165941d107901c1400a6144103000d03402701d40000800c0162603c0d000c1188070b150020300076490240d242040c4801ca0388a04000c40106002c001040300b8419180003050060a100ba0248012500f5a9a4000c0c20000d8001c4108079030b808408503040c041b08000910207442d044109540d1030746500f1100285800440007216254100130009030b25003042840140030b11000b90040151040d848100006504601441d000643d43c82115104036a024020039000341b9886003800c02d2541107040c5200100c8009214440e05c145800c00e01c41e003030342c1c46021120b0309509440c0c80c07590020f004004901521155000703a074440e200100100f62901403129540c2041c0c0302d1443d11502564840007102603024a202c0c21025130814881500170a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 50097504 1250 50096254 50096273
    0x1403100b03070e041d0c0d0503041a040e0c0d0b0d0503090d1518031403091203072d0906020105010513090804030501020301081605010201090c05010f11010f0902010207061b 76
    0x120346003051410a83c036080401c04417082e038030350844190f2414502410006085c00305d074000d8401031381d00310801c10317558803001d07601d100354802e001070390880760b1000c0458000743e400c0d03401601d4582400d07105410003404018840e04402c0c5100b00715407401e40400c400d41342c15043c08150310303400409541810126010410320f241d41c240e050350500c000c9105000c21010034800c0901c124001c4500707003410162820010308440324404c0c540c40001c400c106028a070040010110118145545501d6070ba94456900700c5120114140e00202000079102c0740703443c2200343c48151200030f01640c844410356500d000c103c0c02e13600284151078114118031a482d100400c1600241605400798000500d050b0340d079a0b40b982281d20903800700389150410b810041d0911903003a01180185004d10007400b05001645448078484201c0c425103061102080d91078485601840703d000600a810000b040f08586e0040900302521014004900500841002088450180040f070110014490300e0000341061740d5a0410b46 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 50098754 1250 50097504 50097511
    0x60703090611160905070311040305060112031707090806061e0d020406050a090b011418210f07081e060112030203070b011d0604060b0d0f0e15071403100b03 69
    0x10340c0643d0f06960450718007480d00c00001d01d500c2d40b00007601d00e01000c009003102c40c01901c096a5580403c41000031442c005811419600010103e108552680c035040c1d0f2000184403001008071188820085051b42085070303142110f503160296002661341d10104080e849100c142007201c40b10758080300394141041d2000211052000d040080c00e15103a8001035102c50a980c81100c2090302d03080664030650788080c034204850061104213090042c0c124484648840611260b800f4031030741c4021014840885080a01d222103103000d40c0c1d510003002151a45404050040c14090700c1443c03031400c680a0039004803800d04a01d800a00103036401c120b40c2000810407001c050341188010b00c280740100f500718010b2802000007555400b035004901001c41202a00100424421840c0090800041581c80201c2c1d055004981c80051705000e0820705000800150100d4000e5200d0b021440250180101c8a103008055544490400302d5212074440c000d03110031511410b010550507401c00c20b007055800910341 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 50100004 1250 50098754 50098787
    0xb010903140307020607050d0e041a1018080a0303050903040608011502070e01091a010201200f0f041d0108010c0c080a0e0d06020414030a0b0f04030212180406050607030906 76
    0x43e040103900000d22503003002c02c007610b03581c103c500c074500392a81010151008040564040c440c10807900480251170390400700240c041e0040c0d040001c4554800c0300080c1c28005030b0701020323040079201c0f5400c5a4642000350214081ba2034030000c41c541140010a0754126080e6a68140440e03082c1294016036003071501060066106000c00400c110000c074400724043d0901c41c1001801c0400d008140c200e01450420113410341e490241003503011188001d100020302c840c01852070fa40c04d4501894043e61252151151340f600c3c010a011601e03490303403442800c1a64942e8035503c00e45c0d88400c40c80d800c075441c00250703002090100c4404000101450083c0c060141c0350705241000c103138081d01042c108481c1840448990742d001801f808041c1e405101c220314198250010710030492195645101900c000d04101c12031030915002804041c805c00c0209240c50742c01e51080c1d1214050301030300100c8020b000740d50344100c0c20401c0200f80c50500009a40d40c0700d8040c0d503888006444c00b40305550500140e00400d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 50101254 1250 50100004 50100007
    0x501051509011b03030b1f08011e180902091803090d030306030210020616050a08010504020c01060f0e0103060c030e060712060512100f020304031d03010f050a0203040302100b0109031403 82
    0x540f5201c4042c2412850013501c000c9052070200c010010b92107003401418040e45550b000ca040e150780c1c0b121a4a0540b10a80c540034101e6142c00400b8286d11190f5003c0121103500310b800c41c1040c110341e0801c090707251081e40c602895845001c1400501c203555004113403594000c0c018a2114039099803410705c2640a4180041d01580300d40100f000400c1c44072039400580d03c210213001450300c0c4101d03c1d1380f25042c145090360801e401038030001c10380c0350184a201d208a40210b181a40f80c1000c3d0f1101000b06684041c0b0b01a83d59a400381c1d2502c200c091000b41d410a01e041890800c0c1070003401404a00413445010305695640d6641c1076680c0f01d0342c0c403200e0055641e0b40c08041500d850b400e84440365506e220004004d1070501c0882d420503162000b500703d842c24014000d00000030b400c2000750000b205000c07080915220180d0100c1d00405102034040c203018149414070421580c00e03401580a18001d070300303554a401e24441100241e8a0525140b8005007950108201240c2c88565070011b2160140503213 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 50102504 1250 50101254 50101277
    0xa020d050d0b0402041203022a0909030d0e07030309060302031006051309050a0b03010b0f0a030212010212040c031506051509060d020a0807020610030302070603020306060d11030a0f050105150901 86
    0xb501300d802175041420b10107541c1c900401032503010030040d500c904102c003000c01c10200490043c05001854840c850182889070f020500780340c41401034603400003129408028400401e088203a0350901031000b0b0380400c41c00e401c00701d969440390013109e2103803580d560030815031494440101c1d055404080b480d00e580d000410301107020445405858090b40707584c800450445000030806084800d100030075840342c003044441840c0c9440f030b1250741044030b404803501c900741114001c80341d01a11075011103848103003132503040000300f00c0319582003c2a2400b4501c0c401d1200810081d842c1110018007481354024a210f015280740422440141078450010341210304044aa0540d00140d822143e02500400c07100701c20882c0c400c0d41041100c3d849004a6540d0300401d01e551006074580e00315008201c10560004001075480e00c0740301c104d941c11a000d4100700100011840c9c1040540c00541e106642c03181880304080c21403187d0301804d410b803900200810940c1c00090401030003a0702c0040d81605100e074a032100c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 50103754 1250 50102504 50102509
    0x2070b0106021605030c13090f050d17070206090703060f020405031209030c010801060f08100e10030308090d091202030109080d020301031a0c0d0e03040909051c050a020d050d0b 78
    0x125802445650000d1540e8200d6100004100000f40c20442c080d520002c4409055030701d00e042e000c3c003044c402200046420741800c0250701e038400440d01501c40d21804c80d0300c000040d44040c41c014000000720804225856000e0100d03102c0c003003995a0070742c542c040c460520204085600c102c181c0b80d086c040061409607030701c0100381808000000388075600310100341000c282c10203000c0c0c54007210007403070032846c258105034000c0c01c2c900743c1c5103400c4200041040000d02d0300100e1881c440141200c1c2079052081e25144000c041d03400b680e03001c01c400082c080404281850340005020b11904299291981132504000340f02d881005061000c0e079056407254405400706035060020600c0e846155009070b070341c2d8110f0a101161126103210400010040c2c0c0402c9010f030b84403001d89483c0c1040f85004601030320040141c910303502440e0851525a460110b540041040008107400c200707156a580d034203045041c1c00e054807a40203600f40e0700003581218843c1c01e00b0f240710300c0003045014520303000010100c803803101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 50105004 1250 50103754 50103773
    0x10c1202210418020306030d0806040b0915010201060f050607030c05010b12150705130b03130b2d0105090f0a09050a08090102061b160501090b04050706090e01060203040501120207 79
    0x110400188000405010f071400c0501c1040486004103000d504e141081800301c2d41c1c4000c1e07030b0700c4081000402c8011030096500c80e00008001d1000400b0441a4140341c00800305000c9491071031405903282200004d00c11105a0b1507a080720740003084141802031580f8207945030704002004881c995a20704018401e9595020b2540710701c12b2120081500940c1e590000322002c80c00307400b500034004103100c05280044000d82010545610310180c64403500c480301c2008103d50010710003402541c254007080140c803681b1920031400f010f2440700e400c401c0b44000401311041e00c207008450300055036000160801c070a001120b900301d62030b0f01000400291a4443d5414403410401c229040100001e01c041a0745e41000180d030040c14008200084892001d0303040c04500c601e10100c02c03a4503541424000380042980b0000b64207402c181005d02c20300e040c0c5405616620035000364804643c0749400401c42000205045040c0e942c507070003c501d401e0404005540103442c10b03c0a1907929020000c00001032007414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 50106254 1250 50105004 50105053
    0x605030703030507030f1d040209010c0b04030822080708070201020a05030406020709050105031b120307061401050312070c06140412110102010612050307060203071103130509100302010c1202 84
    0x80e24a0313102c440d185001440441821034803010024480c0090100000103170368000107138021580103980e1140c070401a5401d016941d0080c5c0701200700303001c03c001d00d038102c0d50361486120800b8001e10707500352000440c1c094003681da001400440041c01207200050042c001003400e980140110b1300b00380169a9801e241d903009030030507401a0071a4804000b100c40500a49002d1b100c00c8000e40f8501440d030380e18125902406110a1289540e05e24000d01d201b0280122180b403a000074003481030b80c941c0007800c01c4d00803080c0704650080c4202e07408a04611100e10640310340c84e40c41916054010f14140c0c0c1250060517913000041d104008200c0020301e005055103002405100350301140c00000440f001a00b107954940c450040507600d1140c41d80051030120845109039440600140c0365100c01c84200c404030070810303860140e03200000d072104100113580642c00c103c4c1c40844481c0c00c035903600b02409001c5d010f1440006d0128841481d00000101425640d103c424010701c1100d5052a8a005c1e5141001e440d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 50107504 1250 50106254 50106257
    0x1e0a0803010311040c03050402030a030c03110f0a0c09061d09010f020a030b0306010611120f09030a031805150d180503030a0c110303100e040303090203030f1213020f04020a0201060503070303 84
    0x21003918045044c1401104440e240909081200d89880c1e00803e80320a502c507002410882691200810103010b180d5032204648084203da9880b00b9407001035585480c507c205890382c035103002000815440c180105401d80381d240c1ea04d0300410824140c1c000403003401806040d0507541f600420310107041d1510140080c0013599074003041d410a20401d2609102040e0040d8080010748150304d00082c40004446282090003000030b036035004c2020032003280f07008580005030700d8020202034000707140d80b28071120001122522441e0180d40d40744100203884445400e0010f0446080c01680710f0844650320450135044194460500f082e040e56a03642035601c1100e281c3e0505688495002e003c0364070000250510010b034004501e5818501041c00c0b0303111a91090441c20940340780082d042601c2030f0808022654080c046a0300c2c0d1411440b90030198101095102e00d0017407010024040341c1805040540c0c07190080d04203070516683c0014040658810070003507081d0743d03da020004860314200186002103009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 50108754 1250 50107504 50107523
    0xb0a0504020910060807050d0e060a02070b0c0406021b0d0b0a0c09060e0d0f0c0f0308031b0a090306020f07080d02040503150f130f0602030709090f0903021e0a08030103 74
    0x40c0c810001941c1024040070043c03510000140001500004c4594100c6000c0c240252214182c0384500040c010710300980c1028000c10003404401801034024101d264030910310006980e481c5003944240c0c1c029072007030030300581c440c0d0765160b0f8010101c4076003042c003640034000c0540c4040940361100950b0041d0f40d19415035546070f80150008e948581c050300030b40b40d10f10700402c400c203560000420701d034131103180500040120700040c020000c15100c2d0400620905103030800c551307030b40d00b010281c50304200c0301303000c0403007580c1c40d6540101c40c4481120740c0c0403d65180c0711802401c540b40c02000b03401c00030a8200740d917000c02501001c16a40b4000d050310300200c030f0303000d030703030f0f50f080105140c1071800f01c0c900300b41e00b030a4060502c025212040701407940107081e81da031007256240d5424010442c5035207480142c0018800403c0c4021a6841854003003034950202c0180041047e0004031021140606400380040e0426000c0540303246442c1d1851180c08d000000320b030400855921807409581c0280e0040740da5a02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 50110004 1250 50108754 50108761
    0xf1503050d03060303120b04060e040305030603240f070e030102040b03340806130c030c0f0207080d0305041b0e07030506040606080c0702180709030302010f0216080a09030b0a05 78
    0x20001400018041d29080c80b43d1441c0da60040c100c801400700310303107290341c5940b070f0900326840e1030303001c140100002980c01e00141028100a030269100743e8070315002e0300440710075810240d444207102d5002501150003207019035903e540182c15803809401002080301c0d90000f01c0141c0c1d0700340081c001a0010070b0306142d0b241440402520700c10841101c50350b464040380070981001c43d1640c40d4454101c00d030705003681c60342d41e0ba00c0000c000304403101d524910300740351070a0340c90000e61590000d4644d500540ba900100e01c1c0c183c100360b03601c25291148803100d5100040c400302c4240300c1c0d045240c01510a050004600419841080c4120100d4020850045402007088902d03907050207180d411410036501008080d040c0f090041008500401c017161640c00010709a0840d00e400e08580100c00d800501e220241c140043d00822000070b1384000d1f80190f00706002491021854401c984204842043ea00034210003a03840c9940d540110841c00b0034010b59420020201d11900b200702e105a01c0080000354924 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 50111254 1250 50110004 50110013
    0x8030c1603080a0c060207290a090b070c02030c1816050403050705090606090904030e1005040f050f0a08010e0307230703140a0816060e0d05030109050a0f1503 70
    0x800a0001030060011001c0012620800c01c503100c3c0041460904030001681c101032000e44103040c8014240c2c1840150482c0300a50074200d0b40020002c80408185515101c0308141a1580c5180152070a240400030540d040e00a182d40404148090181c1d0829248a030000b803959032400c152620700c1d0404000c10604030400c10360101d0200660802604050a43e180e0310b42c1d80074607001d280e00030b141c090041307801d07a03980d1fa00f40c034666240140085124038003480d0090407101d480240038000c40410350300d44400c9008000b81d41c00d4607440a03884000918150801043c10489409960404d16612011440c48028025203904994081c001c4d6550396003072800e030410b200028140c0000c030313880000800d20b442e000310b81a0202d80e001120403140d4410310b0115404d1815400000b0049030780084c0740c1240c110000e0290071294000c5100b001000103920289484030513038012440040c108000610a20341140e10958000620078400260203200a89000485c2c601584041d20f2000c4883d0400c10003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 50112504 1250 50111254 50111263
    0x30403030801060c080a05030c0d090501090308070e06091e18150915010c0203070803070501061805160c03020a021c02090106090605041a131e080c0907120605030708030c 75
    0x107152a18103c0100c12007600d44441d0343c05222031b40400c011000000c1a031208564085c0c7d000088020700c2041408014a0010300804908000314042803071140000d025501030700d5641c00c01000500306505c0e240304807080049802100020411844a280b0800001d496070740b20188602203002040b141d90601e03c00e0418403214001c8c60a21a602d81020440c07080c0d840c410848840c102805c2c551403444291002030b00701038139074011440c0d510010a03104140301c41500581700311911300030030800c5505032500d00002d40e5000c0b10001d080c05080300c0400346a5100381c03a4802c11600a2061f500c01d40386c607600180300c10404156002103c0721600307180381585001e02e040ca005007000c0c1480801c07140b500d00054042d01491140c1000300711b120743d036089841d035840119040f44202e01c5d81c1c0307055141c81c0c40740c0d00c2081503c5000c1050000070003c01080b9004001402009810000d01200642e03585940c2101c1d011036014514607503030744609000805881c10820140541f04c9240a140c49604010805290 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 50113754 1250 50112504 50112509
    0x80f120307090e0711160f05040603020a03030503040314030103030905090f070f1407060f050403020f03040b0d0902030f010903030506030c011407230a1a090a02010e0616020909030403030801 84
    0x4552082080c4911180c0110208045448a080c2143c3c213955918041d140703d40d04280903900d034020320016040014900c070311441680c01920104140c0c076211014082200c1140c000250456400740050010030301580141d0760252017442e00b441044035508030000240c000780d1085010800781d040138081361600600441e4025074016100c1290700e0044030080041946544040500801302d081e13100d041108030440b81450707049401803064044441c01d2400420044400b9001400b44501c160b071490800f10131601201d030810103140c03d00103000c5030740000300034840c812a414864451a000b480d0001c2c000c4550042c0a80c60002d0b061401030207241c02d0524260110b030400c02c050f1444001c40c0c007039400340c441241e04221044503182c2680c8502d00e55000d8071904100301d206980e0f45008014122508021407070021507000800d03180c1d03108080d139070301c03030090b0080c08a56041c481600c641400401740c001048100400c2e1610080b0760007041d9070050a891241c45038200082c1442410b412041b502d00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 50115004 1250 50113754 50113783
    0x5040204060b030f0c0a0c0204050421020f0c010807050904090b0604150e041106120c041a0901020c0d020609040f06140a05130506030109080307050a02060105010e01020a060906021201080f 83
    0x3c0c62030860801007502800510320b0413420004110466450f124824a00900790702600810030b900b4181001502c6c04403030040e040304100b40c45d2251408a2010070780c82001007898004180a08081c00156445040182a00c0070030805001c000c401d03603940d00a2011003405042c48d00040c0c10030030140800c2c2c0d400c120140c0c01083c1e01c201e08020245200c544280e22681000b01400d400d050440040d00902c0740701d00300c3c441e0801e094180029003004c80c0c000c1084034400201014001310201046803140503501c00503016030846801030400f0b09020980c400350a04c0107000c00e1412030840300042c211401e140b145468565200f02c103100e41e070800c0c0c41c2005107000440d542d001141c0303050001a4040309849960098946440c046056600c0035003104680e41c3c1c2c491900c3e600c0789050352008045821410044d80148103201c00080c40b9401007041c0562094107a01a041c80000350f226080a80b10080c011a001c80d0f080088166080312044114041d0841070040c0144076240e83c1141d142440c1c80c01c40c0c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 50116254 1250 50115004 50115007
    0x32106060504050402160204060305070e0a06050d02010e150301120c05090622090203030403060b0907030605011e0203090607030e031b0a0509070e040e011d06010b220909050105040204060b 83
    0x3038140c00000740c0b4100c2d90212400750f034840c000142d038951048100c500941042c1040000b004101010511000791205164030560315a82d20480300f0650302d6522034983c05c041015640400f40d44201d40059040da0040c08141c0110201d04e01e2313200d254400da1102c4101100b084421003008520100000200011200895a403d24070000359001301000606e214810351261071188a000035000380410365001010b90303441c5d668034107110f13001d0a0101d0002d031203540d4080018000a00031b01c61102070381d0301070755021400c604195580b90150399540100096102c18058071100eaa01c4030020200c141c440e40e03982204400d078000b8036150015031500610104501850b01d0780076245c2020003c100c0e83c08840200460f1101c6905852905c128904240c006042c120100c0900105400240203100c1c00201c02944405002085c1c0e200e00080c01818078020003040024007000c410340300d15414160b40e840340b100301562000100c048070014141146c43d40d44038001c00c800d604c3e107441080300520140903045d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 50117504 1250 50116254 50116259
    0x20102040810020304020a0e040b220c0b0901020307021512090303014203060302030609030a0e060304031416150c0e13110d0509010507050c1504030c020a03032106 72
    0x180c2c8503055510080e05856020000600355543c2082100003803d880b40707900e4040c05d060405002c880001c440441604c030b13841c2c4013182c2011120342d02036622038004481d8402e25040002d04e1545a0040e80c0d501e045210a00144025986800509480c2000100c55645e186000016035030b10040c014504522a003003032004001100e41100c1c0c41c4107004801c11849001503110b500c0407001065800c0000640c4050700c50f0f0310020741c0640c80203090301d00032000c55034103075030391000e9550724072461100310002043c074001090b95003468030266801511a0801296441000c411080d181d000351420704020b0b06650020400c2c480c4c100070117841d25200000600501c400c0d4400680112009441d25005021048000000031020f5100032401c6070a00406542c440344981c05c540548010b0b19291000c1d440c00010581482c003503011142a030203420094054611001520b0405100007001901440500d20800006a0350190164040c52203a00d80580c03084140219a88a0410700040c0c1f842500d403c40a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 50118754 1250 50117504 50117519
    0x5060301090c0312050424030b0604060512040501020c1203070e0d0f0b07020106180f0e0303220c0317030108010b0a050a090f1d03030609131a0405191202070602010204 74
    0x49020f60780c002403100d11030340c0c4100c0c01300ea00f8411644041d0000b500d040a18907007804030b550b810b18000d41d0f903170184031105111040203020f00c07451080401043c405c109200c00c0c00300003046c41d94814000e0000501340402c94800d5410280d60f12a40425008000100b001164119107824035414003070700c00c0c3c648104584d0341c03581d854481c640082d0000150b000081c0d4040e01c02d400000103891058100c5044a00c40503591020f03107440e21700384d0301040c10103a01000300340000027640d209941d900042e20b0b02c13056100d5050421102e815013914a5025444084003140140482c10908840e10b4880e9070b90f0761400e03040908441c00b030340700c280c425a0208401c100517a1141e09a00a60b0101d180002c1c2c000413540708100189114000781110a0524040c01c000700c5002c40a980f140c034082da00b051850703a403103241c420303081c1c60703540010705003100d580c503441c8008a22541c85070321510a4045441c841e820f101c4100200380ca0010441e6100203040c0226002581070084034024131071400298180b6040450 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 50120004 1250 50118754 50118773
    0x10b0409050c09031b10051c0b0631170c0603071701090203010609060801080a03051305060d0905011a0303030f0408040b07030503010906061706010c02040b03030406120506030109 79
    0x59118040e80790004a201c400c12142200c0082000a0846020107800401102510068040207200701c0003102e049500a0141040f2500d041d0303200c03c8011011254481440107043d200345142e04100140180b00b440716080d4441c01e442d04000401484038070130503210005000c1c054001901e00301c0351044000540d00700148c036900d6800308540050300d81c1d8410f402160f141105c00c0f039402c4d500e01702c0d9000041e640a513600441c181c4490b5619100fa99840d0001601d0011082c410320440b6030000c409100402e100388050480300c4494002452541c0c0d035480000c2c9190444800e030201075580d400a503042042c03d115171100100c1c1d1140f12050800060b000a40300e010007400c141d030444c1924001002c00c1095800c031350203040f2514178540c6440050600514030f400034007a0b00041468482d01041150090110b40d220700c600018102042c0e0310100115a02074004108a801039241d40c40f44603565001d0010300081c12040d40c03100310022a00c05000c094441c00b61141f4000c4c0d00d04048100031403910340 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 50121254 1250 50120004 50120009
    0x803030f04080d090311010b0a0e0112081911010605010f05040b030406020702100f0206070c080406030b0411041401022a010c03111b03060603062511010207030201061805010b04 78
    0x24000180d4032820710b81040c1c464001c0031100302c0d01e00184081099000980110b102108400030080c00304e240b070a21007103402d503000300b07401e460410004020f0a40108002d14415124030f0b000f60a041c1200c0030041d1020300c00c0340c0741c00800c00015406c090306c5805d115200003001c091802064072401c0c018040e09a2249007e424490f150000c0083d042c04015011140e40503400b40002c104040d0280d40100941c854100d0782c0010301409004c121070602c1400d400080700d8000618914051400d1026002000780381c1409400540b608942074041c10740c800588020580b44042c1038541044000081c00d1911054460646a11109034043c13001c800e04854840c0b044282480d14030940c55082c00c2e10300d6107444070846540e110b08a88015a00c1d072001d0702d1600e0701e80036400c4500703540300c1c0c1c0d007050b840c0c4400300da080c0880c119040c04102c910f29071210108403402e00e8205040e0000b443ca011782c1c2a40e206a6040d0007503911044100310032060410040c4110b00c140c0e208104030b5041c030340c01661070300c90f52 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 50122504 1250 50121254 50121271
    0x6060105180301090c12120c150f0b030706050c1002031005041e18021e101803080c0c010906090b030402040207060b060c0615180105120106031e02030c0a080303 71
    0x30303070020a07900e0940c010240960000d1000400d036a41c0c00001d055240c2d0303a08111200070440f50391a1085000342ca031984020f07400700c4518038001c2d0030820040200b001c0703000481c1c01502c42d1050b2107691402d0201a000d810241c2e10aaa2041e07244c0c0410714002144030442c441c948100100301070740501c079011009480c0e040f1400b2698610894001c041003000023014844d003803403e0180c2051181500713200030024801d45443d00400c01c0d00c45800c11010140e440d05801c6881e04840484543c4501403120f920405aa81340151136181c0d1203030070054114081d0150264030101404042e50f821850400090015190041480f82441040c1c80705020150009008035004600141001455007113615521001f0740180d803a03075100d4460341c1e6901e4041d241c1080030b419041182c05503003030510003000e0406010050100691804050102e100c07034907001c9038425540e03803002000055500b8801c0b50082c0030501e41c90004075039401094108038640303150a00c200c900d610308200d40440441074030f5000204 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 50123754 1250 50122504 50122537
    0x9010c0809070e131106040f091b050d0510080d0503010911090303070308100510020c010906030e031209010f020406170f100b0304020a030b09071a04030809060a020a060c0e0103050906060105 84
    0xb0340c903004500010517030103076038003e80c08980401c448503507900f00012144560001d0007040c2d50740508242080396030184000140d0100194500c211280e007010b80c10103208558058501d0383d808010b400c240401428100040000004010140003402846840c10800b11000e2400ea80b0100190f964458448005c2c2803080000018029220007041440104400b51002c00c80880d0000029100c490300005280410000c80001c80d2451180c46166501100040214a003c02d6500d18442c3d0303400040071075038250740312002000064030300d001810040089072608155001da1340700110003a20000c0040345100d000f03008000e49810041d000008a4065007500e86ea00d44890000c540540c12640018003001040c40612821030380010700308049401481e01002d2400a5103070b546014465031102618070001400206200c1c582000140034240e0b0500440700c48000568408042e07840424420001c00c0d42c4840c18515541c042c0030b407030741c06094140078001500d0007400183c00740c05511000c00c100d0710b2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 50125004 1250 50123754 50123791
    0x203060918070b030408030906070309050c040f0902040603050c010815060406030902060702030708100f0902030c01030513050601090507120c0c080c0115090b0a0509090c090402040b0909010c0809070e 88
    0x1d0520010700a015012451644c905d014204508564400c0d140c691451050301c002580c4c161281c851103c3c92a8050007074540a441a42000042d282924009481503541e1030740000695075841550000c61143d40a001422042400074100b000c004104441214942039000460b5555100b00c2c0c0543c2c28070f045c00124010f807800820030314000d004000750580705100000c80c000c400000c4404030612094010300003440500c0d101c800392a0000342c0250507511030505040e1540c025040191701238000d588000300010b039500c0d4240340c21001c1c2c0c0528082d582c0c80042c000c60a0b846540300e1502404034000b40041d803208040240440803c0300c5c007425241012a6152078041c0079081394800100c8513010040007921058440b0091501d516250700c11010818002514104819106d105810103000307014000b01a0701800800c00008104276409503131b40c0f00702a480d40c0c41c00d5405000e80800400001c0c1201d0341c1c040a0045840917107585c880340c4c001c1c0e0041046c81078203280c00c0e600403100c3c881002c90740c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 50126254 1250 50125004 50125051
    0x5030406230f060307080f070b1602031504030206070504050d021003020f18030f0609060109150f0303180e060d03031505031c090603050c0d090510060605040311030102030609 77
    0x20090261a0001c94000180650100d00740d040c0c0b4040c0c20b044043d65030240e44d642e115030760350100c813052851035006004200044070009001e0550f56205026480312816241c2c0064208031101002c00388000c043c0c0284030034168100607480c1e00009a003402442c00c0d05080001e0110882c402000348100c1c4000c00000b0154400e80542d45105408030900b0b4649460780e06d0160b00c18030811806000c0e20401e00d8441c150040014880d003c1c610b04e00c05400d0300c0c0d003824003120150400d10784a10303045c02c0040c0c0000e503a0350014a15130041d0701960348c44040c621400101c00a04019520074015a690b100a06c0501e40d11031030f2000145601d8200000c8407174203907040c01c2064030680c7c829070345400341c0c40303c1c004003050000740580c0c05d16213992801c14040d100e80040e4126a003c2e00c008030001800e109020325103842c3c0d4480302819001340c0c1101e031000c502e02d141000765205904540001100441c0c06c004000030242c00c801000f01c00c8000354254a003080109440c0340000b081410700700b0b0004503848401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 50127504 1250 50126254 50126291
    0x60306060906140c120c0a02030c04090803040b0c0910030b090601090305030d020a0909050406021905210402040906050910060b040305030922020a031e0504030c0204110f041d060d0305030406 84
    0x2074400608a5440c0ca020407407640c0c45114512099003c0e004258412662f03150038420a00450750000c030039825504c42c0e480358007030340f10300034038407610300c0303810400c03440f060740c4201d03140d0b842d00016500070075800c1c0104140034144c0c1015100605200c640c4a0510000f04044203031501500742c020300680b5001030540c1200c03001d0a03503210b004139901d018240405c0c4602600100701c1c52403204c80c00c080750541510704680600c2440c80400780308410701d501c65481440130b1710311908980000d0011030355142e5a01c03941300b241e00603586107050758000310103041031184900418000702058100130f0300b031610f10b8a90a0706ca1003444030044c81030030034800410f15000d040c01100d41181061404545030509400058014503401c0108820358005003000d4405020314011940704a41c0f50f51090440800b507801d001c051b0002202d100d500c00c03000d02000e040c48800c04090001401c00d500074105c1e00b400040511030314600504094028904c000b44a804203400104a07500954404400540c0c068001c1810120 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 50128754 1250 50127504 50127523
    0x30a0c060f020919030b0c0316030b040209130e0c0303040b090906041413020f060307050a03050601091203090e0903090a17010b0607031205010602010506031005041406090601060306060906140c 85
    0x718000c2441c8034060746800609100343da10441c0c041b102501c0e01c203034141c658001107500e98000c100320300d07804030154840d030400c618029001e04054104078004002402c00c0000045030b000441e80e030703950790313040e480c041205905c0c1c0002900694641400e002280307807180314651006020710ba0300070100d002922603a100b556800310649504066081c8414850008080ca65059102d0b65480148a201e4036021007241d0044c04580c80321480c065145101b58060a0010203043c1808140390b0000354058000000c004554801d5990742009170800c607405081b40b40c0030300070243d681d0080c02130000c42d86807007400c042a0340f462041d00e002041414401c2c0d014050840794250483c40201302042010340162140700c1c1180e1080d001d00090f0b8a42c40100e088800458101d0b0b45a03100e9440e6805c180c2295021641081c054005440800781d600406482e00701d040d602d005070381c2d20080041005179407520400007e090985000001c0e2444c0c224020140f500740001c42d841c800c000030b808c000705041080035a11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 50130004 1250 50128754 50128759
    0x905090705190f0609050604060f03090804080c01140403020906060c240a0c03050708010909020609030106030b0601020f060103020a0603020a02160602100b0901030807060c020708010504150b0102030a0c060f0209 93
    0x2985a030030302660502c0d1183c1c400c0c000c1880340448007040c941c1c001c0d1090810780780c001d046582420300e003031021075030f40600302c1c51482850707501c03100840460600f40050000c0c0c501d000041101204540005000c0140b100a03000a04014001800145e0b03500700490b801c9041101c4c1d0945034151940d6090504100030160341d404102410b480160448141c5000e100c0d10342030100f0400b00d0200303001a0b0a07100b007203410500084034500180082400d5a11015050303001829003410b20440da40400c0c21100301e50019110011100c01300a010b40c1d0422044000d80742c503078090507880d4595404185201d0090003031105154011800070030380340c402c020450b800081c1060003070030640e640740003940700c8030034083c612003aa0506c80108540d0030420604d5049036800200c903403134414141c0b50a801060341185c081d0850107032090002d0001024003540b400f890142000c0c500c28985092002c08807241100c0d41c0b41913410520550301600d03040031051031010b03000b1038089000c100d22503541000b40300e41320f203031035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 50131254 1250 50130004 50130019
    0x8040b031e0109090b16020c010302160b040b0406060815070e01030b0301090c030204050a1503060b0d1203050a0f1b081512060a051b07140120210601090905090705 72
    0xf010703100364001d4541c180c01914070a101d91503511060040c2188988003002503880294028074a51217540204035100145000010400446d505e11105d18000c2c1c0341541c80050000c03e0100b03206040c800c0000030401d2500030b10f070745c582c0d140e0f110030303801d000500403000d0100c082c941e1a0b240e40660081b824001d0b00038004c010540080c507140144401c5400140c0c0124034100000f4070280a0f8031a113440d00070305000484500b860740e0741c1d40c406030070040340e2540c010544a0383c01c1c00081031406440000c2902e07803008a03052800e103440e641120001c480200704030b41001c00d00e49a21a0040901d848017000307142900c0c0355513800485002d03c00025610795000007035004010060320020030755500902c0d16500901054962481d400c2410030394030b60540803002d0030488a00000c42001003007605101c07080010ad1485005281c0103103655043c0702da017a100d0320000300d8219a4000d100d920700d01001c41c440f0318013607051020000382380c1c4003680100c9030340b44cad520404a00702580030000d0000034003000302103c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 50132504 1250 50131254 50131259
    0x10603021e06130b030a0b0402040501090b0f040305010606021c0203090a0e04020f0913020906150a1d04050a0c030b041103130201020109020d030e12190602030a0b100e0a0902040308040b031e01 85
    0x115a00484590302c6c5d0500d0491090140d25050080b18200c45050351b451500e00d003049506600d6504c007003443d0314030030b40400c00000000c400380242e00041074150007805001d0303c4c44404142881008060100315041000700d0343c0c0c1595281002d07004d41c0c203076640700b40346d5079505c0c408101c00030705990f0b40c65031040300c590401660305c0e480d50f00044024400d40d40c401c481c0d1154020311804058400d05114528000d001802c2000d210b607001266608000068007400e04440c40428201c4000b580c0f0711040c20384804001000c940c040c0100c841c10384c400e440400c030718407106590100740d01021b400700241d140450460802c1d603100350002c101c0c1e1900103080c3c0c440311007546000340c0501218140b01e8000d20301d0b202e14240754132000c00c2c1094007010b40c401c1010111516590b0b031000750700003842d1092441c3d660021115545a041c200c0d403506d40c00f0f17102c4010f541c06a8003007000d08407655010100345801000240b00280200050301d00f281d680365000340d02d90701d400304070780c915515001d400d9881c0040344000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 50133754 1250 50132504 50132519
    0x9050a05030406090503070506090409021c1b0e09060c0d0b13020405100c051917070317010807030201020c06070206090607050a12050702030c011d0a0e0f0702010603021e0613 77
    0xa00442d0b0f25912620992039440d002d0503201c514134401c6541c002004d01c100100c0c0c0c00c01da000307083e0840c4020200e4400210302e180c07103404001c03451000c5d00d50350320404a01045180060500c0043d0154008034149450078903019680c0300c00c001c00ba885030000118038132281414640021010302c500038412590283d221180c83c3c0250014410644100315506480142d14040c1c844640e415402601400c2d040404481d26111528801e00482e11004054110210014000f014003e183d200e40e6a81200761a0407904a660580680240940d0307003201c0c00800050380c0014841201034003e444850b00c0c0d00050000030440e0090b0140c064200000181c0c40d0104003011541041843c41111541710031049030380116001e010300540250590b000740035055a56001b00d6504400410f00103900b410b03041034001041025615a10101c90784103d481030125200322405c001e507100025100801c0a10310b140c0000d121900f20030b40d00100180c07600000143c5403515821a80d80074082d010105034996241039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 50135004 1250 50133754 50133757
    0x40f020a0b0a0e0f09040804031b051203030405062202091b070f140105130f050a05010c0302040602011103090d18050d0803010801150e0a020c0a12020105010501140c030f0307020109050a0503 84
    0x807541c401c0c1071401940304180307000185a4080c82d000900c1604227801d40d42c41c0b0100c5400d49c040c40c40304206200d40000c3c5a81c5100c08a00d90380054006980c83e41000e1424500d801c0e0082c0401c0402040058419212010700303403110300c800c2e0100e4010705603407510911540c003042c1c004007076081035000207040307424026905903100d203203031141822001042d2620140c030700b21181075441810036140035000c070000c02c0c0e038004100c8640340aa0251090071625903201801c60341c0700c000500103c0c0e00030a04020f400c1d028855910351421001c400c80c038603d02103a880381c079075800705e281406110ec54524a14541e20681d07001024107005001711500201500300152140c000b4030401400313600303024280d492402e85042040484101c0903404865448465400c8041c2d042440000440e03c00c01990202003102c4188042002105400001d095414507000510305070040d40d450120100c100006e2800c03032000000c560034151395507001900c81c0c546590490141c0100175000c1c0c2503100b0a10120b050110210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 50136254 1250 50135004 50135027
    0x60605041103160503010605070f030201140123031c050c16121509020a030b15090a020d06080f030304030f09030206070c140a05060d05060a0810060602010b09060306040f020a0b0a 79
    0x12001000d50f25a440c084509100c240030300390018809100850000e608a401100c40b00d129000100718072100b940320000600c4268007001501c07041e150400c862020341405040c04400030340160255961a819100c0a1004080d40400f0040300080d030901c000e07400d000c4c0c0720b00c000c1d0f040542010a981c03005000c2550400620030780322500c03410340c1030140800503ca18008564040d01148000b4030b551a030798011300004200321011500c0c001da41c0b0f51a40c45848151081c0100c0d480140c596515090180c2120f0403600000759a5220307520115180d00c00105481c0c0c0075900d40390011211100700002c45800146a2000390801c8010a5450401249022140540b0761b041900540401d080d410042c1c9240c0354422290000d0041122803001c9100d60051680101c0c0500800911035803000788520345450255050341d842d9071141c00344a0554213001c2d07480d400e601202c02c2116410321400090312a40d010740001c00b040c090381e00e440b00719110780140c03100a150003104540c8402a840c0f0241108801c6c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 50137504 1250 50136254 50136271
    0xf0901020d030603211b08040e090c01080a09020607060504030203120f010515090a172808030606090103090c170601080a0506010b0a09050405190b040903050f07060605041103 77
    0x80696854801e00c100300440f6003007174101d40c8403640181c40421255041c4a20400c2101341c940c1540b100e241c494003090428450720400e65180d10384501d1719001e0314050002c241c3ca07046284004000c1e0b90000015800103640c09000450070482d20001e1160700c02c0c40e40082829080204020502d034000c009030102340c0280524142c01d40e2061029000718500340121540981c1c068010349031401104090310a001000c0c001035041070300c400398803041000c0301c01c2c0c0114940c007880c2a4a041c0c116414007c0d00401c860102d140018820342d24114240401007055008090209100a0580c800d400800b040e41d0000c0c902a401a114040e912400280460002c0c90f1f02c2104000100c904002440c403c00c16000307000313007001da402c00d2070801c201d40c8061032000810805c620f0100d0300e59151300c650b030301842025008032021103801510030b060702c102a40607407281b890080c1b1704000c20740110861b00410381e0595203d5482d001c1e071038540d001302613640003213030400d00d080c0300e2070340ca40c440200542c004c17200e8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 50138754 1250 50137504 50137513
    0x612020918012412020901020a050604230307020105090405190603210203121b0d02040806061f0c06020d061205010b010305250507140625090605070b09030403080f090102 75
    0x210341440e0810304440f51070000d02c0d61029100b103141030342e002d0a001d0b48148160ba90810680e00e805242c001d0a58080c0d82550f0002078a010002450a4292a00040501460a00810740c0000c0d000780959071140380255201c10010b07000a00460b54426a421020300c200100340d00c90801060040c480c0800304101d142080c4007442541c000420340f8001c1c40f1885414030182d03190800300070080035003c50100d81070002d10091103071200500203030004d8030505005180e00d1070024100300c0c6048000c0a018022080069603911031179100c034131140000d400c0000075030350341c501d8044180209011303405550b9054010030048100304040d08100340c401000d90f030501c45c0741c503454441626840d000300c44031000c1a25881c2181d500740108050001c0502601d45d4041d4030040740e204908000702181d2140d8800008101e400040c0e80c81c40c1c1101a240c02850901082424004043c09502ca00718014100350903980004030084010401c84010750307404841507403610b00326051412160131641480307015025 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 50140004 1250 50138754 50138789
    0x60f0b0d060b01020c041a06070c0503030c0a020102010c05030f070e0105160b040606050105090916031112040308090105010b0a030504050109060e030409183305011e150504061202091801 82
    0xc1038014841590070b0580740844070035a8a01308030301c2780d006041c100c80107103803005c00017030580d02440078101004240d0040d10080c01c540c8002806c480b65520702c081809024000e0015911408020981c0b1050501340a01d48020010043c1d0381070007030b40034207920381141c5e211910801c41c503d25098011407040c001844841c0d150380040d500d5000b5054103e411840e5200001d1f8a212103d0701d80c1144811400c00080950303243c054406254480c02d008400c00010500344000c02d41d002041a62001d20700008000d507504216882d1070612405602100f05521803021800307006007035110641c4240d22000409c2185120300c80561203400c184207007648a4a818810350001051024400304030b50b110014031500c041070710200021441d9000e44024000440c40703802c00301e0206215550283c40d91344481c40f0707100036440c0a003049091980140301a008002d2113071119541060a64041c3d54150818011042c407082e0554001d005070050954041108407145044003400845030381600ca003200e00000500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 50141254 1250 50140004 50140009
    0x302060c070812041502030a0b03100c3002030f06090106020a030207050405070e09091f020712050c210301061b03020705061305180604060e0112060f0b0d060b01020c 73
    0x10000042c24154081101e030541c2060350038035940c09031103050b07415405603800c08680200d800496528404c00d03520810303000c07946810400750509a091400500079440301150040c4107002d40c07581c2042c5d8495002d441d02c402c0b003109604800c10240d404045446c0c4c6480070100d4180e80c0166405405202c9072400401d150344081054280390b5015002031051516010a120042600400f080308001d2042e2000ca807903520141e0039400340c196900248500c0401c040313006448400c0350820180b6038810030840d400074444984030240c26525052242d2207441303140728203013080d00d00010011035605c03d8040b00402c0d2104e4010718181c44150b501c52880d00d101d034068102aa210900103005a80a1130b01000285404001428146000c0014022040d6244007144040136501f80b00c0240407055001c00841c0d040c1403080c03800a04d1940741c55141545001c42481c40a00709110141075140c4a0300062030720354680d001005610409026015005a242030020007070060003078450040c0078910301d064451 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 50142504 1250 50141254 50141257
    0x6030b06120408031302060a0804030905192115091506061209110301090602031e040f0b040305190206040b010b03010f1415130e0108030301060804021009030b0c04030302060c 77
    0x750351000d0341d0603203840d60b032500a003d400007829081e411440703080c00c5005840301c40142002c0c1c0c01588404d115802d291070043d0030011a0f03000180194104012034124608108844048071a1003c0010f907107600f000032200101140d4001038038409049400181104150b408407855601a070205500300c0012003000081e00d00701c0c400c3d900010480034540400790110f50209a0140c86140420310654580c0086800c0d10415001501c403607601104001e180ca0072801240c0f40d114803003134048003a1500780d0b0b900d0302ca0b54003c00301030069a2440c000604040c051001c485001d50340b113a0351204180e00c014020350b916000c640884840c00d0400c00081d0b078510a80a981c1601c1e414a40054058180040d01c03200e40c039442e81c026801105014856440c014040061420f20f40b201c054041081c00d15030080d18000c41a403140701580d200b0001040700c3c507800b1001541107641142c81c000c40024134081182c52245580000e022204d084060081c120030040090013164403a03025202035581c0c0b4003095006 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 50143754 1250 50142504 50142517
    0x703081b0301030618020901090f06080703020a120c0803040f0810050f0712060b040f170703020f1201021207021b04110301030f03051603120f0b1509010302070203100606030b06 78
    0x20a40c05000601c001225900081020561142140180c8036142c0001d4220303182a800042003a655003103402000810780601c00c040c1c43e000d00103083c15841c59001c038500351702520400503510f551141c0c20040103c641c0c48500100101d100b140c1e12a62109131031030f43c000301071003000031600c100032405900420b64002d0030b114030b183c1040002c1c20745d0b4041341a2140f000307c2d5003422b06c690752454045400400e181c090000b41c103d40000014550508184100700480e004810f0b41d03c0c0e0184504100603070324511116403c00c020b464802d0f5003816441070502a025900110132030100300020055241c0d40090b2919080000e50780340b01c042c400f035409000494401142d46100038008100600214000205d016491071180c940107140c070701000040c0c0c240001e0301da42100041c90140c0d41c400f00c170074940540c0340080c03203a00d13040140e0800000000c002c0144000010948200464820b4480c2c1c0290706841355160040d00317951a181d0420401e000521541c025400400e14090700340c015800c0400c2075546 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 50145004 1250 50143754 50143801
    0x7031128060509061303060b03060609040503160804050d1104050a0e15071701080303071211160503040819020312030c070803040c03080417070602060709060c05070b0f070308 77
    0x10314208442152640d2000c20100d401140400605d00040c8100360b0310402907004c0c0030000b5041e0400e07402c0608088001d0301091140b1448c0b0b00344000b0550120468020325848244041d03004600d20f0700c050640a40c2e805076600c02c0c3e00411007000c0c04285401d020980e4000c550400c000d546000c201401c480143d6110541c45e4848945422702000740088150440d056003081421054168080d24075144240c0061005810100074061026080a04554201703280c040a100c1c6000203643d030b03a0782d80600c0098100d02c099000c101d030140801030040340e014110501c26249640c5481c0d502060072201208201e006c1d200b03040c001485040d001e020b490061048140340344c41c02d4140d80326040240c20180c0b041d00c5040d035640000002803881c400803c0144044980880c0903090350641a040c808035500003401c0d90006001c000c0a2540251681c0585441e0b05100c50f28014505110b0b2502003984c0015505400001b100c82c40c01d02c00002030040309100355600700023030b6154174091014110781d80e5840c0303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 50146254 1250 50145004 50145079
    0x3020c07050a08030f07021201023609070804062703090b070f24050103030e03010507020706091a0d0f0204082a1002010b031501050406081603120908070311 69
    0x10070201c0400f00900c0386c41e000070040080d01307030000c103d64220fa0042c21040c9900f0040b040c0c1c007850106188020303015212400d0741078110030a29001c02d84405009104104120650000404201d0240e21000300546403140041090001e0f601344280251429001c1d0042100850001b51160a8104940700550711600403a05c030005030742d41081c1410170595284a045070300b00a00c1c0000623a10800d4021030182c0d03180c0700c0c90010768044c10700f10f62015240c0f400719080398805111658001c0007030f03011501000c2007a0b45881c64480d900702d072030007170400030301c1d1143c00c02c03805200d4041c1580182043e00d658106655440a079083c004002c444000f900150b1f0805210400b000f501d4100d0840140c0f04040c00040782d008243d00000342032440d11000301614130b02400041c03203503041c1446000064a0180000c00442489045407220307140f0350720004103850010728550700254414003070000281202411501140e40b80d1170b24500545500031028001d2030f202c49011020082480c2101c000faa4122145 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 50147504 1250 50146254 50146267
    0x10908070f0b0a020a05060a0218090405060114060c01110702040e070e06060d140f1501090605090f0301110d021c020f07150b0a0f091a01090603151503020c07050a0803 74
    0x6950341d00300181c0d400135409100c80005c04500709005080c0719820381c01005a440a403900000c0384400508043da02800e200d208100000742e001035181d06455001800d44220305080c03000071003512482014509950070410400c4068050002500e1254403c40d020b104155883c001c40766a10014810308008049c40804140340d4107180d40100007039141e465011800200340c1c103480ea6402019239103150510351400070402808440496540310840900e4250105803904000601500440300960f20840008160628903a02540b000c26100040e812881c0c480503400c0c0700030020f4002c2041484c503d0032035004520303039425500c00c1704d1b40c0c550a03090080c04d06500e0344454500f144000c000c0c210300303680c2c1c011f4071540e41e1781c01314204018404084c481030640d003401100c2c8195401100190b115101e0040142c880b0ba03008410202502d00360314000510019075500328690008c13940c48034003030043d807014840b490359054005000d44410882128600395a078414401154150301c2002c0660b00300b840708 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 50148754 1250 50147504 50147519
    0x909050f1003110a0f06080a1407020d030b0a050301060e070e220e15010b0714030405010801051507290f010312111c02010212070903050a0f020d060f0605010908070f 73
    0x5403100f40102800070300515440d01214440a6100c0d0800000b00c1c02c43d20070044e044c082405210303000404404038040340c1c100090040d660b080900666805d06443e500c4c40041d903202d24819000500004009102580e1790303004040131000203aa44400261000001442504110411100181c0a850b500d505d070041136001000520000c45802c50364060200300c1041072a0303400060f03001e08060901180c2e201094609515a41c01c0d2401303081c100c1d001400304120903070308a807825045440941d0040003400301c3c0e10090003180f08151004107101803405c140d040350b20008150442d0701e01c154450700060b49401e00c0d80380368604248002051840701c402d2030f0350468800d80405000e15518001c035404580400401c0900c071a07510300b140010303980461400110302c9160308160f04084c060400b8331405040d44c4906403103002d030b1107018011491350422801191900d41e1b04414880e08444100400c081e810703541d5000e007500e44140b60020302c40e2031022036181c03c0450f500040303a0100302c1020f00186090b84 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 50150004 1250 50148754 50148773
    0x20d030905150412030c030506090714040905070c0b06030312150307030c091406010503070c0204020702010504030204021603030c0e030a12020309060c03130f03030804031215060909050f1003 84
    0x10100e8042c0a0484250302003a095540700e4022440b0300703070000d49410003020040482d04000c10003c100b5040c54180515070700c4555800350082c6a52034111004c03000801d0b0400700e449941d00040203246400208072240342c1c4541106520303441440c109680392030355010195240281c3c8294080701c0489404a20081d145000040c503240f0060151041d26640f515220040d140d9035022200450325582c1860780000a0800582c0c4241d090914600311f04020074001c004840590000b4000d585c0000c190b0256070148082e40e00850f40140190759990f8003580ca06d484407108041100401e0525150350581130244042c040b03207203005030080103100d401c0d0320340c07103000201c1d84c00c04c1c0c0641c0800c000c0c080468542400030104032400100450f6203003030460140780701b07032240d03400403041c902c94900520021340e103d18010b4100340c0600d80035442e1140118514010031400028003aa500042c1c1d000903144c4d00300d00340000300c0700000343c20042540c0e0f03050f001100b100102e50b10040405441403e0001441413030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 50151254 1250 50150004 50150021
    0x604050402150c0105090d020106060c08180901060203090102060603070b120c040302041d0d0e060f0a031d07050310020c0a020603040602090301061d06030a11130b04021204030915020d03 82
    0x40020a03002c10607003400015501900c03030519165111000c010a40004000e4803507107030142d2008000365031801c90020260001c120008041d80c0002429154245035400300110a01000708ad146041d69186000785d50b950026860038090302a410000300c40740f4011410390212250180d1350340c42d00c1e46140408c0d18540006041c8140208148004805030322184281000e500640002000781c425101c480c500d000e0120303072000304109018070605480d44a420079103650060364445c607034503031400c02c00907030141143c260f3f4410513400700202c900c007000000510b401119029000e8a840344848142003090348034800030011079a11000480c0c00500301340d4011503016004480c0181014003103000242500c01daa0300201502d200c1100c2c2181c112100c550780ea0b0008012001481380ea4600c1d40c0d810940110460302c24425042e55850301c1c10881140c0201c801808010421540c54000324a8244c401c1e0003601c0c01d0340012803d0340040381e01000b59501340400e242c103800805101110744000c80c040d00068 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 50152504 1250 50151254 50151259
    0x6030d0e06070f11030f0a020112090f051507030b0613030b040305120903030105100302130603050907090203010807060216030308010515071b1404090c050d080c0708071805060303030604050402 85
    0x10800c00c00850700310304a60f02d08921134004951898004810180b40c8000444c800b4210b030450065480141c0e004420004610113000020800301d16a04140c1010b500c51100500b07540114400300d54240c0ca940440c600c100c5180d1001c1183c045c014092042c2c0d401009241c04071030f4a60001400450b05008085030720922034680300c0d280942114080b40140e0058644000640c030120042c04145401c00b02125400c1d55850214240501d4000030b6040f08180c0c40b0b154189507030340010994514040c890000a8940024255500c0d65110049a640c210500c905c034010b0041401161000440d40c0d1040c085940645d00d049669081108100c0002401508116442000c0150f200054401c1d0009558800c2c0404902580c52402103000d07800031350368618910403403600c8005070010740c0c00904081a030701c05a6140a400040f481c0842080c03040415070070040c414101300099950b0005030903c1640c00d10802d01405004100b604402c4d9503054400790f60541040c40003074107505142d4070056029000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 50153754 1250 50152504 50152507
    0x50609151e0c010b0616060f0b030d0207050a0608010503060417070f0809040609020f1b0a080c0d020705040903090603090303110a0f080912070b072c040c0806030d0e06 74
    0x380e600104000c9030858000040d40c0216403000142e000303110350380b07002c01d06560f400d203403041e185000c0d0350507801800700818a03980c54510b20948005039202881c140d901800310342c91880c108402940da041244a25449004480000b04081c2d00c40c40295040300c0e0b01800a00c55601c4556644c40c3c545200e0100c00320500c0309018800c00b24090b100000e0701c0743c0c00b0b14407003540c80e8801410300003581d006400920885004000100700340c0c03040022a580c1506a50107403030020400030005040101c0307503102414014000c6400740c5123500206e940444580c031a000c445116039500248000d17119420340c06400300348507200c10030046000e50404c00800c0e2003458005074003490707070301e1342a51a0000401440060204060040f0841d00a05041d810841e0b0100420800301c10107540241807099642c000c010140c04070101d080140540d0195601696001e18855520042d55450502c100d41a510a10a80c00c00045880c410301641e0a01d01a82025000e0000d140c040c030f000713640c402401d08106801410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 50155004 1250 50153754 50153767
    0x403030b061309140c0a0e060708070501020c0f060601051206011b05060919050318130e01020711010c11190314030a020706020d080a15180b04060f05060915 69
    0x11058000c0182c400c14848444500c1e0a003607016040743e032060100c102c090040c4050001c02810b0f00c06980d490007652800501c0d5039010000b040b0a070007845001040000041990340c200001174016198050704c40c01100c3c404070001306455501c2d5025a015400309400308410074450b0100c841940c1d1003101810318081e0700303c0341440980c17010400102602d41d5001413080c44107021081c45966039002d201d500042e5142e4494648945030712031131250b1810040d00d02003010301030f1103126400c559a914540100040c01d420280540130307502c00b200480380c03155561f000d8881c6600072000109a0b5410007846101c0100f40800d11200084400030001d0811100706c0000010300400c281d41588030701c40c0c1c00385840340c10503800a45001000e800c5a01550410581006101e6000700308a900080c4600302048040261805070b0220300a0342041c890030100d4a0300b0809070019401042061005481c03c12034581e6582000200301158003600b9841202008925128904000104401d4580082c04c03443c044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 50156254 1250 50155004 50155009
    0xd02070b16020f1e2701170a15051e0103080304030c02040e07060c0506010806160807050d140402090c09030a080d0b0904050601062606040c090308030106090e0a0606050307080403030b 81
    0x5180c3c182e01028540c40740101044c0d401c1050b242d4207a040401c903c540401d0071007800f5036880ca0140208002c00c003080300c001380728046c1040740d084040e402c0180c82c0100c2d42c072100460040c05c03048130700d0480424035665149845600c041c1150403660040212821611a0351301141c071094001d030180c0e03010b922902c214a03210418030200780140001c0d1528407000095260035402c0c404164801c0c101508920100101c50804d1841c601c12840d0038540404e10741c0d24043c0030303565030003544001103c0910300140c000c4150300d0094142d000d180201c80801c400d586182c2e8074001445041500b1b0380542240b800c04000450341009840e111004a1003c00c8113400348010690142007110700341c1d0075030320686c010000141c05c9a4000e6002070000c1c2c255412002218100b01c000401800403800b6903903a0710001519032055a800c00034640c020501c0d42e5039696644000c040113103a006d2041c02440b00c4000c0383c80d81c15a40304a00c103c8010b500d80608581d40d1480c1528503c400500907018161a60310306007c99 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 50157504 1250 50156254 50156269
    0x60504020d02090a090c020c1908121803070305031603110307050d0809010203060a06110312150102010605040213030602030c0403050d0f080108010509060c030a0b090a020406020d02070b16020f 85
    0x12103910040e21a40f01900b04030703020714540d20880d480e610380160380d0b04160380070620240c1030105a98070b03207461954a042c10010200c550158650f4010503800034400c0506100a103005203080302d1801d0b40291712001c058888949210080c21540100035849840c400280c3e10405207007e0308043c0049030038800c09506603441220100c0d0359810814080103246d400c41c801c50380004140000714214940305c0301007071407041f0340d0142009010701040d40d200b10800400403100d8001c180c102e95080380c142040524008045818218055402d020010a4900b094800d075101c1d080c0741c184540400745991203100082d07001030a407090320a010003020012540030804800100032607a5140c80c80840d43c000107200385c806030060240c99060070309001d1105400035070140c0220521400ea60b03640c031000303c801c000b402d20006003904526040100040c085003980a041207440c0c0e0b400b62640240c6001080f611002c00c0d0140d590074820a0003410200c589540b0166121480503100348050020b810005281 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 50158754 1250 50157504 50157517
    0xe0109031401050412081b1602031608100e071509050901060206240d12030f140a0606050a051c0906090b04060b0103060b0a050705070b0c03030109050f01050d02060304050106050402 80
    0x1d9039111002d0000b040030f4000403038251001407600d80030605020030041d800d900c80101c81002c002008c529844045854400518210390040854104040d25602040240024031030b031481401210791888081c2d080d8000e10540c080204d0180240c68108440910094086601d0030b0401c02c1064022520b80c80c0e0340d00150180001f074004212925190141401d032281d0550701c401d40c0114001484a1070715030041c3e80c100355a10140381072488078a00c0c0128000c0a07141c225159880c14070081b2001c0c0c034100c0d403203d4007900303042c1c1083c0009915501c1c00d5036140b044581400010300100703d11500d00144c2c40050340d4841d5240c41c082680a5642c65030b000740d0719156003d8444207182001d12080000310b11030300c0c1c401d10302828140082031600d10003600500032194540309200d40003d5000030004c007844000007070312400c41003581b285290700c04941d0340d400901505a406240c040420f603001e00c6410400d040b13400050100390001003035800d11519800140c000c481a41d01c412000c600c42c2d2b03c6001501c0b2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 50160004 1250 50158754 50158793
    0x3230304061d0f010c020906131104050405090a020109030209190501142701050105070f0203030f120108060c0d0c1709010b03100908070611070807030c060501061704030e010903 78
    0x580240b80090070380301110312000c0e140b09041d030442c540000c1c0d8001031a0a10260111072008803981c6400c08210344211070505c42150034500718007d4650300354100038109a400c141c0b000c0046c0d0392007223410303a80c07105442c80c0030f80400c9500400b00b0051030007209003030340030300d180305004030050184104600707603a000e0300311503402328410031051038a003000703111182c0080b22880000d00404407890840d0007404180161030402c0301c001901010711417820020301d070030781c3c1c081c04407543d07840c0d40441803889030001c51002e00c0c0e207034480000085c3c0600c002207030703801844440040c2d46012031a811090041456444d0102445128419500b840e074115a150384074002c0d01001042150084040600300107104006412040c40e043c07401c004640300c40d007035030750b000e038484000a81440000d100403594080c10340000d0160301700091174400c250f8040003500c0c0c0e5038441c180500c0244d8903070340241d07800946485040c0c00c1082203800600464410066841403a006040c100180d544940300c0c491a44000c00c403894 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 50161254 1250 50160004 50160017
    0x501051003020f01050a0f1103040b0d0f05100305071e090c02070611030a02030313030c0f03090f0f050d020f040e0f01090b0604150b0903010605120c040c0212040323030406 76
    0x1503041c506503c0184600900e0400e180050710140a00350000942041080081d000b5031020000c4080003240d019140c50030501d915081c0c14100b42020340341ea5400e4240490600020541015030101d60205995001e03000c0e001003400c11500c0b40489640304a0580c1e80b084404000450000c9446243e458400c2c7d6070251200c2402d00101806000025090742c02551040001d11803003640441625000345003002c608503c521141011507188481410262940c110198000205074104804904442040034100340c900d80c2c964065180f90881d200c0e2640084a060171100140740800001d158114001c200048000c141158640b5204014140c407046039540c80542d1f0a228690084ea540070341c04880074804142c000e5545042d003401071190031100500421003504694017900043d01510014240722660325a452403a5510312905085034040c81ca84840c5c116910f00c04030b24905051020707240280781503d1035503810303100c0811914030320f0b9640b09100350a41c044018002400140342c59034658 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 50162504 1250 50161254 50161259
    0x1090203010c11070506160506090a12020601030201050d020d0e0d050702040b0901060c1b08012307031514030708060f04020a060c0c0b0a05221505090312031305010510 74
    0x141c01c40c0c2460000105010300314110202100300001c1d03603070680c1e9083d6019a00d41161101404440f10341301402402d6000d032a0811152550000341001c089002d5094401202080003060b6200c040a00020380060b10410840c1082517064004162441c9404070010300442041001401d080100c1000c0000070350005201e4107502d010b000701e400d125001c450140d010751600d0070103402d0160316100280803034641e400b21042e5044119800009003411070007801010b84088000c0b801c00180c08a1a4400e0748610224010a12922035159a1128a201e030071031581020b01611002510070045903051141c40f0000c0342040060008600a010b032120b0312400c1d0074103204100c40072903240c01000030440c83c84402c9000c02e00941e8440c080340c0604503030a9440210340030460b0103101d040c0e0300622103410700030f010032450300890300b081c100d408007500c0d070340c0c0b0403401c48040703500c0c0c81003840c995410384c40b03d0403020244507004029a0442481800422191240c0d0340e410309459040700c50400521610408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 50163754 1250 50162504 50162509
    0x110c0a0f090e0c030303270a08070303060902130501120b03100e0706021513020d0206120f011401050f0a0203090a0b03010609090203040f0b040c081005150a121b050d0302010902 78
    0x9002c0c02c5006080600400d050100104e562800300070600700424800452240c0a600750508048440b000f81040ea14030452604204129a1201404400107440d0120000d20031000380309031040c4048140310010424641401110310070203100c0642ca14550b520040840c0756400c1000340101c00d455400481c0c0806403505203804d10b28107501c90800c0d5001001c02042c001d452484441e0b110940c0200040c0b48e41060003c42c0034880d244800940185000649103460448c241281c1c4c0708000400b044540c2d6078031010f060b40020440c1030286c1c08204c0c24003008200b020707004094540a5042c1c41100d00b0142c00b5400210304000c0343d44000420030000006100b90b5504c4994200030b000714030b20551460401340d8500340850720701d4401500590080c000303e41040a00343d00c0200410b1400112416408c468084100070102a9120740f42d980301900c40142d01e0900d4102c0c00d04589004400700070a0759243c0f02c105545044103021038240408000120741d603551008902d2000380a0360000414000c1c9206 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 50165004 1250 50163754 50163761
    0xc02192d020f06130611010212071707020c010e15090303160c0b030606040b0703120f0e0f0a05031c090203010c05090f0103060b040501230a021f0e0607110c0a0f09 72
    0xa4903016100401520210740341a030140c4c3d084840c0c51503c01c004800c04000c0e076009024401040030540c60380c07800d000f1407a42c446600384030102040010245522140c00c00c1e6500d0315104106c9000c034411084402142c60206507200382589506005403410070488000381c2160f018002d1a05002c5030001000c0034005031618690203410114902c624600340301e030000b41940a035210786854800c00280b08400c2511a401e860007600305010107007d0700c1e113005805005003106e11080543ea04c00c600d48180c0701d80c0e0014490103426003040103145404d4545540c6103400c481080b80f4a615512107c0003001038a00f48264140c00c079040c0d0f80c2035141d1066208009050612b49005030400d42080800d2103001c012004490449500f402c020742860b04500a20720110310211598100000118040b209503030082041c03819141104d8800c001e10f40174110410450302d207203134007506607400100000c031014015030031282c900e0305183c11544000000340002d085081250441071400310300890030004681d0900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 50166254 1250 50165004 50165029
    0xd1202150106080402060d0f0501090636020c0a050a030201020a09050d030f0e15070507050306010e040b04020405060a08301809150307060302030412030c02192d02 72
    0xc920035a00d51501100030202500a0f0010303118040c00200200742e90003503031201e00340d1210308005010541e55402d00e100206902d02c60090303001f8005010358108490550403408280c120000c00078051000f0300150001d4100c0c1c40d10440b20700c203010310140407030020000300750f00c40e12960002d03945030781c0c011000740100e409620650080071801e103001c00023a009044010201250b1422040800b4080009456042a01c55034105120700003805408c0c03010101c2c0400c190340040d0210b0b5810799031030513090900700b0300301c1d0090003902511000c03800514003030300400e82010b801840b5901040c0c940000b11f08003003519206442141c0041d402c5003150070508660b4a591104075210380c14500d40322544c4da60502c2580040348204c100d000002c56084002d9103603850004058101d03400700c1d440d0040075001398000da03404d96074586049020900280302e402074807010003041d8040c004818070300407540c6240e00c2c41d1504817145941c1c000c5a0358224840c0e00084240948030904610300c15090050140c00740307400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 50167504 1250 50166254 50166283
    0x309050405090d030c02070b04080a02090c0f030c070302100c03231605090a1a0a02010b06070f0212010b03030a031a0d11090c0f0406031a0a0e070c020a03020d1202 72
    0x80801820b0310011581c0c0d2100c0d1024140400c10b20001070040f8109900c9400c4070040071004078010510303540010740860101d2003036600500c562201034000000d40a0005404000402003000034006240386014210085c424011904040d00c21130b030140c291040300303103071800017582c40140d03031000c0e141d4120140d4005c81a804600480c144001982d0f0340003040305c0340d803003408000070b92000c568940354403401c000c01c40300c80700c841c45ea02c01c009000303495408046070f02d00560070514091214601641201c00307565002100c0300c90300003140d00780300c04070201285280580d5620340e203440003a02c00780014505910150f41c0092981c1c103034550200c01410ba03040d80c0740540c4484c2c030148001000035203001d00114040790170301025900c165414a0511503143e000c8189180401d0000c0c14907010741080c06007103102000c4000308d00020091004481d51842210040715030000030402e554050144a14082e0004d0042c04d9140c2d02da03000301c1c3c506020701e07500b22010174400002c0f0b48225410f004198500d050b4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 50168754 1250 50167504 50167511
    0x30809030114060306150d08030108010c11030307050d05130b041103010c02011a09040c030510020d060501030b15160206030c034206040e090106030309061803110301090b09030703090504 82
    0x4030010a170358840040103807a26055900301000300350b603640002d0a1966000d4096603607581c6a04501380606013642110020607084406011406408402c1d04c0c818842c075a10382d81880c03000040031018100180c04100c24483c02c5c06001c012407020715140340b08600400d0000345001894045c1421607040e40728980c1103914100290f080c0904c104500401c1c0901114a82c009440d1410540032032511944001c1c660310440c0b00ca1842c01010303402910302c1c15090041082043e40c0c400041d01500c03003039040c940e401407042c113413821010046806072101340c0c003030480341c00b01d00001d82c04190a58419600d01019120102c200030404030a0b100c1d1810820308203c21804810001e0580f80341c42d00b41c2c1341c448403c0c281d4642d4090407525038109440c001e08440e007228403107017031260311180208594042030b800541411340c08a030181c010000c13008a10540d242c0400c006143da22405a070013009c0c0001c60b4555201c11401c4042050914018040c121480140d40d44c2ca0191a014009905543c02035004604 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 50170004 1250 50168754 50168761
    0x60c0a0512120105060c07150f0305060a050907120f0204080f060a090803010e0c0f04030605070f021b040b030c0303040e0a151d040212011b0210060b1b120301030809030114 76
    0x51080c20b00341199400d0791115118011060031509006142d00107400c0140f02250104046500c106142040001c5440c02c01c01501c6407414800710800d1401125042195203011859a51281000481951600000156260a00e808082a644150710005c6658040c07a08540084020300000e50484071400c010070607071000303541c0c0300c44500051141c00c401ca00c0700000208a0a10001218504140f0511107540d0355128605640248400c0c0c503d54009200d006c1040d840500008400d0050405181e4080d032405103941040301508800c0a0325030140900701e505002c07910108003803c054500107404440310700d0400900c100302d51902900c0c9411002d202d0003003110740c5c0020a64080b00502c088100450f0b603440c00400d00ba201900a50a155032030b000c03401d11400441c0c054a0b51580e069030a50344010300e0880c0c1b460599045020300c00d0805e100300300d0800594100c1c51000011aa80c905840e002c2010300643e52040d0800d031302c26507081d000000d0300c1c0080d1800b8032440f00f504686158101c40d42c06c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 50171254 1250 50170004 50170027
    0x30112120c0605160f0e01020615030304030b0702011407140702010e01030209030a060e011416050a090906081b03060403020a02040e0102070204020f071a041104020d020405060c0a0512 81
    0x241120000e00300924500c10306004510450081880c0c54010b00b0901860070312440e40d40c159628084554001030340f030180c40390b581e481044016482c4205a00501c41612843c0441c00140603400019a0501c41040b001001480c08082c07540f1441385a000010128940c117414200d5000c014503007410414500c0359001c21800b001c050310401d170340a103011220320080340f00580c002d21903e1100ea5041c40740c0b0540108002e801e8212203401c0103080000d00410300115042108494280e890160922070a080103546070302c0340340548a10106481c00000e026510f903410004c860a42c2c00c030900300e030409580c1c80f01c4920b607006140f05480065005060300c0c80c5c907440c001c0d00c400000400038803480d1200074941e00071a00350141d583c2180c00420456503a1000010050a58001700c0c04075010960f0741d5250303104040300f808007172184da003000d103070f50504001504110080d4082840280310315070a220100c0c41d40c8580000e0580c1042007402131814400a003401407034515000da0b00c161a000c00c204040080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 50172504 1250 50171254 50171279
    0x3010b09040f021206040f060506030109091b0905040203070e01060816030609140f0a1e090f060603050c1f0c110607020919050f011d13051e0609030301 67
    0x4441002180351210355510000700908806404800801c3c008140c00a54200e0b4425207400703214100c4e01044900804902081a50640e104160b404102400108110750f09904200c440da40f14003071441d0b03103601d4541031114440701604101c84451b950710130881182010401d58024146000c2070300301c0b039071503e003008088150043c0020700c0d2040000410b4012800380c0c000ca40076100c0180d090000200600340c0b0ba864500886143c010580420080780200c0b54600c1048060f04440c0d01c1c5004c7c2c1541280c0440181080110440f0442c09040c500c0d40450054032030304010718400c5010300044c10000007040b529540a0800d0340021900703000c03405030150844140c4030b80d5944001d11144902c0180300040701d0b4060100040d400081260130400a03240300c1082116803000900204481c1d25112071010f6403140900820703116117180e0f074032942d80988590929920a0800d043e400712940710317a03942030401d10708010510400b040c20910412120040c4803d540c0642071700b00850941d0b26120000184 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 50173754 1250 50172504 50172509
    0x504020f10020f0f0d080a020a1b0f2001030b010906020d0e0a09050705031801021c111603080907331403130b010501050304020108060f0105070b0406060807060c03050301 75
    0x80300c1032403801c0301c114024072031002c20703140301000d44524080c492110f9480c0c58003000341100040da00000039091085600c2131319001c0105969004041038511000d0454015a480c2a20054400500035001800154494030700d6240304069003403c02903040054169010140107a042c840242e000340503541e030024018919010a00e80900c0d1100c04001080c102c620381d030820301004d4100002c11850f187c11400950244c420303081101404c41460406030700700e0113050503440520081080c550314152268004e41882d1505208240c580041c058050342081058002240401c11440c2045180d240500c0b901e001800084d03600c140088201b4460341784500e00d810301e050111a0640c0d0524528031034100741551205038581c6594a084c0f80f10b0303036070095100704822103503c44194008107446d4410019607004d01d606071510201c40e1a110304003d8000d07000040f181c1041000d214501c049a00c50207024056406030343d000131441c0c1006000b03410484280c20030018020080d89100001e603010003200d04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 50175004 1250 50173754 50173759
    0x303080117061603020d0f0614011403010501080c0f0705010b040b04060b0d050705040f0f08011a010c02041113030303060306050903030c121b03010806070207080714010c020f06070b010609090504020f 88
    0x30701c4022036905400900581c107800c40d0f030520b03005c44001c100202360300c6103082c2c81c291401d001c40d140c0e1032070044624003507414886001d0344c002d000410165024076012034100000392502400c08480b00384000503608154001d6403541c0d11185d100d1024105441102a144425903041c0b100c0c90030900046654410825008078203640d80c00091005071140058030301828003402d1024030a03540c0e00003941120700502a540140d464107a2a02040c0100b14001501b040e06031075441c505080340d020030004181c0316240d146824810402800540a002e1160b0041d41c0301c0d80b0009015070440c2042c0048a100405921507a0300800c184400c80c0722180903036240c65078842016005680321100728511740c461300000e00210781d0100c00030442c04808181303644034822035400c695800399142916580c942d0180301c0d580580b0098041c10349654400c8114a42d900d0014001c1d03000094240045411035200000950303118011500502c00181e00001c070400030041c504084c07003a8189600041c0103826480503da1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 50176254 1250 50175004 50175031
    0x50a06060e0a05090406020403060504030f140301031a070311040801020711041404080d0209030d030209040c0e0a060c05150114011101060501050306061b1005100503150103080f07120306030308011706 88
    0x101084841d404807400b27168069424031845c2040c0c40c002c0c01104e45200040301280b980c12045a51050301d6091300c0c1200d0300480610b03486c61007400683c1010b600684181c0805450701c22148a4429a030000d1004020301c000041c1e40300d0042c02d081149a10640310035200b1810008080054001c80c00e400350481d0b00b103500c1542c0e4681d4407260000a1141803101078042c014207041da1926074060303020b03140c194401c4c2ca0600c400c880c10304084810090329000107500c0030040d4401d0043c5480385104148a41c803072022a4084243c00101d00291f0609034090200154024011403c80d41d01c50a1203a0b001020002444107500f0140007078503c1c00000c03c01401000046000d000e0092040c030f81e1407806600005a904110b90340c009000600411070311a079000e941c2450000c0d80d410000b902d40710000010040d61103590071507076180341c180d0000900d9801440e00344080008558440c0400c0c61010103a1000142a455813a000e80b81c0c4005a00040130320f01c01d0768105030b02800100340b0039032227544011b40c130 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 50177504 1250 50176254 50176261
    0x306010e01050603091c0207061106061e030c030a14010c140304030509060712030b0301110405030307081e0f0307030f0e10050601090f08031312020109060e0a0b030a050a06060e0a0509 81
    0x652911b052180c6000c405484109160085900855084107070341065036401450b000c0c00003980d076140d405445c2183c00079400d0503070141800c61190a481200401800e9034242c1c010ba90010b85001e9034000300f6920b4007003418038040310400900ca112084081030808648030032241220007410f020003440941848000100705e0840d0391f03940d0840303444540c49140100b4508180d00700030b000382890741c8000c0c003942c40d08295000020425054404541005008501d40341040e070315105a504100e8030b200320940249d2110354400d00007800342c2400020220039a45902d00300c680182910701040c0392918491420251100315032002c24012400300d00f0034004a2103031070740d1004803240302ca554800c0c020001402c6000c50840ad0100091850486144200300481d0f140e48159040d00e44e8200c0080c08030700061001c1009600942520405032402044400e000e60740b01c0e03004d001c81d03004440c540380340c42d901d008004a400036880b0b003402030410341c60555040d11044011404c6a061405110b02c01d01c00f21000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 50178754 1250 50177504 50177521
    0x30e0307090c020105090f03191d030a0f12030501030c0e09070924080304051809120d050403170702031b0109120504030506010b0702031207050f01090302070f050306010e01050603 79
    0xc90080000c4401040740c0c01050700000e0003081c0544200580380150382414800701800010758241540c1000100c420505400301950301040b14001a0003a0300d420014449540c1c0611072a25060b004030102100c04c4c010740381050960f600b00b034050003458900001070001c2001c6501c1c3e0070071364a40810088658a5010804d45402042d60100c031403542007050101044d001c43d0b141800311000d404d14682941d85a200090b140d0149006d190740000e106240c89002a42002840350841c10305015140501c010780b50f085003d500094940b814141c4820070711080650243c00d075079056282103100c40380c41c01c02480c000e490f4810b2861030000501d10380351400102d5820f60203d451a80c2c4074074840c5a5800940010703200382c10611042d181c030700529000180144140c4221200d09078018064111000c02c2c00c0042e5940d04001d4042d540c0740325440885488080c24801c162000e03010750001c144d0b951034032005680c2d4602e5508410f0080d0000001000402c2c58916980d040d500c080b100b1903101c0d50384998 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 50179860 1106 50178754 50178763
    0x100513090e0a0807020a09050103030917030705150a2711090c0715180c03060b01021605040e0a1b051c2103020913020306100c0f030e03 60
    0x80b5180000d03a0400100b00d10b0340b000304482e41d01038407081c2a40883d14242c00c1100030070490b58090090041110340c0c0d0200c044880000d600d02000d680d512616404504440ca07254041240070580c0b00060b50000c80c1111000640309080c0019030f004000020603910090b1500342c1100111515070130030f201c60520138034001030800e04c1c0c01e101d07594450040f5000d2103001c043c647da41500042c121200742807404054061072242800d01e046092440446070b6542c0658199030090510b41c401144129249003102d508803000a52101c603e1603190805c09100801004070040400e03001083d00034401c004180c9a043c1e42c0303100254003414a0348240385a00c1c0001e0600c0381c080c84003008150302c1140300740410402e0303e0050f051003407000c04150075501c058000311060f42c020082044a00701090308691114403850410158241d546520108800c1038002504001c1c4505025416440810 = true := by decide +kernel

theorem cover : BRFrame.Cov 50000004 50179860 := by
  have h0 := BRFrame.cov_init 50000004
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50000004 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 50000004 ≤ n) (h2 : n < 50179860) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
