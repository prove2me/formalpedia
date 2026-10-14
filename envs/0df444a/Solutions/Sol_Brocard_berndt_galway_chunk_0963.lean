-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0963
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:31:51.009782+00:00
-- url     : https://prove2.me/submissions/132b5272-5ba1-4e88-8800-c8f49d938c2e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 173021582 ≤ n < 173201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 173022832 1250 173021582 173021591
    0x16050d060f0c0c110618060306010509180609060d020306041101030608010c03090506071107060f03020904050702251805040c030501051603050a050c07030302070303090b0712110a020309060c010f 86
    0xd8001000c010095400b039580c1c4c4400b42e9010070301d10b840401c54002c5801e4480c400c554482080502c00103802c01000941400b00502c03c001d11500d4001e0710780509500d031310703c0320720074504007040142007800984800d0045c24120500350058070000303041c0c0c1d04150030200400314802202d0040340072b4a02500014655401d143c400d06440f6055080b683d00c061044058426694a201d4120b94004218000300d2240d40700d8181007141c50f000f0b8401e11b400c00c401e403034054070700f446030000b2806840c015108200181c2c0711100181c2212001d00d80800d051401c0c00031303020460b142230b800d0343c2c049214400c40038509548101007070400100e410010011640a802408103150007122446100768903044200480e09120014201d0400b81c8541845a540d080600f0b080c0006034508800a4010120071402e1542d500d41c0000803400f02e0780d802c0e12505003695404001c03a60f030f407100c005450340805120341000d8103011080840307402009907411464180c421a80f50030840e8407060240804020303440710035160 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 173024082 1250 173022832 173022851
    0x8121005060d0204080f0d0c021c080f21162a060b1513030803070e090f07031d07051c1a0618040b061309020414150316050d060f 57
    0x683c0290048a00303007002d851000c00202c4500b9214040210050001003c0180903c0180f030f1036001ca90401101d8040c801d6201510b5603408003d40c801c0d40c0c0310b10840350100d0140d40d084505809018a044114030b018114100080b120380c585100d101c003581400182000030701c1c90b04102640c3c4190341000ea008201d5840d82d801c03c80c0007812810340080c05045c00c07400741c0031402540300c200c1f4240355203094080032040c07941d2126000da8001030700003000c008034800d034000160b82c2c0c2c0310002d000340d045041d5025107092815009d800c0318400003030b10180190b0503040303141006020604000321007066400318207095900d0310082d4241001500204000c01c41100342c14070034004520310744264010b442081c0110350f125240905079004880c01080300c00c4000c005041c506042038200b00c81e420303044011410004aa0004042c0d075081c50070707260b4072018402000611029400110700320142078000d4560059858280c000c01c1105001b95800354030b402c0d160004001d459401032120180c40e01d02048500721 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 173025332 1250 173024082 173024107
    0x70f140a0e090f01030c0b0c1b060702100305091612080c0f1515012a022d040f0522020109120f0507320607050718050906040812100506 60
    0x203085c001594800140900071405940d2002202c000c0c81000d0000c120400745018242070b84102222101e8022409000803001a2220444a0114032441d1804600c0e880c258203d80c0c6000041c0728100009841031004001079190408101c0400303820020b038541d100301d400905850101c441d04051441d114402d40200083e001c102c410740220640010700080c00c81c24801112168207442c240c0101852903118083c51200c083c1e4507481c040d01c041c100c80d5100d40994140844d055200c842c4806c0611004a050340b9450240300b069018500d524040089084c8102d88400500ca2070400a00d80d0540071001d00941e0301640f1003900505200114071300584030f51406650207103145a04a443d03200e100d00115908188085410a1014500c0e001c20b0004940444024140702e040080383c011104200410104030140140070140c50740c071000030002c1015240400803580000c103103515a401c88800e000006c2c0290b4115500301a002066100c152600700d0111041c00e810362120f580580e0000b0340c1d1040e401c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 173026582 1250 173025332 173025361
    0xd06050a0207020904051b03030a0806040504150213080601050312120414011107032606010c0c030503030a0917040b0406210e060601020106080f0c06070c09020408010f05070f140a0e09 81
    0x15100c40c1c05021f1812205240d07603070080e1920480806c3e46140000c00030f0500c0d6024952050055103150b07520300482c00000200d034402c0c030803101f0291174810144400902042801d00500e03003070700181154100311098400038040d22114070110a80d49004c103052120405505481d030325000020070100390500002003295200380d80031000f04201035500f070800d040c10754111007000c1c0318151982240d030b900c50045840c1d000c0b110040302c0d00440410080046002040035601c903440d100d0700000d84c190b4609102c2c401515904440c0007000d0100418410b114290080d0340494110341040100244090004c01d150400109020030040c98104548440320000074010700030320307080c5c0003040826114100340c0c3e2140c4001c003045510740e0220b0022003803400c00b07100401d206d9000350f800032100360b12601400266806a80400002e82d1600508200c0c05003910035603410050b14107080400961403000071389100c00b191440803d100340440e55042003800b43d611084103600081640d2928a401d811800122 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 173027832 1250 173026582 173026603
    0xd02010b130203040b010306050603011404112404360902010e040b0d150207020a0608090106060e010c060e01020d111201060c03020a110a030c0602030304060b040501050d06050a020702090405 84
    0x200c00d07048070840e00394050310840b4015604141540c425a09548541c0c4c0a0300000d03011a416650f180c03078049000000c01c913441d00680c4100440c1c410080002d08219800f41d100110001c8a00d4038520044d1618415040790100c501c940c49010401c080910b04d80001402003518140c04d03903400b45007504404503544564880c41c0700340c9a20304801d5007607051104a40341c02c10308a4001c1c9101c0301203001700b020040c40103619903c141016107060104d50104640e80465440348000c50051424400400001c0c01100058119490044902401a00000c0600020880140501d5070300d105482d1003420a40403074070100000c01050010f00425901840715502c07012001021201180002c03e00754407903580300e61480d0f05a4010050146140c80d440c980440c0d002c0c680e94040711003440040010100000080200b910303070041c688074a060304080044e40c400070350286c0308604c2c0900501040d41c4e50445007940c2504120001125682d0004110007882441d001a5001e4030660800081200000b80078405 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 173029082 1250 173027832 173027839
    0x3030403020d03050d06081603080d02041205150a020a09050603070c060612051005070c1502120f09010b01020705100f030b0306010b1b010915020a02031e042105060a0506060c0d02010b 81
    0x72550344c41d0a41c1e00c0f40e8568008654200e0126020404100c01c08040c0030940c000e2f650051400369074103008182c144006400302d9458000340880c90001e441c2040641d0300881c0d0031340a51074201c10142c02403085029004e500c1c8540008000300700c3e10b078400c0c100341086540c00041000240e44401d58944080ea0100044520740701b031012070081c034506801840d0040ca40750721040000d8100760360714001d51040d41581601c65a0030300603030000210120001b80501c00790400c0e40381e01d05200c05940c2c250f55070040800d0540d4000c0c070040000340c4400001303030350b002c0035442e00503080032140da03084014044036020650305100301d100203d854142500201141c000c2c00d40000110105610b00c203003610602c0d170303000d000703110310039003c5140d0007294009001c3e15040780b060f02d1a0150000180074240011161044401c0c80401d09104018401a100000303007e201f0b240002903400780d0718580d0f680304c0107069800e0a07841d10b002c280a600c851050303d110a0280e82910303090207107200000e0081180c400344910 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 173030332 1250 173029082 173029091
    0x1050f091212010b07151a04060905090607110f011103060427030509040908030f01140105161104110f030a0f0b030c040c020309040213090e0309030a0f0203030403020d03050d 77
    0x820030040402c890703071141e0540e03074081240e103440701e03c900a4000d21016100c0140301c41100035290b0341c900c00d00c9800d120324413082d000442ca01041c80101d491a03041000114034000901500500020781c117988403443e4984044091a052001810810161001c032040d6080507000300340c8525090246100b8803050724100312003600308600c204085411001800305500e030460320000700e4800d0000740680c44001c0c0021964503210b90b03412201c0c4d0300441d501b010382c201500040c042a211000c40300403003007003441c3c05801e22259016410302403003542002001c804000d55101c0305500c85800016644a14100c2641c5940341000c0c6443c095001701c844507102d41c600b500724003140801e80304460040f607025006100b014070402c1030000620b80c240301d2106510007400701301030a45d80c0340001d003c0605d80b4007045522500e020051010784468141064280c0c00c03d010444d0107484c0042c0010b640d03a080ba00c07200d8118414008030f82180300302e4001a4100c01c54464003001d140c0c11400515100d141a0070420 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 173031582 1250 173030332 173030353
    0x30b060c03030117070e040822060f02010c1809020903150106050d0b0a030b0610171008070509130b0703090b10082b052512080f0c040b0d090501050f09 67
    0x103403183c1c5e040c081c0c51b030290018408900424000c1c0b0140c1040741811002c080d402c5c0d4030f10b460b03001210440d07112400280350b044201244650a009a100c40000303030810510b5070300d07160780c0e0710042d80c200d0140c040301960110741c000c002d940070400740d41c460848518a91031941c4a56000b0007562081c50030082c03050901f07030340302c00c01e003400d18800c0d0440f0780104460381284c4074035003000101c0c001a0440700c10030190f0000d9262215007100e0003809403044503410019a80f42055142c10050346510441c03052483c1010001041c16020080b184250700009610495840721400d400408036010041c1c84494a401008600d04c050088031003624081001c80f83c003013071641051130084e40c2c101c16205908524100d400c02d9540600045c225002c12540020704500030015100104501d42100303643d13078465500300c008407580040480fa006441c00c1c0c0c941c2524a8000b080040f0b5102c2c030302c0f54800c940000655005230725000d90245040c075901000900041c01e003940c2d2000e0f10035064a801c81a07014018024 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 173032832 1250 173031582 173031629
    0x905070305100b19051605010509070609060201020c0307060902121501030204051612270609030e0d03090605030705090603160207060c031b02030309060f04082e0b01030b060c030301 80
    0x220203000803404d103600c6031004c0740c10480310740c0c211440c840a810390890704100010b000780034983c0b260080c00e008000c00e518001c0002c1040b04d00c1d41c0580c00b076910422842d82d221a001c0201c41e5681d41009012510b032a4600c0442d43d14182c0b07040300c45450094829804040d015155110b040701c0c02242d091080c2e444e042d0355440a001d040c0000300100300b0400e0400703e01d1825402c40b40c1805e840303018a5401c0900c8690306402c070080c2da80c1c111007031541e40d103a035010550809070300418558107403045d4803449031a5401420700701a5009081c00d100d0040001505c0354400c00803208000806080c0544a04101801c400016481000d01001d40591328002c0f0b4110700ca1924003001d141c0507503883d25500784201c0160010000c160040e0707094002041015402d0f02d52000502c104c0344c2c5004120f550703510300b2684500300340200c02507024140110344041a07002e201d181b100200302400c400055220700100040e00282208055907400002c045007200c0b1103003010020f54100c038204175141d074104040d107168 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 173034082 1250 173032832 173032837
    0x4030b19140f040201080411030307050a02190b0d111e0c0d0201051005060313060212070305090c010f0f020106030c090c030609020306030703030521011205101515090905070305100b 80
    0xb005030302c00225001401541c4a4030369560007900a9044600d030310102404603095500420042d105070b48039800301402c5040c01d2030b842c0c4801e05c42da61050141c6040021144040c424030500700d038075980700c008481e0700d1020a011510505007110030040c0800644800300d0742500300c01c10030a600d0140396107440b0603d0045c01030b58840c04040c61300640c050705040400000b0f0300068203401010459500704000940c103031004000e40901510000000e1406490060a4410003040804281c1210700c0025043c0d0700a294880044410f0070400c0540e980403204900604c016070010781040f054500020724210242d0181c06890300300c0d5000d02915440740c41d490103900c025155150140d22000e000c001081c443c4c4064211304441455032042c3c4c4c1c04284401600510a0308098134901420b603904007041303801c1000080480d50764205001e64202d10b445284410000d01c2498100107018441c040402d1003a0714000c06444100020002800c04d132000400610040b1748804062680b0b06021a4031100c0006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 173035332 1250 173034082 173034091
    0x6100e0a05100b0f0702100c0c1508070807180303080a0c0305010b04050f060f0d141602070905060102190605180f030306130b1c060506010f020705120304030b1914 72
    0xc91a00391800f8050a416840582030b00c180b000300380b04410040c0d0301c8200181e032412842d03660003015449401c21807000221940041001d0400c0200b00c0d07159a044000342d9880030b032a00341040144e039068426299030300323240503008400c85848004804c06800680d84d0b40111140350041166040c40b5405030101c1d03200b030182d01e5001c6403d101c1045640b4220f0400e1005000283c021410100c0d4080c90040540080d01015081520f40d00351416605500d03084590255100841084804014001a442c0c000310302070600815240e10004c0c90070b034020400d140740300b80c030100300c1d820715003041c14808020403007a101c400d15603d0402c1e00340060030001615900100c004000b03145961120303420403031000c80009200a54035210345102c0e00c00c1c0c0d0359400d620b100840301c4903410800c0c40945480002c6070300041c038150500071034040c400c0704a0380c00203412040d0303841035540c0a02180d10741d07810761841c0038a900080c10800000304209401c10b6800780a480d080d04c144080c05241c00d107042090b608d060448 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 173036582 1250 173035332 173035351
    0x4140a0e1605010824060706140606070b0a09051f0f051605190e0d03020105040210050c1005060301022a0f010c35010803090f030303010302030c130e06100e0a05 71
    0x104003811005044ca01d00400041c00f85c81c2c101c03182c840442c41ca40c10600054030203955820f50a8140c4d01d40705811680000111122481c0a081d540c4003011070f0f00290046901d250388980c0002042002c000014144088902c09441e11486420090203070005045504066041502150303244036400542d0481003000e4030b4030340c103140e844910032503070780800039103c0100301e1800803d02e0306850354016411502c0c001c1d80045402d10781401401068004078002d035081140820440c2d0f094680420007a007003441411020403541c076250b00190185c0075821442c0a44141d005142585000650405801c0b0403542d00742c4001002c0c40f41c04c1401c9a890b12401c0f00410601400750040c406485110544032030000300b0307002c000c180c040e404654183d0076049101c0c1070b400015102c0052030300180502d03951004400030351842d0304540c007280d12040d00740f100d6030040d240003629404001075504030b250360106503001c60f645032500780f144080c11485440b40c0203012222601107803040029004061240d100340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 173037832 1250 173036582 173036597
    0xe0105010806090702010603080403151406060f070303060512030a080906191812050309010b03030c120f04030605160815090705090112061203030b010206090a0303020904140a0e160501 81
    0x107209114003c08018190001c655841e600400050065000391029600036440c081c0d0300000407944204494014000d0101030b120b5004200e0a5500e1034120b564046454000c0d5482d03d1403032030140c01810843e0006a40700042e0100002e401c0c00020151034400c0700d564413175403144c070340e101c4694840310240c500e89280040f840c047d12407140d00350041d941610b141e081003c00341c00f083d1a000c020074400880840020000418802c0d00e40d004d0062004c40382c8210060f5141001007040c203079176020103101c0300d9003005c00403803d180045194000e0f5802540c00440c10b0100d40740000c0034203041c0b504a0421408a0203d0000c03071800144900041d4007044080d1090f005034461100075910f42d00440740c814100501513015000340191805550000c0030030130300004102070585400340a031115a109181158030030010800c10b810001001d850384d6806040050360f40d902e000203c0d014100031034000d084160315000784040d614596003c0040e642692040e10850108000810503255203486840d0019642 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 173039082 1250 173037832 173037841
    0xf0e0307031812020913020409060c091e140102071502060609010902040b070b09030918061203030708070309020303070204020c0a03110d090b031003051501030c08070e0106050a020c04020d0e01060e01050108 91
    0x7654070160000c131b4000b08907074018130650000c0e00307903410f440c0b086880c0c41e2100d000000303240e017003041a805003541101240c200ca64108400c1480003072840707010a1005c031066460f0f2641d000f488080090810a4028a0f0740600c0c0c82c0701a40e038a2059414034003c60700600002024480340c404d80d4261818600001d20704403968a85484400025044045070700003000006041d6803262a0200915088100c80c080303441c03d40b0801011941c901070701d41040c3c00410030030480c56404266140e000c44c09040c0003400c25150b00219155001d260b400035040307480058680d0015000041000380144644d940d0094122070030f00854982c8400c181c000045944041d0034003244281c1805985d0051600c414029a2941ca440b00703860f100800c0c001d400702002c800018001d00c04486942d0700074000b207170f006142942c0360640007224184140b10b4035041100109074170341418401e110a1131070400050095444964294120000346140740000005d90700c1c0c0200007514a02b50764009040b928161101980c6584 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 173040332 1250 173039082 173039089
    0xc1c050f090f0f09091605180708180a1a0601020c0f13020c0a060204060809010213061202070516050109050f0303030606070c03051c09090e0c01050c010f0e030703181202 75
    0x514040d10750141440c00c0b289a103031105604c052156a2039002403200c50744000d40c54052004580055020b044102c1d400901075040191403034000b251807600c000103a030340841090150f0688951a01d090003000081ea080c0140411507120403c1000c6400b00580c6030a001a41e071103403c1d02d41160824100701d1a50824a0400420300c503002c60120098902074032201041c0c103002d03601c1c10480d401a404203051016645c0b0080b015807007401d98008602e000125900040c175041c2902c034040c2004152a084038103100b0940603101219448422240c008025201c11030900626008d000d00048100e10001402d00c2c2541d0000c0705400080c0165240d92102400d010996000b400c003501d03428100540000098010042c04004d0381c3d507280615091190300000411981c034030b900c40c0d40d202d1306000206030100070209640300a070601b403c2041e075400e40e8641482c050484c030310004190b140780007008002048003000404802d4030a549814036428002c0f03a01c500d4040354000d091071401081c000034010304 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 173041582 1250 173040332 173040349
    0x609040515090111130f050a03050a0f031718060702071a1e0c0d0305011502061519030807020a06081902130b040617090102040503030f090a0305030c1c050f09 70
    0x2c0c00e140c00403d41c00c407a8580034015a00910f150001041c0616080051580755000c02c0c020301806c44035604160300d161205c5d0f5079054034040203032030301400c80310440806004010a0f80c000450603c14841ca00c1d011441c40f0f999840e00307001c242a40615400600c1e4544080f4241007520040040b0003101801c0703070901c1c141070300022108149040031410b92004201220041d00c8802034100003030800d030425850042c02d598044e4001d051301101110403000e07040d004100c0c1399100c1aa0080318090000b1100014003030104803d080c901c213042a0030210520410100030040d0900079140c585626030340382011540307001d0840e80c2c0340c640c0c0c060040c100d129a10355001065041d11020b51044142d849071101d03103169025a2215003c0780b01d0b581c54203520041c240d032041d40215003400071814645070002080d100e114803a400c02d100240000d0320400d80e91810710810155401c03c1c216919102c043c504c2d9075031402d464600051300c0c5015200030040e207206008032503880100642d81c905046114042c0180103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 173042832 1250 173041582 173041591
    0xd06150603020f070308100801090506090106060e0a050108132001030509070e010e09010608010c050c01140408031315110307200a0201030504051504030914041401050603100312090e0609040515 85
    0x4031f00d10800184807209000303022505014502425842c14820555421110903134030520503c00000c0003807200f1780d654400350b4222042030030903c03030729962014955172660201200411482c800c4003039031210317080001d6141c1800003c1e2401c218540392000c0903030b5075403181e110744c01140e00b51800600454040b280c0b0355030030500100020991035156103a08d400c0d0b6400454500000301e0214a5580b5480c0034003d20385203d5008110052070304094803668054813004015501d141022002641048003041100003084048082004148040e101d808501e51054900000142d104001760051201e4408064001c151180c001c105400301680150003800c00108140d4290003946c82034060300390017440322403280348207641c0c0800e81420858424503202e50000c0060041e854424000d15510020315958191801158895126515404130741742c81a8140c1004103404401da8541103244d400058040546200d00d07256440c9039118028000708100445024082d030740152801c8104080002501e0f0f0007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 173044082 1250 173042832 173042851
    0x408030a020f0c010905061504021305011103070203030c030a031b05030a050a140f01060f020c09011206060b040609080d0512040303151508040b060904020114180d06150603020f070308 81
    0x141002e04043c1c2d42150520030342a62a41c101d0800c004c252103000c1d1004e001004100d400714180301440f00e50004a5500340a0a81400001c25507950608030400a81c1c0c440740d070041c00c0f01da1303c1c0c280b0320102e9100c0d0071440840c000300e810b01c804003504101c201d550701040301c1550340c0c00b801c50741c44040480c00b41402074682c0d0754a45d5940045226032041c401d50521544601850404a5241c580010000f40c40411240e08541011000c80090f50f5000100350441b04800160894442e00d41054001414280d105803049003002400140c4143c0003181c0c0001c0300c03072803415901c55261204040d1114402c440c5a01c03021001c0c070000800083c02540701c180003017146801004d0094682c1d040c0001c600d042c9019001003210034082000700008054456030144056a035803000d400d10743d0010705000025441c0d0100648049003088000000740007800560400a141004200c03043c01d208004108000554140800c0c030000810b00a000b4021110100c1580725090300d000c1003034a0841e036402000d80304011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 173045332 1250 173044082 173044087
    0x4081c0c030e0105070b01030f0201080f13031413121a060904140c0303030106021509010b0619110d03020901080708060915010e1203040807060e06030a020a020a051f140408030a020f 80
    0x1b0807402040e09000e14403481401c20905620300014245c801c0061030441c081924104005031035400f403c89007030581e0715090900c2d8407084400c1c266120b0090025110062401c0b000025000d1142102c10520601442701d520300740640103040c9082040c100ca507281c2043c0d0031000b1600080303050008850340041c1400350307841d010030080003e045601c20382c802030043c0d07c002c41c000524120700c074049801120a100812941c42244046071050280e0050011940503030340a02000c1030140d1003581c0461070340010b48548502000000c0c0c025003190840314002a501c1001030040c90140700801d018800c018004a13481d07884503180403007076941103079071410041c5011694210383c8400751312600381d00000313018585441c10b116942c0d2070100d00340c1c880b10404c4824013000c0c0d280c2d160760301240c1d0055103101015944031003481041c1c0c940551030b440102148036501c0014080c404001c0010840708006006000040c4001d0701a80e5601d0203603005001504100302003001c5511a40c001d00d240c00f10808900d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 173046582 1250 173045332 173045347
    0x7020306040b061504080a03080702070f030515070809070b160203070b09040b100c0204050a06180903080a0e070902090d0b13051005150d0c0f030804081c0c030e0105 73
    0x2030400c1400d540071140b9404600c1805254038280c032995204507892054a030500d8500f19070a40d461940c0d4038003030244000e07003002c640018800d00404020304151540c0c0030040d552032408503070700e5180d2266464000414004600410312590070075000b140014000c040890419080d50782e103511001c41c0c0310301c01c0c04540610f00181c5040c000c0030300034050041016180d0400d03800b480152001561803d1064807645016050560400f03222406260140d50008050799034183e100300414458000002c90780c01d4003c03100c10b5080c180c00c03212102d44a076542c2c41060301c4601c0200141c880a41c41154160440d050912814178540c1c0038003000200100408a0700b0001d80b11604016401d441d210030109007c078060341840300400441c0120440e10908000d145025010282d2490360512040d10960b921f000c4001401038030411030001e0300303a424440c18415681e140c00402544030303104040360f40c003c924070515600c0712120140d00d07818090301d5820700344040380d904a54050b62140c2142c1800824003140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 173047832 1250 173046582 173046589
    0x20f0d0c021012240f05060405030d0809120c0105040c0801060605040b130e070216050604050603010306090302010e0115080c030601030807141c030c2304140d050d1707020102130605030a020702 85
    0x5070410382c5800d2183c2600d0410f40317110707481e00e40d64008500a4504000800013920006a41c00c0c0548040c6030103003490321550007550a10305101c103220b460642c0880c002e0309021041d0b0107a400b130303881420b081c071500c0d942d4075040342a6040ba10a030f0010400900c002c00c000080d91000740b842441d90303d6100411794031043c1d806078480c4103440302ea0050b80100c400d0340c002c020f00030058015003c00c0300c01c14101440d00f0000b910912050200502032500d0b40c3d1410704050003500555074800040009016800c442600701c0c0202d502880796021501c240c0c010900b85060114a40307058a40203401e0700d244c114544c45880e11401e6000605010f4800c8088444001e80011b000c8442c24041d80d0b00405d1080d01403c1c020048240e11400446035200c62160385540ea103041c0481e0100c480402074042007040c3d800000340303054801d03080946540119440003500c0d9a2201c0440d00d9211170381c060503940d44908500b00d0803401624410494a0202d103814442c1600402c095a0b01441511000d490101030340e010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 173049082 1250 173047832 173047871
    0xc1009030506010f050307090b0103020d0609150e06090c0703141606050a0b2119060506150c030306010e0a120b18011a1e10020f0d0c021012 62
    0x1040005654560148200710090203624010071407203070882032160500e00003d0f180c000c0c6104d09a101581c8030b6a10806034041c1d0180c1e00440e1710b8100c2080310340d90712146400902181800c120100c00140ca010461500c0b00300550300416010b083c68071036503500071404001c0e52000006034144a00c01030b2010791180c5502c02422035100150016040d6206440c05030103941c000f526078940300e0300b003521003021074448162140761039a080e002e003113036000038050b03550178015203945c0055649401c0e0362060138003241e0b0f044035015601c140c0e02542140b09000e8449198050411030600710341080001c90100d44c03140450140301c190042103128516038030481c501d200070b00058201e0310495202c1c01c1100207030000d0a03208002c20210003c2c8800743c00c00c0c82010203081204000c501c01c1c00c40d030094608040c1c9a0b030703a80c1503020018200d6400c4412600000e5903540c0d82080e10f5145103e0b207030131220094030814045103150760142110074441c00408003a15102c940c0402515280e40d00c084001101c446e0350305 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 173050332 1250 173049082 173049109
    0x60f1104080109030314061f0e0a032003010506060403120207150f020601050a15110a0f1527020607142401080115060c05030915031509060a170c 64
    0x79240c84640b50240c10354030040341c0081044003810410070f05840e4501c030103810307000c5239003800780e4448000400d036269082c40491903004969914040208104584020352801075001c04e44c41410583c801c050907908201c91558005400340020400100350400d0310440c04043c0c019240046d4490f0076032400b880d15200e0440015603001102480c0540601c1041e01400b02644d11350030003810081e0384100d038101d98000303408225200b40c0492044a040c81600f0030301d5440809601010900c0c20040b6003480c0603080d40801030324280641c0c0e0302030b00d2011900516140d214001170220615000c01501d500700390b105941404881c501c040d10201c1c1401001003035400e8a030103481314030400c00f0705038000c40142c1003000c186e07240c40b01280ea80d0901c00b900100b11215480c011032001001e10301a821405075030056904010b4055903014100c401c070b03000d903108940c00d045422000c0341210421402c424159911900102551428080c002122420340220500d01049070752551000c0d001c510890310300301 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 173051582 1250 173050332 173050349
    0x2f0c010f1d01050405190501060f080303010e0f010302100309020103090b090102030a06060305040f110a03060203010e07080919021c050f0102090f0136090c0201091403040f03060f1104 81
    0x44528244042148072000444400c40080250740741c10f50740c8a9403288000803004061042d200a1030401c41c007500302e0006040306d012600325040e6070348100c0d5603e030028009c0642005842c1c0c00243e9941000f00c61324103e0703400400400c0e1003c006503054004201045d004e170704040e1541280e40c040b904407a03100b4052210540010382d603150441c040812628260400001c0500740700907c008201c01450341c40546401401c2c6101994510000801c0011651304c010645800400006a807500400701e2074407420722516600d8190761116401612842c1100312402a040704078094000740c02c0c110914102d81c54104030b2400a8495900c610b4901940312801440c145c2d000606030000382002c03003440d0040c1c4020308080c1007441280001c80c055060b2002c11038042c079018601e00b40084400c1c1c00500041800010410140007071001c000e0207820001d10603204c0c4440f401214034403100000c1203404542c5440c101d10b164504543e02d160150070401d074100c1c9042d03103568001c5003502072200241300425050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 173052832 1250 173051582 173051591
    0x309050102010c02030a1403100e040c1a040303020d030b0109090212060307061701060503070c0b01090911060f0409050c070506010b1e0304030806060306030a050d11060a2f0c010f 79
    0x4000a094a43c0390780031400710741050080d4811a904240d2226100303620741c01c415101c1e036031200140d07440c88907a84640041c5410740c0a0109110300e00c0c04000c242c82403007107034443c0441c1c45420141c00c0e204038840140142d201340700c04402c20344a60b00c14050f10300d0525050048903541c85141060741c20156043c16040c41020502c411854100070f401e00801d600c0c20114090702a079201c4806000c014401e00041c003c00000040d140e41c0b1407596070711141c1e4042c02e40c0c8042d503110324041000300f1a491044400601484186001d841d000040c1c410684810203103070302e81801c00744010301502d0041c203007a100c014140038440000f0f0003801501e002e040203004654592000c0707480d81112104043d41032002c3d200c1003040c80082a4000421a803064050f2240b942e40d03114080030a241940294014240c0c0c010b0141001d889a03001c80c2d0447c1401e558012100c40d9110015501d00300c0e0349015204c20034000700c0551035460880a02a00954822035030389501b0009801207803400e450400316031402c819a103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 173054082 1250 173052832 173052839
    0xc01150611160b0f0a0c0206070b07030b0409050c0d0305040f140a06050406140a0509030706030f1104080a030c0201121103240904080c0307020d0b040303060e040503031b160309 78
    0x70070103840d10000d010365402e801464500780b0407079882a00c0700711200741c800040e03404180d030107800c1040100e81d0190515a46074001d0503c03003044441a41d0450000f400c048042c12507203041d00400c000c0540100c00381c005440890108817240a0100d0214240700b0207000000e920b005c6102c608004101c030300e1000b24203480e0002044081c2c0b16941102c03003806001e010030311105034030905820174580e007a00c4141d56000544000c1d1468042e4001003a03151003895030100e083c0b03604d50025151100058828021441c03604000001c2e4025030203880141d510400c2c0200100c0d209009030b40d4500d0040c100301d16001c0400c401d50080d20440300350400412030000034400c0c01c100781008000c0c101c0a40780e0102d04446420700081c803940004d1f101520b861008100444c0c8a2024001c54440642c02420154104051f03d000e0381014000ca8050700402c0c503106000908021000056220b9588130015519550320900307500d0f030080d0002c00c0402c803020b051007148410002c070046030481c2400394036001b40719881c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 173055332 1250 173054082 173054117
    0xf010e0105090f1c031b0201060801060603060b160609140703021009081507050c0102070f0213050c040303260f2502030414031005040f0c05010c0b07050c011506 71
    0xd0250a003032095118861540006a000c201c204c668100c0600620706220010340803809403c5299442e0880c03100c6120703e14074030350150310401c211160701c0000d201e040c1c2c0d121801c2e411100c0c24403d1600025040118080c580c002d40e28a02203180b18400005408007141c40f0049400a400010032050f40020720501c19441d0194078010607284a2404216460600442a4564050f0344401500281c04000b01d0020b6024105492899010b04000c6444061a08005607045e1011070241d0240400031f00c811070b00300250180d60300ca0035540e0780e43e614080c515681201d04031455004d6408104104120681840f1200c1c1710701d000d60b21440d0481c80d41d0402c42c0455a141c40d06050810b820180f101c8240380441d0048261011207604800d02942002244042801c001d01a071000c0c141c5450f1100700810852000c40c3c6d2800700e40982c8040110580300c4005403034180210704003074100ca80c1c40e00004e400610903001042032004080021462003121841185c91065540110003c80c2e00700a01038107400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 173056582 1250 173055332 173055341
    0x609090c1e0c120f0702010c05070302090a06091506080c071104050a051602150601050d060f06020601031a010b090603040203010e0106140301140411011412010b1207050a20010902030f010e01 84
    0x3c80041160340381c0545881400818400c83c071000303040c070044000200a2000030b204d05030003150090314848061500c81ca0712402030540b401440181490900c000200040918000054660790b488130f1240b9241c80f1100740a9401031242120040451265503078191194016940240d6101d036000c40e031410f1000c0c5220300769201e01101811035100d041b1480c50f4110900c400c035002182801d1032a5620b03c1c664105c409080282c0110a0451998a00241070390740010800d040305c1c061300080810800d082d9a01d44641000e1043c1c1518000a00031540640f41c400011600140300800000d2100c8020790054203403400c40c0c2c810415404403030301780a42e80c2400e014095200b1111804031403c0d00c1c065503014035400c0d08044941c1080201205818030491940c111750311100b10303a00743d42240d83c0d10b0300403541550000301d083d004e0f02c0481003c40c150500410030f031400294103851b01081100380006902c4c085003400702e070052a41d01c4000c0f030005038a05200d0406525441000851043c4c0d4919401d801d48 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 173057832 1250 173056582 173056603
    0x303060605120403031e02031f0506031e0c040302310902031b030a0203060115021b100e03030412061508060108060432010203040c08010b0609090c1e0c 67
    0x2404201c0803405070050300b1940c0d07001e60305040c000740201c0d02c901c071520401a0a465504d400380300000b400038903c540750365004080c4030107030074458180c2c4410910203a408151600c0d120629120101c48100050350f21455000300b490160074102075a0b500001c6902803220125080c81401e0107c1c0c0c40c403190b20807044004003090203410b1228400c40e601190340e504840d0004030041d0384034052602d680d50300740402c80074150000d084400d1542c4400a415042400d10300c410050b102c1c15206404242032130080e1401c0400042840ca0501d030fa448050b110b00302e441d82d800740c1c1400300300000300712503829500145016001c6c4031b000406c0c000c114151800c0c1d6026030450105c0d80e104600402281d100014440c0c3d000d940051036481c48201c02140d910401c00c0e010b0321500c01d0340888820110000151301442c412801a01d045007400e5039034903507900321140c500079070750406030800c0403072501e0070100e040d160070030303006654070f4940100c40d500e103031101c0c1c0c429018a0038050009880807401c030080041d100c81d07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 173059082 1250 173057832 173057837
    0x2a03070f030605030a1b09060605031503070609050d02040e01020c07090b031b210613050114040203060a02070302160b070b0c040e01030f1a160207060905090a0b0a0305010e01020703030606 83
    0x2d08210004e6500c0d55610310041940400300c400803483c950020701c0000901c6503d10501c29143c0780e180180980d00708807004105440c0100071080d00b840c1c0024600201c40e01621000041820300d030500ca507880080d10183d03042601d0305003061140d01c0900c010542000c540020f1b11885082550361000e0780d0f1300303510a5100794056404410303003103a118508a180b140841e101c0301842a00c00c0e21000c501006208030055025940420140307880c403951180303200d8840d030000c0140c2c0a0204400000e0401580d000e5059800100025087c0c0b445500070a4518040e00498040d929a1042c07050500c80c190850b00e852200890782030100074880c541c0300d40082003244403900305410300550810030041480007400c1d12400386400c00c107000c8001d0582d11112a010b40340145443e2000c0e55800a20f141c0004500500c100d000014402340b00d20b030901c0660700d0003425507075951610281c4101a18000f010030764003c42080c000000a00240302d0075000742ca09100251302e4240f40e0401400721202e41e4054002d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 173060332 1250 173059082 173059091
    0xf01170304030b010b070c09060305010b04141605030606090d080a020f0708190f08071b090207030e10030e0604050d08010501030b0d060e1f021c02212a03070f03 71
    0xf400c05003019042d0b400e5050000e444032103a040c100100d200581c0a140c00d240380680200601c1419040b006000c04140d4080c845040380b0070b203a0409441c110703a03e1440044004209500600c41c02c000c42d001f0704002c101034200b002290010700c0003610a14100d5040d140000c0c02c10445806000d50111201022b025158045c5003400243c0c4480e610807030344c41c1c40211075840100b001100b00b05d110340780390400c07012a21400720b0301d42044040784010440e05502840700300090404014000c44144550641d03a980760303d00c500b42800009203c4000039414180c40d00200c240412003003140b68030460007100100000c52a001026181c00410707040603040500f0404040e001d903c68801d41c400301d0b5800303180010004c180307034160307818108a1550100310b410081c1c00c1031810503094000c3c0c1825016200840c10010720f05d00c04008030310610009540c1071044c0c0c080c0d2500c1c1585d0603030740c940c000c1d1064040d0302d004440258043d0540c50032110301c00704c2d0700040107110b0b515900404102040011381001c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 173061582 1250 173060332 173060339
    0x80703050f03070c270c0e030f01060f0612020d1b030b03070501090608090c09100603050105040c0e060703050903030d050a05150618010e04092f18130b0f01170304 72
    0x340c540046006900200c540844280905da60a1400f014041d100c0c0000300030a91501200510560130340c039500d4401e10401490000191044c030032041122030074250f103501c0500d0840241c6000000143e006000d40c0c0c28001c03c1c00c00030103070040820f24045100741504d00810020081d007258003130002c05000350702444090100b83d0b0828405010b540c10344c10b02909543d03503060b0051400104004842e00320040005101181040741528400d9400d00e40f03080c0000d07a01c0e2014801200e43e1010100c001801c6603070b5003009070800310014204140285086860184443d004c207245601160340c0c48955559401040b000c040c551107140e0b005505071101c2d0751a140030300e00107251030241d9840100c01d9001c680c160300f00c0f0703806240308a8004c2c0700580240100446401c10117210740c02400c10a0003030714400a407101d2507907407000c01810b040d0024480c5011885a2482001d843c1d030090400641d44800b2100c8404110204422441480c030000c01c0c19556041c0200100d04848038106148254018030090 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 173062832 1250 173061582 173061593
    0x30907030b0c0c0304050111010f0e0606100302090a0302101407111305070c150b0d0804060f080403050f030a0b060c060106140a080402100c1506060311160312020c0106080703050f0307 81
    0xc4045071401d00c8c003451403c42c42000103006201402241400031b103480903400c050500801d10b0b900c100d004403154100380b00304100039001d0782300d0944215030005d0442c005100502e0304181411001000f45031082c4016000b52421102d6401108182c801e259181c0d00001c00389840900248510006501880b0604003640c010388003c0600c4070081c0b180c44040d90f401107003c0e07070342d20962185800038081618070f011400c0000c0650300501407003000485001541d005c2a00a00e50749018070740c0b41d82e605207008490300d066880381e00085c2144041075103c040d946015501c8002900c1500b5045000d41352039450620301400084050b0b0a00c1031003c0c0c240070600a464110a11640c401d8060300c01c1030b010709842004407000a4000c100500040d0325005030803143d9100d600550075505542c40c200078413508015206894040c50030b080b40080d42c01141c500000b4440d90200081c0702a0700005400c102c601c841d05400e5803050341200505521005e410400d03c00100300e00c00140324200081e615280194452 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 173064082 1250 173062832 173062837
    0x308060103050402060c121305031207030c080f180f01030501060c020f030c030a120324090f0b0a061706040204080303010605030718060905010809151812030907030b0c0c03 76
    0x60506035110000f40a64546104880d0380010807030507aa042c0071419011400c6030030600d01c41d0b29202c401000454542000100b8214035848981034506080f01550129200c44481c081150651014090b035071404043c1000790440801c603408805003500400d060082d4500700350b24560402d030814004100036a001a604402603406640741c1001c852100b01007031610b03081a041c2d80e00f44c0304003a0300805004d0359810020503480d15035401c3c4040c002500030002d030401072402031719103c410701804204044443e40010340005864202043c04441b540004851070707013a5000700c0100d101030802d0f481d11141107000740e1b440001190110f080909102d104d99490005002e007505200c000404980c182d4001c178140d08082101d51001c5200e075445540061906803507115036400300c0d07440001b183c4000b4000c03e564603c0580100034104c26a01c00100005c02c0c03150302400c4010780101c0c2e04021720802c0403c010340c800d000715401442c2c003624600e08107000c003400400e41203207444140050004010302004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 173065332 1250 173064082 173064091
    0x9030512090117062b120306172404020315101403120703030903021009060c031a031b06040305061f120804050607020103060803030a0504060b0a031e140601060507060b0d0308 77
    0x3141c1500070103100403400394100320a0050003810b0290280c01701d540c3e0540200080d501d000000e244003980c6805596600c1d40c6515426103031180e0b10103880340c3c02b490410550346c014001000c07651070880c800031000c40c02c0400d079400410a812400e09002140c080342e0000300d505000d400628a800120f00040410301401c00010f08258550380118103061003044600341112840d5000c0042e08890f2078141c00600c2c11a01c9507010034240105140b1501000d10b58100360407014026041d2540711245003151170b000b000c403a0398451014400400802c10420545100e040070a48081400070b1001e000c0c00c64407a9135000b81054150120103034001480c4006440c201d1702c050322211340b9502c0d00e10043c0d003e0561500614401e21010040009100c05074111a00440c0513003001c100e03203140d400c14000c9034082ca010103020040002c000c166807041e03840403510782d9805510950352500c80c103130315242040e0080e400b2000142c00031803a101480f015100b0440300c1482100c042042084955011304202c00c000c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 173066582 1250 173065332 173065369
    0x50c04020315030d0e030c010c0201230409020a26010f060809070302040f0f0b0a080c132315040501031a040c080105010b0d110909060d030903051209011706 69
    0x80480c05a400384516011412001010354440c80b42e044c00040c41c2d41000d00b5036622900c900d4520f40c00b254002e698604031941c0694032181d00d44070304418a5440c0c0002e20010300b00b86403c0200041e80c0c802c40c400ba0100008542e1821148040c00010341e0100e10402c00c00040454020300411098a400b00c030300e821a2098104900036546810402d401c0c80e03840e0b480a0740060601000c49004c0300030303034481040c84001c06420860000103009000e00000c2c0ea00406910794482c0b1440d4081d4981181c0600264841000200d82d40b100d1483c000001d200103845002170404000502185070307826802c20205020079102004958559210b01d411a00f08002288800c403002d004181849005100c0342c0103458078000901071541c0d00c030b107000302583c00282d0300e0223024030708414902840d00c01011145428001001d184140e01d441e81000161590150704400740002c144c00000002c0d800c0c0b041c591080340000340030303849810000014140b40c402c080d0705240f01c0e0341d4408101c0580d549510342518141e215 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 173067832 1250 173066582 173066587
    0x5031b210702011805030a080d05100819110402040b0a1205100e070509031b04181101030510082b0f140f040e09010504022407030806040f051e060a03050c0402 70
    0x10040e500060005e800c40d43d01805140d802ca01841070403802400e0480c480e040800055940000280c0c5101803806140741780d4000780c0403842c4140c052501001040c0c00740703151802c1c55281c00c1c0002d0480e0311030b50100410480116030740f070510341c00004051024881800030302052074081c0f41c1c20261602e5001c1d80b10064078401c080341420348542d0070780c0d00820740501207171001d039410700d0121b89038520582d0040c4a030f81080c02c8040c1e00c241c4620403009040c0c3c02079014229040d150b006601501005240d82407070094620000381d8850100002e6001c44040028240800030004440c1111402d449117101402480210f04000075401001d903008107449c00b480d1a03e40071b003014180d051703115581c42103121124000a001c40118190b02c6607000302d2084030241070301013064600307212004c0c44c0321082c100079000340b2400c1c1c042030154130b2485e44080018000642d40d0803001d0741b10215182130300c01280d108070746051004030200c803c2d205500300e001160340126151a40d030b2030030384e94000350300080d0103280c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 173069082 1250 173067832 173067857
    0x503130c0504050a050f091501171c1e0c26090414010f06020f061303031401030615091104120809030a03020d02060a020a0c02040905070305031b21070201 68
    0x280303001400078150082052015080c10001030000c1c00d42929185032150f4a8004640e504c0c40000d0102820400f07005107942981c138080c200f0b9034010050101811600540e8044045424104200e4010000680710b08400ca40c8035418807000e40d81800d00c080030b101f030705903001c404280421000a200801c0c81e10b00046d40d840288015007500989400e180c11504102820442c41505030419043e0f9507501c2802803190f40c0ca40c012070743d541c90f241d080c51554004d64045543c0009265014441e54081d08000c10112203503c010900040240d00079500c07581e40304005405440c2c000c5034407009064016081c81031440e0000d074034401c3c0c440c503c03130455108034140d803800c03c11440e802580c0103100c0c01010395243c003070715050280d00c41724080060b10050140e6800248019030910982e14001100e655001d40e1202541c24403009042400f826221031158100000000c0d01c100300500d403500202160110400700c4800c02031130030745503002005410310904840780c2103107020016241c806409103010908a4075 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 173070332 1250 173069082 173069093
    0xf1403070317030901090c1211031c110a020307030606090f0b0f10030e010f050f0a05010e0403080702100e0309030c0a1802031305030a0216090c09090c02030427050601050a050313 79
    0x20001c0010182c0094690024040c1d98000d03075400824010b0640603100f41d0004201610b440c40452f0541e8141400309080c00d4151003032a01440b0003024008440f80030510f5000645480110760003151030f59203e00050103110b040b8007070100780c00840c0394140100e012400004000c80b420815075805481d541111340340d042e02c07030f4201e07104044c0e4080007001181000100a409850221141e2503d4980000807030312403115071150504a47c910000745c0d1940c4c40b00d590440740100007600820441c49040c80c0c801503406c1c84c0c810100a5012540103580d101a580185410100c61481841c0b007161130380c90420142500103d804011210b450380180d495880806000e4800c0c06020050454403000c5103410130a40c0004d000801210080c0408082c1540ea800c100161105483d8038400240d6003041040007004076000110190750f0f42c01074138102a04c0b045044900c0c001d20240c0e0f41c030b00d030307940145881c0c3c0c102d507102c0c160304a0070030f2811500d010070221002d005803101034110b1803a031040c820600c06204 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 173071582 1250 173070332 173070341
    0xc12020d030e2803110604080c060315100e01020c12060105061e0d050708010e0105100f2304030209070f051902070e04060504050615100513050a0f1403070317030901 73
    0x20f000d41402da0b814030340008440415403804101c5940c40304035440292803501d242654100e40883c4020411100c0c000c0a01605400140c1004e6659071080c880b00407070b0755807081c820142c0c03465544007205036041c0c4000a2410341c6a0008a008448400c0c0510407485c001c1071940c1940c1c0c058420503514040d900c462010211040700d041d000d4400170800d203100f40c0c8190825406030a095603098450390300d1b41c012099040c1c00303106031940081000160002c40380600c0d41414040b0071814458083c50800c2c100e8000c41840c001604c0342600001002c0c400c5141181c0400c1d080300140c0780003001d03401d4020340a0024071920303001d0b02d100e0321902160000944208110400b502c4900b2007440c0e50300705407500c80040c0c50250b808031003500070385000800d50204020700003410f0000520042404442c032105464680c0801010282d15900c1a0302042603240c84410340c00410260100b103507140d2805070111402c20b10307241c8003807081e0050b420400205521100300041c11840c035181981d41d03181d00c401c0c1c50041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 173072832 1250 173071582 173071609
    0x30a031a0402070c06030b1e01081008030f041701020c0604020111030705031204060f0b010912060902040c110708150c030702010f0606031e05010b2d160c12020d030e 73
    0x1e030002a203001000080b40b4904200c680984050100005a404000190f41e9021100c040030f20081901c0985600c6100da80750044036245504c0c140799140d518036811070788800f80010380701c040002c0030013500d4196900c2800803505a0300071810090068110744d200c0b0006803020381000740c0b0244400c00c10b10103204a0341019070010403a03540f5100040c0c4007261031011282075039468603200003d41c03180414002d4884806050f03691440250030500f1000230648200700a5650700da9901e100401a192480780048105032a2102a100b20440550034506840c1e900103020640141d082e2212700301c80380d20785a81241c00e03015900c1c0c0325039410104900510120246440032410130f43c00207401900355001c0031342e000030a09900f2001048400c00700035110b081c821560418001c0081941d6441025046441032140308105035608203101c000104907003080810b20602000c001e4414101b04000b403a840050152a40c503003219a0181c00041d1408500200582804081c0070440c5d00fa5981d65600f0300d41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 173074082 1250 173072832 173072839
    0xc050103200a0305060f030f07090c020f0f16120302030901030b012f06150102030f1615060f0f031a04050f19050d390f080901030b12030a031a 63
    0x2c0e0802030000801408003602c0440c000c050350141d2110500780490b0f80070707450141d0001400300515101d003003001040b82d10559001c60091030b5084280c20414403001d24695000c130018110380c0350302d4444c10a003000796440004520186222000080e40110a84020000900b8009001000400180c80d9080d5440090484458a0400b000c0301e031140c1c603100440440741400c40d9100d035200404031998021800325280075a000b84088900c40c04030100401c06030b0440440b2100e0503080d03070348411441c000d0074100220652201c2091100f03c0520384404010001c0746c54100540346581ca4814008420566108100c01c130000003e0500000300422581448800125641101292401d88401110a108807001d006080da0041c40b07912854841c1002500030b0001c40344d21407100301b06c10f060364417014100fa03e420000700e0100414008826051300d140142ea030b007507030382e00508001000c642d4020011442400c12001000e5411400000d4401c414010b00700001c01c1d503080c8040c2025003010404143e130 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 173075332 1250 173074082 173074087
    0x61a060307030c08060126040501020706050c0309010b010206070e010e0a0b04090b12060f0112030e060d0207050114010b04050f130e0a140601060f21090821040c05010320 75
    0x519941507118509400503a40d4000c4c185c1c4485004446016060001520b0810020724030030950480e14640c0c2c2e08603115000051a00b03402d81d41d4003090300d00464081407680008010044115028041c600c0240c0092024016601c2c107244060030040301c55002604105c0100d050a446889100042c800307030521704030054071142e070f0314004800780400d02440c60043d4900540015403070030000c2e03442d00a0a8184800d145a828074555000ca0034540f04190304018040103102c0d21922600002e20592103172030405a0b85126030f0401074290381e4a643c000200520039401007100c05050f506032804d0707601c102c0c0c1c0341c02c10020b00d80000d100c0703814111700d030000030780783c034000f00340d003a10004032011032902c600c6039044a603d00020f1300e51a03c4003446141c001c01c6c4c03445140010345104a03000d902c1095103081d00e402500c2017592410868440030421242c8810002d4218103910075550343c030105142e210000001c070319180d51241005a4580b01e03642c14191904248a54100c5a010780c249003003c040c00140c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 173076582 1250 173075332 173075341
    0x70c02090405030a170105030d140d1a041a010f0e0301140c03040c0e0c16020d1401060612090203190206040b07080a0e09040809090c0d060602011b050a0c061a0603 72
    0x751242d1201c40300601003005124a00c0113170b5400c0b4500d0b4121100100a4600881c050005a610440000900741001020403c0200c040071602c10384100d607014540315a2041d4066080c84100c4101a50681c07083c01d10380b0078180144c0c0d01c1501002c0c0402d184c5000c050014444010902408540034468031010f6140c04015090002c0c00c05184940c0c05400003030100341d904d500807a02900140d408600ca66403c01543c00c0c089c2c10b45c00c600004910141600c0b01c0c10f002526982011000c6a2100803680d449a1003000010ba00030702d02030340c031716641a08100155940c2d0000350b4480232403926030040c0081840c00d0041d5034909040d100100407600031240c0e6101c0900e0310b82c1c2c41d54026018200440c0b080d07005caa505040c60f04089108903484047e2610340b0307021208009018400902e07049100e2030410503000701c00d4050003054024240c503000426000b014100c0b140c503140d180e40043c0e08005060160304d5041d0392040011020b01c0c4c000303100140340510344560898051101d1400c0e40c0201c400420300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 173077832 1250 173076582 173076593
    0x2010506030c0103020c0a240c050901090602011a090903040b040b0a020d02010501031a09071505041d10030314040503031309140103020a0b0d0f050f06100f05030c03070c020904 78
    0xa8800c00080303056035244062107005500b24083d140d841c0b41c03243d10590b1444000352804000b40186500ca07014228168540000031003507403203140b404000141c01142030740895030841c640c98003400040c0028084250901d90100d06205100b02e220b02c100d81c064045108440f0900c110380c00b402c2d4041116a643d0340b5154658440e0784031620500040c400c84a6001d40d4500c10312500d41600d40c4040800045010b40c0052031010201500719011401500e00c001510130501040180102c40c5844130740d1180c1c58110f5240500010030340000d0b0121548007042000d000540e42d41003503942c1070500030302201c0c448051040c54002e60700007603018400014a48a42402000180125180c001060001e0402e1071300c4071076100c6080c1300084d0804280b10040c8040f0f804000540250740c0603c10008400326801010b006440d4196200098085100280030bd282000c070305444010400f402d020340d400488100003401840014600f6400d8503010000c00c044c1c61103500042c84142c0c00030220303140e074200307030410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 173079082 1250 173077832 173077841
    0xb030f03070c0e06010804060209060919261c110d09030c0501021609020d110d050a0e030a0e2202070507060206100e0f0c1c020306041103012303100c0201 68
    0x80e00c0402c00000d00150644407501114071881040e51241c2c010748650b0b5440000e50000004180d0002c0240b101241035101c2c090007220b40c550540342d00c070031240340070010f80c001110036080629102c2003614090404d1000103031f00681500c401002090401d1040c0116122000e03000c1030180742c040e22a00d800844d61107290390095034001e500f0f0385c49550761030005980d0303032100390202c3e0912040d64000300841c020716030150840481c1040301240c05000494800f40c15409441c3d00780c0c4e25981c03441441004c0259120b900c4201c5602d0004500d805220140608802044010903118031520b0701700c0401e28030b2008003180740826581741903484010500d8031585813007045c000c210041c4075800001c1c90040d0801e511f082221050701a0611540340c0c0101e8029610000704901034108041100518800301d221580c072703000030341c03010044e140c1c242441004180c4003850359624000000f400144189154015000c5c02c4443c6424201c08411250001c00e0410418060412141c2e280011109803d50107400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 173080332 1250 173079082 173079097
    0x4060b0d0602070c14280918050f030405061c11121b0a1d210d0e010503010f120302010906020a020d0809010c091a040312030c03050a091203020a030b030f03 69
    0x360010139031181014070b4242c02e044180e035403100c4031050354126060070600d0104034038115407805401c0e6840714040c000741c0703400d00c005503d01510350314254180101400300c40c421000341c1c1c2c06180f40c20314090028005014410804004407060b07180c5604e801f41360360014131000420381d41e1507280c01f0701e00480d81d20568101e50010001003081c040354090308054080b00c60000103038407005014120100003502e4944007100302900103540c120080404072405e41032064043e10303c4014800d20707440c0134004003503090341a9031905101d0184010301019443d503440c0820380348000400410045a8142240174001840005d060540b00013668800390380d01281c89130091120b074450a4681d00ea00c080c4a00700d034126501c0c3d90000ea1805428032600441c07a0010100d1094401d0007424240c482c1c642d603000403d0fa9540e500803030355499115154503058060700c0d91103281040c0401c081c22091705c4d030150b003510007641801050360004108860700e01950203100c0360040502219000c0c0303003282c0030658a031321103072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 173081582 1250 173080332 173080343
    0x50304060c080403050f09030a050a051c0509011d0609090a06260607080702030c0303010617160e04151208070501050f0709030b0408040915170f0c0904060b0d060207 73
    0x219850074042c01400e1841c09154156a21403605e800d40c03a1991850b00009005545806161004000710307800300b2040454034082d00140c44001c0c0500c034030744c01000700b2180303c4c81844000c0c44101a0707603800c404400c5100c000c0c000010100241c80c000280b541c803503204110380c0b204030241401100501940850305540040c928a100c560301400f02d00c41c440b022508001c02540b0400009146912a0348005c4d001070050040340e003800c3d07013000a281160001d0708520001030043c001d21400304200030a03150030004152402c00002e8880e50014003110144181c28000ca4440302c0c2c0c5800700040008440042c50456580005a20b5500d44040c8952003681c054034258200310102d00d480b2107528541d07009080580f61201c0325440d66813040d41c10740c6e0081c000d9480da58103000c0000c112000380980c0b401c2d02c1080d000e0741c140608040e0503103101d1001c1c1043e11161380c0907509072800410f001a1110f05d50030111400c20103542d6628000c40a000c4442406400000d800044001c02c64140c02400843c3d2251 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 173082832 1250 173081582 173081591
    0x120703180515061507020607060209100c0b220b18070602010f0b010509100e040f0f14010b0c0705010e12030705070603060b1603080604141320010806060d091205030406 74
    0x83c000c1150300100c2c104640060441040030030014a07103c0001c3c201c0721312a4001505048043c03000549520018403c240460300e50301a010820002c510b04c0ca9010800602e0401c0e90001d00e0222011400901e000402e01640c0f00080303002c2c643c4851326a100c0d03481d0041100c03540c51f00d07154001e01800c2140c441207551810440800e00940c0a2401d0300e074080e0000d40741d4003428007400c1c800c440044900e01e0441c0c0041d602d04903400303541801c0c010311030255900200070510702008400f8440d8448164003440741c2e40414000f912a030303040880c030300d07040b0b680074644107002014400008180002003043d248907488001181c42c00c0140c080382980865002e618108007040e03840d000f404151003400003065030038901c0c684c0c510010380910620394201001400018960900d00010000e40c101600d03442080442d0044030070400c22151303030441c80f88003001d0821082c0d09603000040d01c0c900303029004500c144000300d0443e0703807198641c0c4040f004c02d4000ea41440402c9001102420b1340e8400d44081d148507061 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 173084082 1250 173082832 173082841
    0x41010b0301030201050901080a090818120a0b011406040b030411010f17131b0b09040f0b030c060a1103030a0603060e2a03030403060501090203090d02060c120703180515 74
    0x5101035904990b01a11103a28285000c1d0044640000081c03400400e036543d884150003007518600500f02c10b13a00d0002c0d00c10800040010003641c0054840c003160300303900500c07016002030018641e0314111344410718514460329180000035460701441d000500030600c080704110502c48000e405002c008800e0701c0e0104070f900007203030480b210031061540c0990950f6900101e50004003003400007104a014600480402860704494500a09268080f60359144080380d140c04c18a0144030302c440020b0315503000c12050340f03004042a06c540c4200c00440c4140c81c0403e4402c0390345d00800741c14850302c40c60401d172a030700d02d080e0f007010005080328041503c020340740100030440d00b440010a555201c4280903061f0483e200f160240f520140c3d5928016054003080c0b100200040f80380c011240a045e41420150710f0345042c0c201c20f4648000690400704540c0000140502400b51104554510410004003151990f4140e0103502030402040c04102c4041d401021009001d004101d110f4002803910500c85180c40c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 173085332 1250 173084082 173084099
    0x2211201120308040b07050904140105010e06070c03060c0203070f032303070206150f04090f1403070b0411010c0c0e040201090e01060e011115011205120f09044101 72
    0x100480107000c1015503000c10086410241d60f46d501001ea85032191a050303102020070b080d40c40c02016900c601c4d04642c01800f0039a00002070884500040d500d071810304d104e0303031286247c4000a2002030020b070f60740d800d510705c03082c4280211a00b040d00a0345030131005505141c014031030b050703520041d1440c80b003030444d05018100d81412a4003854959000707041030384138510045d0320035802074095584a494600180c00301e88440c040c00d4043d034000c4e030000c503242029091600895000402180081e0000c000b0500040e981c0001203030002e8104009851803504140143c800e01142000a0701803910144001521200600c82900c10780c401c1e82c2d0f506140d680c0d018203e0038101d080c081c20001c1605500482c0c00e5502c43d40b04642c900201c00100c0e8000c1000403141a42094281c0010902e0803d5046400500208005101407540e50780d150381c1c83c001259665031790502030400c91600c0741c0e8455494114a0381680c0c08481c010413030740c1c41940c44409241c00000c808003001d02c0380c243c10174007200010300c094 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 173086582 1250 173085332 173085359
    0x406050a0203270a02031006090f090209040f030e0607060c0f0f0219050109080c0f24010e04052b0e010e0609120f16061106060f09060102211201 64
    0x75001e070880d07081c00c00f01a8200d400503600f01c1c45030006101e010081c0d80542c0d8100f0085980300c514100010b50603003032070790340015038428101030003400e41064104001621380900107544607800c80ca4080d5541103914084440c07001208401ea4461008a00030040c0802540704c00c2d540c1c10342c2d450342042503c28150540b100e0b02c1c0404601e0141e0481d070340900440006042d0b5641d080d116000003d142403140d601d0100d03c3e0003140c2c144010741d0050303c0640c110041004030711b0700c0c0400c110501140d009a00101c030421001401410700a0405901107020808100b00c001040c1c2110120300f100c5072514022890000b070004001c000061419001c1c40141d4010b81c6801100300e0040c00040c82c00100030184508001c01102641c518400e400e40d0581c1e04400703202da404001041c1c03010494140c60072100401d811044031070601f15400c070005000440d500d0a010354044030043c1c0c0e6070700d11942c4040050f401c0054541c5007030207a1075160300401c8ea03190000000d19020031b4100c20b9440b1039803100c0207850300030b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 173087832 1250 173086582 173086591
    0x40b0a060e06280809030f18010c14010510050409020d08130e04110310060503101a060406110f0a0f06020d09140d12020a020d050d150e0406050a0203 66
    0x506440414814984a100e088021210107880e0616107840c2845907a000030141d64100390f5504200d0f402d030700303c0360700100035508071610400960601d90f2000c1049031520840e1544a001e01482c101d0110f240d001c0c00140841540140d0844613100c0a800d05601030941110044000958044042010b2520b0720411451603005094050000ea169031050f25a601003100b00803141d00140000a0301843c01c4081d5114501c05e0202c8206640c1900502d4580301d2000e201800c4607062000902075918002241805034940000104840c0740d030f110750444c2014000310300b6410040c00903020031115040303010802e195041c04103c80603111360074816900c03001c0c440300040140b03d0151038200842d4958000d41141b100260b0005102c0b5132035500d14902c8811003040f1003054000c00702c02c041194000e28a411020341050f000d41c41d01ca60b4013070013511440ca0300ca01748180310001c00d1101c80c8000d25441800d0103410345c05034254140c0c6494907664a0f44080314121030090418000620701c0301280240c82c020f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 173089082 1250 173087832 173087839
    0x606060a021b0f040c02070306050604090f0f170d0b010e030303040803070507080408010501090e010c03110901140d0207050a0c090b0a18020d05040308070f091a0a0c050708150105040b 81
    0x40b01c8070b014148200b8000b8544090f44401d500300340d41900d540314414645030800640082c055039103503181403000c1e207000a180074030072071070b10420f1000309120081d00321040c1d5010240c0040f8030254546001c010f103266221440d43c03c03010174a51070034200d0303500c000c1a80c03000f600c1c0c000c4007400510030540c0d241700484008200d5a01400441c1c622805607003d0300c0c03254030516035541010b89401c1041d08555007684003003941503e40c0c8000c0039001081c8680c402490a9140500a1800c40100840c07d0301c0b4400c680703030422405821900760304102c1800d44001c40e0107a2419540c0f10010709001707980b074141c404160303100742c0000720000c0c41d01803921611900b80800350000300454640302d005503040d500107102000c0d00343c0800c40e039200506180710b0503100341d1190b218100241070a00d002400031901c0048603050205d601c00a02c00301c0203507641c07801c1c150100308415070b9914540c0000c98241b1017182c0b0040c0701e44075226000c07586071b1002c0b07101c007894080c001e40c05045030303030350010042510070f490a0f07a41c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 173090332 1250 173089082 173089093
    0x7061101050c0a050705120d0903030e0c09070809030904050c0903072304181209030507050402160803061206010e0f07210504020a1e24092c0703020c0606060a02 71
    0x2c003e00400180c05e045014200751413020441000c000442d50000f814140f41c2560f905c002c204054040c0b15140740c0e0396503172004040d00010600410268100584031506001a00000401c50481023040724042c002c0a0018005030400450205858200c81c0c2c1951082c020307002d0115800c0d100300c41108009507442d00d04160085041c0c1844001c000000d24411000c00018003203000c5081c84190b001c1c450226501d812641c0e207942046401c1041c03903044503111305d0040041d00000400d00070003c0f4441e40040f8100c1c1d4a07222000000c07201d0503028840b8255001d007a000041205000c2c1005101d610301c901c0c00c80240d580c3c2e41e0115480c4644010000c24034034002c050300d41c50b40040d8001544a817000e0710075941c054980e2544144503810041100610300c82d00303014009800c03800d400b02a0304412000c02c1407190303500b00014150101034003031510b1040c03084010b030f00030b071140710402c0c041107040d40c06071111070400640050195120000000c5140f14010202d04a03081c410308031032805e02d850b0701504 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 173091582 1250 173090332 173090347
    0x1020403140d09120f06050c071a0106020c0103021602030604030203131a03010b0a09050a09020c16030317070504050d11040e0601030b070f030e030c0f0d0504080d0e06120907061101050c 82
    0x20805a4962003d076020745e509040d4100082941c07144034041c03e10162902c0d04c130481c03441c3c0100d8452400c40302188410301c0f14010023160b900050711040c0e00c182403c000d40c03503840c8121644c4001c0d8403180e0195040c8a10070900051640100081c40302c96101d00314010701c1e94445078005501d4092080300f8544160410042202d014020080c21250300f10745081d030a07195580c030000f5460107454000c0d400305980000d071045040001c0294242c110017480000b581c443c40c42d02d0141841c0e6883e00d03518480c000440005458a05c0b031000c40300601002002c2401d0348030282840302c4843c1080d0b600c42e00441ca00721519407641030018501e0704a0723501103040c03c42c50341c5803842181c0e2411400100e90501d0b40780c0d02000d90301076040c80540303c11408400101403e030b0134103488619101c41030007200144502000140607602d00811002251101801c14122100c000404101140314007481040f00b0300c203103428403041c4200071480b0022030f40a0758452069030700642c1000e0032158203850000c001c0008100c003c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 173092832 1250 173091582 173091599
    0x203030f0c010e010606092606010911070501020a08060411090f19080f060a150f05010c03120e0a05011113030212030f0f131409041515060201020403140d09 69
    0x41940c1c01c030620020a12641a0f0012800c0d6055500202c0204500c0441440340d41d0380080c0103410907885909040302080c42e0808c0c5621070030107005581905403a002032011f04458141103400b00d607400402196680c2c0c01403001054a070007035a03058859820054003004800ca400c0984d140d20b0401400e083c0c04d071003d4400c01218408054056007414008800061030400034002c0003001c6010380c02824141c9486003040c82140c0450031a848011a0010184454564108501c2c159a02030030f150381f01024038281620044420038010200718200340c070104910b40080348804c0400d204000070700080e80348920329081400b40e514101640b0b600c44508001500d032030a0b085801130302800603645040c000c2e10128140750300440d08815a02e10000e0004019420348000d800104141c11001d540c450400001070b16000700030b40060040c1200041c6540544003d0f403203911007140001800e503801d03541740c43c0070380030b0b411521003900d008003212100d800d072040c0032444000c500c00750b50790f9003401404e0500a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 173094082 1250 173092832 173092837
    0x8060906010e2b0224030a09060f020319111c0f0905030f07410c03070602010608010f05010e01031202010e1902030d030c05191202040b03040b0903070203030f 70
    0x3a4050580c00d0109262210440c2c400321115400c800302c032004031640184443c4c040803162408000d4045c1480707840c000c400200750b940004c031040000c0352141c0e40f030070010080e002607020140c081d8400018824640031360360b40b08203d0420b00c2000c2c00307002500718895625010728940d485440804c1d0040120b00300559100041c0c60b03041200010390080d5075210135141d500f14404000a00c403000401805000c010900c0c1c1480b010b030b05102c0050700307901e1071080c88030116203c05045c0711280c0c841c440301038071020310920100000240031140c0d0345980b541c009028207424032030900c86501e8444686030282860007441c3c103840c50307036a90001503440c540c0d82210708680150740d0011035507100303808034112030f00740507080011300c01c1460a08100e051340105803e180390643c0f00c3d400e0607d0401c80460094024054420040280804198507a1503200a591031100c6480c011801440040c020a9500280011794042d9005003191080c1e95101041c003a079910949001070341c19071042c064081a00c483c0c000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 173095332 1250 173094082 173094107
    0x711030a0513150806180402060d0902030c030d090f051c020906150c06010e18062703041e080a03090b0d0b0d0c030303180c05100c1407060207060806090601 69
    0x1000c5500640c0d4807145114840c60f07100e1100060301e14002d100d01844c10a807188050034204180c00202e0410781c0c0003401c02d109001840544035181c0140c5002d41d40c00340b0544c05905409000c2e90005001c0fa0001001b007910744c09682180707a5000b00c0802c981c20120300460350f00c4818041d091040c1442e4081008000d80103104960200a01d081555411030000183c9090660540140402d504001c88003a43c408018034502c40888400119804076100107005c5410800c400b400b07a141c594146982a09151103881600b001e06c40041c00140c01968104480101c0388102c1d99444101e44034552140c640f0601003001d00042d00300c02007480014901c50041980300d908403000180803007000e0100e40b14a041071816518240502010801d054040c0201d080700b0b0982e04e10009046d00c5aa61280903100da8050540601e41c00344c0c010074001d014840840555030003100d8017101c02c2e06014a1956101d20b4000e0704010701910340002800b6008491b510b000f201c009041500c540e41312001141c0c90041d011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 173096582 1250 173095332 173095357
    0xc0604030f0c0b0d0c020d080402060d09060f09080304050c030309090703020c03070606120201230a03020c0c0402070f1103010203150108040c0302090109141005010206010e040623040204050711030a05 88
    0x40b0000c1c8081d40b0500030207a880c22020041303041007480c2c1c4040d04000005480d00180640c503010480180d07900b01c12141e11484039640021094641c0c1413520043c24403006000713102d80740903401c078103002e0301e01c000c0c521551140c4100c0e560607404c4802c2c1601ca01502c055141c21a13880c4000c0307294117000b41c003e0705000540070100c9080c5400f544441041d0340481d0b00880300320503112a044190750b0300c24440c1e407808540c0940ba00304c40d410329251110318800c00881004166021401c1607045106006006000b00c0051007036407100d01c203051110000030401403c131120360a1200303000c451308060003034038440c50726942c208105201c00c000540740c02d0030007042160041c610301c0c0301000580c1c1d2424014041e10a14000003076604449a000381070b003402030301459040c00c80d080108038980e030005a00c0d0654202d100441c0300c40d1074034509480546080e200303a2100503a00480416420800000c05100f80c0c021034041c00292204c031001c0d07804403130845140026800401c0045021401440103240245101c1d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 173097832 1250 173096582 173096603
    0x30f09090405120318060a09050c0d08070c15080f0c03060f0609041b0e060405090103121407150b01170705030606120a02040302040e0607091211030d020f06090c0604030f 75
    0x1200c2c0f01550f600464040083c3e200c580c580070801d0300c040081d240c0c840c2c14a18100300050081d01c9035079948400b03403803640c811000701400c58200000681a0f90034140c5c05480000b6468172203841c1007039031918003110b40c0001d80a0001564503c650b17a0f0700750013020700fa00340b03078038544a000c24040b1003202980c80c50341103082088059841c2c3c40310710402e600c1e20a040490b05d081e03c00c25100410400310304407103520401d001d20003404036654640ca0141100c0d801080e0900c24a4114402c0e2a00354038484502030561001c161001400091510810020310601c0208100c408103c019900164800c032080300d504c0c1404001500340e40070b00000d50300710b0070007450241414050620f030040c0000440d0700070583c40e00031130b0800441c14603024a0510300c02901c003620083c80c4c500700040540380700d4420240103006803c801c50920161141c80010410042c040c0daa008040000180d0348480d0308100751054400c050005440717140c0803460150000000b8580340c030342071960311280c01c01400309106841040d42c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 173099082 1250 173097832 173097853
    0x1090510031401050f1503030f0c1c080114010804052e02210105010527010309020909060f09030a1d0f0d140616050403080d0912050702040e030f09090405 68
    0x184021410082c81c1075001090b01e1410300c200c40007581002d003071203816550700100d007000d44d500031059a07020380316000d40c151107482e6080d0b0f191914a164000d504a4080c00102c440c1150340408403505035040040304042e00312074140116003002d4100c0340a44160000d044010644c00e540220114406034082c111184141c00c440e41c600301c1c0d0000f901080d4111040702e824841704d000d90415401817509003416414080800c200d4520606580414401c040c406845102c80d81c1c081c0c4d022004c4076401a0800c0c906140010426988003815512010b20021003c0000c650000000456a02c05415512510421101184a032030020ba1520003944338044e41641511510f8017911851a6405000808020b15180303640c1b500300500644200c4041c00d1203000c681800e500b18080b101205e60104440d035441c00c13401034407001400740d09001001113009001c80c08085d58800090805a802101c0070440b01c48019106035492007800d5254020600c1030010030300d541b42103182036034094010425038032403608 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 173100332 1250 173099082 173099093
    0x1605090d0b090705040b0301020702010e21010501141f0e011d04110304030f02070501020a031b0606090c0315050d11130c080a0e010c08160e120a030212040e0109051003 74
    0x1400c0b1841d80003030740308400810030752609024140c0c4402094002310314040103500000c25264180411601566a400c0d4101c90150145d0441d003c81d40004001c000c0d550311a810008455004000b8a200e050b5070341d4000c0c0300b03803040c2c24030640c0c22100b9126040034210010040d5942407103030001c04030301c42d4220b400752500d4850b4000d0307450031988182c0d041e03941d15207458050b19004144044004540c010801881a40d80005070107591a0b010b080c034145243e028008950452030301c0c00000d081604103100082d10440d80d80051500840d00d8034103012880360741d81003402502da1441041d900c68030240703020010840c3c000040c00c00c0a0003405514842c0344c1000c1c0d90081e03c4100c050707a000102075a041000b0000184502441070130302d2002403148002c000001485248060000d000c2c100180d4400010b03030740286d881c84035906014041d50308015104040a440c2e000c00041500507000b2000c1d1070032600c0e82d000445041d01c5a50100004a900b40342c100380050000400c5610400c1d50381b0700c04404140d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 173101582 1250 173100332 173100353
    0x90d060b0a0f0b0a03200306040518010903021506100e0d0302010b1e0901090c0f1404082d0d020601060c0203012702040b030f030f090a0b040609030b010e1605090d 72
    0x1480010013030359220440c8006080301c100058110384004100b40300f4a400c061031701126000340c01210085200d03110282203414440c0d04161000039036203071011035001c040c2c0100d4000341049982c1c0d01402503a0380c82d03045c050120030201391000003981840510a440c50b04d594030041c40c501a100000d400081c0b00040390108203204500c20703031442200403400d104e141c44001c45024000d0074000f401035404040740030f401020040b003884184190a00d481c42d65a4400d0291001007810800f168421845104840000a4010b890002500b0b2a402c030040207640082c4402170040d60754000e1a06a18101c021290703008402001c0741c9c15505c0301480c0c4c000390019225052002c10a10315024051202d10400c012983d00440d45400b03500302140600242c000401600c19111480040d20342e150100300015007454803981006080d00c0b000f2501181c2d4951269411095a00c00d01c1103d01e2641c030390f052484515411100c600211651101600501d03100340d028012181020b82a20301d28121651410020b4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 173102832 1250 173101582 173101589
    0x2100c121505210d050403030c1e020907050405030c0402041203050d1e0e0c0904020901091505040c11061b09010f030e0607020c0a090209090c072609010311090d060b0a0f 75
    0x2005050308002000020700a829500204d4106030b0300d02851580c020305620b140340f01c081c09889030b4062444039000310001c405c60300e40e401480c603004e0346821400a4100d40050081c540240700d140a14810f5003458401c507000d403034003014480c0d130040c10b6aa04881680c4a0b510000560303440e403200d031038403c07292080411203818649011407a190001040c0f4980b0300341d0781c040ca115050107414003001d07131a0348100c281555190382002c954403800945041c6606034541c0202d4026140601f013501c1d19900c003540080c018018416a00c290701e82a00d845451510748500c0350002204100104030740d802886003912a485a040200d0141041c0410781e082400449550f00960000d000d9000c9502d8440c00100c0604004e000071030500e2641004103042e144001c0106015240004140c82440381c3e214841c54015404a18105c0c0c010180c228103800750000440280802d041c088049105855181922403011019040c040c403680710b40caa20b00501403081d0419001400000040740070b0400314403802c0035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 173104082 1250 173102832 173102869
    0xd051b0d061a0907050a0f0509030102070b01120201090509100504090f060519060801020c0304140f09010f0302040b090915220b190204030c0b070c09020c0a0302100c121505 76
    0x1914020b600f8000440c0009003000c04005040254090b030a41054802c41039a4071882c1040e151490312010900a104402c0090100d102d590000501400242a40d4550a100380d80f0100711036a0398090003e0418290345e68030381d11803c0242440141002e5000380075440c01518003181c408a0b5440b20700c00c6920076900541106601aa20806490300e4000e000051409000841c40c110103500b1554490050f40500609600c841680003850350710b8403100c0da00e0b06001400203009503500e04031f40318581c07150301c8124040c03810000040007502d01042c03094420016880a84400e20302c0e0420381506043c003c114403203485070f00380c2c010000100300d4012106c0512030345508040d420081c11100c0080f040d1b1140e200c00e01d004000600010b48072814100486964206132602c54402d4a41075a00d0805a044070000d03031710104e007140c21160b0000301c0c0300340c0794020340985070400c25181c41c10f010b0b2a598410000401e00d01954404142040d90001e10074030b81000b140d1900c2515040042c0d0341c10100c2c04078164 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 173105332 1250 173104082 173104121
    0x6053f150102061b030a110f07050d0201020403123207020a080c0f0d0501061e030201030b01030b0906190e070306060908030406120507020a0f080c010b0d051b0d06 72
    0x840c0380d0812500c01188402d000a1030781c0c2c58842003005040b8486148183c0c20200440030403507060140d00851000e540600b0031503110410b016407240284c0103c0402ea910b8803c00c21424007090040c070072242a203400c0598415080401101580d13061034810300717440c40301c010001c0d203600d22410300404078200702e0782803400e9034400c2d03140100480c988090700494026000206084031b1959035084000400c9005e6402944c03401c91803d01500500690f44030000c0380030001e86212000c421212050309480c400d0700d04103c040d108100460072603980355501d0380c11000c0c2001161091038020040d501068011911681041c3c03640d4648641640a13201d03840400d03254030342400303815008082c080c042d0645000030741c100ee281507030050007002c030401e0442134680e03140c012a40140c4284035810755079800c60340301c898041041c904840154012010440554070707002d206040c600e44245014000c54000c401840d999001105a00c0d080900e9154150710181040c00e460000c2d143d401030480c2078841c1c80480c0c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 173106582 1250 173105332 173105341
    0xf080301050f03060c040314030d0509060406141b0906070611041a0f07260a0815011b1121060108010f050c0304060b12011416030606053f 61
    0x2400d600b106030070303201e44c00800401009201c502c055804481e0400c058003902d07000442e800d800c40c4500101071007040c0c14041080352000c03000620718042ea118401c10014005a40c002d01c00401c011b840d944043c030208107112500c180700201510b03e1440c018005850b08000ea5121802c5405c181a240811540810b00b04020602042041c01060714160070519005132030b440e0202c2e030f00c9500030081c070840300300400380350440644000c0da90700f030304c8401901e40d18801590043c20030a8100ca80e105015104400030301c141d403144414001c2680c1c0e400000041ca2035036540d1120b44c4040c403404030780001d1803040319500140c1114415018042d00000b0b0025541801c08203403d564610f16001c3c0d0071401e1009001030142003d044030b91080d00000c0016144403860000744030340a006901807941d40c02d0541404034100100c114500491104c0070540ba81070044c4015003d6803110310540022650610010700000e400604071001d40ca00300c1d01d401e9505d0311840c004d19286540c1c181c03c0d01300c10b5403c0d0410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 173107832 1250 173106582 173106589
    0x30c0312010305160b040317041203020c030606010905010203070b0a021204200103021602040203091f02040501030b0306091507090f0b030402040507111906021603020604020316030305180105070f08030105 90
    0x2d200f541d802d00344d02001c10f0402c80b4010351481a80b1000340031100f45051407400f600c00b0410f840140071079101c03c80700b010b11400c000350350342c172030080e550720034052600400c9841d8066100c00044800c1030300507504180c81501d80701d4001c58010402c011a5400308403a00503698101a02e5105910414844941001d204100704408031030081042c14503104006080004681032039694510758101c40c050f0342e070b59034546e0140c103040104904451007010809049964030240e00500305a42003a40c0802242c0d0002c810981e50741ca040e2001c20150308044d420f4054100345880359644a910740c180060300a90750b00e0b0500b0f87c102290700c0404248804030500c021441c0601070703181c02c15040d15008880b84289509c035521030400c0c110010308000da81c440041008a26015110200800100002050502e0501948a16045030200c1c8030b40901d05038211046050450f040c00c3d40e0701642e44604200e08044020504020910401c0c10b200040c829400041c20207410940e00c3c600c40d00c0902d0f10b039450700092 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 173109082 1250 173107832 173107843
    0x504032007080601140315042603150d03140a02011e05040c09020d060506030f0f18030904110408030d0c090b070312020904150b0c0c040c0c14030c0312010305 70
    0x203045150451a0104a030200c0010030505652158520b2a032400301540003074a0140175440c089080c40d400001c01003408071811007201c214214001c02000070840750840c40035480216500c0c820b2210482019041c1d003000c0803d010524440e08003080c80740c1403503400e0402e40c2c00040314080140c0d19541010968440520700710b0f03075a08081020b0080d03081076500d54110034458003520f0a11070b40030a2030b10b000c1d4101d8000d4002040058613031940c0303050a00d010240c40078101c54400342ca80616001c0b9041d0380e84ea402c0350680031440c0c0080c40c00e106c6954100405013460409117407000d00203000c08282500305000900240a0088000030010070bc04400f508500159000100100d4117000000219070005c8101340341000002005940c1c424903400100146282e032014076491300003600c08035550544000034101c1d12807141c212010445060300708000c1e2050f94410600103044c02c04020700250790700e00001040c090744c0080d079042c011050410b602d940c21a00d1807001102102004000303214042c0074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 173110332 1250 173109082 173109137
    0xa050a2603070f0e062706041d0408121501030c090b120604180803040c0f03020d0605070c051903081008030301170703080f0d1a091801060504050403 66
    0xc865600480038050040d4902008003107006000885840080e038501c00d1619202c5510b000780990788803283c0e0150ba030906d81d1050031710740889455215101d201e1401006950440c0c8240d5100c0610703e6001c014003a017407101400480d14004c1c140001c4d01040d01c07020440d403080342804000d00004140070001810ba5850300d920300103104070305405010b40d1403010102c584005003640c6a411a80b81d41d400708004207546164a40501c1091074541d0401201e500110700a0303000d40c41a0041d02e48850781c80d90300c41d68900c8020b501074501c9001c40006a88d5410666001c0341a043c142400c0015480311410207481201a0307049403c101502c0f8101500300e0f0a030fa0b00a5040c00e110681107003007480f696581d11043c0102840b07031285006d4032403003800820220014660040082d5110b0007000c0920060b500506007141c00503046c441e2141820949940941111400030800340c0c2d41d0311080420890050b00208000320395494400201e0180c850740180d600a600c83d5807030030010300701d09080507228840003c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 173111582 1250 173110332 173110373
    0xc15130b100503030a030b030c090702010c090902090d060c030b120106050301200a0e031204060905090a14060915061201030302120c12210f0103020a0506040f030b09010e0a050a 78
    0x101c0070311050302c1c004203031015078609040008565888100192604036215402c1e5406031000c1c3c1000280365041d0002881d84081c0d03254015002e46501400b0245e01a0317008403030300107101d03e07540400b142c80e40d003180c080760040b03040010f03001500b4804511415013610060400d0b0391038083c200401c9c00e09100da4241c1c43c00d00643d01c5403014625902a0743e911035041e195040146007a56191660307000e008050038501940d491681e502d80d6160040c0c030003080f510507944158040d000240b0064000e000302c56915501c52090f6a00350355840420610f8071001e0050410400c03030114803001911000010040b101d60684003c1d002d61443c17030024a0311f003007045a0211702d003003030203002e14038807000407441c881051180700103454041049641100401e0070014000c07122001c401d124950303011862640c10380e80217648894509841d44180715803440f9901c14140702031400c040400102d86161074554101343c240c2d001040035410030303c00720301e00291041c09072a95081402150200145a030054446200c0c81 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 173112832 1250 173111582 173111611
    0x190c1d060703051c0e06041406181f1104030602030a0507111b010309020901121203020c070501050714070e07030b0d12080a060302033c0c01050c15130b 67
    0x750b500030014020446980e4445402460101c01041a41c0240f00100c0010084070014a42400c002d03041195504490003180107002c007040320030b030f64140c00701075501072400140444000d0303001c0041410a1200c0c078480442d5a0303200b144180e14000c00800c025800b03420050b031642403244040048410207040002070040d6409401c00d000d01c0031070020000c6060301c03510210030b915680141d0150014003402548003200d1000411581e41d01c0d08114043c1e4005c0c0441c081004c03186030705908038070402d42c2080c5030752b0106400b0070a543c810001894400d1044003e01003803815040410b2030300e500394000c07054240a00042100e2641d0510400c06590412120021b2013501e580301c0352065500080d0303403401c005080c4000740040c200b40c0c1050004607409400c0b101c190b5034031a00c5482407800d805882c8001c000c01050318070b1980f8070f4203210116050f004017800b4a007080350015034880c0e00c00429041280244021081c05411940401340b03c1c107000000c2261507004c07880c10800c0e604000b4161507210042 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 173114082 1250 173112832 173112847
    0x6160306141804030e090a020408100507200a05010c0201021210060f0e010c140609010b06030402032814060a06080f060103020f0d08070f110a03120503190c1d06 71
    0x48070300c05105031079000031900880e1600d003002ca811754445407110b070704505044280f2559201750b50080c01100c654106a80c030700012241c0680540310140c034007a0001da10f209000350740c0e800106040240c0380032403048440c8000e480d46c401d401d6842c020040741c0983d601195941c1c5001c5420405030b07011070703c0480c02c01070504010001c0e00f0940342c0d020b04810050781c1c615003c2c1e2a406030490904264121400c00c51402071442442c0c1e0f1544101c50014041d405c14421928506100054900441c1c0c000c01510103da220f8050107181d80711600d80c001241071040c41c00c80483c03080911920340341c07640f5018041c14906010b24009994131a441000c456014140654512034080341c000e0540b541242d0070402403a00b00c4c0024403075485014040d02851001034003c040004152442c000701e480740300d466080007c1c01c0e0400101c0c10042c40040c0075080310030340719042c032882340340103507801459074200e030f180c0451680031841150188071444000c2024141100a03000c00404090415441103880a203000310 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 173115332 1250 173114082 173114089
    0xd060204052107090c030b060c0d0905150304060507020c09160f09030503090f01020705040c0207030b0a0203091903051b060a140c09040e0c030102070f060f1a0607030e030616030614 80
    0x4013486600c02c41d542e2030070101c1505100b0380081021540080440e40c4400310000785075141d8485c00b640d100450610140010103003000503181d00c1c41c0303e0420201c2e05564480c1c44500141030b0040c106821402808480e000c6e075980c0d40245800303106107214400d0000f0441501070403502480038a0820b100901d5800c00028200004991081800360b424401d2800c0f80341c0103030b141c004181c101a0380241007007022184a40d0010300c1c501228040c1c003800e44243c0341c9418140c200e2209403241c800c560080d0303a44110940c2c1003500e965a4910a19240b4a49004075a1148034084031031031000990700036509102c03074090280101000c2c0529804007800600b0540c03070065a0b0f2007801070b99030045840f41a41c1040701c0d8140641d03060301c140500255076464403454800c000110021049540602d0000e0034550200d0b644140c607a24286603404440c110b46c079104010701600201400c6041081d1159080035544080c40001d0007800d61407541c294180444e100a42a102c0c01d8100c0d0380726103a4840040040e82c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 173116582 1250 173115332 173115343
    0xc0c030c090114010e09090f06130506040f0c09050c030118060609050d0201020f070b07050f070e0103080f160303020306030706030917130902040602070e060609090a0e03090d0602040521 82
    0x641490382c0f00d400315000d02c0141c036456040503001c2d40c04500a01008a4105e012a929085002140c1a00c039141c2d20314820091040c2540d501412561011000a000460285403e181e1fa40241564038406650f5003142d0146d0300100c0f822442c0d404084010001c15110701c600300518052540144546801c05000903c0c1420b2031260b90b106210164a21b415a4001c2c4500d0311000088800d6440c1681c03914406891503006680071039040c40703081e031844d1a149004c5494815250780c0002136110741d00c1d43c1c459400d941c00a1000f041d10460411040b1542003102c155040d80c940f0030784001d600d901d4480109414140f440c2c0c080c006060402c0340c4c643c00540d000044280036910340c0407080c1c0f290f520884220711410300d0b0700121072461000401152071034000861000302d401c4031500380d5981c0e850b042480014060040c150390080008008170708105490742105991040b01d074210303810002204005034009040c1c43c81903981c0d0342d00040c28041410268880000400b100d6030b5001a0b401d50300a1a86e00e1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 173117832 1250 173116582 173116589
    0x10f1b080a11031303030f090806070c0317090c09010911040b072910090204080c330c0105090f0a0308100f0b130807080c01120609110c0c030c0901 65
    0xd003000201c1200080c02080c442109070141c4044a44030076078210b80d420201800d0200b9404074049004869032244102c03050019691620040c224039190b000c1c00b500c032007040d58412418050081c8034621100842c84c807442c410000303440189000826a000c0c00500c61040e004552000d0a10b2407005103022000c00f298111003403210810b641e1089810041000c0c00c41c0c040c03254800903402c2540c1075044001e0080d5000d40301c503040c018249661049014100c0c41144950b0150b5000796007040024500059050000c104010107a484520300c2d101c254001560700d12019030154004c100c2e801701c80e03003d204142d4008203140003010342c0c0f04d41e018055603401e00d0301c000404009140c0700051044203c045440000d00d0768960100219444065810f0540c020203a6025954003d000001c0c07841c6000442e00d0403510740070b010344000d1402c40011502d001415a00301e0109444003400507110000e8401d0440800c00d03101e00b19280c940c4080d1650409066000041c4a54422500c80a041d03540060f0141103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 173119082 1250 173117832 173117843
    0x80a0b04060204090212041a06010806010c02012109051507020a1707080a030203150103090c051311190f05090112090515040c0609080f0703060b121b010f1b 69
    0x116640c0d80740c4040a440b076900140d849500102d42c5110242803d0003050141d80314820f0078184c0c01910071b60700c1d2a40012a2414005088040030840030b50150380040b00b66801031500c903405403080c0401000890b0b40510f40307062031741d072640e100e400d01c0810710040d958080c038080c404842d400e0a00c00259a03c00c0d010f0050301011600388181d007118240c0049440319940260711907118020040064000e4008840c0d0b00321224480e40059020b40c8640310701c807481680400742d44903d42c200400c3c81600c43c08440e05280590f541c84011242003250b01c041c00120002003501110f210b4241c80082c00e1002d040641814082c00344400c10072a84c102d0742c0c00d0710142c0004000641030741941001441e0200a40b0a512440181020301040c400300010100c19121141c40c2c1009c003541d00c0541a0f40c80782112003d107407607040081d007031002443d99005641200d0b4010271160000b541d00360310a083c1700000044882010071118070740d401d940c110003d0f03a420070440c10007070341080205d01210711589400000900c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 173120332 1250 173119082 173119103
    0x6040203091504050c0f0d050706050306030a1e0c1512020a0c0b10080d1b0f05010608060a09030e0f0130090804050a0e270c0603160315080a 62
    0x1c01000811460190450103107298415007403a050181d2a000301440244c00b03151038540c00c04040c1130602a0101c019804001060540d207000300449668001030540303039060040d00b4441c40440c80d1a04a05c060f90040400103000b40b03841e280135858079a050b88050802da4000451181c065003001c8442261201e00d440035035103040400c01292050814000182102e11440a000d1442804004002a500e031703001103070f42c3c550044400703a41c031482034620400c604090900c00000288004400048584510004241aa150035410f070605004907040c12075607a0b10701c07101d02490351241a400c11b603202680d010300c810000704002011800040c00d0368008016128070122011404000040800300107030041201198034136054089030b005104e01803281d5a070160200c0c0102c058015240503944d804250140303042085200003011400840c503030300600500c00680490740b40c20000394442d0302d000440141040b1502d8000d0110780e03409101e521054640041880f4100000441c100c0064000750200f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 173121582 1250 173120332 173120341
    0xb18041a091002030f06010f0203030c16172709070801030609150501060e010201060506040605070f051c090e18030423040e0d080a02031005090a090f031e140306040203 74
    0x1072400341c44502d9812528400070411103486480c002e03240c051a0260380e4210005500038040340ea0f800182c80b030782100e42c801c012a071050140102d201c80001d00c10117142d84a10920700411049030000c1c8004003d2908015032445542c2580d11450101e21080b5000010703400c08580003052070005002c000c10300c59641090a0600c8003091000117149403550b001c1c0440d40c0c5442c8000c0944179802c00b003034055130929a000c982031401c40b05444c01e030f03041681d0301828420140c58450502644000c1501d0501840704540c0d040f280000d003108445080b5142c103659540b404407004050b580c0200703800c0c1c602000700036034510164040304860407183d14204c503c6039001c0500c0b04210004a800100d60700518000000e000c00b24007040703030483c0040507103910b0385d00c0e81e403d0101c40a070311040b074442d1101000420b06120900c2d18600c1607401403446000080e03060400c1d500d842c2c070240d01950a80c0850000002d038035890340340c0e1015195422642c82d041c5100240e0300d0310f07450540806010300c3d115907004000903 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 173122832 1250 173121582 173121601
    0x20304050a0c030503090307061b0219030507030606030b01060206090d03020c07080f07080d021902040c0509130e010b011706040504030c050607030b01030b4e010b18041a 75
    0x361241c126101002c85582c130700d05070b9580d030f20a944031402405415000107d15004032621400c403518442c00078406031199003045441d0409244418440f48108804004600c0c00c00204000c1e41c440d840005e800c2c4c3c01c0d81050070360311005034014070071540b0800401c0300c440300103d0b00f28407115050601685a01c144107000b0304203c1107801c459124800c078441c0c202c00e42130000e4420100c3d5850010f8074031401d240a012a00d0f002100c0f800c200951030060010010300701544100110340680c034281d414032900c8030010720301843e1221150070319501e8441d60300d5828000e10800e0107005c4242003100000710700c200c0914207030400418171881079560300f0000d230500d4040c08800300296440415122245455030300500100811050f550000b450180c24040a0500e01d215546841b190000c82c41017030400c0c0d04071041051508028204020302400c0781040e113059442d006220b210301c40000c1110702e42882408440c80300300302c402054264050a2101140c12400000c1d1503402c807008403081c175035410550 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 173124082 1250 173122832 173122843
    0xe06040504091104050a0902060a0f050409020703020f1519090507050301020f1207050a08010e070309150f0f05160f0e0303041203020c01080108030919090c020102040501201002030405 81
    0xca50440e0410b80c100d03082200c844a0f0040b01102102c00300040d40350f801c04403048a0340d01000940005c0200032480141e030040080d91804e810b2880c4c501e250688860320501a43c05c40181203001d070340a40c01840c1880c038248004680035140f600b0201c00d40c689400a02000061021046004d55842c5054000d1040a0143c40301030007000d8025035442d00f0040344804582d014039a10b509a10307c0350003140886100e10100c80800080d541c9001e82070742400f05a00c0d211001402c01d40c00d0503569103c4000280c0003c68072002d0300c3c1d00c5100001e60050ad01c0241054450854161880e549004104241c84080c0480c0303014034130091402152184061000760f51280d40004207540c980b00100c5c0c0000c48030400c41d101c1c203c1d00e120758261200c0400c0840152620031081c0200a180e0b0800e2024801c0d078149003890042018910400c1d100b07080da100d03105400c0f2140840c0040c0141d4001038140031950300440411081c00004485130050082139051940b226640101ca1507401d80020105080c03080406c607 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 173125332 1250 173124082 173124089
    0x705010f0c0e04050a0c0519030608030a20010b1509040b03120309010e0601030c1406120c09150c0a060c14031e06030313050f0409021e01021204060c0807020105040e0108010c0216080d0e0604 84
    0x1c81c1d0741c44413784005004683c1d503035004ad12505548460112009c4180600e82c0c41e950040d181c02d404174080804403655400c008075640c0c016990301d5440042e07540400c20b0000408883e00746075664213244104074207642e200c03911070010360701107001000055006142c20b0300b1100400d03202c1c25484841c40c001000351007200d640d0584280c07038201313208a11710020700a01200e1030403184800c003000f04150004080c0540300c100c400540000312001d021820f0b58001c0341e90304100b494510f0054011514921490b08159103007440904903c594015040c2c40b5104243c0108045005509242c0741c107034041c186c44c099008043c010b100a40e00a062034445400a80135142d000b05000e02c1810070a00f91070790f884030010114018415404090f045c030399600101d80603180c01da030301c041106241e92540041b0380e2110108a0420008020000d050150356022034082c3c06c1e02c0c030001c00c5007114100000e20708403100c0191004074881c40010131900c440000d40d050903400d9810200401807080740042c030903000302c0d030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 173126582 1250 173125332 173125349
    0x90b071e05010e010c03111215030102070c08060c0c2505040603061406010504080a060207050f010608070f060503010b0405040f0e060c0405190311060705010f0c0e04050a0c05190306 80
    0x418008000c4190845010f400c40c240c003c0012400c002412010395800c11501c1040e03540c1002041000d54202840c55801100d1038100c4031606055030100382245e00c521b07000e840d1000d020f6010302051405001498200d052504401d007407400c40e00c203040d1180303004e8403005540c0d140ca40c00328400380307689100c40c001824000c0003044040c3d5071382045400303401e401140038181c0c1d07102e00000d04198040c4040e01c095031141d20040074900341544e103040080d40b103854107660500c210040150244801d016540141c0980c6e40a04003080c5403c0c01e20715a41001e4100d4001d002c401d10060151040081c1958101c61040b00d01260a6603802e1804004005d00d1440031914042c4e40c08010621002e50010411101d007514042200d040c5041c1c50041441540402000156001c079540901e14040001c0d294481c011000021058420031124040714034240d625070104e5109284051545000d104640d4821441035041c044100d02100040c8a842442186551f124608284403c0c01d4403e0344000090400350 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 173127832 1250 173126582 173126633
    0x10f09030506040804030b09121c060f03050f060112030f082518050f030303070f0908030408150a0b0f01080714030a0f0c020f0c061c02070308040302010c02010606090b07 75
    0x18203000d21241e00034041582c7c210f2002c03000c41c20349030001805480c2281d90b220740504005904d00c41101c4d01c521021000703401901d521000c50ba07200d401180e04002e503c034000601c43c0d40d107490031860400205074081c2030002c5c0201c0c40800400c1e04004d00410751501c500d010901952111041016030070028051201100e0400c8074412403a003050800c1040c103210782c800015a40e41e0010480c8175400f070900780c4c1d0190400c0c40854403c07401010001e182041604101a1070343d180c1e101a445c1d60450391141203a03078800c401c052182d41c1c90081540d0400d8801809100300b002d84000300305201824004581003090500000d2041c071320600440100340c0460054617540d04001541741c01130104408940301d035a10700018400d0443c00050315812800c0707550301803c50402280100009034200c151a5403a00c440314114041110309803008181c0781e8460746441c86207051a0400030700710384c0c03112940d10079689030040622000e1780000001048410440c5c040e40d503800203140400b1300c00d500940c010204a00c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 173129082 1250 173127832 173127841
    0x1e03060a080322050a05030a061d0313090605060c1e0c0a030309030c0e09100b0103060932070e060705010b0a121401020f0d09050f121305040218010f09030506 70
    0x419502544501042804041e925104c40802c500b03c20144034040d410740c442044040003c10603040580245040202415002c000e51101030a6500004442c1c1d501c003030500b8180204016440380714041c0c68141c0f5001d0a120b07601c0445503036031006090f0503100503400c40601802d03940c00c002009001c00040c1c0624030b195503a243c0030300010240d00045500c5020214042241c407448112503105950040042c0682020a002c880041c40c1000a0307a0405844941c0402c000302c00740208403080d003105d20340e0302e0030345050120603555000c140c0360308510f01104401d00048540c040c20780c048041c01150f9450380e44000d071615500421031100381e00d8102070842030009500507590842c3c19980d005150b44d0000d004d00c0c1400900300d10500c1c20741aa1544c0030f1211904921655200c03005c100d110740212030a05e82c120400501e011114032482d203002ca0001940150f0005910040008000030342e0151705000c00c1000c08802c0d04550029581081074040d00c00c2e0085126000040055070000c0548a25041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 173130332 1250 173129082 173129107
    0xf0203071715041805011d06161202030403050301140f0919091e030215070c0b060d050114060a120b060402070503121906140109150320040503010605061e03060a0803 73
    0x10b80711300a9030f46520b0450481d240c90741009210f848400c144010341020303982c00320701c66114007885492504000040709103082e441e24500c01035010b28000c2d25066101d41c946400c03c00f111003110744407401080101c0c0750051681300d6018807500a004103400482a50f00ba80e60040101517070003010b0b2020b0314100e805c0003034449607007010386010301a90a03940072500c82485039404030000d031000300000760030703c11450224044056480d00604001c19100b80c40f54142c45003801e550302d0384a10f050b0022030384103215a505e841c4040034003c1040d18200c40b00340c24541c07258415014010500341c02a5000250901000800c1c0102d9042c241036031407202c00307410203206007421240095401c140341c2c2e2a040c8049440d2451071000006d001b016076407200042c2c1418900d00500300c2441000b021f258403844041901c40d40116404000c03482c0c030011503181da1901081609494190744410302484d01042000f413400100380410b00c900d5102241c042d902c0d2901070210b00c8110083d448661b15000103c1c0000c0e2146 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 173131582 1250 173130332 173130371
    0x80a0b130c02150f04020d1a040b010e060a030b012114060105090a020c030307030b0105130b070b0106030c0c0f020f0607110a050109060e010c1406010e0a0f020307171504 75
    0x44075400c40e01c910114180307400500600380d070400701e09510040010010714021a41504c8a480380d008c505484961000d203080c400010784045400420b4070700144030312604d0001d0a50b022400300c540d081d6030b41c5191100c03401503006010b01c40038062654546208509040d400c0c01d48507501020207201c1c0840c1012260f2201c2081c080c0c07604c00d00040000c154501100e00a0350b20020010000c0e41c0703140c56500e0f00380c1c0140000e90034141800000e0104200103860340081000900100030a02c2c0e41e850356184c003400010050300134005051818048410981d88840030f1b08920703520541501c0c8202c450f00010b9440d49191001a80c48040050700e0030812001c60680c940170300003940c01d14609a10f6000554186440b03001d5000080e0b0341c22040c0100d50b01c40c0031540340c07190050f0390b003120541c5400210fa090030401d03000801003403210002d10409240c40d220780c0e405a640b4090450035070401c141d00a0260b040008401860314401000c103541d018507091b5814103600040c03081110b036040c10b124440d40b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 173132832 1250 173131582 173131601
    0x5030f06090c0402092d030708010b040b19030f080f0a0306080f0c0102030a2001110a020609010902031e031308011d0303010509220f050105040b0c07030f080a0b13 72
    0x380a01070b2a2000350410303000303031240307010000c00b618010313444507002042c811002e60400c14401900d8050303c4c00c42c0c8040c001400500300b90b80002c601c50000704184429208010b0b41c15001d003000e1007400d1030751200c0741001c0003072360740c0403100886120b200d080010b050701541c0400c0d03150100c001846040584c0583c072800840d4880c0c401d64402c9071801126940764181c00c1d2203e405130b0010001d4641040c4071b014418405181466160000301010b600542102e103d018010030070440081c244144503010004981c1c0058100020b01115606a000c00d40300c1a0240703100881c01e00d0344d088100482c0060042c0c440a0385c0c030309554001141d84a04d124081d0407032030350320804d003c0d008582c0442010040100d0b4103880c0c014200741003030b4840b02e60200f218201c3e00d0742c6100301007040c030801c00000c85c030160a107880f50040001003a641410b0910f01002c401c046c101c4407250710100844800250071500003003200e0701900b032510340380da103140c2181c1c00b40c03000741b00b5079612107044500d41d03054440036800040b44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 173134082 1250 173132832 173132851
    0x201050f010b0a0e01120e030408010510050a06020304030807020a0e0721020a140a0c080a05040302030106170c04050601030e071805090304030f0807241a0102122205030f06 76
    0xa07640c9a510190310701c03c0b9000400050601c0c0700340c0c8115400717140c0d040d91505a400c1d000420b005890001c90550300950884001651160140406408401d02c407030050f1200720340000000c0e00c0c1c480081c0d0350380702d00e00c0000c00045012660800303641d03039148080e008014007225051305d0b00d0f03c070b40000d000804200307210182004074004518404824405e9a00002c465160160101c240141c40c3e01c09800c00e5417034004010100030142d000420440290001e82d2181d00c411f5250341c1036104050030758003650880c2082c01c0c2041440507124800148000c6119815200069952281310048001c0d1007150a0403c0c2442044000140200904c48194080703c0c00c01c4100480c2c5c807141d050503182d1059201c054440780c914020000800c2c02e201c01402e0785071290b01018211466005c08046007103140200b444895600c40c4000c02c09803c00098201d030402c2407020741700d400348072912403100380101180072030010704003048031003805e0301018110003a040043c115a108203013560740a40d140d6089a20624 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 173135332 1250 173134082 173134111
    0x501050a1a2202041a03160822050a020a08030a02060f010305060403122408060703061a210a1b0206040c140105070f0302010b0f0a080c0f01050c0d020105 68
    0x1880080481410030a800600d80c8141c0c0000660b41c0100200040740304000550810001410707003601c0107544041c0c0c40044c0090740360318047c070564040b010788000100a1155260410030302d90601c040750f03440031048200c441016003a5043c094504080c40300001e4000c240c14501050550001010b07040c4007060340d0880740a6911a4402a45c412081c0b00042480d4040400708000a018100f030412504840000160b080e090b6540500c0b5001c50040c11070218119040510010105215107984141d6504050110b285070443c4010500791150048021600104650403a801210792000c01c0c036201d420000c149051080581005203158411000190b00c141182c0b20f4403800032580038880d6130004108451310b13150003114004416000398050404c041044201c0002e0001a910700c41c8030b0207035000103810103200303080c440b8032861010100e00c1520305403030801c2103110015028140c01d03416100408586000001070f1103900407003090080318016030f24034000c650f505600491103081899000319 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 173136582 1250 173135332 173135351
    0x11407091a0906030109180b0403050703090914010902090f030a060b030607111009230a05010b010216031101180e09061b07060b120a110306100518070e0402070501050a 74
    0x100303880b8920b5203c2d000074050004018224050740500384d07403508240104140e0074140d46000d440d140481d011000304001041c7d00d01450f41c4807601d48080c000a08040001032051410100710010510810300b185400041c0e51800341c640c04400d0a1200c805403c860320750380c840c80e00c5400f44c41c3c1c0300c90150080c4200d00008040b1840b0340c4590380d0100014011300525004040180080d180341c14064548942801c0f0b090030302c4a10105030800d95a03800e010303081c011507614045080d5034500b03143c0341c1194072600202455030b086030401c1084a0380130400302581d00740d4000580740345120502040345035003881c1c000903451180a041c68450222401500d169641c1d2448070000d501c880400307500400010f101501c000798540c2c0c446014050300500c21004070341094011481c1807091403045950b0b50048220070384a00b001c1048980189000140c81c1205040c000071650340e03010030b0401c0e451820100c0c00b10300440e0007413a0f800038005000e403065585041609016020740800d0f0358910502e40340041c6c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 173137832 1250 173136582 173136629
    0x60d1211030a0e1e0a090203100302060d05061008060604050105031b040303021015030308041112030f04080115060212030c07020a1211090c18031009060603031103190309030201140709 81
    0x10480713600002d00315403403e1b0502c2003241c02500000d0020903907642c44603000c00580e5a0401400c003526005502040c0c03071601c1d00510404445100030841804009800e000640d96010709890943c0c0003864696140e40d21442c50b091041e80c0ba402c1c1145c0800000781c0441850b0f0702165176a61054821018030040c40001d901c1c81d80030020f480701070002a04a00440c0c00101c915000400f1440018024240c401074404031500b19441501011801c0c400001c2c00c100e103403402c1c0180c0040d442c607040d846002600c1c010300603445482c0c0d1014001103480000005948150200c259805580c0103045000340e0b079114143c010341601c07502c600b660803000b42000d601c15450140d052a101e01884420309040180c0285041d4512051000040e8180038a11030303544a0301007840b0714203841d80610b0700032a2180c90350030040d096805119212405400810440f040600048203452101550b8640014802900d080890040c414007a014181c0e2042100b07004025900c0701c41181610a069041035540c2505800d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 173139082 1250 173137832 173137879
    0xb0f010e090703080d1407032f0910091a070303050c07030e06030603070504141501020307050d08100302100305060102010c020a030207090b0d0c030b01060f08060d1211030a0e 77
    0x86901640c808401403001404001c045c00700039804180c0814000342c291040c0460600444d6801c000954070360400b400c0000c2007103402e10480c481105082400c0307066614000714418242c0141c0580300112103003072172070b2140d4040c4004145146081c0c22a03e610646400c46038482ca82c1a00040c1c1400b0120389103161200480c4d21242d8581c85041101c943e01c02400b00b2074000804c000c0d07241c014000f00103910303103c500413410317000d0720030382d180c1c086203060b4138900b90100710000080d04560051013004001035001540c05115202828400e1056a0354480107251130142d4200940003520031030403201031a016041140070714400d8009109942a800c41280d94a035202006801a40300b850108030f0001d0b2944040d045000140a91060800b80d4603804144940350340102c4142c00c42c100100b0009a00400091001c8241d180100e45410103600144a584042002074200a0182d03504042c0b50f0103004900b80c603c8180d01030700e48419004001070040784140c030901e0700412200b8900c25243c44000d10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 173140332 1250 173139082 173139091
    0xf21100b03040201270f0305070605070c090f061a130e0c0d02130306060f061409090a0506031e07051503040317070e04060311010e0904120c06180b0f010e 68
    0x98203030441e03440d5001162004c002c070101046145c0b0412808081c02441c03560300b00908605900c1d1401d16285280c01c074a040034070b60051040050510003040098484990281100d0659401003812134010321410002d04030380d442a178000f2180030030114881400005407003e0f904505500c0c0c460355551040590b4404201c0d844981d0f200e04021030710400713190764003400c0c2c4420142030074014661240c0c1c2d4602103d0480d040707103022a0307401e2020403d48e6031040c80a00c45103400c01c01e01341020443d101140c8074880240800d20a140c07600d0001d0113a85040004001451503030030f032055440e80c1d81d928507840b000380d402228000c100402d441a1320852007400c8901486c0e240c0e0302e004030b42e09120815a1015006843c0c0d004000002c0c000450b190b440f0b0080c000514081e01a01540000f001c0000d0000301030f0f08003290290240d9030410000c02c0d400e82090660040c04c0c00c0c842c0503105946030130001004640101d9001d6015042d5410600030405215486004900803012490362100d0300035051660444 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 173141582 1250 173140332 173140349
    0x1003060510120e03031305060112051b040207060906020c0f19020108040311010903030b01030b030f06011a0714010902040e070e070c03051207110d110a080f0f2110 72
    0x703102103000ca00c1050512145090348100180c03401c0e41002d070328115881541c0c45459075104001c004240001841514010800d040c4894a07000741c3c0d42d2142c1c0c0310250050b81140c0c40108440c404495292078046491003a40b256040041191514202000303401030320000701c2c40d2091600320003480a00017000001007094507000da0301b240d0a80d0045034107481c0213004804203c1600b81c210030142090060584081c8079440110782c2101480005040702c3c44001028441d912074580c0c007a2103040810303e40c2c19110f0329010407001c0e4500c804403241510410700014a5507090401682c0c0c2c24006601800445108071001e0000f581504041d541d00e038520b00958040e0030030a00401c114034010502401010b10034100302d4146080049989814441220904046440d00748500101072040c031007050042090b0030f0180c070300a10ba88940340e5884a100b4010710250001031020580c0004400382c078046403920100541d58444891a4a004244190205076651000f4049180307645061191020b555330407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 173142832 1250 173141582 173141599
    0x5010606020c010e04020a091208192606040b18010801062705070210090b040201020c010206070e1c061806051005090601081003170c070b09102001020310030210030605 74
    0x10f80070080254003400009080c4415a4000122890127030741040015006066031034072a107070800f03107040c41d0002010400030402d6817034580c1100034100d2a2420760889202d50075015075648004100103140b506038144c2d000100c0d0341d0510650881c0300c055416103000600034030003140d6039140c14903481c203010046040d0820b4209198501d01c55a4000380e03002850344100c80c003089480c200712301210382c443e909a0b010588081084195601004403524400c028401440d0758074100d20010011501c049084d8072423003252106034900c201c000c11444d10030f40c108a0400c100c0d000c00340560550405c4c10411a902c504000c0043c80d282d441e0f030030860488402810101407561004011100b40d00c0c0104107083c3d54000203008170107d031541e2048d00355a030040f030702242d0b81d9221000042c580a1158000c20070000104040031f410740700e00010035107800c403c3c02e001885900d102c4940d45008988039032107100d5840441040458042880d001d81100d00a58419490429004086060321002d000f0950481440c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 173144082 1250 173142832 173142857
    0x30306050f010f05130e04060203041a040c06030b010507050d0809061005030a060b0d12022103040507060c0f0b09010204150201020909010605031008030301140f0108040b0406231305010606020c01 86
    0x2c4c078002c0100c025800f0346034250580300c4d80d2071040400191402e0303a500350701004020070042d561080c81c0701d40a00382d80382200d034036142c1d41d1400c24414601481003010f86859022009034000c3c2c00341c940c071640c0a400d50f4001600c1120040c0404006c84540d001846440b000c00c020380504a60802aa04041c01901c0c7c040203c0d203600c0d001c0c20900500903040690181404081407521000000040195020304a0320b01000c840d075111024480e881e072220740c0c00700248000103500140e510701701e450364109000c5c0b488250414441140a50001520b0666894100181c1680c1035000b00140e803201c0440600708003607514109d080780501242203400c850309200500086004801450380070b0700342d003c0250682d4492040d241950800c1e440a02e202000010310110b40c0740ca4880001100c03401c0c030b0f144e07045140907203480804c1000540003600955907a40c1c01c081d1089080350760891088582501c1d09141000b2400c0040c00394080d006403280d500c1c180707000c904148041140b03024100140c0d600400743d581d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 173145332 1250 173144082 173144087
    0xf050c01030c110601140d080a02013201090905012301150809100b06040f06200a02060a050a12090b0702060906090703021908010c09150302030403081801110412030306050f010f 78
    0x14804590740319019600c6540000c10308001404127407a00e03070000c5208000ca2549140c034111484031070081c100000c2644550100c0c0111450444401000c0403a03032201c03d040150051003403015890021002e03070f07030300540f203130f80120020704980090901111403d01d5000c2110000e000380e50b5001c45030010040c1c110308003000d42010038410001800286007aa0b15402032201e10860351005010404a59002800590702800346481c0407000e4044c091000065000551354458842c600c02440320200e00c42e00c9040c4030f456a11190445c59504000c40149414104440f0401b200c10340014850309000031042d001c0031980d81d0084040c00020b0052600399420400702d0405052600f40e4100310314030000b44880d013405445001c2e5041d40354940000d00b030101e448d440082e82d03d800c80c14140100240030011f5482800039601c1000703040303881c0d010031038540700030302601c00d503036400294040100303000c1002079500c410364806510a490801035642d4410030306c419210004981408180380c00100235a260 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 173146582 1250 173145332 173145359
    0x114010311131a040509030f040b0307030204080d030f0b0117060f1206010b0c070b04030305030406050a0e07060206070f0207080a0b042105041d040c0b0904090f050c01030c110601 79
    0x300a20010003260b10001e000212025110600c0c00340c1d190741e040702d0721401c2c58892143c0202916024502c5c00803481442402c0344114070407083c01c1c1d280000020300f43c40c46513054801502489054504842e0380b108002c02030610081c400c0d00d00751520141440c0b42d8021500796206424905640072150b0380c0e00d0400030300034110340c0e159030000301c02c6868910b642c0c0c081c09060701915062410503220407010003090700c1d0403501d400c00f0b003c00904200500c00f007500141500c2e80075900420115140da1848900c00181c260703c01142c60b140720b02500030410b80e4000c6038042c4144400d0303070b403c00c00311441c0500b00e980301d00728461021160440011031010440174600c0e19031240c0144002c042c030f030485007010b1181c0c00d036050350ba40000f40302150070710140c4401001d85520342d580489910040c205500c4d11550708406d071040702900c1c7e00c0094640c4040e16280c0140561360380003800e14084096a0510340d4860014014681c00a40f50400c1440b682d801070312014002451040200416801c2082200504 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 173147832 1250 173146582 173146613
    0xd0b0601051c1401060206011512052e2306180102031e0a080a050106050324150903070e01030f0b0406150602010e01061a0a05030a09020a0e040c060201140103 70
    0x601801940801c0210b042c0aa42844080c0000d020b00a41c90007030000c2c103251068005001e0341d441c505e04139054030760140f4100c40c11040a100083c41e900c520190030144401640b0b103603030441c2100036030032100500c85110700454050070b40d121640b60001d98140c1da400b905c60034031039004505005a40d14041c05140e130290071041801141e28200343c00320300003925081c100036a00c10500014020451560098603180c120804d468180015418114040c0581c0402002c26214400ca10802c10440d00780300c0d809080010007504d6030003d601030001c00c0301503500001044d03009100e00c810004d0400155000700d81200d40044260244a02d41d03036a030480150040c0c01078407580c0d2540f114010380e86140200fa002807000d41c000003044030110071800e003501d0701684103440040c070780501c0c144002c40075000c5508140c8a03141044e40ea075203e07200300c0010039011001039042600030078041510800081c89a008034014464403c906581d1001242039881007003d1101241240004000180f4002e2244604 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 173149082 1250 173147832 173147857
    0xc01180603020d09061e0b03031314130204080f070e01141e090f090d030e0d12020c03070c05010909051b070201030f110306040b1203121003060612020a050d0b060105 73
    0x96000e0351903813010342c0c022030b680c040390011409501d40242003900c1f40340c0d02410300350040c504000c035003c0c012802c440e0901c10a181603500c4218040169900d06504400400f40304c801c43d00c0b2911001803d603901104410640c03184200000800c20400140340b0070b0403100586c500421101d8002c0c2440790710800450302420703507060040c079200d290340e6114245d0700c11540403000740e120f850034101c0e0358688100c09840000341171038040030306800c1e00042040101c880c0c0c00c2c1498541d00c42040201d0b0001d100f0382d61a44024040810020204080c0411600880b04241ea4250b030494450a14034122074041d1202e002c0350740702d6110b0100741c2c16860302400005005042c00603061100c070720000140c80310052080c1030b19400100b0030680d440d040c41804038020040d40c401600c4420240781035504d220f4044d401c040c08e903003c0b000a241581d24060754018603840740c01400401da44618011562404003c101e1282040030008035860038183d110707034085600303d001c10803282c03101d000550b0340b940290b014248 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 173150332 1250 173149082 173149091
    0x10509100914010315090e0a1203050a052404110409140406050c040609050d0614040c0f080712080702030c03030f0a030501050603060607060e011d030c0d18140a0f0306020c0c01180603020d 83
    0x45640c2c0402740002162586012030a403804040000c102d40c0010300d0300c0e0300580d000f0440341e01444076841c20044410182d40018422244800e8601c46000d80d03803000c800c5600b000200c140c22010ba0740018022803080f0010320a5864001c1c1c41c00d03140c0154000c410029100c03100810251900340c3c01d141050740503101c0000c011441840070200841c007104e007902c10421440c3c007000740c4100f8140c460014a6281c0c05444003c1c203004400c01c240072818005469500040b585c441503660070301480d000100001e003101c0d41d4a4080c1d000101c4c98211807403540129182ca0000212820f00008907403207008014411440c00c2480c2d9a120001c00c46980400711941d602c0b40021750b00c20f4585405a50450700d01d00860b1501a03400446c0d00d8200303008200700410030242d000c610549082103e0000765000180174141d0011800c0114004128680c400400d615032402d0010500426170b006000c103c0008080d690308180c030340b0056031810800060340034500d2807030030108070062081e40501220881c0020216 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 173151582 1250 173150332 173150353
    0x3140310030b070216080706201507180503010b13021813020403060e0712020d150c0f02010e1f110f0f030601090909050307020f010509100914010315090e 68
    0x10782d0444100c0e026005a030200900031030007600d03506010010b01c582c000600c0e107107003040d030010802c40c0e80e11064602c0303900c400c030b800394480802c0c001e40300006401c1482c40c107280f5049400401030101d0022628800714039510205090406010b44030078000040c0242039081601800b080081d8809034420310010711121101449994603d01600040782548025032201d056040c0f250407500440d825290315403140d44104041c0180e95480f910040d01120042c540c03641130305004042d4103a1341c113020003507072401c00341c0405190046030010070f46095134020014400c81c04070942c0c1e104040014150b280583e050800d46484e42500a000080e0a090100342448502c1c08480f589401c11100510000c00100801400f541e020b00c0400c02409466024030481086407102c945078850000007134000c00d10400c03041c0180e4019001c903940310001800400040129000003440c021a50003105a40702d042d1000448a45c03190085468001105c06441011442c00f4429001001c0280240381d04d03004060045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 173152832 1250 173151582 173151593
    0x91f0c03080c09031b19050d26040b0711030a170d15030c0e07020a0f0f060603081222030512040201020c0d050c04060f0b0304020f130e0307120c0314031003 69
    0x903144280e5078805d400b00c1010500304034112000204090002d02c96030410090340c0d980f0345428003500c1e0048201d4200d000c4001c52244801900d005c201d0404c00b00040004a48040710700a2003518001c40000c018050000109500d501580d04050641c50b4815110b18000b141100109200c11103a0780c00941602c4c0ca0f45c400ba240c04881d8425034481403c000200410b40c004007020f03074400324610103000c40d10929501d0074041d0702907841c05805922002284010406103a00c102c01131030700321400d56112a81e04030b00107074a800c05c8078102c00c1740c070001c2c000c07074a10101400001d141d55850384900341400c9403600e03c0c4002c0440288103904520429010a41c4c40e103e403110345d64500e0040c4081c00380855001f0a0205444160748a12204100700c44100503100e560340075240c2055044078090078074094080011a140404044030440c6850248041c98003a0004010000140314002e1f41040f0150702800b900d220003d440060040343d844803106000104000056900144624080d900140c4949030b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 173154082 1250 173152832 173152843
    0x908160e0612070f080102070b0f13062304050a0201120c0c151407090801150609170f030406050d050f010305070302060a14040303080f060a0f05010309080705030a0302091f0c03080c0903 82
    0x15405c0b0740d60009105c8180b184900c1c150340e002e00c103001c28000c54144610042030174182500060400e03955160000d00681c080265444401c0400201207402d04260a1403070300c544842c00e0417030104648148520408815000f20f00344c00340c1c0380e140c9c070a0840c0180c84001041400d2140b89559a0f030740e2004581d80c50140b000d40d4000e00c51951000981030030040325508485181c028010030199203030b005c1000302e500c600744c00d0030f5410346103000b40072000990030030740341141c014913040e0307507000106001c600694010040d010018520005001740c3c0c0f0342030f0102c2402d01013800080c14503041000103101604020001b81420700e81c030300d0400740110240e201a0b805403c203403c1100001c43c00703028008280215041690048022111503850780c0c40e0002084440c12544604c40c10300d5141e1190500f40580202a60180c940120a81e0341c0c648252800400130360200b8a0103208100c0d010b04240e108110615440044000d5211001d50034141c0e00c0030340e60b00d08010884846218204024040c03500c0030700a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 173155332 1250 173154082 173154089
    0x60a0f030b04050f041709090c2104080c010b120c0d230606040b120604020405060a0504090803010915060806060f2101032f0f010507120908160e0612070f 68
    0x2041d01141406d18260320788400e05040300051312028005000da41d6210054160000c40010718140d4507450030559110180c0d540207400e010012150400050014400013016a082448020400d50920004000310380303009007220807150780414480490360400710036107100c06014083c06034130400c503144010180861000010700f140c02070818404503041500a100b0210300450308103d45854070b107849d9603581c1005001910654546001c5251502d40a9a400c0034013006041400042c5507801c01091070b038028402c9603030041c5051900999503a244000e0401d507087d90b5201501ca441b1002000b01035040300b035180640c05003c00c040c0000092100127100200040b88115010350b02d1802d02e581031443c03030100842c0c00341d021900580e0030340c05080c030188520300850b5682c400d2401800100d4072402001c070000c00007844211740d00d404030740141c3c0150403a000e41c000c50f0ac80b0455440082340e081c2c01031150b01c1090044901040d058a00003080c0e500c81c14075082260441640c505413800c61541d60391 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 173156582 1250 173155332 173155351
    0xc25030905102109020105041a03041a060307030b0a18060c021605030309120102130e0f01050102010c0f03020c010e071413020a080103080d0609051005130605060a0f030b0405 77
    0x2084181495a98205001da5a080802040c00c210f0540c01c501145401c0041c2c0031940c80c01c41038110780c0214103907005440440e1614898032014442004140d0080e00c1c103580d0740c2480191080c2203c0360010280c801c8a01402409810307140d40c1c0c4118202c040070300800c1c00c2c00c0c0c0b2228600e8100350041d00b040c034200e004440204010002010180c1081e480203070900c07a80c44004424021071310004112080034105844400190410400d41350090040607486400031281c000005203c0e0048000b950203a19041c09001c41a40d850006900300c0b210a200c00001c03403030340d55040520502a81c050b008803003403003001149000203080c14609000713242e0441c11198460414003200c9040c41104981031b0301c244e640441c9001c0a848004c0c241050501c40140707071140001e1034035010406600840020b0651a20a02c840e04220603119100d2105004041c010482042c145d4105400350161308120f0b0390141c045850079a003100d0071104800408152001d0640701c1544003035a8a661290700d21134003608 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 173157832 1250 173156582 173156597
    0x140a0b07030501090b010216060c0501090f060903080c03160e1f0908010b01050c03030a090804091401050f010302090d03050906040b0301121101020a0c0608041505070806040b180c2503 81
    0x10404003281c145000c0e540c110740c400031000724500404200b0304241d274464104040031001924290740034003c039207001003d05201402d4641003106a80029090f60300c02e07200c1d0841750b50340003055411800b045420116104841c0c0518007030710b0007400c1c059490203000d050500b40f169548000e5444101c0158207a0005e14500420412201c0078884d02d6116082440d00e5450917188800c81503030713400082c141e6007880e40e4401c560020400d2810448000b403c8598050003100110340100400402c24401c450107a418400102d040e503110344220361440c20018185107000409840444842c5c00c012003850300090100001308001c01441e016500074800c5115107812110341e403078840040010314814070b05540c000003020000500030513088090b16080d02e880c08a03540c2c0d900300002e41c01c048450014500e403070401400280f591018980d44107080070345040c011500c54100303024a403042e111902d042c80c80071201142c0c1124541d8010701d24076146034100501e860311650407042aa514034000c07000309800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 173159082 1250 173157832 173157839
    0x1b03080a060605120f070309020a14130618050a0b06130311010c1703130f0305031008031e0d02040302031f051b19090305060a020d0b0a080a140a0b07030501 69
    0x9401100042c10aa00d0100c0c145901110303044070600c4c02400d01001e000d62100090102440780c0d00584003181c0003001600403c0d070740c01c1c01051010f201d1018502410b007104c103104c1c03038007900d0103407034100c82130301c0d0b440142280c2c0c220350301e00242400b500c04540551229103030686550342070043c1c4a00203a4222840c0100c0c83d624102851098441c9a64184801d0b0300c0d0940100b00e4022444c5090440c01920950300c0e40c50324840b48031079604100040c0010101040c950034958406e026500c00d12a07000b503404c94646642180d035813070080f03030202038140c16021500c0760311894200182005540240c1c000d8101500c9900090030051020905882014150400c1103001400cbc0100780d040360345030050240e5403045008480b40c1d80720b000305030f88600d4125003038149254402c0001d032009540050603107103981820f03e4214043d51110081c01201821700400344034900c0e10f40070341c4046648110040a0612203030303460300480401c8040d0150b081c040e02e44020003160003c5e51480c030070300f4186d9000031036604 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 173160332 1250 173159082 173159101
    0x2040c17190608010902091b040503160501080601031103150a09060905060910150c1505010b0405030f01020c062e06030209010f110706030e010e070b07060b010c0b010302101b0308 79
    0x102c580c0100260b03030501310a0380260b1a415400d9800815540c480c1405071140320b0f42c6c84840c0310703660095403d48180030001220104043c1000103481c0c0076a00c00c20070344c882c50b004606035000040d034880d460b4400c002107001200d000c0315052400c44041c11512a040d03560486c2c20844185e41d21120074141c44508104051034200d84040d440308415800c4003800742440940400454045a0318040c0216074100030301780020181018503038207103401c041c050b40da1241c00d10700e40340d005803203014003030b105d00046161132107810300a4400b040560001040a81d807441c004201c0c841030000004200811562185c03403001440c115400548440e84025980d0b80344140018008800203041c8000c11902c17100b80c9585070b4010421b54101c03205440c01040c401030110361140141000b40d000c10540c4a01c403c001402c0100c00301414119008440400581d564000152185503410400402168110b030040c4018a091144004d84049601e0040020528034503141104020500142d0225a044003007154200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 173161582 1250 173160332 173160341
    0x4030b0c0712022a280f17060f0a020c01020a0e010f020f0c06090604034b03030b0a081902040f020f040b070305041d040b010902040b09060d0b060f04080f06070c02040c1719 76
    0x44050580700340c0c007040040039071108c1e40608180507503000140030601e424120780565108880c010021542c2c1c0328580c0e0003502038800300d0aa00d01107242c08502d0b000c4140040340e00381404190101400d803501c010f9013081016484100182d03070140b000c2c8400300204454002c1000c1d0302a040c5860b071020300310341102d080e0706001c0400340040030a225078503500707415541c0100301c803903941810003040c3d004100740000d48100b1150048e0b40300f4400c05070701b45603500d42103c20072002c0d4001c0d80c00700701d0310601302960020380c03291500c400480d0340c00700800c2180105080c02050050702034549a801d05840d1f040340195a42e038203030a1545091070009100a1007500e0021600611014200f14503081c42c118801d0380e180106034096214180101c0e1208460310030f41c0104154040c0289403075940d03442c04004005a400c00d0081d042140700d03444141c0b084a02c00108140902c038162916040000030360308100c0035040c56004201001540300c0001c040c031950501d402e00481d0100710045203c0c0c4d04100810448 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 173162832 1250 173161582 173161589
    0x1a121e060f060a0c0201093b040c050d030216090902040c03050622090203010507020624030304090903050909010b0a020d0207120b070504030b0c0712022a280f 70
    0x39000c4808038549a919041143d243c0091402e11581c1c0d9140d07400180e40d840416070105900514224201e805081c0381480c0e50514085104404400c1141c0790254020030400c5030001e01040c800042480203141940014108621030302c100d40190910f85d00301c82040c80d8503032001c010305440303615103001c5280c203008051000c11107181c100b0403807404200284001c0b5004e11035540700180d0141203190035000f908080208e90700030f0001d0049040849000b0341e1490212003d20381c4200c03200d0801e505810b21000d81890b8a00180211f09050030710400c0402403070407a030211306200c8100004045030f202e90500c1030080101c0c07504541c9844a1034000b80c205418265001c0440d0403800c1c0c107201080c410100c48040a0b081a014911641c0d120b2055440c0d11694001600c3c17040208108040003540301c00a0610600c50341c40c1e0341c0d6920485601741da8820310207190030602c0103566294500507520396400c040c0c074900140014452010b9481c4056196601510b00e0341c100102e15090180c04c01058168004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 173164082 1250 173162832 173162839
    0x613090c0806061c0e010e0616030b0306040b04390303112113031b05030d0306050904021311040602011407020c060403060f020f040b0c0601060e06041a121e06 70
    0x404400c8081c4c3e5a2404030780148900090395407600441d9110254000110040070780100c54260900d0709208048203040c0c0c0c4440d0000303090001041181c140032031103500071644000d09404a464a94440c0e040d9105040b0001c0c168581130004024841c1c501200000b146140404088040c15410000c012092900394a03080d507010888500c5601c0380445200e01a0107640d626940fa0701264050142c1e9201030350014284165080c1c3d9000100d0440b1018000c8410072400c480020581800c25400d86000380f25250b48640400b0001d0098280150000302d801503d00700001c2c10081103c8036070342e039009a000381d40180e5440d0903503003215400041c0740d40c010345a40010003801000f00002111885103000044c01d00340c94010807459070805d60140d5000480c0700880c2d03516681c950007a0001070300700e400d00c0052486248000038082e8040d085171013800c2e6015092a24042c1441505802c00240e18000000a60100060f4681e0052000654019a040310040b0808603011405181000303000c1e2441e4030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 173165332 1250 173164082 173164087
    0x181211060105010207031e0501060f1409011203031a100c1419200303040909020315011a0901020705120105010501090819113106210807020613090c080606 68
    0x107030b1380c000078034108036a440241d00e03c08800c0d002031140d0040050500404541c03d150001c150f8900c3d40000b04184c035100440d91600740d00350030030003103814003e12070f20104140c044008004684240c0255040203658441c3d6810f41404c400480d054200c1142c0d180c00203205200b101040100b0010f5080030300c003404005220b00c03400402d03e4140419001001000011030090000707609101c01c100514454008060f0380d26103079260085005049500000c83c400d00034011500e0007202400b1205050b6052428200e40d1519031100207040307540078070781c10341c103620603901c002039907584000082111f00500c500115295151100150594a15400441143d0070450301c000c20901001400f00c0781540003000707d21900301c4080400c16400c4032440000c00c11178030f001c0701220b44920740008007182d4048542003007482e658200e005800c0d10031004d03c4040c04002174440f0003094074140600748050000b001c0758908480b42d1012408102c0951083c207a8070303222508501780740d0f0403807111540014103a40452 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 173166582 1250 173165332 173165339
    0x70905030f0d0809150702030403121803110303370203031b090f06070609120507020d020607020a0b040306150510080708040507120812060f03030a05030a1812110601 73
    0x9071140b01401c0301d20100312028000440b00f050400c140110352201c000303d04e030f00f070900660003034403944140815504903400f00300d0112158455052181c0b0718404c101120740031030031540c401c03003401b501900145d4588014068200306054a0510f008c03000d40794000402c4c41c0c03400785156039580759001101000e54205100300b00d445e0a40a0822042c1c94106e0310080d40da0103030300e0000fa240b080e006c0740748d5002080800e081e4204001e07039204401503030203150581170b00ca000d498221000d21840c88000e40103009400204014185800075140e541e10041200c0344480c0c0705d035549881c1fa00300794400c0e04c03160384070100303004c00c000c0302d90101c00541800c3d40e44017590003900d0005010311902402d1007041044400005050010038000fa0000d00b1031070326625003200f194203054000b600300e81c6101c143d00c00208045007041c03801c1040d001c0b0540010b409117007042d401940680b5507803c01010500c48680361a181d40c0b1094907011170340342c0e25126030132200001d0003201c070080c034000074004010320b1a813040c401803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 173167832 1250 173166582 173166613
    0xa0807060f0e041b0509090105030f1905010b03010903090906080a030c110d02040e03090108060303040608010303081807060804110405060609120a06020a2a08121e04060507090503 79
    0x71501090b0510704681240e04011900510034024903180c81500004400c14550340000204085c4804454400003a40c0314010141c94102103801212a81d000180d00e20720407030501c00d030141d11400341000042541405000c20309480c2c20640480000b42d6890051007892585d104500190203003900400410580303039805096420b125102911040000850205940d1034000d070a155503070251080c400d074080c0011903580c9800460402d40400d02200005040d800d000050300d088907520381d60600942d18540b402d80d540300740a4000d00e061222115000340c90318040110000510303d07a034800c0f10b43d2034a0b0074072917070342daa4010f07440c0e206504110a101241c0d4843c004c1c1e61141c40219003003524441d41281d1545070040300d2800602c07542c004140341c03103c1c4e81c01102e04e206070084c00c032600d200e800c240480c07110040b010b0f200c004e15104050199281d403401c02825107038040c1405418840040d9900c2d4400294081240c0495560f40c482040003400d43d070081c1c182006160684c002c020314030441c01007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 173169082 1250 173167832 173167847
    0xc1201061a19021902011b05070f090e0c030604080a021507052701020c1203040e0a020307080105150412020f091006030e010b0a03060207030e090405010c031803021c0203190302090a080706 83
    0x61304000001501a5481840347c0702c030941540c0c0300044407030136561401c198490303641501c10030701854070b03000805000c9a030100760a1807a4030000c010b4002a5140c0e9640072041d0000f244031310861250810003402c3c041e980c0c8100740160102e45030f25031202001b012000400182943c2c2059401300319081440316600001c154100030412601c020051408860640c91401035501280350340c0d5240c0c0601000c0c040302d0307000314010b0360f03141e480740041e0380c80350180441101c0f100801d03140c0d503000300020003400c0240b206081d00f051000f060103c1200c1800c00040c0404423754141d0b010000003902000019010303c181308100f084c0100a04c103025640000840100091001800450300061801c04142c8500d950f1035003403900800a00d290700b094141140242006142400820f1519031030700da803c855101050000d42d41507008113642086807488550002050700040258441440440e0315031040301500c0801c545965001030b00c0e508180b00304501202c039030340314100c13130b0f0800701c002d00c05980e01041d0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 173170332 1250 173169082 173169133
    0x30203070b071206030c050306060103111902010b060a032a0f05090607080408060912040b03010b0702030c04020a020a0c090608060c1c06030c03030e09090c1201061a1902 75
    0x2194007003507503844000d8540c80d10201103068950715090010040140952041041d40d0040d02100c81e03650f80d04005408803038400c00c0e51500310000744014822130300a68441c10450300c80384000300700d00001a001c1400762304401d2184002c00d4070b50081c2211980300c501c420100030310720700c21900780c81f0131950040c1140301d18105000400c0800035048031951900c0080b0381105034070403040342da950b0340d0702d03c0c0c2030316135009940b500300c1e0b402038020014004503030310151403c0d58021940b2a16592070099400b101c0d0f4030425049805020300c0040148964592015240c0c000301e80d000f4000c0031169207003442d4138100300d4201d421aa80f4002090203080c0700000c1681e8003813417030003845507101d509040d610841070070307003d250311000c1c1400000302c2000094216541200c0c80380e12501203e01c401d4080001d651411201c001d401c0d80003070003001e0700d450309042c035014841e4481d00000e6002d4607400380c40e114a00440c04403082d6540014454882484900c60502c03000803440074040400d040d183d0000c84406070700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 173171582 1250 173170332 173170343
    0x20c0f010c141606020d05040b0406030e010b0406030501060510020a050a0b041406010f090501090b15090609031006030218150d080d0c091a0a02030301050915060a05030a060f0303020307 82
    0x2246001003102d0840d003845004280400c0307a116480401641020003094081d910040c01205800c58002d40108155005da50f0340c044102d0a0a0420800700c00030020358409208664941900c000243c44500c00c40004c0c600400021811900748018040d16901c23243c03a00741150b00450b24440800c4001c120044031070b0340240c10040350340f04c604204000c050200200c204e01e010348800015880d0002e07911400b12045e40200340441c2c0c0e0399400384412500c1c5000e070143c10011100c1c1501c40c80000000410f4030840003803646003404031480109140c0800c0308901048070780c2d42c0600780294a44103c10020719203107048541c0541c9800d00360f0218149144002c113004c1d045000421003001b00d100c0c1540d8800181141c10003c00003544402402c101d158410414402032645991442980a4080f03c0a0b050150000d5185900c0c1406201c240030000b001030541d01d8442c4c00c5004580e5912000b400c10501641c0c403161a030504024401c201c469030381c481064080309500410029030040b05a8410a0700708 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 173172832 1250 173171582 173171597
    0x9090c030c050d0c0e130503030f0103030318050d200304030804030c05040e030403060b04090b070c03390203010e03130f090b090c03100e1806161e02010b1804050d020c0f01 76
    0x2d11b1094001c540d58400070414040402001005804480031504881c042d0390148490300381901407000e42c3c000a4001b800a41200c05002141070103070840543c0e0b41e049501100c0c00a80f480501400c5801a42007124944000601081030120b112004000307440102c8007000b000d510060030507503e20951100802d05902c440004440b80e80d5640040740c020707040543c0111074500150020211078150340c0440c0400c40d591791200c010500840809205141400301a00c0210392008401000100185c22a407564a9152090706001c092010b001d0f030769940e0030f4070701d0403908101880891500d40d40160390318501d1f0400c140030130f9550340b8145030011248108240d490711682000444184c0e260413482c200818041440800300180c0083c855480540f0281c65858a035000c04400340e0a4035060440042c090740007107400e50b0300040c60342103801c802c0d000000d2008011004207142c002c05d11603181c144042c000400050003400c0c00684c0c02d007034062019283c880e100f80d00050001455940d11070400a45 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 173174082 1250 173172832 173172841
    0x52512060603080403081b0f10111b0106050a080f030327060c04150513060f020a140c01030c0e1e040608010615030b09090a080706020409090c030c050d0c0e 69
    0x5560004002d160800c4450365500d0b22401c01503403a912030b030205c01c1c0d0400c210307014007046000410012502c00302500980082050185140081c0010481d002500a001c10104160320b070304462aa013401c40c61000401e02500d800e003041221141540000740c250440540041d501d0340c00310480e507102c40168089040d421000e20042442c0300d42c40c110141500c141024041e0030950b00c0040c100b1182a40d074119000e108400302290140a405908403210030401018096907001d0301400804a0f6548110ba0600340755488a80268031461a440c0350fa1704401920440b65030725018108040e18a420114613480710036005c600d071040c0310405c90a1004c04480b0742034090f512a041100100265002440030a0716060703207019000010611401203880c0c1903410314941400800d444c0310342c00310006030404218980703440103254402842140c141d07900300000718045803203101e9003030018024060111001d003075140c021011082e58001e54420111048000300081e40c0c6400740341942d102c1c94100d0b5140e244c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 173175332 1250 173174082 173174093
    0xf171210140108010e042d0308150114040e04080906030a0c0e06041805040203030409060609050a0f0303140906121315060f06110708191b03030509060306030c0a0f03052512 76
    0x400c016082415100184c4040c1980498807500071450302b10703400c805000d150010f5a0380701036008000c034002030034002001b0b4045006445680680180802e03864110820009039240d44210b0f41e4101e140c3c1e444034415202c980c4011252420101a21010300d01070502a201c450400d07007d04400c10741d40c0b00c000180441d1001c0c01a5802040781e181c0a1102c1504d40300054400c040d81d02403075014481030341c00005e01e4100002030f94101c0350152240080d4070f889204c2c002c0319520401d03119030421001c00c005030380b185400583c3c40c855118101e000900c0c00c050715040c0303145016403c2941009080550510504615000020072203010341814864442d02e40020740c104009503005c3e500f54000c0703e5204041200145800380c1d040c0c0b2454500040c1c280302c0c1001c0e41001d46502000d000180c00384048400e0b410808001e54121038000c045034803003c8010000f1b900d9019a0700000c840188621041080000800c40b01010341e81001052035403541c00c080201c0d82103540d1180404c0002042410018400c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 173176582 1250 173175332 173175383
    0xf0210090807060201020a1202090117040c030203070e06030d021b06160803090a020a09060b0904020c01091515050301060308030f1902030420010206040f171210140108010e04 77
    0x94000b924480d559420002e03000750010034807040410041d0b030307036110301d124244200c0764a64416100c00e091141d0301d080040c40083c0c001e20407154101c0565000c0050b80d800c1100100a00209a016006213003c405250074a0f00c004103810540d8000b418241100e246000b0136071003023006071511a181c082500d1200400a40e100010f0015500001800200f0b0b40205401c0b0302c07a03001b6503036803504c1c0e0790759800d030000c8510340d11541100304c0d41030090103c0780c41c040d0001c0c40c281c0d00300da002098084030b40c1c44034410b000211014540f10b0b0b0707813200780c10900d501d007100100040c94224001c22803036145442d40c00d80da00c40180150000b0101e42e0000d554180240030f125486045140119143c0c1703490700d0003400000405046a0450f84d00c0128045550f02c0020040c2c410703030b0b0002e041000481a40c2e81c0c0840c00503100044501c5510900c44803c030140c2025034207100d100c41030f076246140b03880c02240106420a00522130b0400c140c4c0001032218080111449800540c00501c46101d9071100b40b0070482301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 173177832 1250 173176582 173176589
    0x309061715010e0a150f18230915150c0c0405090a120c0c09050c180102030c010c0302090f09011d0601031812080a0e0a030503130f0f031b0f021009 65
    0x403022444c0807031a101c401c0d801c2c06440c0c46544800c0100c3c1d0743c3c074400307a079802040e00300014000b00060060288221a015080056541c1600c060b1030004640000e2142c0d0030841c4c540b501100c201c240090585044490101c0e41d110300c484081c03600004100060300c513811080343e61700451310303800401c180810412526036410b412003e04c81e10b08801d42c100070018066404260303544001094041080c0b4080d200301130103245101c8205180001c401d000744d804000c0c044030076040d070005100444044400703000700c803140310300c9560045c2d4401d00181004a909400b845403402074492400500c160f503254021141d011011001d440c25950700d400c0100d0282811b041040080407600b0550030400c0500d4040600c600740c20380711000160f440d40d80d100100c13034050302007102c254400d4503600c0c040790143c0000d40d005518000b00303da8403010b1751141808486203100840c5d01c032030512043c07001e1650080103401035445c10900e181c5100f1503a01c488044440e1a4030192282030101c0400354258001e483c5080107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 173179082 1250 173177832 173177839
    0x61404030206131a070b060301020909160201060308030709180b0d0f081603031a032b030605120703051603110f0102010b0301090506090f0a120806060c12070309061715010e 76
    0x6013050800603260715080302c54101c0b00c5400c2c64001c5002440c041c026070b000703200d01a10011a9a840e01e511603816180342c042c180c195541c0d6980440464075072401544124025101c60002c585081004140d250813451124032080c5003410881c5541c0d1864504480203800c0008001c40035500d00f08007509110b40091401022a0300101c0c10415405401a4544d03026041031119071082900526498003141c011041c099440c00701102050087e8490301040c2c140a4540000c0d00c94940c004188114080740001d130060b4098141003041000410014521443c4030340000c4c0d10500c1c2d07039110b05461409420543c89214040706a010f5130340300350f0021451000003070003030100b0001403d1480d22504151505c16260161010a03070b141d8400041110105520802610823042d041c0402c0358501c0e00175100311391140d0b080040507a546000c00c1030080142e100c10b0704640d104850302e0042d03c0e0700056072200041c0803404e80769010f002050342d00c65034001c0305050500c0540d0300e131000489046c8442144941d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 173180332 1250 173179082 173179109
    0x50603100e01090b28050402031305062703120705071a070c050607030c050306040c0e0306040b0f07140a0c050106051c0c0509060913080d050408030f0106140403020613 74
    0x800c6003c80d04502c802d06000d0301c40a5010041e1114034580e801c40d440307010b0f0009043d20003000309040650040d07034003a50042103243c0800c02551503604100b82a030b2150b1882d00d010f032000c40130a0310b008810b05480001001540f0705a0000c65050000400500407800c0c030802140500c14000000c00d024544a0913174034894591410b010050066082e254043d40d04c2c0c4524800950b40900a01c503802e00d100e11a210f0710309541d14041000040c0c000c5030b44040400c4142126103040b40c804204050096106600042d903916100d440008142d40c0100a80b00f00040c0400d10009142c00c442151000c040d1460140c6010300c99080c81401b510407640090b800c07003040d50080c40049101502202c000703104005900c21955070f00200301e1456802da40259101c4500400704402811801c0c205c903103c0d2080115a00f0080444000d8080340d90880f000e660360700d030020800014056800060303024125034145110102d030b01c04590764840c000d60000a00600c00003c6d90b15580c203c48200400a080c0c413a42c101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 173181582 1250 173180332 173180339
    0x203100e07032c0706140f09030a0606080604060c0306030804050d0c0b0c070e090c181b030a0501140108071409010903081615140a0f0b0907092d050603100e01 70
    0x3140b407420303c240015030241040c00b04034144030f200803032030701100040404c0c101111250050401d038098800705501d0b104058071107001545502440c0020548a009840340380341c1802c122040c2d8400c100e110003050310344201800064000003c2c2ca041d01c00c250307241d040c921113a107030400d030078001e40d004145515004100030402c608005005415540509004c000356203071504000e945111410001d0384c8944001108102d1482894500d07034440c0100c0c403040da0b001c1180514245580c02035804251103501c0300010301c8030030040340e0008205903003132801e4881c0340751034400144284c0300c240d40c0358100c140c002426802c0780e00c5203850308003468000030b1441d6034480c07060340e00403100e41c1d0315001c40c1c9109127410955501c50b040e00c00c0b02e541c100310703070b060b03280c42e9a500d0901401801e44414460680f07666041c4064551509009148202426222149010b0901069585000741400c40d15203603070301d0001c000d802600b0130540c202162801c1d501152280c850300302a8104200d56008148040c00500000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 173182832 1250 173181582 173181641
    0x90103120c06110c1e0d140f0403081201081507080a0e071806050d050c0105030a0f05040b06011d030309040e03090d0302011a010c0201020604020906060f0706020711040203100e0703 80
    0x400e048000d1a0072503041c022000302240c881725411079555141c4d08000c82c091030050003a40c0032128001445601c0e03140886104480000780c0090f0000d030346001c0041039105450b90b2002540380900f4251005020005c401102600d10701e0700200458200300528011814a40c004d400c10f100c05540c0b0702c1610041500c0b07412041d21b5484402d600640c2070b0a040b000106418000c15001d485078010020b4075140b0b01c00d00066440d5800a800b180314166150380d1124040f9261040c0e0f40118031612080d032003810000001030402c1c5c0080b060a00d000b908140c104a981d4000044404481c01581c0100b2a2092601c0032170560080007401500034008520301010141d0650050700395001c0884402505003040004684c00301031300200902690080c00450f0141c41d08000640c0d00c110010211843c2c5940c0c505005e1823074115400c11601d460700415118100310712060044041401035600f14110701d00400c3d040d0070aa401c5c464146c00328145001f094120340700380c01211500f030070240b030340c20178600714240c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 173184082 1250 173182832 173182837
    0x9020604082413030f27080c09070e06040320120a030f0503040201080c03090703080c0c03070b07080306010f0e0303130302011710150302070b100608090705090103120c0611 76
    0x6190702c8407803500c0001c4a20310042d0014902d0f94142d565a40c03007030b02e412015181c80811410540180040700810061085d08050040280441c0d40c05040389503940c0f804c1c8200c0060150000003400340f00f8000c0300e0f5036202d0006030360440e600840908128042c002030a0b0039420f24410440e04072041c0041341c0c0c5402000a14502d40e20700c80d695540101101c21000c031414002a50000d000800f54000700c1d8004036250069034200031000103842c03466650769166803131a40441c00d0610103030048440c00d01107240600c081c01c0184111594240b8220183d601d8408501c002440320341031222844d80c24203000c0c4555804910700c0dd000d811a44d550b4008103803244c0c8a10749200403400101d90820781407514204210040c003034080007188900c1d50341803904800c0c001850450050401d83d0034070aa4012840c0f8031062806801d041c420100e4180c1800c0340107200b01c07801030420006074000807040001d5195104014116030b04141c4040c1e05403480d040450703031810500d4014002504000c060401203044800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 173185332 1250 173184082 173184133
    0x40b04030b010b0901050d090212070303080a0c02030c12030c070605010e010317120a0b032103010812070f11120d112812110f011b05030402030606040902060408 71
    0x1959001c50781da0352440402481492502e50000c0c106001010884100390040c0c000c8610081c8400c00d010456000d6526000302c070750042d00080d40340720038003603107013400d11035161032518901c003641c900002d08032200e03950a00c100c4079903841c800001c00507143e2041002600d041c3c81e030190040c0030a5070344414440034110203010550304595440140e61614201000315000c803214006401da250350382604120050400610340c0385c15020700c004101450210141c20003801c0005001d0700c0c2c40b0350400c41d100d031400f4000f18001c18040020080c0100dc02c0e20401090b41003a884452840a212032202042c0c2410501c0030004061050802d1600d2aa1308413455080360204503003211040c480ca80e2002c61070b43d035690784482c0094401e070641d2000c101c0b0390180340541e00180c10310345c020403804140c5520304600d480c0c60100c1a59640c0201d5844d4041e141c1441d1400142c0c588a41507060640010341c0300d90015203018400c50b0f580000d241151250420784008201751800d83d80c1600418400410780e040010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 173186582 1250 173185332 173185343
    0x1090e010f021612090506120907080a020a090b0f060403050d03050a060b070303050a0209060a0207061704030f120908030a0b01030b120705010513080a121707080705090103020f040b0403 82
    0x4100c050300840d503100350f6442101d1065030400000140d00d0741c41c6540350303004002d000c2000200d0013040d1501e07503400902d1010f48444009009107001d11000b4104480c581007030016400240519015944d40e20300740090364044500020343d0003c0c0c000140d290701c0390010785e50300b100012800100348200450a0f010038100303034078240301079551070744400308840d1107004841c803501080c40f402c3c0111b482540540c0d8015484100145401001000074001e50424241c050043c1c2c4500001d210041c0d12520020401c5110200c540340c41c00d00360303809401c0074054100d1504211001d4803011000e41c503608104c5089410400c455540d00304031306110080c02c0795140d500c1c08203081c00760442c2c950401c003040d45840d22014001d050f025040072300441e01944108045400c07041071100c04504410203004115005200380c03880500d521040c40090043d546003c080a020082c21007001807994100c641e1a52100f254904a9918028680181c0083c09081c240000e406d002250110780d003801a03008009407070085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 173187832 1250 173186582 173186591
    0x207030c09050f250302070503090406170f011103010608041a04110f0105070809090c070602030a050a0e0606030c010f0c0b010b130b0309030d0f1d011505010e0913051501090e01 78
    0x25001101d450f13900c0151000130490800c021501e00e105c0e601404909120703805903840e005030140014155040d5420115a1074081c601501da9007c0400c04081c01030102c030020700420400403580f500c0303070005208610501c001c58001804000f0541c1172040e1582080400d0542c03401c0030701342400c10f2804204c610b40030b0b010292080300749600400647c0c00e299071150a0074070f000b8040c020302030460070103080d4403811541448134900003a80e50014500ca203039070f901c000446143c45204041a03960205602ca51500004180540c5440116044960710b0313081c2010b0001314042c01c011104821400d4003d0840d03418440081560071300d840041c034511a401c1c80c40c08096840b200c941c403003072005482070611684100514002410140c11402840c81c68040c001442c00440025400d61421990380d00e1103139660b140e0a24440720040c08040181c5000e203401c04112000402299610101070050201e207100c0c005800100038041201035522415640050420b582d140c0d40351001c2c1c80340c2c0c405000b5950a2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 173189082 1250 173187832 173187841
    0x40203060f120d020618070902090d0c0905190204051804140d0801030507081203071d0a0303020c01030f02030c040302130921022505041d1603050c0d210207030c09050f 74
    0xa20900c6c842101c07010b006820101c0c40c1180f40e00003584421a1070f40c114a01440e6000801d4851507980c00900071950007003030302d00c1d00b00b1a52813101181010074407113510510050010341c0750042c02290100002100d10459101c03070504404e40225101c00618030311034030302411856a440444503040728411021620240c0e100c042054a030300c0400602c01600906000084480d842420360700c0b444034426820800d500c80c07000106058010540090380940d00400320102c46513854880c040d141000e00300708500b1070a20389940c40f10f40c07145110103440340210541400700951a80d0184020680c04442507039000d219401c02481c0002210340c000c094002c15014034004030314012401d075009190400e520009041204010080152607444841a80c50002c0702c034a0707207002c004280c5000c48466001c104180b441c80e107503181681040925019400c0710445100003201c160800e008003100f044d42ca10041103000c2c0c00c0f8a415900d40c4013602202c0030900000c3c011b811940558050480c02140324840d680303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 173190332 1250 173189082 173189101
    0x9010209010c1209080102210601030e1c05090409060e120c0a0f030201140a0f0b031c050304141005061c030e061308120406020105101202040203060f120d0206 70
    0x1a42006602007140305000300700152056600400c43c820600f0408102603e4884990880c1c000300440b12450300040341c1900a06242e030101341d8408c50918041c071a4000c207103c1a030b103906000c2e082c2c541e52280e9115031204c1901034000e503001910040c104011000350303810407030058044010f0740d001c1030245440303039170101802d4011500c0023044040102840c1d05d5a40d210811004402d8007a0210755951851030008492501413a005042c203290100320002e00b0001c804c221140400710522a034003200c50440d800070700781902d1403240440e0501d25242e68480c140312925800e1903811a00c0b6000b40d44840e0101c45056020034041c8005598118140c0d00c00f031144104440d040ca070280210703620311154000351508900410742007074050244c003038050b41c03174021501c0c0070b09040820b0108030b000b01d0240240c9a09116090b80010308815041101c0c1c9401015405e800c16a0400f0f03026580000004d070090f1515082e01d00b500c4400b803d0031440c8604050840d0700e86446612000041c0901d2020030401c29 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 173191582 1250 173190332 173190337
    0x6090c061b0803060f060a020a020a0501050406090e06030f030a02030a090b09010e13150803030402031629090a060809100608030d180803071806030908070206030907050a0801060e090102 82
    0x4440c0d01c8018000802520360140e1600300030090382d8800c803000a41c0c0201e84449000e041107100c0e540090024941c0b43c8100b208020080d00801d04101091101f0804954050355500407111642190b40d516150704000c0b906040451220401707034031000847d001020b50000080c40c600d0080e07903844c52166242c17060b20410784507000300140080e040742038640ca0740c83d00804644d44005039400014110005402d5400030040c0d40c1d202900304d420200c100025420180110b1480c42011501d08040d5402d10310f200701c01408000403481c0080000e40401c1c50080b040c0210b1710383c2c500040042100c16075450008007481070440709016207000c1c4524058041456000b00300664000c40095420500114138100042480b80300d11050569400780c000003086940000f14060045507841c1d0540050016142001b500554801402c1520b800702c00001724000c401900c0789140c1c110382c129641d460b4030a0040c0703000c00b5070304207903441146030000107020203055010000311a240c1c0f05460a540d580700b40d0350b00700d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 173192832 1250 173191582 173191607
    0x90b0f010c06151703090103112a0f15091b0108011809021201090b100b0403170d0501080706020c010215010905040206040e13020a050d031d0409060906090c06 70
    0x40480c00100d000a0007508501e41450001c610100d001d5510606a010b50001c00c0c0b96513450341000aa280300d5507458014207812948202001d494000a0289a903006107860314100e141822034030b0f8881c0c014030130304c2003101c003150481c229200c80c03100b0403400800072000c0d10400003910498a600c01500540d20143e058084161141c490581c070303207249407110503540510424110b54884960700144c1c0c0340c074020051020100d0000590b0031051130b0004d111140078100010094070603c00704440103d190448003a00e500c490201c0307620018020320042405164010702c0c1440c146400800c6102000807040d044503001e81c01c8800180da520300682c1c85514920342d00c0c84410114005002d420a15000f2036045071021b400d82d445c099803100301c65030034801514414181200d0012000c1585854213500740603000450301c415180841303942c0074001c2014140701000e003220382d4000c90010b036540d038000f80c0e0550300010184003a40e61850080e0081c026081c04540d08131000e20040707a024482c66420064 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 173194082 1250 173192832 173192837
    0x4030b0f0a092423010306150e0c0a05072109150e120c090708040b06040b0d03080402210a050601060905010c060207050c130b010e010e31020304080301090b0f01 71
    0x101458402c03011121a00684400070064441c20402580ca2584d1a044010300e0502d4048a143d4114038044045d00c0c0c80ba14400c2114024102c148010040d0254081d0042a010442a07840300b002400780c840c3d00600d0341c041d05042d0407288180140b0503406800400c68582d5072039030007481d2111010800300701240120400a46003003ca203949051008c2221440901c0b0700844803509040400a00261411920440001c154005000410507240c0e84290010002c840038000d143c0c005021805401cbe0b003a034040d003003119035800f080541d210b15100801e60044412801928030380351075510750320711030520101c40c40d114840c0000303441446000140b05654050303645010203102e5481e090003a4102d0701054945004100000f002e036501c1e039444590596603841c020481f10b04120000d002c0d900d1540702d85040c840100d90005256868a0b00c4514002c41d05a20741c00b043c41c00810508880800c40102203424800410b0009100764000a5812512a040184144030b41c1900348005003601f82d51482c00b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 173195332 1250 173194082 173194103
    0xe060c0d0605150a030b1f080604110f1305010f05090d0f02030f0a05060a4209140a0506090c070302010902090f090d0207060503010b09131401080706030203010b04090c020a060204030b0f0a09 84
    0xc01e1849041081d030005001080460341403110f5126601540c860345604cd05e1100c0051a11402504400b98400901d400d0030034000c00344c8001d001900ca03104080c0c030b0505c01d840c18070b960410041040d0318400100d401030101e43d81e603402c9209441da2020030a50581c0c252080c0c6001681407001030140030040455100324038800321002c0000318204101c0100d58241c03030f89100302051880c013002c03034400080000c00f8000c29012a144030070500c0e140080c0504c01c3c010b0034041080301c0d0303444044003e40c1000c00d007400c0a81d9940d0703a04040b401092240e10096005c1603000c240450110800261802044403805444880c1030403801680e840c10329105100210328280010414402480f029213940c0748090300c44104103c2201201c81261484a0001e40d680044001407203086000c0002c01e010380b0703143c00d0031031655052140100300c0b40640d104040b0126102c801c25030006100b030160640703841c1d02c0102507403a10b45a2401500d44141210101c110150303c10000d400300ca1035008112002c2d4101d000d062 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 173196582 1250 173195332 173195389
    0x11406071707050708011506080903090f1035070f0e0108071b05010e060109020403150203270d08130b06010e060c07090b0f040e060c0d0605150a030b 66
    0x1904003500c1661680600c0400003803804d401e0241c5425a0008590040101e09008e4040c2041c0400781c49805564006e118180c02d076110149802000300c803c4403a040440d10299003103880b0100391440d00040700d09080041642c0380041035821036044d21603003021060741c83c0341d81141c000100341143d070005010449140010b500500240743c0000840c83c05000c51000d03044010100c5281d0300c01120a40e6540110440604061062601501015070194071b401d14544441c15005840c0407000c1040d507002020982c01140c201c44a191010602c0402c40e880b05400040ba4450017900c110ba40400c02c40e1700080c004100366250300300360ba948140503550350f031219001160610101c68000340c110b0802c21490030184010804100108403450000c034074010765100f40095902d01000b0180202e060150051190b0400f1584903032003048016101d40380c81032a00068081e004640c002c2c2c6e0481c50ba2010f8517001481ca900419404800340c40a2041840000611540c407128410030a0800407000310079 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 173197832 1250 173196582 173196623
    0x408071413090807020907111506030a14010e0604050a0b150105180d0b13031b0803010e0c09060a090603150302030c010c0302010b09100303080a0501060516230601140607 75
    0x10020b075400340c5195410300b00c295000c50700e00300c0f05840000200300e2102c0078944c0c06030200140c008200c681c041d2000c117410000082036817031519490082c111100026062036558003544048000c111890803070b5824101824007a8485020000a80d90803150304001409500e800d8007100e03003501c0c180c0d5214981100d00d00181e51040500100c181c0c03000c142d2202030041000e42c4683c50050103596a0a400380c070b032914001c0c3c0400d0920b001514142502412200841c951005403411a100c210000e039803960b420030502614454002c80650041c000324807507040c030b540f01a00c50306903202a201080015100e070705070100c074410b030b110080d8190702c11404402194401d0441480c114880e000210f01c061441001170419881290102c180e01030501b81041419802000315402c5400060104801e5040c036000908030305c03410580c4400901c0c880610010400180992003c240c001601030340c00c2040310707050740d403158803c1c0700e046403c2040b4440c2541c180390007002c0344e144641c00b401d800c1008422940a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 173199082 1250 173197832 173197841
    0x702091806011a16030306051908060403081008030c0a151e0b0406030204021b01061208030103030e0a0b0309100c030c0504050f0a0803030106030e060a02032404020c010608030408071413 82
    0x43c1c5101500303003c81094071010441d0303808880d2007610301285060134642440001c6042c0c40807990044980c0001b0400104045111070b040f40e014a8001c826980354028466080c0302e0798450301c50391000040407109040c0103d82d41000500ca80780580c8075040c4551420103440a000c2d807201042560424010302c2c982c40d80c4035030b02c0c3d8000600085400365032a00018100c1e008486481c0d4602065641c1c001c1000d002e20466000c0c2041d102510f409008940b900d0300310b0f000500008050214603148603650390b0761401b04100038030360075584594a181c5641450341f40e136035010a50701028188000100300600074010083c1183d1186c1d074940c10070785080304024680006140301a008900c003940455215001d100440c0070700b06545010a542c00307105185440d0407401000110094410310502c50321070180c4001c04217100380b500104100c045031100060003445070103207038045586400800100345202101600440d035080064460306680c8559890081413054101079021201e00002618039070f16500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 173200332 1250 173199082 173199119
    0x6070309060f2318030706090212210a03060302090c09030c03070b0d050c09040e0a05060106080103020f0108061203030108010e1614060c01020705120403020f122a03060408070209180601 82
    0x2d8000300710034560805c1c1194071040303041c2d4400f9118501402542801d00700c0c1c07085141034500a001081103107220030314102d007844064250260000b180e5910368465040400516001000c90110742001c0302440130640c00b00030543c3c0a4080d810b032001982c500850f0010449107450106442c11809218210090000070015420900240420724441d22148100014070780284010814200d8030b003012860520164800d0042094134030041c00180c5402c0c6044d40c0e0003d0030300700000c40707172200400582d0712009461541640d01c000300000500800541110107210008010384044044802c4160a6840d40d40030706404c0705c010480d0710105050803c000c001c444240d000050600c441503550781d0130042e460b5070303c034921040490706200b075242085004540620841c0c10104907601c10982544910154030400701d00842e0794808004001d0205e141002010000d0030b843d6180790906c1c02140c00e400401c0143c1c000c035000342c0002c005602034003c07400c640c101c5400500f210303071030300080004850031040d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 173201438 1106 173200332 173200351
    0x9020301030c1206090605091606020a0f0f03090314070905060103020c0604061a090c0403060b060a080f040c0801020307020601140a0308030a02091206070309060f23 73
    0x403880030480d90049450f074400c10321030414030b004180b00360300035240030304081c200072a545010541d200190030310b44d42005a5034461000701d0341e03000202002002d5046000b0060080365003030769115a06c070721914040380440e40781e036940a607038811102010a10ba00043c1d0503c01c81403203015440d88071000307203011414001070070400d694800c4060405402d8503520090f00c01c0c10aa460441c0700c0150001d000700300c290400c0c0c29915901e0384617200c1610081e1411420b0980c910b040c2048820b0b003141543d0346c26054441c4e9003000c04504003e03004464482c500d001c0007447c5903081c0003640c403a0010f034020701150341c9040341240c5404542d00360382e40700380701c070403401d100140b8440103594020f00038100040c0c490103000041070000c5916103038660984030b41d40802402c40e074990040b4500f00d00c18003043c04120031050100c0e040e151404400d4254ac1e207880c0115540b54050240c0ca40c0c01f00d23401 = true := by decide +kernel

theorem cover : BRFrame.Cov 173021582 173201438 := by
  have h0 := BRFrame.cov_init 173021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 173021582 ≤ n) (h2 : n < 173201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
