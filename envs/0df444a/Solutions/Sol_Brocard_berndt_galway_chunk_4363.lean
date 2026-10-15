-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4363
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:22:54.929057+00:00
-- url     : https://prove2.me/submissions/e88f71b3-7aed-47d3-b273-aa7815023cd8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 784532374 ≤ n < 784712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 784533624 1250 784532374 784532383
    0x170a09060e1f081902090906240f040f0b07030f08100317041d24040b130c0e04020903100b0303161406071b0314090409030503010305010b0a05031e 65
    0x1c080d41d01e0214000842100c001c0c081d0303a003103402c00490700e0041d0060491104e180265440560700400c500302d5035554030207100f240c41d501d45140c2e0841001144441014107944024815418400c4c1d003550b98034200b1589a0300c06240d90321280e4241003c110100120313030320103013602402c0c00604d0000d209031107140ba54070125095030400b41210b0030451000300211517020051003203030a006107003078228126040c40000c8040031102e0751112200315801543c1a03008a4010b665004018800030780c02003641d0100d21801c08107e08080f80030307030700d9450035101504010040d074102c104480542c0380c1541803001ca40c88000702c1903c840030f5070301c42e505503000342c2d030034010b49150724003e00003800e00e80c0840c100200c0c040c2d4181c19181c0c0314010100400c030403512030100c004220040b410900f41020082d981240d6000b044091003003008814000c69003070340d4841c0a8030396024080d40d1004d8880d411420200c1c2118404010584141031030103040203591004100841c0030030f0001e80158100070f213400c805060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 784534874 1250 784533624 784533649
    0x106051206040b0601030615030c09091a09010509011d0402030a020d0309060e03070b070b10080f0a02151305130f0c110d030608030d09170408010207170a09060e 71
    0x400d589400c1000002a149214a0142082d901180c5504c0011b400b06c4030540145032480f00810324020905000f904103845031030480c50945601c1e0342d5500c20408481400240c0b4500a210901da0481381c504049110b0142104451112295240840110364090900301d03003d04107980303400040c1995401e000c071a04881e005840e5001c080c1d49468002c1c141940c0f80039140100d03156603281c089608002583c04140e9099599a074a0412582c460941c26100209401c003100045031012884030818000f07120350302010002032078862440c0c810086400180305040b0034400090100c84100328010401d14100e44094902d440350700068180d51b40a444a0100114180e05200500369010b50008030840580c1d02d1400341c2c0d0044a180000b201035409038410100d07a54030600c20403003010080c3e1f0004541c1842208400604c16096400c40c1e400c0e00594800442032350b000c1201c0060054810291154110b9010755a1502400c8200075100c1c04450103a04100403110504c0c1c00c030754881102c620070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 784536124 1250 784534874 784534879
    0xe0306010f03051c08070507022403092b21110d0f050f1506070203010603060518150a1112040f03120b0d02120313080106050a0b0327010605 62
    0x60560719030104940d852100c2c4000c807080d00c40d56051403820640380c0c509030026403140c1d0b100c4c3c440d5100d003071080300c0da41c00000d8140d80c010f034205070603c4512754000740c840701d11042402c09a03c0b49040305e0498182096109481551018242c03500030507407064601c3c002480d01030601c0034802c011078242c81c04410403000228101854038581454501c0c14074080d118192442e2010b02c0100d601040780020794070151303107d04201010b1004170b0540710bc01183e51014400283c400e508100841d0002420344640d03500589103d85d4500512507801140481d400c000029540100500d0200c0c2e0420720180d14000c100030903450380d840d922002000e4080c1212440e440c05960000e071070905007008081c044100100b1004600d20800034100114075000b00380303825100426030710340b120464090020070003141d003400c1490700040101c500e149100010f040040c004203000042c605050005101c0000c80070b4020701201d5000748208404001d1007413420300e42d0815200c0d901c0103043e11482c0503002d4031a503044980d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 784537374 1250 784536124 784536133
    0xa020c030a050307111e090a0e030a050d0b0d020901091a0d060f050a0e070909150516180b0d0e070e01060309060605060f0702011107080604030c120206070e100e03 72
    0x3401d104000000d007013801e0003103c408a545d8104010002c242e442441c4035600322419a2020700645042602d881c0d100440c85c4000c10036800f0f2140030780c1907900c000001c6001c500c010544180c1071042e1b10408244500546408407804030f00d80004800840500c14043d04584950700004c0e0a64920003155126001900070a610a40e0307180600c00791140d03180d030307031a11441c003000101e545419020f45403880e21904081c080aa0400c1079950141200c400300755014a1320803080141d14035203100d100d00c01d00480301c203c072021290b440d0083c03107642003200d1022400c07102103040c8002c0e001d92048418003065108002403284402106909040c09907000592201480000190703141d0143c01c189080d6101d404100007040e210400c1210700c0c0104000203014017000d100c813800650050b0962100c8802000c02c031070140e030b641d001c8146000c804440c114001403e0060200c10006841c80700d4960504a001805440ca0011402803c500468418621800d2011480f509003806080c40042004001d010b48 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 784538624 1250 784537374 784537393
    0x320f060a030908120a050a0b130c17131208040834030201051012050304030809011101050109061403061b0912100903020d020d080a0f020d1406030d0306080c060a020c03 74
    0x140c5034007101301c410044080c01d0a0014001010710b00c64400030b09001443c0b00008a09d20f01c0d031314001c00b522508007042c00103c0744000100200c0b020014494605c0c003032604a080c103140b40039540066030310001010720800c4403d02000680d0304058a030903c3d0303250110600846601000c0039484202d031942c445580803901401705150303064020a20070740b5038400034940160b03180304003007041101e41130140c02508140424800915403000910000605140031000d0703201985541d0308590080e0700a008080e03484504102c5030001d2a490301c45d00301b040b0003416981ca00200700700d045000c40700b824140b4190010300441c42e503980021140d811003d4400311040310b210401d24000804442c18180c0241c491130f01e4650b04944001603090302c07031040359265440c50301d45600078406081041c2c0380d08000ba800b4400300b0030303543d111f1107298601542e010940d000360404009050402c001100c1c20f0007094284076083c8106880007540100222003500c0480d0740b000c50b00012800e02d0031028110b40e0500a08040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 784539874 1250 784538624 784538647
    0x712120e0a050d0c020604150306210501060b180d17070c1e030804061101060e09100515010905090a0b0d050601030614060901060f18320f060a030908 66
    0x3580240e511440c21a65500440714050300c0041a0444c000d611003c00c120922818080d10f240d000b5001c0c0a0501013039017a1901e01e084018000001c102c01c8000307100c606081406070902401c0b0050075004074041c54001f0364801000030040c106071243c060401c1181c810100030803891552540610640342a807941c4661500d43c1e0007030741920891034400350074800c024071401c100d008201160f81c04103407030f0f140c60701d84501920002d514003892900741d507030f80200154803024000041c2c031400703401000e4403c0c088124200300842e64007901c5691201c915080c8050140d0704410401c1c01d0b10320442d001402961000c856401811414480e41c0e0000c0911507990204640050098141c0303101d08002d01040b0108442c40034100c8080350601e91000045004003ca140244200340721140a0f18000c2904158a40b40804c40c0400c4d0b4800c02010110403402481c9000c440c131a05060301540b04a41007104030f01c0f0029403d800030781700036031207107000046042007140284d029400c0240d01c0b02c900c9032103201e40c80c807 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 784541124 1250 784539874 784539883
    0x810091104170c0f100e040207060b031c0e0d020d0f080a020f01090b0103140f0f24150f1c0303090b1602060a24140102010c090b0712120e 61
    0x110b4250310000400e80d0512440400c3c90f00030402c019010001e20600201000603c00381031105500f80700545445800a440340d000030038461303003e1140411b11035001030600d40b030000c4100c4900040560031030f442c0d034129400b11810b04130144c111105000007085000041d80181d0a4800400d8400e5011580c0200a00d442c044e102d2100e481d0240c400320f04040131643c0c240c2d04034441c001c04c500c1420005000052000c2c45c03100e4901d0919003212000c05010344468640301c4006104500c0c1c1d48070000c0c8629815101e1000017044003410f24515280c1006071840080b01640d80444e0702c01c60100e20700d040306032502e003104c204085950310910008590303400c02074020088080d01342c40031000c2000244d250403280d1108501ca946503802440c907071b600c43c100d2200030b0964400c3c00e0a242e460701109903403542c0c01c00949014010108001d103401c0751034800a421101d0006001c0103010454000b0083e440840c410354468941051021800c01c4e40c10354104c503c60303114100c0403e0315141100b0003078510740008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 784542374 1250 784541124 784541129
    0xf010f2709240e0412051b191e050304091d030409140a0605010f1d030d200619090501060e04030c020f040b031b0f03060f07080a0209100810091104 65
    0xa02d9500864a8200c0032038269000c4901410941954000b8101c0c00d03c10402032105400c860000002d043c46210340608010b40401410b00d05102094100f00b4001c910094500d901c10403461340340300c10460390340e02e9224000c0c0d21800c25000c0e035910109200f0724910240c26405911001903d56031511408060300500d000320303541e03442c1105040080c003072003498824a029504161107600b242d501100044903003030300d0010b02d04c007025110340c60942e080d1010045c01090011903104d080070300d0144d80900d00c0c10b81c66035900080c158000802e011041003208d500c0f5100c9450301802188002d90b60a0003405400c0590190442c11021000c0005241d41300590320003240c4202c0b40340351144501401c00090300d0b170a4030143d0b0305400000d02800205045000d0524200b00a4112281107000c000007038200501103444038054410401044004ca17848aa0b00307078049690b01c41181015528008924603e1350702710050203100018000c00c0382c190000c0c8414005125442c001c1c0900140040e403059160440e1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 784543624 1250 784542374 784542431
    0x13e1e1201050a1d0a1113080f0a0c050607050307050d1d01030507051b01140108010c0906090b04030b041b090b0102010b06211e090c0f010f2709 64
    0xc100209140c64400743c0d6204844050101e5115001c9022013414581c2d0003130100c0190079070760000145101c00700005020340408140e0007429507403800001c030741004802c6c00620601c0e004141e0680004010124540680d8026110540c94188604d80703940303180300d4241c010f4054440c0040c282410740d4003041a962103c0c03501c0340d030807641d480700d001035050b2032003562031801062045c010581c010100c4240342d0209102c641c00410f001a00d0003082140c00c2003a0032003515139454021082500e03412004820042503146040c2c6001c3d4903107291070390113001d1400001d103000010350106007441100c060082103100d06585d4240601c0d03542442c0402001446a030f0b5002d542041c01d640510701d45002911b805803414403040550121407400390612540c02030002000c4804030204c11035085000b03c00c2c80c401d0068a009005449048003000070080402c4003990402c210341918140c82540103884c3c0e001030030710740c10000001e032140301c051800c2d00140d0400302c1c8c250300d0440e4a000f08202d00c1c0780c101c54940741 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 784544874 1250 784543624 784543657
    0x4090c110709050106110f0c150708131a0310030b1e0f0103290406020a02030c120733050a18050102130605071a040c05090a0b0102013e1e 61
    0x1e86c0345450300c4c0c00c0350b0711030901141c00950304e0100c5404c2c00f00e801451039824142141ca400c1040d9038031700da25008880781d0000c003d001c40e0144850344050310030742c0c041c10000703102a0462030211b0075494008584d00004120303508000201d40d840c89803504104928020342c0c9440e100b40380c0380401c890700100910060742d0380c182e102d001ca5582800c24842e00b54040c1c2c283d5204400d6a61610f929010354407101804045100c10040c005030711505120010800710313204409603403204a070500302d4040481003030500c40c14400841403441007821150700e00281c00c40200116444d6600d0032a10001c084150300040150701543c00901041410350041103c1e1b0525802c1c00c141d1516550200ca0500684000408070218600502c0800c6900f410480d8000c0c850084520b11645400114140035010395002e6076458070b80c03d50510540e02030190b06005c1070710303040351003000040b115a10b101d1981014540031214440e8600644d255540d42299050031600d02d41000070340d006668800e207580581072004140c81e1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 784546124 1250 784544874 784544897
    0x605061c1b141605070609080f01020a050d1e1e060e01030c05061309020f180306070816030f020c15130203030a031122050114040b04090c110709050106 67
    0x40318000101c040d41c440e640c400110303440d1111070b05030380d202246406011a41e0848440002c0003040144090851980c8010110b4500052503180c009505c88070020b50340140070315100640e000084e42c0a5181002020807140030310045440c1002e64a4420f01000b0300385001000d00101d110417443d8a03142501c01006165a20900318245020038003004001000c164820003180c0382040241c16803804078800011856502c2102504030b9105040d5580d6003440400c0c0905401c55455a580103590190050942403034520700042c812100103000c054004000400045a036119a00c418107540c52410110342c0c0340c100040890361444c0b41c6034203041c1c25000800090041d8094414400300c154060010750a220a404095003e0004110840740c6104144030201c0e00d0740c4040005500e03002241034400100c0c0c1003400052003050102e5a0303040d8242e04001c20021a1a004100d6080390040d03100010320681030641201d03a6058500201a2885824030108081e8081e030701c6a03040b6070f0b2540752208080f2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 784547374 1250 784546124 784546151
    0x91f0906060e0d0804090b03190f02040509030c1f0e010f0204051c120f1115010f0b0c0a080702190902030105090f0c07021e06120a0c18120201030605061c 68
    0x101c60f21801805541c050100301b15440c0300f9080301d05840c034000d080c0c804242540301c01c41c1050350308010603108031410380848000d41c180f0748100c0e03070418401d2000c0c40c0740880c8014419590302408220b09850407446c6588040100c41e94081e01081101030002d01003004108141030180d0814007402e8800d9142d05070707400794003809001243e080e5500c0301c50200200030402d42501d0601d00506c0c0301c0144902d650b0f642846000c140f010f0800021104c0f4202100e505084200c1c2000045400901007035104000c180d03403042002a0500980b64810ba24030395a03680392001c90303401145c1910b1014031040c41c000204040002c0e07006141039480a03140104070f50380c0d50001d0300501000740c4102c10b034024104100303000750404081200c8035812425614003149a09404030781c440e07100840410344c101c802c0041c009001068000c5c5064000d0501d040400d00216500011a81d800c6208103c0c8558400c0c1000b81164042c4d0000001440002d0603140c070703001c3d005c5980300598030a0ba400207006d03181180c210700c0704 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 784548624 1250 784547374 784547389
    0x9040609020c062a0a1107081b150c1207060f05040305040b0901140a030e01150302151c060f030b06150313050a0f1101080a110306091f0906060e 64
    0x2620300740100761135112102c94013022154154015914038103409558510005a0010114000559500c0c2001c0722500368150424202d41c01100d41500301c000000801c1d808601ca4050040c003c0b1040c608240201e880d02c5801e205000c00b203002c500941c0e00303031155101c421010300b21440c019002403103c0c045003500708003191300440b401004141706000c01d00c080100d0324043c0100b04010306002c0c03010b85281007800c42a400c4003030240006034943c1001840b4072000c2c0604000c025103106018801401c5a0000e0515102502074880001001c41c85513104060709007143c0c010b80399682c040000c2c5480300404051200e141c00700380e07911440d00c004507000d070500040c0800400d0a1030b0341c0c10308640b50f0700c0481c083c9815040e0140c40768814840700f030b00400c2552643d20102413150030079066000e0300e0b00014140e1440145050300c071038078110000c00c440c0f180c042240e44c881e1013194241c1d80c6c0e030350380b04074a440f210003079804141c420b0980401040c550101d511410a881003034440b0f01403c0c20071000c00c09003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 784549874 1250 784548624 784548637
    0x3141b010210180512030a0c05040b03130f0c0e0a110c100c090b0f0712081003030c020111060f0a0b060a0203091e0607031e080f070c0314040b0904060902 68
    0x603402a061481c085040fa84482c48000400062030030500d15901c030785242120880000e0142d0000005100034030f005480307852842541e50401c0740c102442d0444015060200402c80305221240c0c2d40c01c0e6040119440c0b100c00700d41c1d070200d46981810b0b12010381ca032860b80101d4084004925224648201e40714000076a141000101e00501e0400101c00568019084407030048040c0214003030040360a0700381c60090318000c8921a032280c5c8940700c508018501030038200405081c0b022010500021801e0242c000060b6900f508203240782040c0307880121140314890308618510300841050141e03461000c04141d0161464410600901038180100885449200c0324a4050f80c800c202800d003c0c104200444001d0540c5000561840d010802045459001180071000907002e126400d100b100010000380303c294091034030280602d08071074400710294001d0001d40a0007800c004080c10540b00c1c45d4512085821410100e8989a0762161a0074a0f004440f079544102c1c10080082024251407090703d24 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 784551124 1250 784549874 784549877
    0x1002030d06092714010c02011406091003080304051903031a19290f03070807030501030f03030e0c060c010b032a1003020c0303010b12180d0e030c090103141b01 70
    0x20681450f0705030b202c2541800c4121190094520f119044d1842031040d03201c0c5440030740000c10b145500c00481392040350014901403040c2c000105000c02103002d0301044003920b61107042d5030f503240c580c2e040030341c0342000c544031001110840642c0d0000301645074215013a0031b401d888c500c00f580350980e0200140c14404807070754404c0804158042100703801d01060041000c01840e421142c842c2c200600341610380c800100f21464820000501c000c0c81d510122455000a0601e01001203504560700d80d03c10305c00040c409000c040e16450300a80c07504052003824000f140080203250340340603441040c2d0103000892078982c404c0c001d804800310750740140059505101008401c824050b2102d008000b0005600d20102041550910074a603040004200440c0a0300e144dc0c03a00d03440e1040c955012084104c01003203000c80c1501c0402c98134000c0b81c0010b40041002c0b89050032031a486206000c01d1030540008011a4840803810000041c0501d803480421412404c0c01540c2807204800c4541c0105107024180c20f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 784552374 1250 784551124 784551161
    0xe01051501050a03140907031203021c11270a0608040206070308090f15060f3c09040f0501050c04030308221506062309040b0406051002030d0609 64
    0x1580714070002c3c03200c1c01d100d050005618268102072807008008a03981030f210740c0421024001d1011070b4941c80303424100c0c3d2034150300c1c1182c0e03c5280705584c442c00d4043e140440d05d46009055103210001030b1012103452400c0c500b8803001045a4460581050003968014109801c0c003003145446a45041c0c4103070380103042245440a80c3d074048400c7c0100901c0c5034080c0c085c2d421440f5010000344901e044d20321004000c2c0d022410104100401c0c032181900d0f45110b00504c0e03038050500511441c1c198240390001e2420442c0101408403064003040b50903010707030300c9143c040c00c010410080b003c4000340a8020340c001c02c0741d5038032410300113140c1c85140406400310300110005103a41c0400c040c880c0c008103501c0a001c0e058016541c864000b402d03d0054044090780351082030011980c4030000010011541031000c05888801030084c000e48100b000301400b498894024110545550b0001c0005200242207046401203c000007502c9403c113449034035003507050810008060540e07000c0e01c145140201c4030700 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 784553624 1250 784552374 784552411
    0x207031110150b09091321080601091d15040e0f07080709020c12030a140103240c140306040b06041508060f010e06071407152327040c0c0203010e0105 66
    0x1811b41c4070152000c80d090701c0700b5000e1540c41c65800701141003803e01c64072541081e040680005d48400a03d401410702d0700d130350594850328180b40f01d00d01c40d08124103410409800c0e081304003282c0a0500e000404051384240210030b00046c01c0010403404896490040c0c841080e00d40c04030409911507060300c21055801213124100d152107100c000c41e0404034407140060303441840c000140184100f44c0c4269800901c1c1da01a540944092040d540300903000b6a007084201c1d03074020045c04010300c81c4408500350101000060643d111a0304c5200c141c0002860180c0b5280e0b94114195842111108040000c0c0c412020130028280b0807102a48010140c44650058040b64144005500720710001c0d00e054800903805040c10209000380c2024081c41d01588010b0b840c042c00c0500b551a008a10140841130560010070313030709124042d2a68420740c07620100600f0010000305410200d49402268031501d00249510030341d400407086003140b442a40244a0050400c01503400c030361007280d62401184400600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 784554874 1250 784553624 784553641
    0xb0105030303011a0a020a23060a090c0909030509031002041e05030c36010501030b0a0e0105090907090c1805030c030a08090301090b0108060f0f090a0201030207031110150b0909 78
    0x50117074442c91b84111101143d40303403180d4468051032800c8a0000680c4940012072580500456130301c0102044c040c0401c0105540d03035103460f0b1903032140780c10060b07032020100308062181c41201c0000c0802070844240c15035084040000350301c02c2c42501010001945024040400303401c60b101180c00007405410000c20002c203101d04103903140343c8080c040b081c882c25181000c42c41e2491199007000806000303047d6042800242c00c4403880704c036091240a85490821007400300a5416041d40c0055882c00490f49171044c1032803070703c141034200c0144a0306000d0b011003180c4c1d201a10201080b0540342417802e03903985005243d1204001d03118a0b0b05038015412a00c003080956004044001000d4000113189407541c540c040c0300c020a801825854000a082c410200c80c442c1d84107401c01c0300c071003601e1018100f81803020380e1540d0492000741416004101d0744185406071180503242c4102d1b50507580c542a054030a500140308005a0482280640001007240d1440c0002d0310350050001d405041d454440601 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 784556124 1250 784554874 784554877
    0x60105033d0c03050a050112050318040213030f0b0612060a0506010207050a06021b060a0914041401030f12030e1009020f10170105010f0c1e0b070c0b0105030303011a 73
    0xa000d5030504010103071484401a80c400c041c1000c150760740c001141c1c02c10120000030340310180c2c45200fa90444601050110b0000700840b0b1400001500044c0c2c0705010300081000f0b40074038240501c600410381e07000020300500303001140003280314490700340c820f60b03030718017040300d00072a204100c2d040341d003c076000900402003079100300e0f0000d5050040f196401d5071035002440100c01c41c2c00c00401600b115a0110f5800d498032801d06101074102c070014104130b141c2c03100a0502c181441503001c7d80c049040400002d03242d60b4004100e0f0b400c051100d0816603183d00344880c00c50b0401c04100c4d071904460340c041106034401c1c8100c103821400704000c0e01b10381e03194000034809002c003d00d059900010302c2d07031015010b61b1804a00721046041d61210251040c420040b41d840500582c040750500040c0300c1314500d01d60707119452512140d800a0107020007180c080c1006440c80410f040105001d1102040c807018541015540c55044e02c10103941c40d8036a00d400600da2079000038850301c48040340c500b00102d10850400c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 784557374 1250 784556124 784556203
    0x70605031005010f120f0b15040e0601050a0c080a081617280e0601080f010902030606060c03130e0a15050907140c01020301091a04021303060b030102040504110c06010503 75
    0x1a05003460f040d45102c03001200c0c420054206d026036590b21079007076030419220781c1072074004c0c98298030f003054604001070250710390041c0320b1410030100098032401c03180a1062640803903002101507440e1403032140054101038080e03890046080f1055030891b429413107802c80b50414100b85450700340684803105d03180171f0908000b1030f00d0040080d02342c0c4030a010205104211101c1c075040020011540f43c2044681071200840da05a120307410b200102003d030303e0010703141c0d8100c0780c240e507501c1e681c0b50f090400b00c0c19070141110703424a8802c5580c00142000d612031809000e401e0300030041002d0a0329890441d04894075100322500040c20000040b0028000d040c0000481e0a02c2d8600b840c10281d444140e08990003608860495903450f1145464600e5900d00c414484509440031494040ca55142910000b03003440002c4c081625440480302580f029010384004000c050002d008000c013003041c458582c0c101d00c5c9400318500c903190000800d446c0004101507004c04181c02d0082a00140d640b10725040d5206 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 784558624 1250 784557374 784557377
    0x30306091a180c300f0c12041104020a020a0606050402040f0b030c0c06040302030c120405010c02040b03251703092803140312011e06080402130518070605031005010f 73
    0x1808030aa0030f80c4604d403001116405130004401200a20000584001d40600203d101171100c02c05c221280e061542243c130f003080c052007460788030b50369840c00300c002c0e0070710b00300c40ca4105001181c441c5400780c0010700007203498031400040c00790a8880c4180401c030b00840c4940c2a42600c0550200000060540255040241444c0c0b00d441e0074003003440189030240543e000c40060780001040604500f00f807011000b2480551107031440c082c9001c000034002c0d62003481c080d02c115580c0d01c995810ba41c081003241000c01c10690341d0003e00e001032031381c10320145440c1304078030400c2d011410346100520007104607124136800500b0490760798280c049118054007940b85900501d61000300c04004244881c105040788041600116075401004d03880545040040e801600c2d9502c93b0281c890f5100c52503e00c00c82a00c0f5540750051045d501c6000055124003004140b00f04580f600060005c207460000e204100301d1101c8045415180d59501c0444591104507440da034200d40d2900d0501440d032041043d4520360419 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 784559874 1250 784558624 784558627
    0x30f010b0a0c06091407230307030b0619211104050c1b01060302040921110613110907030605030f0d0503040b07030b1003050a110702060a050322030306091a180c 71
    0x103664040e891b101c8a5002091085000048000e48645105000351042d0098010b0010309107103139501d82200c1b00c05000b091081004841e480041030581008000801100003090f8001e070340b40602c40c2d07203403401c044181d03680f00c035005642045003080e002d07150040300c24905903890888000105840e03500d800391960455501c0b141c000000d0f0751f450142e41040c900031410101d040003a0f84d60b45100001500841d0b092040b11643c8480c044400300f41e090f48030303600c03950349000740f14540b41c50604501c81340340e0640c0c08034004050050700b40d8158422016617000360103d40603406451102e036030b034281641000c00011313000c00010b000100b0324a8040d8003c0d0703081c100401c0e80c01c0c8140000d11030014001940000965540c200304003403495000d000b842a01582c0c94615091058002c42c800340b18500382241030040000c00b11300008980c0300b07080030104984280f03612401051400902a040a02c1038103a0a41006c81e90007060b149400d05411420004210301c4010f00e40c0c0364056503205005150342c2c40d0080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 784561124 1250 784559874 784559903
    0xa0b12090a06050103030815100e0f30011409070501122702091303142104050303011a0301061b0501060b0403050a060c03050c0a14070611030f010b0a0c0609 69
    0x42d41c01103a001e144030762108071003440d203420280c8410705c5001c441c0e44604000942444029004400344072210400d42d9004481008140072400030012104524505c11001c2c1040300b4000815102820040c090302c002e000c0b031340038a0810ba2609405413402d00342e980101e001044103600400c0540d030440d0700c090011900156060600505109040400c181142000750010841c40e1031044554001000042c202c1441d546440007400b1080c6050000030800c000210090304e002c15507890000301401c00002c201c1840c040c9865900d0b03401c28814030065814011001000d000010305580c1a640c40751b940080b0700010020808440713500710b07810341d2255600d45002c102c00070001d0042c0b001d903020300000d0070340103007500c0c11904641c41d050313200080524001c144048030480300c08654942c0d10700d00d0070225030700c81c10010b0038044c840c43c07038000d040600e0b00114908100c1e00a02039880794820380710f000c8643c0c0e42c1d100d10b000d0314031030740300345500180850004a000401c0303036205c00c0e001c81c040d0850f41c21801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 784562374 1250 784561124 784561133
    0x2607031103010e06040b0a06090e0603031e0706060801050103020f060d06081903230403080a210c0206060306060a06030f060b0c062d070822060c0e0a0b12090a 70
    0x10700a0b0480c011025074035041201070f040a0040c107000d448107a4103401058507240700140307001240e01650b011a41d188022801541d01001034651014403442c0341c088100c1c1070b1802c115607a0010307808540d01410070a000a1000042c400c05040366000b40c030712a51480100b003041540c0d03001c14034202c482941d03070301e0201da412130070001e03541500305400c1d1014003400142009081001e1000340c4001d8a0102d40301c51412914480c1a1000c0f00d0307000e44600e0b1120311999050340c142d503846440260036010005200041240d6030002c40d440c6100e038003a1030039600c4803420715856070011904290007404107102000400e00c80e61111102d20440d5400203440754031602c28080550041c840492642d003c0c17018004003540c2080c12405a80500310302e281142d110101e0301300123150080c514400e100b50a80001c5025001001e042407602010f00e00c0042c2c01080c1c0b5054005207081c03002d0b14001582c0381600401400d2020090003039a80005129043c4961043c100c00907510051010380707180296612030b400078 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 784563624 1250 784562374 784562377
    0x60e07080606040e030316050a090b0d1b0e09070e15030a1a01110703030e04020909191a03031b0a05060a050106020d26150a09020c0d26070311 63
    0x101000c2014260030305094080006030351200d544000650020001d00414031940312a10f8903d05041c203000c2d03100d6054240640c3c80c5032480c0c0c005005242c000a042002c4041070740800140e03002518240c11401e41c2940842d050040418041d400050000c04904990300518880710800e10040921419a078182d00e07105075608103981541c072403511904146100159402c130f00d80d88a000f0b103004060080e001c5070185d900d40c0a0303c009014004205401c011a440d5601280c24942010f402c00710785081004400301c0c2c00c00b00700d540b08417103403800e900c03403031050300034010094107410050095080945035156402007403202d04081e01c880c454003c80c0c0c80045e01c14002c8a01c507101001000601d989000c00203814920003140b048100040c0c1d81c1c00500c18880d90803a114072072003008904e103281e44c402d140d4031b010800103001198030900300040081c2c101c1c3c0e103130000d01c44099441c0544021600384401904d1000380561826100c4114031440e60f82e1400484410b40c0c000390b035141c003143c805030350742011005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 784564874 1250 784563624 784563629
    0x40608010e03180108100603020304031209080d0b06040b12250f1416081e040b09040f0e0a080f070b1005010f02060c09010c0f0614040b090304080316060e07 69
    0x182e41020900c4442c2a0410800c0c0312144404c0c00e0030141e600e0110b0041e403110201d07000720030605602001050a05100d000719555030089864101704201160410502c0340e080010030103541418880c80e91038909060050303804031002804007908101030a6141c0700a00d00051091480301500401c0680403845020b90000c3e440d11078a031202d0750305803074500402c10701040340001900c1100300401c0d6428420729842e540b00c03680102c0000e841e0b8203803500c0b00780840d0320235020390300004000c200130400c3d003035500007040c55080442c0e007001200d40c40000c01040d68025410100c0136000020f820307012440040c01085070102103d1401d00d80940341c0d0326030b0700114040c0d40f0f00040d1580c110081c007081d60810030040e50800140001c24203450900c2d8941194419220028100081c1382c50110403c02110201107840764040c41c180b0507100e90f203040b40074901c0115016500380340e9440200b00c0014021013154103035192840a1454804844403810043ca80301c0c0040b2003241ea640c0141c8040c0380f041c04036501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 784566124 1250 784564874 784564901
    0xa0203010609020309060709030f112707030b0913060c0c080f070b0c03060d02010e01020f1b030d05040609050108040c17060603060c0c0a020f150412200f090604060801 74
    0x2160304000c1d4100d4074006d0000c00355030510280380f405201040030000b1582003143d11401d90114150481d0101d8020032800010000214070019032038140c0d03101ba0315503849040c481e5410004500c0c91020804011000c1d210035440300460b85d600800b0078065048403004190382d0800140f83c0c400740d41c1d4008254480c07050030703055040200b0342d2420001c20340d1549800006652005007503080c8480001d540f2580c007000241407251194010050b40d0092103140c00320000c01094410120f9104001e100c034095441020f1b10a0184000b4407110034016000e440070348100e592a051800c1c2400b0040d90042c00181051f03424900d820f800040c4031038a08001c4d00c050b402100a441903081c01d00500d860f008010300102c00c040c070148605900d01200190070005140c0448810704000461b10106080d18800202c0e802c201c4400135002c00c400c8610000c05506a1088505583c2c4014102045e44420340000800c1d03400150754143c40491310780356201640000008000050b01c0740d032109080c1c21660124450701 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 784567374 1250 784566124 784566127
    0x50607050a1209180f06081009142a0f150703090501080c09130b030312040312090b0601050715020a0c030305010905060904080c1624031a010509030a020301060902 72
    0x8040044000782c0a0940340903081140082c1d0a10002079444800703541080040b580d0351202c1c003d2030b4060f8016200034051034090f40c40320f5480314142405000120010b44400c00d510701612030034100041d03031110303801d1140903010081e4090750714480c0b801c400d840c481da41b1560302c0165030041c2d1b4a500740d251007118005503d0340e80380042c4c44c01034612409603100c83d050001e06810060620040000c4800402049881d030b40780900c10a809401000c900c0c90f134507090302c004100c07e11024100c913002d50055000f0f403a071006500c074008101c41940c0c061030b0024800303007031031012030100d50051000c0d0403050700c80c590100c81146003580b06030407038001c0c40d4001d0003c0c0c5088800024940c042c46000c0c0580b96000c0c1c02d000914190012800305000604000c004410014032280c4000c8203108020b070b18890200450107540e030311003080c41c1c2c100001141a0340300600300328000040c0d001307205210702e20031040071a21044c055100150342e56080f00000d203402d030091050000060740c0a10858010300b034000c2005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 784568624 1250 784567374 784567393
    0x1203020a02100c0f1b08160201021c090614190305060f060906030411060c1006051305070f050306030f0f031b0d050f03040f0609030206062d040203040c05060705 71
    0xb45885045104124168038090140c4440ca40c400090303004100c00741441c0c0306022840001944520030b12001406d4400c1c04584001070a04e0310340d4046040b4002d9084924140400942c0c402180090064034041508004200b03c81e5016255982d84608004070541c00d1000c3c0c00711202c80c240c0316001030400a0780c0c401c01c1158034a00b215808030074400c107452080c103007550301c27000c036042c0d10014002401c2d070090b810100d40f00d03584182c11200d8107820709055442114000400e10301818550203a01d10801500490a08410440c425240300c5d0319160b0f90b200101c60740f400290b500750300107008140c0601035005102d1180d1001c00860442001c0c000c000d42d40e03200358081c040031100f210914108190480442448295030040558050b141f005420702d6032070319103107001500a140c03a1801014241081c06444c181038011410070301c250b005803417015580341c0c40101c8510695605000240f14502c1c4c00341c1603c00c2c10310354040d40d4843d1103041003049817621040000c045421034030301200c0542c407441c01c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 784569874 1250 784568624 784568627
    0x4050708060c090622120308070f0c0f02120f010207050714061306031e09061e0605060f030406090c0b03011e12060e10060f1403030a080415091203020a 67
    0x79554003a990140807401c2c800316000280a6100c5e1010718802c00c18021210100714500240d0b820041a150084402c030b5445494060400e82d0200c5850010440c0d494040d20b107903006240c80f0000c1e60388410407410058039682081042d500510b02c40d12148200088220000c400344010101c050140d401003245910308041099108101503009008180030720202603851941e002140540300103050204100c40c4210042e900d8840d82000311200390b0030301c0d4004083c81000d0f80842c0d40e424407442801c8814840d1048101a51228850143c100a04000c0c0d54230b41d42502e806550854400c0f14040780818403622406905202c40c0c02481c4c4803e00080100a00c034401d42c00b1440c0c4140044010180d00e02c0e11000303202e190341c20840501465100e801d46103220900788004100d040704c5000c20001240c503026070008003031b02c9000d1801035030001c0040143c107150003c182c0718003c1c0603681d45c1c5115a02c2c0d0b6507038011003005d2103180c0e5010f512040101c00190303103414400f801c0c4c01c199500684881c2203900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 784571124 1250 784569874 784569883
    0xf04030203070504140115020a05061015090e0a11090d060b120106080718020705010e0f0c0d0b04061e020f0a0e18240406030c050f03031c110f0304050708 68
    0x300c0c0713214502d080041e081d1500001509811103143d514108000c80b59414142e08041c030a82005245000300800c100d6103141d40f0401e981920482e1802a4030202110700c1034401c11501e00945126056480008151009075005000d0712010445d0060403d10729401084640b480104115007003622103165443c3c1c2e042900b6400244e80144009001d10752400c0b01403a25884036018000042070940c07550b28080000d078040724145540a00208061640c80c589c0302c2e100c4c425000151414080c0d01e00b25080e5241c21400010201d801070900d02c5c00e529151741e61401090400600c250b841249401c1300540007003440034240e81c00310107004544c0d0300504a001041c201404212511401c3c0b00a540b0104501c45124282d00c43c00314910500d2040c0315007100da841c0307059a0354056116040501c003108010411260808589040c0c580709423071000038041588a010303001c10950344880340422200103110540025015115140080746000e01c0c054054039681d004445c1512150300000342088001030420 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 784572374 1250 784571124 784571129
    0x504030215040c0302042a09140102030c0615042003040b130f0320190b01090b1005071e14060f13030c050705030a0f0c060903020a050402031b0f0403020307 69
    0x1d0040c03507150035651180200c1103408013a01a940e944100701884004041940140056166001c60b588000d28001c05000d40c601030034006500c081900045540000103036044d2485410141056966106200008407004024580c2c49a16400c41c2d188803104041e00784512074000c202240c1d286018100300c0103030ce00c0504884501c045074251040452103030745010b400385900d40b41a0011001d407113010803c8180c203402880c82400b9911031760100004251514406a01c14640001d0f01d03a40c82a0744400c588851000380d8108003040040c48600e03220708010001244214044100980f00400342c1608002c9030408903000da04e00303a90f050403200704000070b035030013040280d00400c64030f01000d07110b8418001c408020305100c1200154003c000e8103204020117000e0242c1103800310411401c01c8040798011420650784203131074000c041030300d0b80705240c554156600030f82004174503464142400020342c401411414803e00c916011880c580601d0020011160701d401c0d0161200d003580105400d0090300d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 784573624 1250 784572374 784572403
    0x9050312011a040e04020d140109020f03010e0a141002030f06010221040524030705071a040201080112110a031506050612040605040510140103060b010f02060f0601050d06030605040302 81
    0xd801c0d152842d5514048405a400700302c84581380b80c58620110703d941d0b9480d24010b0045000c0150110700030415480011030500842d40c00d05207c1958007810300301c8201100341885a080708010502080c442e5403245526880e071400c640724100c9056100c403c030f0704291848010003100c003052210660b41042900454080341880010351508a0a5405a441280305040c050854500c2001c210080581d0404407400038a04043c0c0c2c84c680400b004003140c0c0484d07012601907150010640300d1a180c000614419681a104d203d40c607400c0c15511510f08420f00012104a081c24000440548820317203580300840c407504d00003205515071500380701a0f031070542105010711400d016004c04e000c04110b103550803c1d0403c034001141e840d1828050305100e500044546190308100c0f5444400181200150490f80100c6041001101c520300443d0f070354150040500042c0c1c00320b4041251141c0c040101904004141000e84c03034811022984010b44a1710707801691416620300802007815018040e402e60324120 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 784574874 1250 784573624 784573649
    0x13050a0b1b0328150b13120b07050d0615020604060e010b01120e070b04030b040209071407020f1f03020309100c230403020d060504030311030c070605190905031201 72
    0x800f010b5890081c400284141d0082848030421a02c40070341d00441354400d2504800d0b280036200d29400241d40c0c0003003070010014421b03e100042c4510368460002c3e10b640d0003040790b680ca456a410455250300003481c403128440d6070300b80028000da144856181c40d090a50040c040385e181c2402c0c4a0100e54955a15640590510200c0c0400703aa22000190800410b94000506c8900c81c1403428503141c91a000031000d80c3d00002c001c418858003e40261185108071150a65641c900804a4082980143c509841c074000d1102c1801841c194146400300d15003e410380943c0b40340100c218680783d030b034040e0071004a81e00105000200300d0500184104d00c940610038411400340c000001c0040000418480c13891071208106420010014200d50045400070480780300300045090800c001c0c0f206407422408a8940300004028801003010744c1e200b1030100215a0902c0301540301c00024080081102901e44018501c0c10411a610310500070154005d0008646981255a160002c3c610681000206111 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 784576124 1250 784574874 784574881
    0x140c03070e061309060807030510020913180602031603050604060807261e0c1509190302061201230d0818040c02030a0318050303060913050a0b1b03 65
    0x10808441032558406a4449654503c02c00d44001c02c801d00f90400512142845e100081d0f460000a02c84152070056007559618079411841c2802c9100364608a074000c080300b40580080e4980d82e000018041100c4866001d801c8a80e0b9940100c2c1d10484450465a50001259006aa00d0710800754010819201081180d092405565544000d445506080c9012000e40c143c880b4070000700750f02024003182282c900301000c0440c50000740808040149602c00e81d1251a281d240006080c241e80081d100702c1490100b0708403c1c40070101c201e01402c1142c1211000010041c0c84d000014000c1c480107907800c1040f54186803024541031a501c0b2001c0e00e80f000000c60340250750768948031402403a80610f00d55559030854410b00304d107400610003075900501d007104080c0e1494011004009000c010354007002211080f81c0aa0001c942c1e8040c0070344640e006000194150802a4402e0f80010010a01008040243d52280d180c500d480c0000ca80c0490b0741014080a80c10141c059404061000401c0b411880d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 784577374 1250 784576124 784576127
    0x1a030108030702040c02070911190f0906050d090503040e01080c0102030c030d020310080d080a15060c0602030604060b030c1201050609010c0308070516060e060c04030b010306020d02040513140c0307 87
    0x10302d000607100395540d00803101c8007030003044102d0080c02c50365401d00101d01100c1d00e08000c0e030408022844401c140400724251103115800030030007010b594841002082c1084821100f5412680c0750121031680c6c1c10362a00442c030100042d0004259000c000501781d810f00c88040d00b090a5010113505651003441000c07400c0c903010060310b40e1340c09072150041c3c49580c0c60780d050b500c10341e20354020041c5026110b0800041d9903c0203955114106014060081a00c1c0030390b008940303a00c2d4480c036070004418840301000120300b60029500b24030001e00108100e03441e106035040d1b50788140c800009040002900740819569a04820b004000413030700e90342007141d4003001030141d511581e8010f04011f607040004032094022000d98941c0740e0170348607400d41e100072490305000503c5a012141c40e05e00c6008002044075070258222010790f1b501000c00c014036440c40e52500042c1d003082211a880c55028080030910b501e528190f51060780e40c517040030640594851650300340200c094082d05011808004102616 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 784578624 1250 784577374 784577377
    0x70f0812091503130c0b0a020105011a07080d0204150909180308401b0303170901020c16030213060f0501120e03030f0708010e01080601050f1c0506011a03010803 71
    0x200c002e050b0306a038a03503818100301c0d110042000000c091601c0600e0200e41060b4000103400c03040b000b60002c10803a42c80342c528035114850b201c40e0300d07450070f01000400c000072015005460030399148600981010b8071113056440c101d06c000840c4e0b0001301907040400c100d05040c00b40c0017100b0164009135011000a40b0020880803004015030b4a1461017880c20500300e46c202c2c20b1a200341054140d06855000e525000c030b0140700180400d03940c0302c2041442c42d100c0c02d00c2e183e101c821a40d040c0c50f0030001c45111008034441820040c05402e281d542800b0b00c96910009120306118600d00310b41d000749080c25441044607050700c6100c1007032203e00d401d0052110300d012404c83c6e029900242400c0c2c407440700403103106000e85680600f008031404003006200c03410011845560103145a43c8598040d6038840f100c81010316424819003030740340c0c401401000582440d1203011802c010144ca001c41d00f410528203484074400c020402c0310198484001081565001444c0c484003816542d0000d241d545460000c0b41c1c2c0f03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 784579874 1250 784578624 784578649
    0x4030212030c160f0f0804092018010c121e1814040f0204030605070e0111030306041517070e13020109150c020d0b0f0a050103051507030e070f081209 66
    0x16452002688418880142440c03601217a0100f00f407118400c00f450651a40d4000b8031034901004e08000d00100c1d09180030100366181c40105841d1400d140720120f6003180ca0b0a92501903042c0082c1004080100c0d090504000040c08c80e6240e802507501c2214448611140c40407090041200521403140800e904180c4a0103c422800723460358519031080000b030051400c140054980c5100140000410160780c116620a00c1144c54052410140000560f441080030351a464a81c004000040061509174058860400a07088280c0d0705601e4600558244e481c0920a00182c0d10800302006851900c80c40c25a1000c0c001140f000c8103a040c0d80080c1c2180c1c00c0c5c1c000d2244520b255410f00c49101d1180a028810f81c0c1c008050a440c003030385040014002000f62404540071a201c00000c024084600803a0b049a62100080c400381b2103d10150584000242281c402c043d260075030b09414860410291024080c81c0f018419141c1c5004000d610b44095080840914402804105620398450415040d03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 784581124 1250 784579874 784579897
    0x2d1b21070b04380106090b0403120e12010e1c0c060e0a020612100b0f070f0f0510060e18070b07050304080a0308060915090601050d1503030804030212030c 68
    0x40700d8603140361003410480c404100f00414440c1025180d02c010040b9210690541c8440f0510f4060740c0300d0700200c640418901459030300000400041000540e40d4106036515801c40c41e1515000e102b10001811f6440700300082c20b1260744614080300324860074050400c0707180c070b51001c180041110780c101410601030b504000d400e40e80e48000e0003903c2e9100f400480e156640c018070241d030301da41030180f500010708107690342c0c2041d100c02000031072419210412280c8034501c41142d14201403441d6660786103420440e40c00c8400041e026040d8002880803ca03030a49040f520b034000c0b50f200d060542080c14024002e00560701c1100f5500109400310011466505407000002c4007540c41240c1c1c2007052552260794407092603441550048018541e2104250b030154404890743d0040d030311000f02481c243c4001c003400c15881402880407840c0356004400801c40d4080e12100824040d00b0910551002e2110703900980c04207000c40f0401080690500490003c110207803002c0e411814003d005c504107000e0368a201c01c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 784582374 1250 784581124 784581143
    0x1170601050a0912030f1106090325060905010e1009021f17010e01090b0d051005101a0a020c030f0604030c06020403240c09050102032d1b2107 63
    0x354014800d0700c0d42c00c040c08404d034413901c098910740340092030003500964403400100740308008562860b000c50748900400c10342e03000350300781f000c07024000b07032000c42804c200c40800e10240350100014500740240d0384030901910001440441c100340d07071800c0a11001d002102c551500e40c807130005a540c00d6000040c05681410101d0108901d4415108841002d051003440c0c441c4070000940380c8000200207050341c024040074884c0100103c148001d0700080f1400a1507500301c2c4600c1150400168411a8040d000d810070713100d25555421011440d01c40031b019461017480001f165a107a503010000090001c406400400072215900503040d02e440340580001d0412040d50480302c01c0c04550b0b015070f4007941d048000040811030310424142841d40040c0709018103402c000c1800c00e441e0007251070a04403101a0091440c000700001c020104182010300c1d80710400c040c040b08508071480c20702034490007146c20341c07041031a94140800d9281c2541403060b500490602e030f07800c403405040001030b20703807050b446103006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 784583624 1250 784582374 784582387
    0x405010918021605060a0b09070f1805040603080c12130605090f090a1a010f0f11190c03060605150405060a02070e0903091e0a030f060207060c03090b060117060105 72
    0x400183c07045003a01c8003803020000c003a100344040482d50030300030040b01d501040480e000e10207104e01040100c4140011a01c0781c01100581070242621100701010300e62000002030326840010101d5a554005848201002c070310440201002c1102c5000d05c2107420702c0e281096a10340c4c24044456150003903100304400403480d030206486e168107000c3d55400c028140d5005240c6522807100800707070b01851150034003180306242c00c1c650080c4400f40c118039507a40c4900d1000c054047c00c1d255610f5010382c003005449180c01041c40c0d1020780c4485c0d21214401c455400e501c0c0d1640c00c3c40004e540785500002d104002842181c60080800d01c22a003c440c2c040c0c079010b03120442c03004142c0c1040c3e81584042d2022013200708000d41c2c01000b1005101810301141c1c00c04030070b89541581d0703030301e142d4079511140c04c188410014004a00000c0e8140d01083c41003001601d4032010303640b19000c2d11001e0b0341003008291161000b00c00c1100090300603501074030070318014046000032103100100803c09440c1138140100050503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 784584874 1250 784583624 784583669
    0x50f041713091d060703091e020f06030705030f0c0f07030305070e03010f021b0303160e2b0311030c060f132102070e071e051209010f0501060504050109 67
    0x1079070040c024424100466400c49640504400c4074280710740060003034400050320280280721f4007508a400008039440d071a105c400b14002c003049014140e901513200746040c00b565880340011440ba9009959594403410101240a00300078060700800001c1d1051200304501401e9034155545190149030106080d1550b81c0103503503900003418015015400d1940140c803040f040e1700200300044003d03c444c0c06022000d421151070703020944012414151424400d50354a21500360703d40f00d204001d0000540d418190707014004099281415900109100d00000038150040384002104600740c002d10f20b0451440c12650325650010041740c02c544e00071010920003a2181c0e07514a5965000070000a001e20201d1032040300034501413280c005126022000c1000505814101d0098185803204c801a039203110a14540c1c0d00c8040102040020510203001c10401d12510580220f0145000040030840d0b10510010b913a0305800c45011301c4820841040107076805000502290100480600c0440900b0403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 784586124 1250 784584874 784584907
    0x70f0b0328020d1b05040f030b071103030f06100305070f1808030c0102130512060c0f21070201060b0a0504180608160f0e071d040e0f030a03050f0417 66
    0x141ca240c0751001c00c20301c8050000350302c801d081440c8490081919910840c00311400d128a00031b180e00c40025540410001d0030510b501034010a0170b00f0040515084c0e42240c82c5160000c803003e002000140d41409480d0a0842c080790400c1003d00d0140701600d800140940100b03e41c0c000c14040001e02085012507407540340c0424080e0240e80156650354101c2020b16000c2d40000c01a103440075990308000503949450794001000e4038400e40030386420780d200010020240c00544001c0e400b60420442e820321101400d80c07008008441800b000070b1405d040800908441494026030030380442080006051600107050702c08581c03591100c1035010f5903098038a00500682d80c061071a9200b80c402540500182503c0d8206a07640085c01e08039041d40e03001d005a0301031054905401245550030307483e0006255030840c02c140d040140c00442c0c80c2e0310790003505250000036981c01180d90008034256462a41c10b0140d40c1d0441307121242414541000d49500c00030034001c0305400201c0f040028026180346880b00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 784587374 1250 784586124 784586191
    0x607030c0c1a04140d0c0e040f02041805010b0901030308060f040e0d020319050a120e0c0d03121a0901052403100510030c0c020f04060306150503070f0b03 68
    0x81d440c0d000b00740714100085250440e010391010030101100a00090401d9006801c1040d04401030300e003003d282180200700040040c106465100c810300c0380d0700260300c0e1806840500b0030002440c820b60001c42c2041404c41d04c0c0742040d24820f0010300c00400c0400c1d0f00c40348840d0400d004480c9140441da88000081c000d00304000752482c1806007400d4510300b10340100203410314002c1002048500d0715250411903480c450340800001242c884090796080b050b0b60b07400010100c1d0f481c401c85071902400070001e640b442b94038200700c0000310780d4240200d41c69414000c178030b234142007001c03020040c04000001405c070701d005001d01e80c09a0340c030000700c3c40941d0350550007060300c07900030003200e5813818808102c10501955010749801450314020791900f152003031040c25015112a52030098610342c903400c02000d8102c49030110b6001ea11513901101181c060b00c241c598901864213050f0540b403601040c1070504405500c0030300d92050030101085044003007022254892907030041c900c1d07e82014142c0c203861030403c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 784588624 1250 784587374 784587389
    0x20318190b09030c0322052d120712030512041520070312021c0e0f010c0206160201091a07020c030d050f0903010906180b010509060607030c0c 63
    0x2000311035000c202000040000d140280400702040d561140000d03500e200c0c01c54240e0441d4801c0051070410b96a08030306050004c48100c0c524407040d625030000745120101ca1081e41c1c3d51101051103281c054000001d0001188141d81d06c01c607020f540d014242e02c400e254469030000c1816110264101407180c8222a02d05100f040a41caa9082c0f50800f1075010901442e000c0005140640750501001010801c41d20004500000392821425540458982d042174048a800700d400344402010083c0700c00e0300d03040766040005c000840b500d103212071500d00314454421203caa4500a43c62906d580d02080c050743c42a8904c1c0a0b416080d4a442c1c200d00400920030041c04407009009800c41c6a41c01d11603480c06013950340e00300e1303014098841c10582c8806001d2040000324000700202c20006401c00041c10224100030b0002844010b6911680299040c0340703411207120502c070b041401045107100043d805000c0031713658180c1d0b918060022480d2441005009814005a51043c40420254102c1071300a030440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 784589874 1250 784588624 784588633
    0x924050f21030c1c0801050916030e0706053420060403080a0f080603031c0617010e060c0405130504080712050316020f0601090203090f0115060311120a020318 70
    0xc0f00381546860184501e54481040c2e0100340c2580c5109442e5a4141d600040c2590950740701e158a5104985c4004d011005164031201501c500c01c60600001c40140056210b180d84d81000c40b84080c022100c00303a500c0500c05a840300c8840a101c008001401164840c00309004c0c184d40d2072303941d07010b2070f014009260300c14800900401002424009013405807030f282c440803114074a9400235603100800701d5030650550300911565541c2c1c0c440d89c0d100c0303280c0b03624183c3c00140551a00c486081d081e4000106070340983d1281c2403400303002c2c3c0401c09107a00000e014040c1d41860704020000d140c0d04078002030f4040c52034a0f0800f050074882203004689080e136004500703014034040d585000d095500b0807688011403c0d0150400b0903124008160000740c0101c0d1f03009081141c0c01e0600c003000a4001410300701d100c0c81b441c035803842280424030800c000d002003081c541c5049071404400a0070b9483d510344200c081320050000b0a10940da6081c081c1d0080c99580e80981c881d507460030ba54201461080c11451030703105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 784591124 1250 784589874 784589887
    0x18032004140129070f140102070f020103240e1b03091c03110310140d0213020c071a0c01201204080d061206050a0507050301030b091002040924050f2103 67
    0xc0d10340c85c0545403413083c003590b40041c006075003103400c0b400380d0503000d0241c05150502800640c0f1a51100300041188a900d41e00001c1c031600b039070040822078005403840d464100a21007080003035030315484c8cd10483c800e42450351802241703443e1030324a890107040030300000c08000b500f0300b4003d40000c1210f44070740c10610707120300e0a65580025943c561286e80d41d40d034100319446001d41041d00c0c03400c40b10344e009070420300d2400b0078035507080080d0b0141c104006140944500860140f410381c1e1030003449070289610a44a601d4902881d0071078151203000c0034040c0d10060a424811124016a400340f1281c00e07101125558a0614042910403030b0003544003146414008101c00c41005a1405043e000b140d04000c1c035560208003100f100c0c4203440040116a0500041000880744902d070340c4e01c140c4100130343c1c0400040e482114203a070810307002039880544500207280c40f81102d000c41c115442050215081d0245000c001c50120000b04039072034000c94020448192010601903504c03012403210701141d90711007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 784592374 1250 784591124 784591133
    0xb0304170f0d0608010e3c1b010c03140d0b0a181a010912050a050a060b091e0c0c010204050d0503070b07170703020304031803200414012907 62
    0x5102c0c1069840c07080c989a408150080305114007003400a80000400a01c0c1084c415042d041c0c1030341c007080e40d10219010000300c4a1501041d41d00d8880c221a00074401080b058054078000e801000d105810481070486040200e540070380700d4105180180c19956803984501c1d0810003030814042c069810013644040052821007030803009065001840c030401800c40040c50800070500e90130740b8280042c00d115020300c5600c140b0403441614a20540458200d000c9540d0360034140b500803803054a00c00c4d034a11a4001d03508044003410b5000380d94540700c880404400c2c11030041c003000503003030079401c110200b03480d2642c070b100b54101c03005040000c2c024400b816403884c0450f030f6640305100840c1e1104c14000481c14090042d41c0064103401c9402101745c056a550300228003c2d00003d209408001c3c0b984142c40c6002003444111014500428481c039104107a200021071019000310107134010b514050000942820001d00b182c1075500781203c000d400d682c0c4440810f4550f21019100320f4000002030341c0420071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 784593624 1250 784592374 784592377
    0x8090d050f16050916050d050a0504020a050102150a050714030c030108191e0305070818091806040f020a230301060603020412021504080d03050915010602070b0304170f 74
    0x80d070040c00300c400101d42d5107220100b4090034031072150007580480124030f49a008907865100c000c5c3c2450498140300d41d42c2034983c1a030380240c0c0d070f00102079a100148029410103002d00c102600e001e0000301800d401100c42d0068606005000c1e540c0c1d90307a20004101001c3c401c2480500341c440c589072071038907820706c082526866403007031241030200e00c1003c42004146042003860740c9426088100803038010341114030070300c21080340340080b0300b00041044440300040501000e0058400e0724800c2c0d8450050040034000f0001000e015680c19860b10275050201d0303a000200f01d91700c00da0108007038090070038501c0400c40700442c9400203400003500c030764500f1074017100b09803c81d91b00000310001d005030307030752608150100d1107240224689010205a41030250420001c140c0900589940362458030f941c2d41c0c000303403c01d001468010700003034490b02401513904003041040764440031094a142c0b15454504040c0d6580c04038070a13048240700c0400040c050000070503904240016440d102647c80c04900c203102003d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 784594874 1250 784593624 784593643
    0x13030c11102a030c060507030216060c030605030106050f040b0310180606120209070518100906140f04150302130306140930070f0609031211070201080408090d05 71
    0x14115002e001c02c6420441c0700a029154240d2100c04011155440d86405800b00800c1001456001c2040148044402c003002e040303d4060380c1d000903045030b215001015100d081c0d10291107a07040640a002503610b00604c800740c107108460020b6844800340c0401e0800f82000a503544507480e181400c08441604051104100d12580c41000003e03154807054110b411b20050194001c482c40000400e200c0c003c800600f042ea00362130f410704000038404d000608544240310710100240d4004d000308092034200b6000d00c0c04514951103141011010424081d2031b000702d210b64403080c1e92182c0c20303600a034025070480e01c3c1d0540300c104c07032030b405512400c10501410300b0b0902d42c0b103074102400003d4403001000c14140d2210700f0b14140494007080507000409180c121300030840b804201003050100007110000e000b15003520074040400c0100329410090881103040a22060317050410503c149000030910854010a0782401d10484a840c0e0741000324403805004510754020010b80d880341c1c1400000140c0b5842c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 784596124 1250 784594874 784594907
    0x109030504080d050708250f080a03140103020f01050328050601090909030807110c030f060f0601140924031806150f09060301090b0117010f0513030c1110 68
    0x22010300710780200c030070348203c1c5000b428298086c0700c5000c131894070300c0500b00507808131b601c2c02035482c7c241d844821403c6c5090604030754051000540344201c1c0d40501030229400420381c0904459855a008580002800750282e07040200000001c1c035000d85603001c05104018000e0300800c180c260300410740003820103491990100e41d40d1300000800040c07a015244a82c2c0d4113aa4100031a02c6010050321082117042031030b0b070a03000b0300c84210004d460400820030301e030740008010a01400c0c05904800b0004003d072404c0c0c1040031030310810920b03d030343c1412101c5505056804c8000c0c10320b08651604421103041d650b10600030700005108403640030000a002c0d6020325010f96000d0b440c1c00040c50110200c84104036000168070b14011060325040742a264407c0001c1c00110b40424159182010075000b6003125900c080c2d1040704000c080000d10500c854a010391204000e1810441c6030102100c031182002820098a40c03100e00811000e464109031900c009400f00b0745940d40c1d00405003004d51402d91104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 784597374 1250 784596124 784596133
    0x50903281706132a081b04060914040f06060215070306080c0904060f150f050603010f0e090f0d0906031808070f110a03081b01050c0301120c08010903050408 69
    0x1000e100c03026a940101030003003101c440444044402c3c40502072202d2141c610403408841d03108080c403400a813407041c0000e980e52544528200c940100c140724101848070200d001448207205594100040c60152800488061400d2101f54001005040d00804a054080c00c103400007a403203400042c80210000821032220040c4d5034880c00b14100c031590f105189440d840085070080500b801c0c488940c1107030149102003140555220517405580b0189841d119026207070204003d10300150b0140000360004a501d50326551409801641d0440b0902850148034118404240410310030800041c0501a030740954000554094002d8299403491140501007410600a50400d075144082a034041e940250254108040b6440d00200700c0f030b140f201101c180500b00c0c00a030040d52220744807001544140113642c1c4e1036180c0550000ca00160000202c030580c1424140401c1052510903603040d0340018031010303010442c2c1d041c19101005940d1140c4555481e00708000140b6501400600540790050202c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 784598624 1250 784597374 784597397
    0x6070c03023f032203080c0a05071a07020f01020a060c0e120109050a0b071b05030d0e0613080c120301080c0418080307030213030206120a0c09140405090328 69
    0x910b607501c0750941100032504100b100c0020500241c07000116100d4110f0700310303061901c0b6920306007203a20103e00c011a9a21850b000b4040050401090001d40796a0300111154102e40929120700e004044000340715041c03540500441d0b901c20040c0c41011a0030a1040c00000403400f40079100c1010400090b0082040050038a645041400740241c8581c0c000c004268800303a40d2a88286420090071b03610802c50781c0c82001500401c0c48040880a80c0910065503440301004c65050455160b40c03841c640e19000b590400c210308134828006c000c902d0708060925a681d07014100c0c3d0b82040c4049054443c000004000400c00000004031209881c0c801e4800700212040c60300c6d98504100000001841041d0820000300c8061190300580f00c682e641600d91440c007612540003c0064000780c2030984000580c00400c0818440d5000b0803005480508161652600740040031118410400c1c42500658035103020460b290810003c40d44131092005028403078009202d01e40c4210500301d10300070700040442d113030b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 784599874 1250 784598624 784598719
    0x729030a0f021206190503031c0213090b04181a150d030e330a020a14010911040605130207050f010e0d02010c05190e01030e060c07140102030c030606070c0302 70
    0x705d001e84030024011800e00540803401c500247c0040b0021118940905c00031300714521600441014044000b40445c425890505010861382c10000c3e0700481c07403a0a081a02081d0114000c40e600220113812107510744c1c444058000300709181c200d1640044a2031040f8040c154440d1280c00002c1e0111000c42c07038580450b0502d503160f500350b1101c00e20070599215142c805043c81d8001c1c40c80507000c0c0181c0c1d440341d080d500e480300e821407102d45000d011b0f512492440e080001000640040303100440c2e0030000142058041154150890541000c2c2a0b00041ca03000f404800c0041e2400040d201c1c001b0301211081c1540380352142c0350240303800e0140d820b100c405100c05002d1030940d24009403c041c69204d0300d48104040310041c3c4c80e12195410306960394145883d502060086500c10041100d0691f0fa4040c2c1d0314250010300c0c6600340500b0203034414001d12807198001d904803a008001154a0360304c0d12401c0c14480b5500c805548000e5000c004580c43c81c8810209095084209100110054002042c0700e103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 784601124 1250 784599874 784599919
    0x30c10020705031b071505030a050a090c050607080904022b0204121203020d050a0c09050306040f0314040b21130b04150b210729030a0f021206 63
    0x10041182d042400440030340a41d0101811013030b0300c1141207545450f81e442d01d1100c03200e182142c28000030400000c2040d100031501825402c030703103e400100200c00e469200c2e83d00b151042c1c0a4148036400002d110700c14014810165a0008e1004000b19a030390007840c5003a600701c1e0358500c10780e5409d0345143c244031464480d2080c0d504540d607180f808a00300006030303139a0070610030061100050680c03d000c01100c5200758030070b413446000510b07400135448100c00d801800d464020b138007040c8254004020400049c20100070700b2811030f4103003403604020300503800032151030007a07800003140286c010603050405541c01d8a4400704a104403c81d0340b41d5100e07000c203684411000345024000503d0b18010500142c030142c041c0010555128001444061481c0011004226014546500c0112807240403003550240304130b4008100e108202e60842946260b9140d618000149003840030f18040b00285d68805103800a28020f0304c1e8900c00c40d03444d010b07148035000307c01c020341c1c050b4080c510407450510700d800c4484 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 784602374 1250 784601124 784601137
    0x20405030c150a0c1703070c0b0903130b070201053a020723010b0a180507020309030d030e010209040c030515011110050a0b03070608150901061d01031d030c1002 71
    0x12403542c900f08892009440340f294810701101e01801841c00d02d018140342d040554068a0241c1e140b1040510900300b280110f00c0140601e50a40c00030400f5150447c0c0512038802110703086005251034402d20700043e0781c04d02800442c050944c24031000c49403000012041003000e0906c0540c08041380300078900140403405071000052a011448051213200c002001c03808405841c2d110010695903009804650188459072010030351801c1c1c0b0312505100c0c0014090250312001520042d42085102d40c0017981d03444122848405140d41c80c01000c071080c03002e404494140c40080e209020391201281d0003001820101d844031409002e2503a0408958031030b050500800000130001c0c003002180c080c10f80010840501140c82041da104140891034400340172290091001d604c81001501d40303000112092603010100c01d1040840c031006020054102c481e04442e801e86140c00c2c03001c40380b0100103800920040e805c0c4044041442c400c0d031161000003000b45000200c1030309440e0550009105d4005a00911 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 784603624 1250 784602374 784602409
    0x40902130e1c02030f0a1b020301061502060919080a05040f120212071512060306061e0e040206030a0504060b0a08011a04020f03061c120305161b0b0903040315020405030c 75
    0x1000030308641481f0745580e034805030303606019003184c484543c0001c4c21510558400005e8034959901746025035018008140c0c01416000038080d226a041e0313101d1544812060024441070011524403219803091003030b60702a180282d03040411648910300c1804158814000b24410740c0c13102c1076440b18090111344402100d80103850464050000304d0180d030107000c2c44400406140c4d40da140040800c0d128004c44000780b07801d070490004e0041e0007582c2400100c0903000030001e00812000d0200584852040760f6100b0100c40b80007500da1164075081300503240d510100c55001d280319030081403521066001c2c03c1c1c845460542c0c184050410b40900040c2d0168100035845801d0900004200e420b24240386800c0f03021b0300308052010320f243d83c0c86120840c180b80846001a03a100b00b0404021030640c0364081700c0d040c90804082c00000040c19078480c452400b002082e2024607030104502d42e80800c10350340a142d100508a61050364100c0b46030080d049032040318030078842e26085c000f240c1862072100c0701c0101ca2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 784604874 1250 784603624 784603627
    0xb010902070308010e0601050d02070c050901080303040b011412010c0801081006060507060207020a0b040b0304020411043c0b0c070509100608060a03080d0912140702040902130e1c02030f 82
    0x700170501403602c50003002c40d030500030b003084510f1304e9058134401054030070704c02e0303124240c880e040409010380140160032000d0030703900800600010400316100c260444a584071402c0c1c0040400020902c1c0e4952022000c80c00d600300008131580e95000601c0300d040c0d841003012900000c80502440e02039500920900c408034400308412008501650002c06880740081c140500841d40d8085200311984550301c11214600003209200441c5041d016422001558036815400c0604041d400b0302200c00c8034020540c84c081080d11118940e40d0003501c1ea1560189061500c1466a03511403a1a10350140d00b0003203403405049404122450710441041c02050346402c80d061523400e10700d066031400005000c09520000903500080000d410360010444910403e201041c048620714108040048908031a81801038819490005480b280e0540b10810380441c0c0126901c1c0f10b9001241c1d00ca15041c2202c2507039414601041100702c000034003a0310b13841c1d5114000b4509090302c181241c49014903541c10840180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 784606124 1250 784604874 784604879
    0xf0717122e03021309080307050310060507020a06030f090b130302010506030d0f050a170a0e06151c03050409090309080d05040b0711030c0d0302011b1b320a0b01090207030801 77
    0x410b4242c0c103205441a130340000380300000791a152000d070021251040000d80000130440e541c0c00840d800e0000700818104241841415800500c02708030a00562003095070328030009485c2d12103604040301c1240c00c0480d2590909111900d00d0f02c00d225150198003544c03d1101040c0c0c1800c000400c004400c0c52035590440b00006150211010f61108405404005003515400c071051002c407101c5010321203244001428000304000941401c0d00100f11010040c0866a0305005031565801036480b0040702d20419101c1c24189410f82e03050059411998607149843d0080041641000c2024150f815860440d0b061400c0910103d5442c4200d01490740d02280500295001800000070f0b501c01c3c45000302a01c011704441c80c00324088001c4284250b0050b034403280340041c042c800f41d000d000010214a4403200c0c402242d6107900c0d04000124004000c403003100100682001e0b0390090120b646000c0c0380d2984c01c202c200b107500f0f90b981c4180740213450611441c000040d0440c40c42c8211a400303603041c0c07202d441030303171 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 784607374 1250 784606124 784606129
    0x40312200a0804021908071805070207140a031e1a010605090913020907120c02010b0609060f1e030403030b06120601141c0f0b12030f0717122e0302 65
    0x10010f08100d0308404480082c8a5440d45401d11750082c1007624001c200191800741054080b040110502000c0c51a14003800001a40850030400b540c20b15265102e2114221010400c1900c40761700180001101e01440d01313020301201c1d400c0c42003500a210300001c1400d10b03115060100403e11a20022580c100801070726400c140c10078070341c4122481c1c0d102068001c2c036000705600355011116200081c0d69200346800e000d440b80f1135550140390318030082103006507050202e5118803500421034401c0750b01054614149000b0710449284208451007030104901d04802e2075070940083e2001c034046801c0c0306000030981404030070744401c649680c2c204d04064850800641d50304644480f00c1c40504010412142003d8201c90300e80001c507510040003c5105211401104960041090901c03c51000c4081030500500205507403c20361105280755540c071280ca41200707071201130400c0703100d83c0780e001c1007808402d4180d007145403103250b0399200208510300482c000960126003034000344405c0540f40042c070150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 784608624 1250 784607374 784607387
    0xf0b03061e030109020904060506120d0f1103130b1806070b0c071a10031403070206041e1503050105100e090106050a0216090507110f0706030f090b040312200a 70
    0x104005000004c5040030703074000c600d09120841b400d4513075580306e809010480c1030031041c4105003001040945003803881141c00400d4410070b2840030080001c60000745900c000203208841034a0900f00403246510783d42c691142c1c050300311413400c400003070031140750705041d0400c00100e895040c3e100d0f40344a6156074092a030481034000c0401610307000a0508852004602069110300980c025046118010310398580381c100c0280b82d09070300009030000d22888006840c1c44007500e040e10031156580c040342d401041401c440c0c84d4a1f90040380051604030041540b0780c0c040c1d00c01c5041c1c450a40304002104542c92095071811040f40b01c09401c00312550040001034030030800307422038081d01c1c4140c5290030101d10611520301c42540080c0032803940d076030034441d115812244107036016150401500028254501c2c840e03d1320064803e0400b0702d511010701103581442544a0341c1ca240d4003150500740c80c1840d040c024200354840d041d0081f058a0f18583c402e900d90f41441101c296880440d80d185001270610046a82 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 784609874 1250 784608624 784608679
    0x6060f0d0e060a0501091a0303090d0f0f060603060e1b060c10060f05010215131b08030a0e01020d0318260f0a0201050c092103040b0c03040f0b0306 65
    0xc0955401080601010510116000f41400540441c1d11350502d00301708111340c9042441c0401060311203820440d900d02005484000e401198007c40480190610310301800725940003d280002030316850040191326800700065074014002003081d2402c0009065036180721a5681e09071441340c00034402c061501400800d6600360402c1950640186165003005446068000c51204420346034103100300c0d40d0410001d407000307044038013000840c10081c200d088a6a05040090140070b541800602c074118015a4100100039610490750b658000c01c1c4000d1501c4803000c1c40e14010f00500f810841401d1103801242899030707000301ca003622045581d03108105c08865200f60304008821040f80400061004081d2503041c140c0012240d82e400c3d42035000342160001003034881403803410700440e0350640b1030001c09007080cbc6480c1d40c0c0c450702010094141c0e10710b0107141e12445042c84000348103031307211602102030400c488a2034510348036551a64540d40e0107000031039825401081c5050410905202034030710992 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 784611124 1250 784609874 784609897
    0x20f21091e19080c01261e19060e09030f16050a03020f0d0302040b04050d030e03070906032f1005090604140f03010614060904020c0f0a120806060f 65
    0x4041d001101055600e024031620000039035000308200300d0254103004007880c60000b440d08200b51800e04105511600c1065140c070950100c4d07400080c09140c18009400c9603006501d0007047c0c510304403202030b1514a500c41000011402c0500c0000e07815503030ba81860103080801c01441c2041c84035601c580c95600010005090b28040e0074020001c924140070f4071010a009502030400d048604611610340f000504161041610401080011103640d40c103540680d04111080d480500d514101103c0742401d5684990307160151160018240340640d10040460344142000c44940d40d08021600b4558220908420b4003518042149006e1030003100764243d010103400e1040c00c1100f25408600d09030440c0d0840340c480041c010303241c02d49140c00610048002130460080c0a2203042c0503040c10408200d0781114011200814000700076a5a90150b47d0504212011502c200641c0203541c0d50f40d80e40740c4800e841011542e41c0c40345400380718010591043e00042c3c026071420030381c1800000031340e001b82c5c01c400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 784612374 1250 784611124 784611169
    0xb0c0f0f030a0c0c0f060807020613030f0f02031e04080c1504060806060c07090c03050a0e0703081c09050106030b1305070501050d0f24091e05061c03020f2109 70
    0x40d85d9142e82102c4800b60030f06582e50600c40c80c00c90070180c5040800303814614040325500e000400207a00111514000d58949821802881048026031446c0074011010301034440c112580b6410680d01e03806001210320460869101942c440107200440540c032204005c2800104000c1c03150742d000f441c0494100e00080c1c00c9038900240c03111140c3c1400050b8018007401a1902601d1101e175516000742500103480c29000c000a0704040c840796030301c000511005143c0c0324041110540321202d0440050b1340b220420050008000e5490690300a140c54041100d51900301408034000d003161500c0001c2d42d590140040c08101e0902005448507003001d800f0b9400c07281c56648601402e04a4000c0e5098418121034181e214842c101711038000c44c1042c5c02848169113810b004a09403044c030829032468202c0c00341c0005950320385501041c8136001d5035107000150949031015100700755000401800415012055890100e505d1000c1c03420300c207502c1c001c0096070310300340b06444803450414110301841e6181604013 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 784613624 1250 784612374 784612379
    0xc13180b0709030b090a031d01120b0307080102040e01032a060c050c06160210050f0f16050604030c03030605151801090f180501090c020a03050d11040b0c0f0f030a0c0c 74
    0x5003000e204c121030039151500649504030416801030b01c0e0001420304410310003400904040000d052a680344248103104e81c80d440c815240c0e880620000700900b020070b00039940e1f01c0c1ca070020700e400e40d04280f2003110446006a40c40e43d40b400c40c440c4400d040c24544460803442c9244c0001243d2414141806403400d00a030760031100f05035584c00051020103d44c18010300c101516004002d011011004048140300702000200408201c1c0011291800305050880b074682d03446400e90305040c080424020503500c02d1205000600d5088030300701031428803d94060040d6510342c81030201807041034680c03c01c0150184810b4280c110b0f2100417014028062400c512055a00c0c00e022503009410381c04141d0b00341005d540041541420300400c1e0160070f4070442031190385c035450802580c61000800280c20840e0106032004214003581010310000212800c40380c40d69100d40b07040203251701950501c801403041d00410158814082540d0042c02c2c03588018504104024070251155010394008a80740001d60001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 784614874 1250 784613624 784613633
    0xd11010f060e0114030d08062b050115170a030c03050903070609210f030e180109050601030617250503010f0b040b1905100306080d020c13180b070903 66
    0x501e0000d10907038124950035494000d44418102c070141c5607a01a070071005469607010b400848840d000482035594000c01c40306034804241003006001100c902d042c1c08601a000e0110540100510320300c0d0128400c0d00d02d65038014106846540c00712580c49421a000b41d0300800d024034030124580307010b401c0c0380380b03014540000030307040400300d0704008040380b201e01d014440c2d0070100010714402c011101e40c140704260103483d00da4031410503090050400c8400100d0200c1c5807038030302e402038034174a401c1400030780c3d1b50b150102d60018010449010340007078503094001031801400c80005032030100d9080a00b00c0503204101400420100fa1103480d041c242180e40040e042d1000d20a07002d601d444d5a8001501c990b080e000c10040d101010825407192040c05240351074201d1400c2c2d000115001102d03a202c9070104808240e0291680f03902141030b82c019407600382442034001c564241120b00c11640e00c40040d45040080080300c0110120f00c55009030f5900076800528003603002c60308a2040e00b0303c0c09183c4d07665a40c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 784616124 1250 784614874 784614881
    0x16021002090a05310e0a080d0b0a06110607051215041d01060f05040b09160201151d0a050712020f12010329071706041b020703050f03070201020d11010f 67
    0x80f000d034013005800c0b04809040541003400d802d81901c00240600c1c421032814580e503000345000940300c0000001d08008901859110144514009d030280c0ca002c0d9645601604100b016140c55400303005080000d10795a204800301c0e0361000558418507459103407542d01488a0540d1848260426550160030080301408426416580d6844001107002424409090203203446584410300480c1405088201c560300c00c0c40441d4085101424110404617580c001c80c0503007072000c0824401d0000b1400031a00b203403400f203a1010702280402d000c1140c0c499170802c0c030868104544403000030340611104207492000390000d0902207008510682040c461514011440c482a4011035405032a0700f80400c00ca481141340d21400310107143c111006181406002d49240c010307184200440340b9008c00140103690321b60200c0c81203d0b041c01c96a0f0054055800130b9640d500300c0c08207030740510407580c0d8a640000b0010031640130035810f038054801c180880c2010740b480040190070070a69500d800c403060020703d0f02d01c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 784617374 1250 784616124 784616149
    0x30501020c0c0a0f0b0a1d1806040b18070f090312081006020304060c0b04021f03021c0510170f0d170708130803180a061416021002090a05 61
    0x10250180c82014000c020840d42e43e9404842d000c1c646010800032050325030103803814051682400441007501c0181c1403402503000c060302d503000f510040444240110440f0300c03440b858003500c080001c44090010800420142141060351211902c00140c80e2882041514a48001800c0c01c0c1c0b40e0a450382c0d11103280d102000603070000110030504000d07055030403003c42002419513001840c40c00d8185000207091403001540601802500c02c0490110f445d107000340b107002000d074401c41c3e10b501c0c5140001000f0354010301000001550b03030308145021107018811070740180100182d0064080c5031000b03041c007031003540b0440a40c1c0d00809060240c2240240501c0741c44141590b5020070b640e00383c0000c5070703c0b540094081002c120b0244108640c00d00c14880da1f0088030b4000c1074841d101c0d550400e1022126400030921041c1e801000c0b00c1e1030030455141c014a04142c1404c0c1c3c80b803d00c1e0b44400c1c1d94a1290b21886000b001039002030a0910f090355958010146004041d00800c209a00c0d000461165030910 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 784618624 1250 784617374 784617397
    0x2104060504051e060a020901050408010f0614031906180f05030408010609060b030411220b0a1401052508070f03020c010503060f0613030209010f080705090601050a1803050102 77
    0x200d00300400c12400b031200403040c5038210000392094105032041e0f543c541008004840d01d40d800281041c1603805401542d00034010f810007030050750183ea240501600040c89804240358941c0006299850007003200380200c070310030301a03818281103901c459000d0020f026000c0107400c0186c80c41000b0550a405e140a541e0146004598851910340a2421900036600c01c9404e185003d509001e8085e800040700d40080e0440090540c8424920000364000751b0051083e080740e100d000300a45e0b100898004081051089405130b1001c3ea8504001000b03d18100129001031010482420b100e40ba031501c43c80e15074201e81c804040c01702c0c60b40c1c8044090f0720104080d114610444008002c03d60b04003c00071404600386401811070a02c130000c640780108890480c1e11440c4085900c04c040e10511100000440d0020101520395035a20f034035038108801400348422900075000c02150b1401d1480400340a80c00607569580341006030300302101c2824030f2154003810020805800400309400340041e01c0c0c0d80203038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 784619874 1250 784618624 784618631
    0x1c091103070f15030b0d0b0604060f150e030705060a0c08120106050702030d090f05040c03020d06060c0c0b0301050904110d021207150c390609090c08100506210406 72
    0x83c031404810002500b40900101410000b00800503162000304610300b0703600c211212042c1c2c590a00182c040d005580040c07000c10800030300042e010911400e05506468952201540159500c0605841300802d01400b0b400610800c1900c001070312407868654041d016044032405c000880b03c0b0b4400c0c244003030344680000744000c070300401945824890784500e07a499043c02c2c1e078924500207041344448414411948150354802e65100040e000350122032845c0d502c0102040640d454103405032052115a90940d0b8131079101d84081410302c0c180701261b059030401081c0c034010b80d85a55034042054070480d040c0f03800c5001158183c00503103848120700d071846110806480100d05195410b0344282d002c2e2004000c006050041c0c8012400320101c07a00c1e41407201c404000c160b04a28801c0c08a844440031064081c540d403000040c103258880c1c803020030381e50040030078130a10306c03801e8044406010550309040900740c0030300100881e1400c18020032040301c250380640001d00b48420360a0502d482110282c1d642501d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 784621124 1250 784619874 784619879
    0x203070c05061c020310120b04030305070203040b070609020423060909011a041503050303010e090601060504061b03020c041103010504050a09150c0905060301140909031c091103070f 80
    0x1058024001400c03040d1200c1d800c24840c0034103503442c520161148500d4650003c045101604d403411b4817000390a00e05030820b205210341c64080c002150072941030300003900c0e00000c244040c0c40801158100c484003e03001c1d04095040e1030b960014401c44104a902c10b640d4098803414030941014510000140c1d43c41c00100d1414105103c4081402007070710003907925100c00c12024010206104068082c03d5030006284000d0071071315141d52000b81c201a02e107100c0440005006100310300000c0c419004142031350103a980c1c4400c141c035540245d015036004215845c007205c07650707229103c600126a0081c81255640e01180700030034102d4004148004800c1130000050059040c103028054100a024800308000d0f8095203888035528840500e1103022515542c60a031103520400000014044c000c00040d540d581d58160380c0008150503820718003a42ca0307a000904030305800f0007560420100e1900785807520384411200c100815909004580804101031802000d80b0200140400780c503540c81421003450 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 784622374 1250 784621124 784621133
    0x3080a2c130501120b090307020a0b030a0c1b030809160b180d0206190504031b03110d150c1b03180f1d040609022806090812131203020307 61
    0x500224030740041c0d41494010400903590f526041d8406402811110381c075100c41c400c440c2148141680030350302100152011450010b010015402003242c1c0c03c1c104080490004150b401404110004c8081c500d001e201034042801104066030042194060700d0308044180e0f0541940307500d41c0c11000b0500b001141c074494103950014008041641144c40c043c1c603018507800a400741c460410850500c0c1d401e42c0984400b640a1800d0f14059135000c0052801d01c2c1444410ba2084d4400c0c0c801a20f407040c1413600362500b070515142080c907458010400c008040021038901024161216624040188503250040a01c10120808245500ca5611009000340001b5500d401644c3c81e00540da02c0d10482801300060306041819020341c2c0c0c044d510594031566a400e01c1e038024502101c01942200d1001103a103040380c0280320000e0f1310080456950020380c1c80d1003046854801900620702d4035400150355a00d0403c107500980743c400e40030741030b01040d261100a440e0f000d09000318200c0240e4000301e010000c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 784623624 1250 784622374 784622389
    0x10050a02220f0911041e0e0103060b10210c140325050406020a020114040b030a0c02010e0d0206010306050405120a05040f14090601030f0b06040608040b0601021603080a2c 75
    0x500c0c480800b800100140b0030541101d200324402d001850700240c500d465243c940032121b000a01103078404103090740e961304000015042000072203200354480141915084c0c040c1c43c0c02075041203400c10482d03401007040050320050882241c0c0c80d040c0854044000081f140101c02140710f2410740000c95880811090071078507200b0000b103404240308060005000441d400200c03006800c1e02441c010010003c408031060b06442690070600001e500002044a494910b8120700b89a000c40c0c0d000300103100100f06480d4032140050024801600b05c0b000401c04201d19400003a001070041c001d4400381c050000c081a08c40c2e03c0701c054180481c1e4040f4003042004241542100240481014041510500400524170b0030300109014189942c44e00c00c80902ca419038489401048040c04241d95980c035184040c0c14200211003ca4144001100040e020351020440034000085029180c0c401421075030340c2081a0412229070b010400c01051220640c01c4e1140709054158500b42c80702c005110442c14030210 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 784624874 1250 784623624 784623629
    0x2b05150703050103051207060b04090302030a090e07140318010212011d0c030a051b18130905070302010c081903060312020a0803160c0b04050303010509010e040510050a02220f 77
    0x9051502e801040454000300740706070040d0813001d00643e03c81c1585050001042d07070b012050b80103403408981034100b50f0004010030708800e00d502e03403041003a61014801c82c0303a10107c80f11000994840ba01c0300281c51100040c40d00b00409602d41c0100312210a09103089803c00f0701281e41d41c0b0780c090010061171029050343c401800d00c2e61040c138020310b13220391380a40c41d2101130800d5032455503840c0001c070f0380f21207008061294042c0c810159030701c2c180c0300d5140d980d084400c0c8850384540003000c0d5124001001d480b42d100007640c40341c042c000051868005550540080d082501d070b85d0010801c000148006180c00004903038141c4000030340360b00354100b41201500020210b03040d0340c03125030020007283d0100c01341c9602c2840200c220f28104940c20049460045200300140050302c1c2c98244005c1010100146040e80c0f82500c070300107641e90b82d40d12014042c40580300640380d03403c18403102c807400c02e142e04225032000c1041c10240c07400c51105841c0c1c3c1a14003071002c1d11800340351207100740011280540c08000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 784626124 1250 784624874 784624877
    0x712020303130f140a03020304090f050108070905060a0902030f010e090a050705150d050405071403070b0403020105070c080d021b01092423090406060903050a022b051507 75
    0x640ca021030b20044000304400014110b841c030b400040003080800d130100e90304001150151000420f541c9030180d56500b00340114103030b05040a101c2c00008206202d2241203070300c800024070003140b41044401c01094050700090f040340340801b000c070792020f20f80015402290803a00414156142004c0300c2c14903030001d0a009081c0d045031045401003040002e080055500031100181030102004d0700c8030840c441c9908905090b401c0c8001c2000303100d40418500e0488002c0080e2000001c1000100b40e00d88001d4010310305001d40c144001c1c405548070b100074100e0584145150700c0c4054443c07010516000c04609070100580c8114501d50030510302e540001c7c4461000e080401e00c060602d1300300114109038140002d080c07040700f01584407452041084603140c1c880048038041e0300791440c0c0e90460302e901c0f07401c125000e2820600b0008195209008410860740c004001c3d010105242d4204180304480c55140441242c1000306402e041c5503400b1145042c91295000342130390180c2c1460040d841800821040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 784627374 1250 784626124 784626127
    0x1f0605010806091501030209040c020f07050f01120e03070c080a0512090d02011b0b10060908030a0f08040c08030f090a0f0f03081c061202030105090d1d0a0504020a0507120203 77
    0x343d00c8030000c3c5a0406240c00012a580319001d004800a028405030b80358082d040043c401c6a140e00450742c1400c208803072058841550700e840c03c0c400c0302c01159000d50b00048032140450740c004030a50110341c2c11503440d0150b80c540b00003501c5414448680b50071110054100f10a0381080120402441200d040702213661410300c0c42840000d540340c1c2d00741e20301906000c0580f2040308080c0d5104444104598041541e0b1110306100700000d0302d40f0813501901c0301003076620502094010380001521001d034203607500c0e50170164001c00111031512000e0401c171070220341c3c0d034800b007540340c000e10140000d100044803103a100c0001108110101540390300010110510540501c00d2000300e44828080d2500419800e903550154415401420803000304be441181c5460400304840042d409908140b50003100240319548900c2d42e4181c4032106400030b40041581c034500d180c1034201e201510b18513010010103004445581d440070400366400140044002580003614404001000100c414260441c3c030056 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 784628624 1250 784627374 784627381
    0xf2a0a0201051501140a120603080c0607111b06310f0302033304050d0807020c090610030204031e020406080d08061903050f0a03080a0911090403111f06050108 70
    0x181c2120041800c64820005c0022134030441401210401031107001e1500030030400383d030303810031481316000104040c3c458010840440d4081d403044032812012400d6002405501c0f2034440702c5044196880421a00440d09000343d1202555860300030b04101a00c0b0340490320800d8210007a8404496500130607000c4100e5071080c00035840000d0304040a802c070000300540c0311100c0004040e11161403a2000003110301c0c104010800c840402c0c1414000c42036119107020361103000060ba2101e0140c1c1c1641c1d0011040d4000500b1031070700c40d02c41a82940507050045c0b4003030f16034558014490b41d503405c00541c200d5402110046041c070340720f030310000c007482005802c640803031a0b4020320030803001d80b0030351041c621803120324104a024040c40e4011035112048070824502c3c01002a1101c02a074400d40100d41c0d90400500e1380c01c0b9a000751007a099000780000600101001040511440600143c04212401d000c003100d0368810030000011030158028004c40761110310440c0b0507922540c000604008140090 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 784629874 1250 784628624 784628627
    0x50606040308040b0d0912031b090b030f0613060e1602070602030d0207060b0d11011e02030406180e040b0f070e301209130b090f2a0a0201051501 64
    0x1683c0a840c0220700300365460f103804240001406a0b820060081c0800001221070980c00d6071140b00c89003481e091604001508c4c40c0d06403411002882281c0c240e070010000a050340b940c003284258005c0d40200300301c01340381d080d50b009411100c0b180c010408904165007800340c002c16114420501c901584020b210580c2070100003034507405803181002c0625004204d0b02d040200c29001801080c0d0b020307000383c880720013500b401d444a03440c412a0340d010401c1c080c0c02c1c1000303026400904200c00c078141c00641c5000d140c00400c80f143e9005070120103448102d10b40c04036000000d80003050249010ba09144540d00700b02c400012071001c050038203400c0c088402c519400e192a020081c2c5070342800e40704c250451415000d10100b40c04000c4150041601551f910380311084150406020500300c02e503280281409404000c104844030030401c035900820782c1e070005411028401203107910003900c05114050054a082c0c840300740300140c0100001c800d01003801a070351b1364240325080c1d00c44503110a03408018400d100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 784631124 1250 784629874 784629877
    0xa0302011409041505010e0a03020f0d03050904090501061706060d080304030201451a0c1224030a03120c0302130312090602060106211d0a0204050606040308 69
    0x40281404141d01651500400190596624403000b4005000f00780303036494002c1002140d40120b50200d6102c1c07860206030308084440e20140c0340c1c0139001102c440d000800700040d901768910708030100304042003641000c6c3c55902811840b14030501c00815102d0a0400c4100e0b030001c072000c40b410702ea020400700459940c500040040481d00807002c0395076a1600d09049005d0801d0300c0d581840d03035109810035105030031654001035403030650b510740e04a410000c081205500b2801c840281c1032808059003a5580c0807820304007a000071500c9015460803c5440340204124001c407080c1424406c0d40c4c607010104080441000d0700b04008901800400c02c0e40e5030701030031454100e4107410909a039101c414108501960441d0019100c041000c00456076920f00001c900090b9240c400000c1c00d054400901c490001400c07074180c818648a01054260b4585281c61000280003081d5509441d00040160058410860994111800050501030509005101c145c850107440103021b108c04000c2000451030500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 784632374 1250 784631124 784631129
    0xb0d111e0a11030a0806010210150b0c0106150203180f012c0316050a08060601050d09060b150309120a1b29040309050415121505011707050603060a 65
    0x3011035160000c041048070a42c0c0400601e07541803000140d150005908101c110b880703141300b6400c0750100106d141190f020b40f01140724100058110316014412020300402616000ca03a481c000151240c1e108030112034410711200010268000180d010408100058107006800017901c1c2c2d0b00720440504002089242c2c03521222400030188046000f417001c40040380c1e034451000504440c04641400000d4904511921a141c81004468070000718040e022a0706445004140c54103030510f422442e2203000b600e407802044412543e21000700c02e8030784c0d48074a00d00d004c043d00d1080688030728108861500d01040150916400801071159100b401d500022081902c1d5484104003030510152030326100d00f404d800800d0300f991825107041000440807100c1203200724081d5403650103107551003040c401116000d50307401060b448828024085000c3e03182018a0892040001c0e00d00c00203100712271422503a081e04644001c94444100c11550720040241c01c0140c04122101ca140d0b042c0680020920429071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 784633624 1250 784632374 784632427
    0x6020d18030803041a0702030a0305100f0b07030918020705150c040b16060905060906071403042a17010e011503060b060c01020a2a0b0406050a11040b0d11 68
    0x1070405c000d4014001104540c1805500c0a040181d0083e4803a0813043c60400020302d040005030070303203a1068040d0110340450f034407200301c2800c160031031003907503c280001e4040c0710460200080740b50175000c5485800b90350880c01601c845031440c145050480f1403075010410070140d4280700c60201c0400855044900000c0c2203035440e41081e500e840c820f400070001501451a03d86424188038021419910601c8002d0913034001769540507003039a4134003019800010103c03050000400180420035010340403519041b0140e00e640140d00410103044072504020000400c1d90003400c000d1000340249500003150b00002c2c0601d641214400246451511000e8038464a940e41200c6c0c80c5c88040c121001710070707c003000750f40d90480004050008290399010303540c410b8000d05040c0ca0110708005d502c0c0d9035903001d265040b650f00d0300d80300c54007d450040d00d503162a81e91250985541c00810004000500c0c22042c0c1c04e0b183c003a10300318003088078074030706c09555020001c012561014503044400c42c2c46040c00b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 784634874 1250 784633624 784633627
    0x2011a01030e1216060b0306011404090317090a0506150306060402070222090b16080f090106120308040506070201110f181e1014040302010e1c0b0106020d180308 71
    0x104581c0f45001d4090309000301d41c0d500015a440b15026400040c0301e45030103102c0501500614800341a5103400034030980c40310308032840d041140c1e45001d800034040c080c0603250604a00c1d490144858510b802501c000c121980406110020448244407040e480400901c1d116031002d04200400d0716110000c0030716101c0d5900041c45011035842030321040b83d000e003003080c04000e00340e1406114020040d14a050707613180c2d41540011155441c010710020000303241e549409071600e86841c01e010511024100c40304c0c41d525004040381b00c2144440d017680090081d582ca00c62030405062807030402030050405000c6904151a4500d2210803008450114204004007561099070780300c110501801a04202d502194207408115494241d4500400380c1c3c20072203042c080c80c0c1002c0c03400c0e191540c004040740000b500a0000f04050f6000d0a0040b080b1301c000b82c03602c0c000b514000780d0b82c4000e68410701d080303811090290050288581c10040441c040d601c83c10041c0240340b80c80c107907140c1290f5521000785101d10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 784636124 1250 784634874 784634891
    0x10506010e120d2609030304170f04121103010c0e010801080604050604021201060b031303020c01020d0e04090807140616390204110a14040506070803130c030501150602011a0103 78
    0xc01d840b5002414139103c401d0756600340034001c03a84a510036541902c010340203107281c14480d81030000f291103c2916812051415160031a01104090030b21001c2d03c0000c0402102641510203008811001c80d00d96283c1c00d44034216800500700c1c84040e00074800320f03440300d001c2000040700024401e4104d601140e2244151030700019244c09440c807600304406d1914003009000c0c2c09010140fa018101303202e6000e4420001a20004a0f030311700d0804607a0340050010b84051046003041d5201f24010350150b6820343c609501501c555480110f039651203d0740e64003030001c0000e179114015000303008400a181180c0c0c00760441e14000c114402000d003882c03c081c469104c009091b800716038151119580a041030040c80401c9844050540000c2c1c110404554401e001c500c0d20340d0444219010360300d00038407507420000c09442e0f60105810040a40d400408c0400803a0003190300040c0070310086120b1000401d0000250306aa1116503403580400709580c1021b44d4900b00e80c06880c841103104000b80303000102d0341d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 784637374 1250 784636124 784636157
    0x20d02130603051c080907050f011b1a13120503061c0b04060f0c1d01090f03080a02010c110624060d02040f050a0315022802010506010e120d 62
    0x21000d04040c01031814200008215010406020120066031440b00c0300c01c4421007901c0c614000c42d20003903541c00c144018010303407905071300800b1100380c18948400400481c1400d12415505420140c1d58154a00320708040c4034504654207500525503420103e503032040b03a89081c03144041684020a0200c04400116940c407a0b01c820b0192843e28283d04903024901d0414200618064a050b1100c03810420b501042039128050010012955525018044440021b448004020540f40c50400111410010b0038000300740210b805940686003155445c4500b00010342102c8150814005000007a07048040030800852581e0740300d00c141d15034030354214082c0c01b045000400c00b40c0c4603174024070120710407941d9102680504143e03541007880c1010a503c030020012811035510000b400c0c0890300070b0039074090515030050b181030b011203062040300817102d002c40c0c4441400c02c3c1d1500010b0b994ae00820890f503a1085a03c0e0040708152001000c8038541420161a503400c040342c3c3e014450906214102c0c030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 784638624 1250 784637374 784637389
    0xf0d020904170732060112031107051203040e0f070804150b100906090f0806041202010f0c0c0b070915030b030a02120c0907030c0504150c02030640020d02 68
    0x40358010100d40a03821004035000484e1506018140c40c00307001c882d01e549900c40041c0c201e060b07400c0c18000c950751a04070307501110100031501c04070289002d0380300000b400362030700c41c0e220b40d0855072a4081c64480c2d040604006400400a05134031a1060320380621070700e9600320b55441d0f005600540c1d0680384400d0a010900500000e9250a030481c41c4c1e50100404a5806090300003070311004d40d12000103654a0680c8614880c490003a01140d03040400800d0005200c07690782d0714010311030300000c00c885150743e151a08403040c00d20f1440c00b05951083c98010030029012140e0b0108007402d1200c152401d00d9581d550355401c2d21280f4082c5592001505441c2d03804100e030000007540180344000e9000801103903030304c600c0d88080031030003140e109001c41c107424080d00500c0d081c0e8105030784403070505241c1403615011410280884007030003c0d880564004d40c50501240303110b448403c1e01600c09004909451940c005801440e41c034040c002c0306468044880d130071020120a40440d480b1500004500004005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 784639874 1250 784638624 784638637
    0xd12140610050c060f060a14090a0203040212030c10061203091509030609051c021516261014130203060f0a030c091104051f0302190206060f0d02090417 67
    0x41c070a5804004500c00c508400d9446050287d60319405d0559030418000204205e5984581c4580e92030005281c00a442e805150b10600042121192980c50003040342154030541102c000780e00003140d001031000183c0038030001000c402c00b43d0704441e40142c40080555055024003501d511b9200d60320348846100703400e0300015582140081082c00d80c075107404da83d2807410302804a400f03004d0101070340c034040c00483e03124001d000703003107010700559913904501100302100d411140612001c1414183c13580442a42d0a0954208580b6110f56040c14108030342d20341c0c0340b6030040400b8050071003029295241d41c040d2503440b182400002da00c0f43c8481b000030302012011040070b5005100b1181c00403d000401100d5011120420010071030011420030503e0a4030031400303029045440d010b103a0701806408184c0304100f5089103401400d065030407642101810b0203040180047e40f22105008036458911744001000108a80c0816108019808542003410080c805844001c460340c1c1c401c015a10074046444 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 784641124 1250 784639874 784639897
    0x50a0e010c0e04050a0c140f0f0c0a020937092901120b13020f10030903080108060709062001060303052701021009021906020d1214061005 61
    0x440c0c1240140140400c001840d50b40c4074504150100c1c0b01c160662040f9022900e0660320300403c000900c12100a543c03040340040003000b0204040b15080b0010005001065103800c003800c1d03154400e004001b490007001e003004da10a0420409110140485403074502c0d0321540c49096248100401c03500c03401004801400703009070f002214076196490400610b04600032000f0044210303640c88005410300782d98414802400410a00b005c83c0700864015204072500d0b20052a200504c81c407000400c070360079440c001c120003080d140c1161004154111301c8a501400c041e038010030b02d03454240c0c0003d0030006184503400605c0700300d045014061201c1000340d00d070354181c54000c4c05440ea0b031b03103070041c442d9002030346107010b5060005034162003080c03204800c00b03088016402002c81d0046080c03060000c244400c4200da000d0840c10b01c4000d032100c5c00c00b05100411568016100c10b51141070007900c880c00105442c2501d500d00008400080b12028407207820200981d0041e00c0000051001d507240c0c07203101c2800703a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 784642374 1250 784641124 784641131
    0xb041a0303090d21091701050402030318040f060311010905090c09100908030a05280215070c05061503011503050616050c0f0a03030b03030a080f0405121801020c010807080a050a0e01 80
    0x80350550418030007003c46c0d100d040c16105428518594a088650540d4001d6054104102c4184001c12081003d41100001480043e00c030b81840040c404803003441c2d00450f4810082a406081580c0010f1104001c24055522040d81e26001c10030882c2ca02c6182e05852150400039262000d00b0302c51613105004c4c0080030201c941d1000515809012a0049000124007000011011401c1c5110f4901103024020301d400030444048001070480c081103000303003584108625940c440c1c0c0420800c001381c600689461040c1141d1751403da040c503095410503001081203007042102000002e000050041d40580e102e900209004a101d60072541c0d80b04907030a00d040c92046400a49449802291003407103a03200791000c2003181448002c1c540c40f4058004008041001c00c000208241203030349081c1d40c0301384228180e4030300804803440d400807070300150b40f140442810041c00c021b403540c04010000c8000c1090078180d82c44e1812420050000c80d0045c001180076132900081041c4141d81c1e0070a01d90881454000d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 784643624 1250 784642374 784642433
    0x30c121b0b04060902220b06072102030c011107050607090f0b160f03020606101e08040c050406060f091208070f02010c0203010c0e041d0c1005070b0403030b041a0303090d 75
    0x70050502c0380c10340e01c6030040c1f904248801c0c51405508440f056039120441c2c100d5207540d0400e240400c40e01010140540c0010013201130a030388203209080701c82c0201c180f400d0716403070142031940ca0310400514500912600040038400205800200f00032100c3c11100e00d03076070701e0702c880d00e0181003560001c0051583c40c1c46003000c0205600410141c0c410f81040d95014089000c4034402c59225040701c41103224000c02d2241700035820b100310842c951050240c0031050040d503450000c60100c4101c1ea01002c0010071007000e81c85000d6001c0811001030180714840000342045407101b5149100300c5000402d14000c02d074400c0116401007003090906a00140204800c1d4040f0314050f02c840040d070170b5144200d140103c4d40a45500b078142e201c4844080400810200d14007400f844405481d90042c00c00b480824482c480000f030840c00381620407031107954041000f14840303007444103480300d4080c0d50001580310f010700c1c1d030192000010f45070800030840e00201c06000c43d0410028490b4545208100160714200c403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 784644874 1250 784643624 784643659
    0x1e030908160201080a0507120b120a061508013c0603030e0312030906180a0c09020d0b0418020127240809070b031909030c121b0b04060902 61
    0x1c44030507000781c0343e40410f99154000841203820403118880452122031088801c0200d50740302000454010f00410034112510b4101403030304d88000405c903182920759011300c01c2c68071400340400007070024030003e008104a8084060541d000200341d407000141c40c1d04403100010130b01824001558007480104000c580700c2c01d00500491001d20701501a10400e5040351451401c98201c80c49045040003803c3c454803005100340000350800b170810094400c00c0c40c050301080701148101d000381034210b00141c1e2064800080d40940d00010090b51181d0b1410407172904401050520031480c42d8240703000c81c0c2e5074100d0700c100001400b200541c7c00d01140b02c0540401c605c0d03580d4445d8245c0381075214030608012903039502280d158908540707230072850700300d010204001c3c10103001950b00b0031030424080982e020194882e00c121a01d034541540054058a5110288454480b9151081a10389014141009000e0020743d0f0401d10303180090600440e180002c0621003154051095168000c00044881030a02c40c2d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 784646124 1250 784644874 784644907
    0x7080c010507140f090d030e0901060c0506010e011d0601020f03040806011e12030302072607030801140105090f030c09040b010317040e0705070302010605330306011e030908 76
    0x100c1d200807030f50b000d0014080706a0001079070a40e55074150503a02c0c18014405104200c052a0b40407000d02000c1c03501711590380c0d110b21489003e00010764818800388001d003807181c5490b0069008003100c080010051000070f0742c04241c0d0007000400880400e5545664004074603040a80082c1c016500010401081030100400c41c80c1c12952000c200580842e00341d405000c002c80745d0b2017024164101000b04600103402034000d130209500980910070940c6602030108206559440030740b080b02c000090f00c404068020034240d015000b452140b0480c0000540080e1030344c8682640e592140f6030f000341c0e09901d503400b0040c0c8841d240c8090b041d050941080d103000240300c0380070f0004950140b05920b040c0034005080d01960708903480744001070031545030072005440c0c5074172550003a011552200000700d143d1712160100400e4070b0086011030500c0600c100603007151071410010080c480420002c0c494180e030301142400c110701022a44922008126405400a00c4010702c000c180060105407140903074582039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 784647374 1250 784646124 784646131
    0x70908060a020c0c1005031b071b0e1014060d09080f0c0f0606130f0e0a0b0a0b0901080a03050a1b03051306051e0d0605040f0b030d0206190b010507080c0105 69
    0x80c101e0307081361140e80030010440101c00281e00003030030600c000740d001004214001c105071051004a4540003542d1980c55000c0e40e800c035400071040000300c0410001200f0102a9030042d034092101c0d04023802d010400f07645005075204244251400b01c0d801c1c1071801542e00544001340e1002220b035903420740c1c81d400c1000c0e4001e11210711442c0201b82250340c0e10360000c10a00d100b840010581441505c03c0800c10006050070042811016543c0f98440c130080c02c03c000c0c04180c540100c400750450b181400111043e19045400b2a0060312202c1c0100141c01e40000c81011641d8507091003500c030848038070f0864800c4040d80841c110b50100b0085501415000340060210a50004140600c5900c0d12404d44052142c82402040318218801074818000000003612030604103000c00306040c1d540304001015a2408440c0301d01c0705541e00b4a501080c0350420070240c0322080c90018149510300442c0c0e50f1107d1040300c3c4c004a0541c1c441103030240d075a106130212100740da440145070307864400c1404043e00a100c2103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 784648624 1250 784647374 784647397
    0x1110c010c180e010b030a02090310270201020303010308031509040b1f08100f0204090204090e0118030f0c020f0d05061009060f0603150b070b191112070908060a02 72
    0x30400086a481d81194034140d40e000c5401903004e03441c0c40d40c035000c182d000800e5400c0041e400d0082e015640c0c0c0502a400c4011000e801c007050640009004040c60500c00b4020b40c082d03001c0100c1d41c0f0050743c01006032030443c1d4201d401d41c1d0b140d9640507000351000c0c2040e55041d40c41204001003104200d46500000d024034030081c429000004150130341d9412450340c1c0221400e903401401e602413103080b030307402018440c880780c2c00150400d59500354040c16600981c04c03140302e068032490310144070402481180004070360ba0088684000498030044c05d40f03036190340c80728204046070000b402035440f40c0003201000c81000d0407009824034981044c50311214290758049610000317503c0011580254041e02040d00c818100e80507100d840c1c0380081d0010b01140d41c0144030007145080c001104544500038001e0341d80107c41600d101c0c5803454405244c05a801600340c0c03014036150303904814060020641c1c840d906031140500c83c6880c0c2060507070702c6440540c812401c40c0300711810041140c00a4000e04044e502c2d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 784649874 1250 784648624 784648637
    0x120d0c0b060d030c021c050102040f1703070305030105090408090a1205060601142a010501090914061302060a0c0b07030f11030c031b0f0a020c0a0b03090604120201110c010c 76
    0x1400308010b039440d08010040c00080c40b80e200b12000d45001452031000b41000c2c0c181c488401e019075141820380e0056030100c8520052200c04001615181900c01c0c49002200043c2d450b000455601030f0450206000f114001d02603d00051f0402c240c1e24211884001c004040813a010381d506651081c00c07240840c221039070b002d03620100d14554081e02c61111901c01c036054030350424009801c8280140b4903088404400003009107004c10b20300e070030320070140a452080740c0801c01c1d80007030804507410414106801c140340d1000c0304000500c810300104070701c840e5040781d1b640e40d1100705000c211101c130007020300500302405e0402488417854045d8001d01c03184448420a01041607004080c02c03142c002240ca001e40a48200000307090009010324000441109400c00b5040018141e030700f010340d0b04080e0814001d0383c017a00001440f07282c002d000354001c00407211560702e5894400e05168689001500043c8264070300640d00312031500030740158001800f942e02950b02d411441511074061300c0032261f2880807404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 784651124 1250 784649874 784649881
    0x3120c23010902010e04090308040314250516060509010e04020d02030a1e0b0d1407080a08070c1a0702010f02011e020409050a0c1b05070306060b1b0304081b120d0c0b 73
    0x701b034000c01507015055103461400d0741e1503803400d85811104c5032510040700c0080164102c18254440c85404075245021414001c2d0502d01c2c189260403602c940384010000740303502c1000583c1e44441140d21130301080c030b000103100c1660408500079014410700381c0c051038004000c010301c842e01603101390350001021007090200342d0031294003800c80e070503540060303002000ca000010200d0000f4040d00303038036440c40c404c0340d14041c0d4900c10182010301b02c941c1203640140000701e42e002d0003040e050300d1006c0c21072550101d400313241c0700600300b000d4403d05100134107200c1c0091803410318a0003944103041c001444130114480b0100394680c54001d502601a4010242c070f000082050401c40348030304001031002e030700d9615204941c209007041360032146500b22a284900c1d0b40120000e481c41c05242d00511420340c80300d072140210359621a80750844080b4000d158402c0c4002c00440c000052119810212030600103a080c10030f80218000c43e001030348002e0103101e65040860f4042d0700000700b00e030140c0100c032b032903c0645 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 784652374 1250 784651124 784651129
    0x31113020d1a121015030b07120b030d08040326160306080303060d0f11100906080f100b180a0f44160806060a0b0403120c23010902010e 60
    0x21801400d0b240c041e44502c80304d504c528900e030700051145905416a5040340d0b85c036680d0801610701211200009180705004018000503809411a0f5030b600310044c05000241c240004c0c281c00d401013000d0100034454080f011039090f0503d94000100e4510800c02e04c0307152408521005844031070100d80000e00d40a03001500c0d45002c0150707030051b0801024a5a840b0f003035184d4055017444158292503044c85505c10034002c1c0ea40d4140c411781c921181d201c14210324175140340504182001009800700310f200b038040103032994008030907a06444446051940715444001c4002014000c4660150042040300740070928001d240c0441013142c1c2402c040380341c130080b45442c94002c0c2e1041c00008008650601841071101042200d40c0d59960b02102250b1002820070700382c060000d0aa40088442d8005000b8846142044280f06020b080401e41091600f89140d070b40c00032032540c9142c0b00041050050348a010494030005600c8421003406504101001403041c0c0d600030700380154105d003c0385a9520a0b0000d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 784653624 1250 784652374 784652389
    0x10807150801050604031209080613110609010c1b080f0703120f120c0309060912030b0d030c061d06100504060501030605092707060203191701031113020d1a 69
    0xca0004d80350a040c14a503a60312030b0381000d904e442d802484100d000104011b02d0030440b140c41103d2481164001184070b0800042d1000085803484c0145410021a049a42c000040e000a00c1d40100700103640007014000c0404440c2c5504144254069500c2a1104803c0004e03c0c009490060949012084220000b0340d0710503102c80c2c200010400900e001400340c4a15030010f04407545900340400d442410380c2d1030b00111030580300c0440b4100ea002c1c51841c009503040c461040c12810554114000c040da644000d8500440c0440080c041d546901c54411740000440a407004d181e9010119181d6040008071180c09420078040e040c0038510b00500001c040d80b0901070758045550142c800343d0a51100f148551040b0500c2d02c0320100028602c109880307980e0f0170811400244141c0e806540c1b2805403203680c0c90b00264a8500750108800304c3c902c6005109040745540c1101e07403118400c1c0540302d400300801c440401c09411100000c5c8085154804041c81da002072104200002e142c42400c6032200811112 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 784654874 1250 784653624 784653629
    0x50f1005160c05031c0c0f050f0403140c0d2d121b02060a0207030b01120b370509060603010c08010b07020109150c150c020c13090b010807150801 64
    0x320380c0458411001c01e4040d041c04010140203406503440c1154080d42e00300e00b110310706004e050459580041c46500c60b0301030348106407480d9502c0c1491a120401500e01d282c1c1c0150300010b8003a03002c11400c9003180380c2c100800c0e80082e030301610030510740324182000710704101c14a07200003854410b1400c840411101100c180580d59101f80600c400b00400e08040300c100840580c3c48828404154140e03001d40e4401c0c000d00b9201c10603900030714501d410340c60700042a503030692011700820805540c200c00215441c14403036106d4100b080c200251034000402c08d48030324081c81d070500d200300d00415100e05030f01c1c00c1d041070303109030452000c03a80750744c491406060880d1000d0140b000055000001440300459482c002c5c9412401454103003c00c40d02c510300707000102c040750115000f00c1c0303540410700100440842c82c0d4460030702d401070402c2019000d240107134403114003403a141e00c03440c000120132210303180b81e80c4074644154211140b40340070341e101c0714566a90040390149001904804d00d0f5170500501c00c0042606 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 784656124 1250 784654874 784654891
    0x1290a0c03030b180f09151501030c0c14010204050103060b0c0d0e120f070503060106020d080f10031208040204051003020d08340c120f03120e0703050f1005 69
    0x105503a807614128010680f03600780603481100c0789608001c0d0030ba400003942c0100c100080d451143e0418910440c44c1c98580c0c0555520f0460302420000e03801500e1400700600042800c01044841d207018040381c910908600041212161013030708980240305501800039100281c0b8100309640e104d03e03245240f401900f149480729881000110081d5100324404030200f00301803c986022603010a01d64104070b5000c101508643c01420b0400c120702d4100300450040c14140090170f10124010340c02003020400408026203040701c10041a004000090214011500034555059507840c50038010002c0c0b105840070b9200c1c0341080b000c04c204440c84494902140d900a042c6c005142907035841114503000010390014000290b92040000b00d4000702800e50304c06a180b000c0102c2801d40b0f07142071a101503420048145c511005400006480402c0c4da1451a8040c2481b480c5840360321035840103040b1000324503410b4004c1c5000041003083c0001c2c1d0143e00400c0b00d05444840103407402080841e00100c4420f0f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 784657374 1250 784656124 784656137
    0x30b0106050315040f180302010f140f0115091203022a060d0506060d090c030507090c2106090615030e0109020102060403081f120b180303070315080601290a 69
    0x707070a28156000c035171940d0401802141c00340c82044100c0c1800403000b416030250751220003903000200d182c414140c034074000320064012803c00300781440f00c40c00140150501031880034001441c40c2e004207a1000284400306403c04450305500d002034696214940c083c220254100c482c0341c041c5001e0080e00f141080c090070311403c15402c054244041d0002030841a04030300c04000720481894a4024040d0b00ca006440004c40a840d41c5450b07132420110354800c1840603d000682c07001c43c2d900008021500e41001180d280030307002c04c910a4020045a400010940d16042000900c42c40440880c408280c00345c40411070b500764070311014280d425007640240180c1041c1c00090002c1d002e01402030b08420401d99030f0032840ca01ea1042044008243c01c404468281810700c40200041080e40c00d41c01100320f61605c0481c0008929a80e49010141c542c500341a11207141c400f043c081d03058100014041d07075003118140d5030345100215040400218441181e5030701031840400d109124103c9134009207980c0c1f41c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 784658624 1250 784657374 784657411
    0x30e090103110d1703040b1e0c030a0b0609030f07080f120306010c0c0306050106021e190b1e10030c150203250803091506180a05091c09030b01060503 66
    0x140c02076166803c03903081c505040d110f08001300c80405188a41d02c9901c030100d090604401d0348845a030300210442014095804201d1006036810544e900046c0b0340d83e0206501c442900041c041c2e0003007403625509440b414454140c544000a00340c07003111405015182e1081ea944500340c0c803009174070481c082c0343d41c042000c10219485031180e964410f000c0d44c4901e05260701c0765074184c00e58000313900050041e0f02c045981c0c699208044118001189440000c0000011006491032001902400644504080c4001403110b109030030102a402c900b01c801c3d0007061504194500d0500d40d180010390701c0351307000c4002040e00307562002070142d50302da180c00660405240b01000401070140c600410a04868485401c000600785800385000d20020005888082201511144101401005640b14040c0e04502d00310012995801c141c0080c0940d002040c2913840b903a1032441c0c801d211142d62803070001510085a21540840d5070300969200d500c8165080c1d1380d03000c0071582c9020644803c9000300748500750 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 784659874 1250 784658624 784658629
    0x180308070f0504360c03050a02040510030e030d0f1a0a08030d0b030313080d080f01050d030302030c09030706090608090c0604050d0c0e070302070b0a090302030a0804030228030e09010311 82
    0x141c0c40c840320080c10101140a0a440d07a40c4c500c450b80310152910000300742c041d018040ca80c0d1140007000e085041510f0b1400080d05204015055010300da81d45400c004051414011540300542c960018021071800380038010080c8801144000c5121084191200c035103003050110007210601d40c011401c00c80c1004c0c802000306080d030044d9500d031204002684540b000542c101006100110140400344601030010f0080040184042d0f80308141d40d005101656411305503000e0f450300b528006032603503203440d80d1195a10402c104103a251003100700010b19254801e81840589030b440c1e503185029212500100d41c0c500d040c050303041e48154180000d110302c1c1020a00792034028082d42c0080d00303446e590f00005041c01d8045d1440000250009a440240b0400b0f503241a0460031115042023180301c030f40c80081d203d0040f20074140400c040100800d00b0b051037004040c504907181c420070340c81204420488000040c202008901245140182080030302d0411065030489030401e030a03070002c3c1a00d404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 784661124 1250 784659874 784659899
    0xb271b03010c2c090a050f0709154d0c09060907031b020105061504050d0f0f1e02040c08100603110c011b030612082a01180308070f0504 60
    0x2c1c40380c54803200024000a0794802c504d050142507a0180060b09080400c4100205580286240180301900604001790f030031100320b441035205141391011100502e2980034000205038a8080e14a100e100c054142d5410316404402d0620511202652041c100e035a542d03844100102d80546c1c0000c0f0140020141e060400310182e1040d101d00d4005101c0c40e0011114500c1d070071080102006039900c2d0b0400c005400d007002600c050a81c0c414451381440d1909d070024000e400c0301e410052001404210b00c100300b1843c030785030188045d444280c400c40455040c0070781c00b03843c030003401c1a0b205500308006400050b0041e103410740a04482200240c9150400c08103030040c14080201c12000c20341040b842002940a00c140c05c0b10010000115103035441010340101aa001c6800c109000080c454034000003c030050b0403604550b20f218001e0043d440302070300040e0f04801a802e908840d50800e120081d81e25900c94442c2201c510903290210079441e1107204680d120912180e142c0412410170090040050491 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 784662374 1250 784661124 784661177
    0xe040f030302182806390b01031109161d01021011030105040c020601080307030f12091104050f06060f09280e06100c0b271b03010c 58
    0x10300c03031800b4101e070300030407880c00c813075250189590907142000380b0100303200700c0c1100206030030716204428006808038801e0800c2c070b40c2003907990800d030090210000c0f040249a5140c69410040c98022503035207007403400c040054803004a21408180001400005000100700601c20740303541c070a04429800007a0004610510803070f076055110307400040307141030114000e102c0c581c40001625501d079450101400156801801650f0a540000005101a42d00003051300c0303400d50581741050b04660000d006886110000f401d41314410305000c40742052246611240d4403183c800e84007045103075105072865400d1070003915003c4e8049010441074032003601000113060081d43c0100000006125411a10282c3d24020150b24440b40443c90800a034110840100d603c1042921800c1e03660041e280002d104040c804c81c014003000c2e01001244550102d400c1c5440203600005040c424600200f907402c0c0e41da01c1c8407500c00801124455000320724101801400ba1030f904c191601c07807207410301c40034282c2c4100c0240c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 784663624 1250 784662374 784662397
    0x150406080105090703030e0303040302030d0c150501060c1a060604090906110307020604020306010e011d0a1d010b030d0e09130206121009061401080703050c0c0307140105010e040f030302 82
    0x15040414410002c2c81507901450081d001408018a07501c0c1c0500008071a281d9603109030802d100070000f607200400d40e100003d85138602203c1e050f1480c5040103c15070301101200310640350800119206402281c24a40741707010b180241c0034242c4141c181a07105100316000c42d0000c1c01840200300c1201aa04000d0a1321f12403a17000c030f901c1240f00c81407001c43e0811180d40c00142e11002c140010341c06e0074460540035240f9584030551660510354200315007240001018184035800c40020010304140d4485415020344c480700341c20345008040a01e01070042080707082d100340640d01e5500461802402d203428200c001030f043c803034550754414142980010322401030307800940400c1101c0c04c940d1350038031030307849503406400111001e4140b141c4001142e0302604069a2061503104007203541c0c3c0c001d41e009601509500e804541541c50b42503d520501030703890a81e070203110104684c8200040a0407200443c103074100200850fa070b0ba503100443c01c1409643c00f030502c3c0c4c17003901d00b100400c1c441e400400501c1e015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 784664874 1250 784663624 784663631
    0xa1b0302131d040b0105030f0a0803061c1109070302040e0a0c090302032b030903020a141c0c06052211061303140c01050c03040509100b0f130603090305031504 70
    0x16040c08a000d03880c5528154500402c0300e041200b0007030003006550141c401a001864070700090340310f040d5618201c06004e8591304e004000a030003a53380e41600c80841004189501c0c00080d20314114420b4582c0810040c81030580c200068944c0e407103403007510212a1141020811511894414801000ca9070510700401052550105c0581ca04000980904038034868280312001201d00b000c002803499104a003c040c00c0c02000e02c00300e0b078005408500340350041100e150103c0e00d00f8480340743c040c50400031240c001c94410076007895a0006044504640a41002c0c00184d942102290500c00014202d0300d00c0b0410900040114041518004940c070b00503000c0d625181c00d10a94203c07101c0b40e0390045907852a030601d2140200c030140000c00210000382012810100710000c81a03c0340514020b80b800303010510002000110b80002010041c40d400030351030303a034030781c2405210040da1140310440d59803c0f441c60b0010b1726511a20031112490f03056981d55080d504c440506000c8a1a0100015402503d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 784666124 1250 784664874 784664879
    0x1106070f0c050115170d0318080306130c030f0e0601030f170904050a0e010b03070605030112021507030c0317010602060414030c07240e1c0215160201080a1b030213 72
    0xa44c418070780103071403100301c500b40482c1c01030380146ca4001220302c03075410181000f1302004a001c02c003900344c1606074403502c9240c5903034440f40804c01408220344500c01c094104121b103014a500365012821b00c0d00029824050040480b0749981d454100b0f100041c4000000c02c0401d01007450303500c104545000c8a42854502090701300010b09641c01070721954000c5549407103001c0c619100744550118060190301404810785003100240c15800144590a10007070b40d4410001190364002e50b50003900340340050b541e224801814000c111407410031040700405c004d108540540310501c41014101c40d0b00780c0c020400c42c0d96541e2a154a802c500400750309900c01404020840c0200b07120074000b5065080260560800006d0031a0760510024000d43c1849215280c40310940c03221b2503e4094540c90200040c80c1c034041d48045094030310b246075026400500822855455451792050280c07460013640c0741c080d2626010600422640303021500c1c096201002c8013900707154001c0d0081d103040452100110b4205a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 784667374 1250 784666124 784666151
    0x818031f110720011713030f0203090d110a0b041a0d0b09161404050102070e04030c0212011b03020c03120903040f0b040801061e0e1f080105071106070f0c0501 70
    0x41903d0342c01400285100f03101541564407034415184100114103d007014206900c0c441079806013250050100104001211a002e00801c111030044802a0030250a14014140340415500045100784280584030001460004807002e1b6000e5805190424034003031a0b03140710885940c080005640895101d5101e002155103172501c3d40c1c401e0294240c021400c42540d00300034109072400122070740b100b105010034400e990b400176000c0143c401c8038096101a072074900742035035001100c000c025070203005072241c0174010318190072641d00b8600c15450586041c14a0070140c1c00c1c1e015491b090781d425402800380c40350080b039804000c1d030080c0d02802903a18084d03c88145584065068103d240b801070002410410b080c001d1150307500808c240d40c1030503e0060780e04040b0882011602c1405850101d040c04a0350703002010041d40c4e01e50f0003001000e01c010381d840000c24040d00044070608081406044150018400411014440c02c8107540303480065580c09400d4600301c41d929015102c541d030704c461030200740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 784668624 1250 784667374 784667393
    0x706020705040b18011e050a08033a0509010e0a030504060e01080c0d09140d030605031c050406050a0210020a030c02100e07052418032104050409031b0818031f1107 72
    0x40064a000d19690102f0070380008551003550051040f03c0c2e0301428404035000110140b0001402003200410961a960741c0107001d084807002c1c0c284180141c1c08500c3c00c26030004000d0086800c1501c1d1f855502c2c0c0c44500549604800320b90480348040c04014041c44503045a101480b035621419408900303941201030396151a0380c9039404004203039500d40c24403041c40c0c204500046000c541c048205041c40003070000301180100d200700b509100b00030400c1e00c2035a0080c008103184d4400100110344074112a0002806032206d11900ba025005100410060016a0040c801006588801090b50703a190005024000c9280d01c02910014070350184072807c0340d900b1005000c170011900203088140014410142400c2c50b455444130710032a072085040c000031100e800c2d68101c070340c1260700042030501400d040d120399640c43c2d044990340742040d90410401c07040e01c000d415444d84050304114900307a400c05260f03548080022880065030900451507130020316400c0100c0311107400c802642400d250b40d81d0110070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 784669874 1250 784668624 784668629
    0x1051303142b030b030703080a0306031106270301060b0705010f0501080303070c200415061e1b1103030c06040b070302160201200706020705040b18011e050a 69
    0x540c240450340750303007030820102c0350001c150019248208003140c40b24404200100d5a8400d01d61100142072032654284002c1c0011a00980c2980c0d40e0394000000034028651800200c44000b401070782d112042c2040c10a40b0850204801140c08203514214466960241c05c0d01c40d640c19900e0f410f0101ea200c58003805001034503c600000300301c411148a0140549005800c80350055109108002940c3ea0003009102c1081d00001d03410035030700da0740f000c4045010708400c80035089030400c019103c7c1c00c48041c00c628103c1d0900e0f6900602c0d2081003c00d42404603142405100140a221442601e09054404061000c0c4940d50401ca803241120120f411600848145d11860700f00400300001d000c0030416031399200343d0a240c110b141c0f513045107903441d9100c183c501c041e040180130700d400240d0136203115490b61040b129034101c0d28400d03502d982c002c1d502c110307078051035004030300300700e020b18513800c021804003068502e904140b9016070a00c0004803420240700c120943700e00074080d0000709610742c00d886101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 784671124 1250 784669874 784669883
    0x1020105240415120501060f060806130216021e0a0e0105130b030309040905211c09050f03030a0c14030906130602041a070b060f150a091e180203070507030e01051303 73
    0xc0a074608911230203c090640d0000007480800c4c4100600c3e540d4403404201c504000f403a00588603200c41d40c9030300d580200e40c480290042c40c005504400a07001841d800804c0c90b044900340c19094450040b00d60f009001c0c03084a4100b03e50060000820800741c10041c840200a0101c03428040914001000d0f02c203994001d48254100a40ba445100080c88041941d031341130703240d01131a012810340710341072038029204010011a0b462a8000800806001006c0744400d4102101d80360b0402c0c9490800419040c0c2a15012907120401c0e035404140d0300e02643e100741121004bc14166490408080510b62200000c54076103600b0803000c80c0100b81d5415064100710103c07205500d0b56103038640882502030203440184103421082901c1220340d10710381d0303554806100c00d0110382c58021150094400855940010082c0100c403210b180140101e688110112410801108400701c5800e03203a904a202c1030b50701400241c0d00b044080017090040401c08640081850003d15040340c00340c90308260001d40d08200d5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 784672374 1250 784671124 784671131
    0xa02030607110d080705160503210601020118080304020f010909020703050306010f03090b06040b0d080d02030916031a0c071506080d0f051206040e0601080102030601020105240415120501 82
    0x10a620b008000c04421032030035040007201400c12060180090103090b5440112100d59a110020400203006640c542c4001c500d49010218040164400c0c841d03048522600562134041c10341055801401c0250b000d94210524500d90789841d000c0c040c840f501516403a060280c0c4550000d4a0f09440c07009014982c000da545d551a8100140010884030021012000305401d00d0183d0340400d2140311034035040f002c102d40000f40700b0328001c046030b02d100b04070700064883e4002150f045001a00341d002103100f15001c0e01565240c4032604c80a4818101d5800050289002c2d6032601c0e0010300c12101843e04000301d60080380c109811680c5140e050488030300d00c1c948103030721818100020791040040b2400d60780c86003172071180592500002001d034064100c200800f4080000441e210744c446901c502003410070607041d1155582c461000714082d40c0705841840c0150318040005a04207400e020801c080800c614409100c41c0014040001a00c034000a86684588000340050322049a0b03604056a034410340010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 784673624 1250 784672374 784672397
    0x4050a020321030703051008070801150512150402040213061d03030c030f070c050d033c081e07090503060109060b07021207050402040b1b07260a02030607 68
    0x150600c080200d00c0500d01407104807000001e10482d040d030b940420585070010b090381c0d0f40c0b0301e0045401907070f501c146428002c400d800700c3c00c541c046d0822001d21158044024280756502c0030700c0360390030075800500d803160880440030b84e1a00c20901c2654116000420240c144241b01406450903200c60b0b011102040344608001d24851007145121984842240a10300f0a280444550384034450508181c2441100144410030424003503440b0010b01400f9014162a0406107400740039070004403030225a100c12172040305540b140d05109500602d80040c404c220040c072a410560b030402014040505554040725080302401c1100c541d42d204a0309507581040d9280740070249410b0400c10703040340c0300590400c0d00c244a0001c122086404d040e905a03150342040c0841e4400c0d5042104c1904210381c0940005000038422103a100035020140c2d00d04150300700f6552040d000d503680c00fa2440b400c000704411420b0b01c08440b10150014002804e14000d030f4801d44560360000b814502c0884000010030082c8c55007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 784674874 1250 784673624 784673629
    0x18140c0706050f0402010813030c050709050612030a0e1e2e020309031506012007090605091303051806190f0807020a02271009050603210d060e04050a02 67
    0x4080c0c01c20078455952195084c03580000380030740380050201034a07001c44400f00e0209881f0b603444d02c840300d030000d0580300c142e0380303d00504000d4201518040e2040d0180c1d4440c510100717000c41213962407031550301d4203d600302029080c0172008840c1c0501d000c104038406d90701c082d182c9a203007082c44c850342400c0d407400314000030342c9100800c411058005c50840d44144074498440c0c0300054550380d9205603403201d00440e03a44500480d40000031a00b40c138201000c0c0d0502d000c80d070b40d0015520007941d0402c0414001c00392202c081c89011800dc1710006510400300f03140d180403038001c40017001e4540030606035040310896180070854943c0107003030039220220754071042c00c02d07558440c21200ea403107100e181c0500300d8203096030000d54913000e06034041d204140c5900c2c1c1d00a4003e01440c507180031408090310b41c019281074842400380d0b52040c8654400309080c0000a4554500441c2a800422191440700d201c2400840310441503004880e0308500f46581e03803c00304e6901c0b81010b030544260302c80c00040c004060305205 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 784676124 1250 784674874 784674881
    0x150602070f0e0117160303031e050708190b0a0b1b0106030812070221090901061806110c0411070c090207020114180a0b0c0f070b0418140c0706 63
    0x110115803400004280000c0902c8081903045600e1041d1214455208003009414503404180018140e941c8507400020903426070000c14801c90350b03100510f000ca00003031465007611801c8030300c503000603c5040042c150303142d204601e07141c950288000190702d1145001050301c5118540002101702c102190b4025a208005e4417540c805800c10001e0100130f1031680c840803540200c0e01d501c0540c40c101c00c00601424802c01104000740c0e08201e0512800301160000001c0e64440d119190181c01040c001180d0540100e501e44114030244281264982c034100c0c00f107038400801c1183c1603d90140c0e0078560850354030350090301607901914040b80c1d0b44940d50303d024045035440f07900c00410140107010020140c0c0e00a18900d4110000300c82032690f03246c408070381c00001c2088142459004080540c00b081d005842c2c070141c441407580b402200c40010505982c01e84d100100e01c50103c0f44601004140020303039442041c11490710079140c021039103284030340c00c046c1c2c200c0d170880d0b0010712040c01240140c00d00c4007038003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 784677374 1250 784676124 784676129
    0x40512070b0a02031e07080715020d1b030e06101203141813090506010501050702030a0b150a0f0b1b070b0706140c09130e0c04050a02130b1216050d15060207 69
    0x80c1002c0c940b0600f47e88840240c0690300c405000706120040e05d44e10a03085030111204942204010004020b094201c0c038080340000446100103494400b0260b40404005507050080c841c0c0310724100c0d010320b00b41801c008401c042008900308100c4041c9021a42061006410f4150880a0400d05150a00300748140c100720a92000e5196040c4520f082c01301e05c0200d00c05040d1303142880c2099840505002003442c001303141200901401c1c0c424100100c1d03001d060304c032030b94030902201c45400555a0f182c0d02c1e0440307a014000c21030549000c001034034520741003030103900845016401307480c2c03000c2d07a40011200503000100e06884250715003641003581c1800004540e0700c00a4800d0090038084140003040020a00255001c4910364980080c04803080030031455891f818000c00c1401246404120000a0342024a1000e010301482e031020911903c41000d480e420500c0c0b0403e82c8881e6645008603040c10110507200050120411000513002035500038006079141042a03800400c0c51f00c1b10007454404140e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 784678624 1250 784677374 784677427
    0x80c1c02160506030411030607020a031101090b1909020a0b0903101109190b0a0e04051e070c02011b0813091509151e060e04020906040512070b0a0203 66
    0x4001000039500441e4007010b542060361801d40782d03034440c074011a200d021000590307414400d0074100f000302da83c001031281c0400c0c0309507900c5000aa050603200d00b6120f22110040040c01c1c0132000030b1150050340040c19003019203a8011800c03505540110315240c04035040b0013084c580000f18031089007020090606164a01081000900c441c4521004c0c0c0d07004504078148038080c48076600c480514251341040141203030a440940c0c0388180b0401522840f28548001d015604241c0011900c01040c0b28140b141580e00201c5c0b1a02e03569540c1c1110045c00c5c3c500120b0511007601a658080c98040070358070314082c8145002e40da1810070307810b400300081056214000b07181c14080160411a940300100007100c059420100b082c0c0300700c4c1c01407000d44406030412010405400e2aa84040a84510031002c8031169200d00c0840c11140050100760b00c10085195000201004100030604040100c200010103440c241c1d2a459154000602982e1000d003807103005070f001164076510420f013451a0012500716 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 784679874 1250 784678624 784678633
    0x14011d060304030c1e020a0605031015030204081e0a020127030609060b032d01021c0c081b030f0c12040b090706210b060d020a1806030524010507080c1c02 68
    0xc1c0e03000415091041c00f40030100279020001c60031803140c1400c044040d186101e41500d0344064000024020740052103008968415007600300701100f19060074440700c2c0d010f200604200000d540055892000b100181e00260b0603d04031324031440c40313000300344020710b1141c41c011030b0840302803d00f00c0aa5003041e180a101c0c5c2c001c400c01c01004144a40003001d000b4601e4150200c1e0040a4000741c02809500e1284103c189060003580500410f0750110003000c0ca1034a4041c1541c4414482c6101c08066014903001c0810420219000358a401809a484802502d03160f05d0282c049130303400380f450700a40d070480c3e0004028050050300343d41441180d020f4403251600400214160304a03050605846000e40b064a235104103144164407100e08880034220040b00a41d0fa40c401c0c83d0000300540d100c0c2403040c01804080700041041c0307219005d580d0045030007500c1181c808441030350b100e080660074080715061120802071640012001009003900d08070f5480600044110b01802040c84400141c0384d8045400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 784681124 1250 784679874 784679933
    0xb090102060403030b010e04110a020d1d061b1b0f040b0904080a020705030a1b0b09031005100f0f0f05062505030912060709080714011d060304030c 65
    0x2400a840ca50060f0075180100b541c940100050320314441b11106107800506101800d904081110014038074201690b08890105481c10412140204524118010300c0342c400440c480c0303031800a02400c2c030303001c483c01400c2004070507680451030114005034480e240d0880f1044a03025103011402c507144141c0c00c0e60103004400c80d21001410680d80140002c042510100740e00b68600c0c803c000c0713000601070140c100d50420900e800c210601c20b004030502c1d0b6245803131440100d035000030203080d21102c80300a4002c0842c0e1707180045001c00341000030070880341c02840d8480001c40c0510142c60000800c0b1682a08140b80d0401c400c1c0d62100b40103400013800340300c080265002e507102402d01c40c0d2808000442440d24645540b8103541184510048182e10030703048585040c100a0124503140500b849444001d144c3d9561410981c4424441c421b418490240850092095002e041e000d1071000c5002e95450750320440000140090300300351015070004544c40406410094100740c0c2240300001404480d03506031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 784682374 1250 784681124 784681127
    0x204060603150306050c0403020901060503090d17042405010b070317100b1608030a0f0c020609100f060503011508100e03090f011b260301030b011a0d0509070306060b0901 75
    0x10b416200c000c00807541c990025000108003420390b070145600800e403101d00d5035195002044c0b074000391080d00e01801024855011070340200f44c518001c10004040200c5541c89407140b9180d40c7c02d15001c501c2414442000c0215000e240c41010f01a01503411525150007550400410384801001d0a000c101103010038042030942c1410303904101da9107841c03c03a0340e8600d20441c2040280842000500c2c6040110502040103c80d030401c1810180c2403804214200c8450310480e038a42042d503100b00103800145040000b0002238010038010b104440002c61090f0340c40300071a007110f41180c0310a8100c00c900d1000d021005c02407000d4202106c1d40e02d0140701e000040c822854030392051000940c070844600300d0a40e2548d01072251204a4044034051b250043c515041000e8140100d02d0320322000140e02c08075580b40c10b00d813419a81038940000c802d0a181c0e0034503c2d1450038110500d01c4402d2000c0501c545800c0040c1801014800d09299025013801491840c241003561541d802050404806000c0d01201740d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 784683624 1250 784682374 784682411
    0xd0e0f030d0e031201171908040302120d0f1107030c0909110a0f061b020d050a0b0c130e0606070206030109060501020601050f060901032703020a0218070207031214030f040204060603 80
    0x1642d60740c2d84891b18031241c0a0030751410340d81178445840d08606446078418000c001000e80104c0c7c0c025986001c90841d02144680c44a0703000e650b18020403541101081240c0c07240d0313950900c035060380342100e90311600d83d111580451006d5220500003912180b40030200000001e0400480c0d1094490a40d1242000c40600d844021401090100403841c035041040c03281c00c6010040d00394003c0c04036501c2001074240140c60f40055a800c1c0c40c207400712000305140413103010440d040b5a0b805d40c04191001c1c101500380c6076020300079000d10381c4068148000c0001d60354980003913000700603040300000c605141800284c01c2c018160320548c0b003014400010b1005880d00003c03a14040424039001404800003d040309150500140c1c0400d0300d40107205d000d08050300000c0d07031802280201d941c51b003031070000800050881012a01e060040c0c10802013000098540701d2100e044594905122900340d000160f04501034108844989000c2d00450900c070547c01c1c60310551018201d203140c240401e503154105400303075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 784684874 1250 784683624 784683629
    0xd091a090703030c0611040b07050c030601050f370e1f030305030604060b04120b01050f0a0b0a050f12010e060d05190c0911090111030a0e060d0e0f030d0e031201 71
    0x9204504e6048402c1050941c400c2044041c07000c0d0640d2559103c85415101c1d070401042180c1500c602405100d09242c001072207030403620b0040a460182000005020541d030300000c4000d0411941c0340705020700f6020580c203050400c1004c001c1803c1a2501c68100c1e0341d0329000d81416401d0012181c108141c0802407821300590750141403240d80c986401000c00e004020700e601041003080041004607a041303030302200d137490174007452002a00ea42c8400805c403205480c250038603882003080e841000000c400d01c0103030007600141d06005044c142c2119210200e1350004d805420f96548800050216000314203441d234010b4420b807445500b141590352010354681e00301071030031000006a50007074108258032041c14007800403282c061011a100c0c0c1c1144040b81c006005641c08142c05030200e0022080c0001902c09207001d0b50344249240000e5070038058198850f208585046413a400f85407400082000540c40000f03944005541c0c0b0400d5642101c02c42d000d11180d054160010002d00320104441c0808505 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 784686124 1250 784684874 784684877
    0x917031f030203060604093207060822051501091d010207030f1808031218030a0503010308090a030b09060106020c030c1503090a120e01030f0501051c170d091a09070303 74
    0x10b1f882c1090034092040810301000c141c2e0b4500001d68000802001c1140e0306100c95514100e452558699206841c404801c443c090240c0000d400c034010740303141c585603200c112030044042c1c54581d86001c24440603000260445902582c0700e6850240b210783c1c5016900b507004000c0d00031803c0c54500c0e0b4000f454040703040028000c2102c07440c882000807502c1d106100040101c0000c07641d0b16070160145292a8000315454541c00c10a00e20400b060f07180030089990130007266032041c1c510781c00c42da180e40d16504030411194001800c10008400115202c0034580584003010040c4204e601d0a00f0091406500280050286d0092484c406040e00c444202031101d12170031641c0b586965070018001d03e018903060000e441303104520a60317209c903a04a40a800300d07c000382c1c0c0c1480148109019030081da030084c4100c0750041c0c030300e0001807003220191040c0380e9110701c141c007100e4440988140c80e0805410441d1555901661040380004000f0031a04540e059805821001d5086c64040c05a0341c440a00788000740 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 784687374 1250 784686124 784686131
    0xf101b02040209040e010509070b13092c0a1119060320130806010609060905010e1201050108011a0d02010905060f120708091e03030a020d0917031f030203060604 71
    0xc555880c0c040e1400850068020003d0003000c0c1c1da0507020b80b01c1955219117501070054045405281c0c5001c03200d003041c084204515491421210400a2044c4900710014800c2c203201d042d40d00500c00200609500c4140080c2248903440c10311011111030f50b06414825181c3c1c44041008240284000301298842c0c140041c07078840c0040302800240e0352160b82400c2e02400203003000d51045200d0032005440303000b0200c84482e87c881030251031001030f034010a0b01280c6620f40c100003030741c820314140b01d0394200546400c4000744002403083c2510002c0c0c0000700180d440d61028100c41c2e50145400400150440358403400300c080b500007a004007440c0c041c060296100141201620419104945884640c0144040e4601e0103c00050402c4810f4400181c1d6004203101011402d4032460035070440604100550300c2c54a0311801980254404100d075030f0010346505c2000041020020902c011412150300d003907032032a010380b10b8660805001c10b15002c100c0007200c01c4c0003503107001441c164000b006a8000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 784688624 1250 784687374 784687427
    0x6110d1d04020702060d06060906050a0e040b010c1b091503151508030703050319090c171f061403240a020403020d062a020a120905030304140f10 64
    0x900680f0078000040d4010700b0000e407880d85420b00398494000c031a540e81c0c401480d1a160102102c0ca40b1406200d8000164030b1403019407246410b50058200720014104410b040b00541d651140d10108004519228048484100041600e034040e40910304204490303110058207654840500000074094400595034a480c5140c10f45494003409000e000448100c0ba115511803500800951045030010080c414808108601c0c00c464007079118074981c00441d0200c0d507810300070b00c00243c08075010110b081d032103400c0050705141b580d2411031038003410303117032001c1613840c14403000042c0d00600d2540f1500179440f01d9000004150a43c4400c100210030801509040e01c4540340c1c80003034041ca4102a40c801c0f480781211341082001c4e40316010700860700e01c9011440c03001003180d0f40c943e00840b40c12009038000340c5240c0000381049014460000762414520303007564580001c6450b40e00550041548103442100c00c00131450002015a104507080b00c5400c541a602c04d0700810101601c0380c8481c3c20032025418 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 784689874 1250 784688624 784688629
    0x1050102121b2404150b0609010e01050d021206150a020d0c05120a1205150102120702030f0601060818030f0d090f20040f2007060612080406110d1d 65
    0x1c9250050390300c4003500795801031140f40c1c070150005a5080384c00c0c40300080701c0d0085c080e80b4002e122450800804103403c0034801d000540303460000c02600c038104401080030180c101845c1c400303031200c2a9600110811442d12100703203e004940c0c0d42c100340c0d1200e811701403580c50541c00070382e01a1194061510031360042c8140b0f01180303070421002100c07880402c04605100070f80c0d40806003003244481a48140807a4036200000a00300304400d500c14016000030b0b46400140415a009009840c0f000d000c58040b681e80e80784007400d10f0406c5c1c1043d00007549440c2480003200c00301c0e00500d0030042502c0075500e02202404e190b101c3c1e1140c500303a100360380c3e1180815004d11042c94031401d809900700c1005070410300124604141c26404580052041d07140004a80b50341c003462140c0040d00382c0304c0d2042e000000700c00800003c550000901100c0140c0c5504020a1042d50500003d0756140f02d02e00703403910b07181000c2001d004001c1a10b551042c640c0301816051815074802c08907806004400e01221011842402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 784691124 1250 784689874 784689883
    0x1140711030d09060e0615030c061c090302070503370305120108030a11070335070605040c091b18051c140703030e0f0625030801050102121b 62
    0x4403240945498441ca040c0aa1030f000280040c446205684c0382c0c1c1e1391011f0300400e2114503903c0d01d070154001c40384c01d520750030300800030440304030f583c50100c446042e941d141e9020b035005201c0442c01a0401d11042210741010044c1003089080207650fa01d10103820050051605a8044000255010a00c0c20800d160003181100d1402c03902204041c100d40e160101190350703500c4484544001001001070041d00c140c0410300030301380c0c0e40c0702e41641c00842c40020315880b00001005010394004002040c00d4000765440020030810344240360104180c54141460040da0700c042e48003070074290501d02ca2259070a151340f403c083d018480e0a003d0303040b052800000b10303e40b0f9a90041a0851081d00e0340b68020700720406000b80c003c2c032400712000c918604446850f260403a0b440001d01060103000040c1c0340c3c0c0303010f0442d000003003030180c540c40c2402c6082c50100c4818450103c010742d03250320a0204018140d11245541c09040c0a000500580070205900e6006100d1449124004144016440f60f845010310 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 784692374 1250 784691124 784691137
    0x613030509041a0306060411030a050403020f0307110108010e04020609102010050903090d0f06020d141902211305060103140714060f030a0b210705030114071103 71
    0x40080101d00f84529142110111141c6907034482c2c443c000002d401813038640103d0f905c42140030042d500b95240d424014002e00406481107003580104602c1e402c0006c07041002e004c03494051481c1040c000080d00015200040c10f03000720a07900042410000562259812034010500981c8d0304a540d0010341d0048071040c01c615112600361504d5440900300320b03400a00c982070b1008100042001d0340312081c18980d130f0320600010a801ca205045d103800821440400d206605001d00c90251502f80540b2a40084400e03c1c00c1c0b58100e41052014010300203040f84000000c401c00000851400b181d00e6009000da28900c282d0500b80301e42d5070002240b00d24a0146080903d5200d400c8039029612844c0942c5074440c40c0c0b441a60502c1364400008a00c00030710f0b005003403160043d14143ca044032006030380126601c010300303480c9100c0c3c640c02601c0180e1610f03c810003400118000720300c444030301110301606107011980902e200c0d0b810030420340399102c2d00313840341c5801c540309007041c802c41c03400c40070018158003481 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 784693624 1250 784692374 784692379
    0x3020a0e19060f2c0403051b060a020a0f0e01080c070c09050103030201020712031b0503090c1302090315010302060f0901140f0d050609090601090c030f110c0c120613030509 76
    0x140000800c0001c4640203c00d44505810001d003076144009104240800d4419040404069201041c00f0074000c0000301480000b03040c0209400909108481c5040010343d4001485940003440b100599805111810000042c0c9040201e000300e44000904801e009050000d0300384000603481c2c2003000320f80d6450003c0403000d40500107980d40b820064001d4111610642d040c50b0034064285645100f44540d0700026203d40c030203122180c400000b100c0c1904014403910a41c420000928817543e101d602400354001000e202594820400701070600344114107043d8086605144010300050b59940b00761040c8002c41d00142d5200d01c00725004995046100c85d50303913070350740c4000350841440c1409801414036188079001404103499103811300c1075038181243c640e80c10b50030500040c0319146460300111000c001c00c2ca80414038001046108080354202c0808960340c90000800703400d14a030901800200940c2140c03c010400a59903400351945801892521001e000c0c0100c041014065000e462520002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 784694874 1250 784693624 784693631
    0xa09090209040b130911031203070e040207020405040b01030204060f05010c080a02150103080301140109080a11010e03030c01060e090109080d050a06031e03080f160e03070504092003030403020a0e19 87
    0x500b04000040280c68400d1b10600ba95442c41c201c82c2c00c0c0010341c8400c1c4164030580c40e24640e80c82d01e0840f040003103a451035034441d4003005090056540c50142c207000783d00030004210703154550310400086030b0055114400d9101e00b600104080c1e80c11440e8182c105402c10500e0fa65044a05801c03030074880d00686201202920a0000c0188420240914160b40000c4920b60740b280007480103484244180c8510406580041c0040c070019400421a41c01c80b801030500c1d0303080c101020b0000b821174101c445441c1d05a996610f0030002c581e191020940c01c098424002c00c00640340e42c4851200c0d00c60414000940c58598004c1440b0b1203040c2d100310001c58003c6e062441603659545034042c40d491456040e0300046500021030030703100421100d10302810300105000d000d0b0751400800e68101800c070703000d958580150000043d0b552500d020396080184101800091080340d0b044490542040c606201d0081d4801d100500060703d60481d483c0554042e01120003596403034404000c5145214402014010308 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 784696124 1250 784694874 784694899
    0xa1509120509030d0f30050c13080601050913060f020318150c0702010804080d0906060e0f10050f060717030f070c0c330206061005090d0303050613090c1403030a09090209040b 77
    0x8d03150250001d11113030042c692000d5990549940d4a1743c003030142590050787e07500415684124203141c41c3c07243c2e118140204034048107030a0742c8203c1e00b04407503100050344801e030700030b0300c0d10800d004c101080f4050303081e91b000508110015151f1170141c003a00030705000001c40072406001640c01038031003d000c2803a05203c0c0501602e0314502800140c030841502c1d03215100440c80c401003103c1ca09210303241120001680c14581003c0240b81072014524072340002d010803035031b0040380d130303915800e0034005113948071550b6814999210591554003c0c0000e041000c030703444541c00500d01e41c00c0001229014820703804910804803423990184030003d24100140042c5002204460b008a0000c0c41030500b282c034000d001a84810035210341c82560129a8041c80030006000080e01aa00164009034041c0c040100840403e184400b2164003490640f001c8010340c2007000a00d0300100582c0504000390051030a110040030f000d07082140600888400a4010403080090b49407a0300c888040b41c40100090310120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 784697374 1250 784696124 784696141
    0x6180b061603200f0604060f140f060f1c11041d0f06011202060412030302070f0507030c050f06090d0201020309130e1207050a1509120509030d0f3005 66
    0x210b51200380f1a051a02d0340d401040900400d800b86500340c4000640880c1c0c0c0c8595403c0000e00c00300c0c0e1080c10f46a5943d07090303c85801407425003482210700d042c10200500704403041100609903070010610032450107004a134814400c0030f00780348607136002d000c8100000c0c039400090007030400841403081500d5903e030541b01c0714000041018140c814070043d00d0040c5d07204c0c00080301c0d045501c107002e9000102008100032199180c08000d05003402841d0050509c0300558030360a0040402c082550590710005061041c80000c0b441d020003414110b8200c00006140e0700400c03c00d0041303a013100c2c840d4420802c998256402803086800c400c5004094400340614844800e0003001c02240e000858030500d0302e050038145800003100d9203c3d400000038501c040003075984c2204e44807486042d54800c1d444040c020002452010280101109034072915140c1c10003000f450f00d8030b11214a2a020840b4403164044081d41048525040c80314a0f130010142000000c1b0a0300300e140c00b000000b100342d1510341041801d6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 784698624 1250 784697374 784697387
    0x6070305120a27060209101d030127050a0803100e0f01030f0b280509150103110f060f0d06050310091a090c040e07090f06180b061603 59
    0x4250401610520348071058800c0855508032001000f00c0c00340c5801d14540048010038440c031038130400015150200010208142840030b03480000030070148000c10101000c090203d0302c44007002d4000700100362140c410300003050f40110440c1e2200414080314803d106003480200441d5401002c856a00c0c1041c0c22001442602032060b009007003407c4005c03e05107210081414100d07070300040d14003134140c100d0701c0c2c1d11444640030300103100000442c501c000000941c54000c022851103441c0c00110b03880c191207d07504004544140c080032101c0c01c0f0043c40014008417a948482400351b9600104020000106a06e485201d442d1515443c0118030f018001d5450f40201c001c1d100c00740c0a8a006841c8201801d0680d2140500100802502c212a500114104848036405000f1030200d0348180700c640e010908665510030f81c031000e900445002d000100081c040c0c522200c0d142c0b502042000d14044401120705e140c40c25203a55991a01400100c42e5250b00549800700d0001d0302c108031414040c038019001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 784699874 1250 784698624 784698637
    0x60a180608061026071106130c120312020d0204030c080303070207120b130804050d0b0a050112021318080a080106020c09040308060f04060810061e030206072006070305 74
    0x110004245000720510a048009080c85a8140380800c503411848011300000002c0500c41005214264100500341c2003003440c4c02030100703101c065071a020300d0074040c1c00b5506035086100c00340c1c00450804006035202c18072078882c84480c100140c440c40075000e840003901c5150320140440c1744101e0041101003010005501489040d0200d41003156a20020440c0705c0b072410001e400c59007d0000502c2615030178048000a030310640011786859150000202041440702d0f041c2c0b10603420b50100101540c1c2842004d0250005292803121144150700007170215444211101d44681c4602c415050881c0c0c0024500d40603501115094884c8520100104696024070401c00148960450102c040c142a030045004a8040e0340d11303030729683d6000600c24800b214841c416009235a40100048885050080000841c6100c6000c00c0703003460010141755000c105120390242c4410501d0801c0169920300450340041d9108841c1082c5c8144490726101c0401c0c0a9240c40d00108009112820141e001004140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 784701124 1250 784699874 784699879
    0x1503020409150614090d020d0f1101050f0708090616050f01230a0c0c0629181603110406032306030706050c0a050703050c0a140609060a18060806 64
    0x2d4408019466000d0140ca03c245404102201556070319001824002e041541010340f04203000003056001c20082048507800780e403d410140c542200b0001a01d9019036011000d107402d505141d640c0701f2020080c0f048010080c068403001030840c003191540320580700140012b0b044000c411001c2e091054450504446856080d441c1030a00703112110081c100c2c1d0440309510b041005290741c0d1816400051170401c186200384100c02d484071002a619000e80381c1000781000c070741e403503202e440283c8002c1080302624152044e801554140110701c048e0091951250348a181a407031508500401c3d4000c20fa17207034a070311701c004c800200442e0883d01030b00107041b040e0300f040103054070580b080504440f8980a81d103460b4550820102006100e101d040580304c030b0440101070362140400e070307524246070040d254001c5645800440052119240c0002000028a160150010030500280000d001841007000d900e110751004030f0340c03403c01481140e0b0003c04d59242d980d21040262903034005013203142c0448002e40b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 784702374 1250 784701124 784701131
    0x90f0f0302150702060907050d02060d15050f0f0d110d0b0103110a0506120f061201020714010506031903141c060302030d09140603131509030e0d110111071503020409 73
    0x110795030304c002004d44c4511038072005090000e09180c03c00210440c042016070b400350040c0119800c80c55148514440c40450542c16a540ca1a01d41800a03d00c18481001d201c3c0f01d849943e00c03c01d80701c41c12090107040d80000c01c0c080c142000c0f00020303108201110040c000010390310002c000c0140c5071080c4601c501e030460785041c41c0307640d920401c146885500a1040480500404508000c2c2c04034112a000307440213151a00d000e030440f00362800c82e0441d541c1942d1201d402c4642e00895142840340c0f5400010550242002c425650802e8070040d0440c400207081045e0a8003034042000e22200f0341d200c03001c20346500f0800018162015000c1d00181c001a0300c203005101e985a0740b51301401c05001181d200c44c8801c5854001ca4080001d1900010f0150043c080c000c060b44000a09155200102c0c4404890000e006040e90a0046c105000e040d001400341e0008500e0502240848505204461007417034482c0030252440c030794a00b8075061748d100e00b20b5110714049814042d40c043e0040c10503503407030540c03c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 784703624 1250 784702374 784702381
    0xa0c0b090601061701081b0f0d080921030f0d0f090b1504021806071104020c0303190603170705070302030111092803150207020907030f0518060703090f0f030215 71
    0x1013402d0103080c4101846030f40b2801a69040f8a410401240783c04e400400c3c0346583d03c6048042551803500800031140043d000400d001c1620309580002d50301c00f503400140c2ca49640d4030303040c0d40d176034403407071440ca1710302600410004604140c035048055010b5080302c0a100a0a0a10308503405090075140c055840680d2003100509050901c02d91305c0d02c505d44100c0c6044440641e0a100195120070801d0f2201031010344642c0c000d032645d0004bc03000e5403100f801980e5900d0007041c400350854001d0008811541008000c0001c0b03860003d2144c414a00d09000782e54604c6180b90140c50209103030300094155007044100d851f20009480508103110040c1d94650b00704185500c0352408124140c40b4140c08014002d092000c5403580c500c3c107100d4900c0410061030260507070001840b14404555030f00000e61188035400c13001d6010700500b0b0f080303c22000104180c21240c4261b540b54080205160101350350f500c0003505020114122007501034111069a10300c219a00307009440d10728048460b0054107000340030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 784704874 1250 784703624 784703657
    0x70314010f0216110f010f0f0c05010603050330010e18070b03070315050d08031f090903030b01050a0804030302090a0e0c0309071706070f200a0b0a1806020a0c0b09060106 75
    0x2011742207034165107020385d4400b001002da4003460300800a00c00c00003194028400503130244510400b66000e100159151113034071f075850b0702094000508002c4200845001c400030340d40c0140c024190364030307004a103049542d000b40b824101c200d18410b4549912519400040050301c0c50021405014999014440c20740c440290700b0082c096817242503000043d11410300c020604840145030003100e40c2c24110381004441205440d82004d5400035201d01d95219840d90800d9010301c25641c06000030300f0f016041005821018098000c0188003805150300098481a260344150156000e40344148900311141042450298180c10446041c03800e407056441c082401c001c403040c80106094404001d120540c1c6c2c920048580d803141c1e201d103505205c0b940b468450709580c82034003004660701a500500800710b070350900080d9890003500e010283e0b0302d8001c024408109030380b140240180c101801503a19006003104403043c0780c400754003034080200413007805a00d25001c50f00328100c9200d0b668101902020944 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 784706124 1250 784704874 784704889
    0x10e01090911040b01051b071806211401020d090b06040b0a03170424082208070203030c1501090501060219060c0e0a15020f060702070314010f021611 66
    0x2001d0000001251031242c1c916154004005a05061412605203a610740e21602d404940c0700400c126504018401e01c045c00652440f11610086158180601441c00201300d000070b07410f00350048041e070641040002c1c8000c0001d0889100c403400001c40d5100c00c2810020700030f00c01c0303050071103103000c2102c0400c005150602500404001c000c1c10110b1145c030310b58944030141844040e0001101e000c0c40005101c620140c1c40ba40c1c0e0810f00311854199071410840140342d500010484040004043c001500078000c1c4212505000c1d0b00c00c804a960f002c490002038918000c0850f400d803e4460036075036001866008441350304a80c03000d1014410762341c941c4420ba0301c4511412041c030041a4001003000032800d00d0300320159094407820424141385a030004130788280b01580019002c80c002c01e030507050712641007010a9089141c1c2002c0e000030300304520300035140c0000c1c3c4406031030030004120b0151204001c2d4807a250f21955040210741c2c2c1d00f4170620089550074141020f581c14440300c01c41c820030303090485 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 784707374 1250 784706124 784706141
    0x10b04180b19090b01031103010c03060303140a021c03200f1c09120f09060201051e0c12010f0501120212040b100305031314031c0f0c05010c0305010e0109 68
    0x1612801266a5848449a8120507501d010350441d03c41c1c810101062503841d40310b01a41c090405602c0288480c4241401d45004a4103a000c01d4a481010030200c0d5218050143c020b4603255210398901e22000b0881c60003070b8188800703a202c0c02d054a00c0f200070303405611070481d120416000140c0c1e141e41d040c00014900072203c0030000d9040401c0300d4855181280402000700d82c10396000a10600c2544441071040b90441681c000300d2078400f220340400d07030810700d840c0080040384000e1000d4540210172080e041e00200041c5032010b0b569001c0f40808141409070b038801500320000400a41c0c5d200c100e10303048900b80c46900e010a0424442d0107213240540201e519902c0862602001ca4403503569a040700803004001031040d11004030040f0014801b030000f08407407801080208035050503e08800c03154188040803c0c8a5807002d05801c511392600300018400603258100b40c0d00034110b02d00d090396003051040d0020321a5180180105405400d94000d5041c0d902c003142c480d010340c0c0c9503500c1d6021609280c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 784708624 1250 784707374 784707383
    0x10212060928020f1c0f0b0a03020d020402070c1a0a390507090f05010509151e04110d09030806011805040209211c1b2012010b0418 58
    0x40018070403031160f400804019024050340341c0380501c10007490082840902c1d01914240e180c05584041c0215401090000c0c00c040b41c01440040ca9035002820300307408640024001c0e038000c1344200600401d0074084000340b03440700041c6103809203004601e80903802420380102041c6c07540c0b20a91150041420706418400e0168000022280c1c1318501104c21400030701140d43e88150500401e03010f140317011742800b9084a00f07002c035055041201b00607900300010f003c140062150a1005c6a9a580c207c0012980c54440c914180b100c0380c01c404503001d0500d0a10300e1480801c002404a002c204540c011044540a56101c0c0b410381c9581004481201c803130082c81350410401401405545015401084070040c01007801c81c4480ca06180c0300d070b0940c1c0201304140c1d0ba0300824400900d0288420f40ca064444940c50502081c4e840102c1c44110510f027200c0203402001c800321001141c0506069a4203882c01c001c5c11b009001003845109d41c0a491120030707007030080b03051645004902140d50301e0000c419500c13 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 784709874 1250 784708624 784708681
    0x1503010308040603050f280617010f0608010902102001020315270a0e030c0601080a0309062d050702090f07020c010509091810020706020a09050603090703060203180102120609 77
    0x1041a190405111840c010b1180c8d658440c0040d141000d00d0032081c147e00400e001040042c01c04810104a40e5994042d0038143d040c61040001640c0d444410b00c000c000e00d01f1b00084040c081e0313a036010f008104880c80c0b00b0641c40042409400c3c40701741c6031994660021902100b0310351a14514012032050382100c40d5820000320041030340801c00b504121141e41c00d4008490401d0622940c035450005c0aa01c1012903402142001c018107500400c0e10001e40b985081c81110200800f120489000c0f00f4849180003110740c401076401544104205c805080d0020907003542e90804010710100c5440c240d43d29405071003442030100565004000f5030700440f500030b01c8503410366a0350b40e0f8003007a260508074401642c016250b00080c610002c1c400350032800c1c06410700580791b620500001d418041d403230f0040f03807158906001700400c2c8040021540e0075240d003c84003507181e03115285092445440b1907240c44007175001155080b0303c62003599917580300f840205c40d544a42e4841c2132080000c0040804902d48070b000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 784711124 1250 784709874 784709911
    0x90b0906091305010501030c050307060809030a0e0a0305100609230610030e0601080105040b0703110d0917070f290a0507170c090a09060510030b1503010308040603050f 74
    0xa00141c0d4940c01014010200704100e9a40d8805007110b409800440d075a000d100c20600c418101040090050007007410b2040c02d6051036074541d6500e002e04840030781080380d2000e001d04507403107811400740107552080845914010401c42480074140600900050b2803030001c203412041000121030081e6452025004602d8560b1414442034100e243d440da0141601d507a000240c030402044101d0083c914800001071505007460003001101020b0315210406003000d100380206080c01c0202d60704404a8040010171303030030500c6c0c050800100b030700252501d400c01180f580144052200003601251043e500401d03016196111210000341f840304088810707061000003414040c0c654040c6412140a0030940f11900c070141000c105654101c0d400c90880401152221641c01c4c4440168098003140200307001140c1408003050200d0308a56101c0b04241e183c442d0a807180d00c0700c11900c41d00045802d07074103540f981c59040103140b079802841100002460140065048240d102495000300340c410b400300751900 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 784712230 1106 784711124 784711129
    0x12030c051506130e10050703020a020111070b16020708190b091203070f09030c0308070506070512040b0402031509010c0905010c0c1a040909030810090b0906 69
    0x4074041e09000e0341d5a07459601100007862000c1c0000e41408050a85192400503041d6480c02842d2105004240340d02d60014011802c083c0c009000c0302d046080807101074421303030718083c0014102c0c10104150704e01a15038005424a28412103000075181c49982d8103100310032200c006c4082140c9520350411282007401503104c2c04a0000d030401c0c4d210681c603180070744002072010041025002400b0001c4e07014510ba074024580001c904200c2c41d03124941060544d0100009881a201d21000513909a104e01c08444280e00d000080a07115115a6521b41e075101003c1d01c12a0316002d0254000480c4079500031142c441c071503000011a005001c441d006c0c001100c9900b04034100000c0300881008108106821422940030f04441030b9100540720a122481c003840d0400162a030074081104141640540401d0103844e1840d500360081c2d680741201400c540021840340c0d0024000c500254192 = true := by decide +kernel

theorem cover : BRFrame.Cov 784532374 784712230 := by
  have h0 := BRFrame.cov_init 784532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 784532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 784532374 ≤ n) (h2 : n < 784712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
