-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0055
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:35:33.108585+00:00
-- url     : https://prove2.me/submissions/76350a19-9d44-452e-93c8-0b591b30c80f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 9712237 ≤ n < 9892093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 9713487 1250 9712237 9712259
    0xb0310020a12020d0b090a06050a0e01030c1e090c0504050108070206090c13020f0409020409050c0c06061003060e09011a01050403021e0a030803090c0901050f06030a0b01090f0303020c0a080106 85
    0x402900c0466400300d01c0d509980e1340c540040403103801c0109102807600d04407504000400b00b1b40182d40c05151001ea0101c0c0c04c04c00c80ca211810b903500320302d122862a15015000707051100c1c400404000e00c21001000540c111a40200d03100e400d586d4031403a0300d980c01d240c0010100000102804219440401840000c040c0071614041845080d0303a00800b49800d20404c20180c8900d001c2c0500910001030b00058064065000e8800d81d10780c1c000612840d1207a00d4900007a0180c1400900a03410601c0455030328604024401b480100600f00460800c2e0b032101b030b55030000c0d01103500b86102d944078240038908500410001c5030700c4209007401340c01c1c50b003140c0100340c4c40380400d025500d41c4441040c1454141d62400804801154402901d90f564540340402c680c8030510420254080c0329104d0001c078142c504050300c201590b0002d032015095a9440c400c2d04045c0c09411155414003581850101d20b030381e4450398401c0a18080e8000706842d04080060202074006a4030030300e003a9140c16828000a41c3c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 9714737 1250 9713487 9713507
    0xc0824040b09030c07090605030c010509130504050703080a08040c05030106060507170d0203070f0905030d0e061303020405150a0b040b03010303050c0c0d0b0108100608030405120c03100b0310020a 86
    0xc00700c0007405076500040149988114448080903102d000300004120002d82c2055080d1032094041e6074000c000310380103443c40d0081000359540080c0e030503207441540483c2d6101641c0f0500030821210b02d95a00c2e00c07031070800d5002e0f111990000304410104000c0c08405c00d0004020942a4004c011303191908a00030810301540a0042ca101c1c0c01c000c00c04504903040080e2103041c24480070456803030401c41c0024203511802080319010800c0c03034070001044d1401140b03207200e02800d0741301d185820f0440000c0045540c403504098502c65194100440940c84911903e031107850140320140c07203201000308000b40031a01c0d5114170b0100104210502004030948180ca044035410f00f8501e403107404049400b81040544600b903078002c1d40c5810350505202884030003e040312103c00540364185044a0400180c6a840c06005070652040100f002681016000030282060005c00d960709a011100000d0030311800314054040070740c44100e80740c0140780030720005402d41061103045180000046010700b4220603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 9715987 1250 9714737 9714743
    0x21218030d0b010210180203060f0709120201050c0706110c0d110d03020703050607050d0605040c020d0e03010b040213080105061009061b1b060e0d0b0a091407030c082404 75
    0x101e4050310710b564000c201e03840c0d030f12250050601544241e080100e4007054044c4041e0320030f205007004515040424070000d80601034a584d8a0045805d00300c1c0c210032200013030341c03c0741040005c0100341041c0d030302404014042e01c801c0e44d503541590503a81c0c0c62031904c00c1180d0303005e01c51010b4004100010740114000c080c8100b00b500d800580c00c040d400d0036400d2001c00e502c0034115000d41e40070030922703507402801410003c1e4480010002c050711a0305000499141140c010050381c441001c00544900070301134080da048000f0000b084a284410126007039030040d003511a074001d0000410311100b242030148d203a010343c0946130b0441c00303480c00c240188840000d205160a00001e620102c032680400c0c17000d5080650000300c1c1c040800d046070424582c5000c0340c0319140018081002100840c0340c50003904e9038168000009590503210320300c068000701030000041340c0c2000c2c0c05c018406241c505000c11340045003e07006940c031081c5071804e1a800c0160300c15205040013400303c0203020b074480d110f1140c5e0700300c0e030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 9717237 1250 9715987 9715991
    0x506070212010e190c0608041115130902091f080f0703060b0a08060108060105090607030302090a051c0605070c020918010b040f0e0c0603090c010c0602070f0303021218030d 76
    0x1c0c44018140101400140703910301e4000e81c41134001122880d944000454455105122407035a501e030701715000700080d10018a0010582c103c20f0b030030300c0c2551010151195018486152480500b080800c5440750340c80036039299004201e94489190001d1861500c900c04199400c0980e0360f400e00800d07051000707201c0044000380f5004103107014484c0d40240082c00841004680e02d072403203130000d80038050803a1203500051205002580e554440d02c19156054070240806040c0030403660709078041d400c195102c0e0303080012a040020190755409c100100c5400e0384d2030812035801182006406e0314002803207a07060001880296006844022025900c1102c0c96490b041010340e11103d0360141641e10071403a070260426908919502441e4015a003800000d41103503020b140e00020700c400750204980415843e04543c60300e842950250442c0003040c1d00ca480c00503c0c0c24001d40d07862086081e06541030300025808510141c40920406420f0b40001c0281c95504c006a5400407295072440f92007041c4100700c1d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 9718487 1250 9717237 9717259
    0xc05040b0705030c0d12050a110a05280306030302060703020c070e0c0909010b0406091202090115090e0f100503150114010309020406031104110301030b06010c020d0501020a1e02030405060702 84
    0x2d0900585200903c0ba5055074802d00d03020f10001c002d010101034500600e443d1501140b50980036200b4929114030681900d8144030150328242c419401445a0402000c00340302e007514501c00444d519815070485490029109007141002032030000300400010030300d0310400503846070400004505e030441e0200c0c0710046e01d95031035001150141c00358800700e40c0c015400000104803000d003240940103480903669200982d69988042100141c2c031004081d40000c0c80d400144501c01c07420382c00d2100004035040c58640d00ba910068582915011114030380808080d13002d201200071804a120024801100200a00c11400e0300b501c0b0250340c103100340294400c0c4d1010000c496406600464180e43e0010010040e02e03a6900345518a022880d444520a81c13070701c14402515402d00060700e0590350003e94501340c075540e04005580e003015814081c0d070321110152041c00020424001056070f00711503550807a0121b158660805003c0c3c210300d05c0400e54000340401d0069403980e07170a55669a4049451348407074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 9719737 1250 9718487 9718493
    0x3081b120c040b03160315030206030103020f041b030906060b0307050d0b0109150801090605150d020c01020d0504030c020f0303041404092303030114030316031d040501140909010c05040b07 83
    0x2038410b0764051260701c1d0020007040344580a000303411504914a882c180400719401a201001604901000754429410b10050016003086002d682040d0b40c00b5200186c032070007444035545d446045880740700c0001d448401540400c4524001c0100400154100c5401c40c14505000342c2140a41040229031075960781b01100780d603100d411190b000f807980b00e01c007121120304400c0082110509019040d185070900c0400200b60511044142c0100c550296031800e0ec410800304202030b512105148440d59028403220303a021a41d4400d07a401a0300c05c1d00c0b0f40f07841c0c890301d10602600d540c1c06204a0f01c86e800030b0008004541a50300d00082110003110001049225407038001c0c03140c000048503e5906070f050360000d80b1400004000c0d4142c620040c0c0100c522040b010805580c1e108a0342e0300842ca803051008030000a016103c2c00002906000e2801000e8030b004001c101118000d80c04801c4040003401942250305082101c00c4c0c0011000000303004044040c0740c081d01c81d200e14840c08000d80070000b20706084c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 9720987 1250 9719737 9719761
    0x5010e04091b0b0a0305090a03090303050703030902060f1b01090b060f13020c010c090807030201020d0c030309120801090b060c0a0311070e01080304031403031504020d020f04080a03081b12 83
    0x102c00c51525000c040192a0f01c41c0e90640d0b080a904240420b2400e400324240c0710001551050340c0c2d500d40c0d146003280d0f045940443d580d400c450802c6061607114040d80f40181d440c0e00141001001d0950f2083c0c5511090314421501000f000303422415916180814012503004a1b40a611000940c1d041d480c0290300310110317812007204607420f2006840411640b65071007040d00b000149950950720b00004d1900d80759003a4a8200d0b81c4030090244e0300c10303002c2041c10b90040b42080742c440e0190400050140803a100e181c0368204543e440c000051b035400040c4603800302d9220b5a20100d6003600e001c0d003007038403095509030350705c5002c040a400d0105280403051015030412001010f001400c0b005000781d40d6840b0600d607250461b00003100c0d05600080c60703404004d0000280d038032a10700d402c2c2d900c412543c40d4061000950010042032200c40d001c005100607164104028001040c0c4400100f09201e8142402062480041e0121545d009612107110384000e05200307907a1350004a075090381540e200c0d40700b4885 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 9722237 1250 9720987 9721013
    0x7020a050609120f01050601140a050a080a1e0605090705040b0304060207020607050a05010504021003020703050a0c110a06020610050301110d050601020118030513090e0d031505030106030807051002030105010e0409 94
    0x142c510403103000e6900c2c1391064001c039000b40070a0b01c070443c4441154a80200b10302414594000081042c00207803001031184d0440b070340104002a00003001803400307001e043c00d10350001e045032485448060400c80d40c02e00e00d1055522841900e000c03400c041c100b442c00d40319440058005007074550081484801c0d135640da000c949070aa4420212400034a00d4070346030380641011034040e4410340c43c943d55405458041d00032181c0555144e0f88041c50422011015100c0d040e8003141034440207407540380d036401034039001c1c5070340c003c2c181540061015142c0041c503e40502c074a07402013400b990410080c440f0b190010303030a40d8806071000d0000314465030b584004070b0041c0a0f8400d13081c07944060860f0f050501d600503005150003040300c0183c1d042030b074030b4035105000d031500d1a41d46215039228908040321107200c0e43c8a00b0804070b2007954414401e60b901c00180c251007180e0030075034084800007000d000b0004208107800c0180785a00d400e500719854580080d01e45401688418060383c0c03122001c000300b10810301180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 9723487 1250 9722237 9722269
    0x807140d0b0312040e01090605030102031509071101020309010605091015081906030c05010201050a0605010917030415020601060909180f06020909010905060103060f12030c0309090e010b011407020a050609 90
    0x1d900c1e40d580e512a44d4171110280302d9619690b1174200c01040300d00341070003201e1080c10107840043d012299801440385a00d001000307581008000d000c21411900c0a00045009010541c00411070a003400204084070750040c00300139280d5100942007080f58480344c500c03400c44e485070809c070b072050f942d803240c0c100960380482e010703584107240c588044100a40710200350f050b10400c0e8003c1010395140c13480001200c450340540c5021485a0f4020404400c0c0001c0d080d11003410001548e0425a84001112240007194408405a00610014080703217a04c500c680008001c2c100303041c00050309103480000604c0c80008042e081d0190311110b041804101e40443d100a24084d0801c5290760b13442007844010007080d20347c240000c5c101a00012401d1090f0101d07400d0302c414191541503504550703010341d48a039002c0801c03001d00c2413406001807403001c1b0b4030401e41d85c3d010f01070001c01d84505050004140d4a00b1008100861106100c12800b584405610409417042a1141982c420f80100002d0081450110354 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 9724737 1250 9723487 9723523
    0x80a0b101203050403150905100e0a0506150108070c03081f0308120402010909090503030f0a0b0d03050409140c091201020c030703090801050604060302010c030302160206030c0304030807140d0b03 86
    0x1c104141d0b10038003c00c2180d00604003028004100c007003a40540d1020b0901508580c031040300303650100350a91000e03100201c01e90480740310500720754035281003000480305400f212800c070780701c00e003e56007100442e5072012207407038200180700303540e0780c0a003484201a1001ca560103038081c502c1458440725a10b000915041030707116840340743c2042104482e0600700c9007240000c0e0720800c005614031081c001c0b10709a07036004010f1425a070310706000c4020403400409081c074140d19110107021b5a182e021644000d13600995845076614209006001030b07503a402d88a0038104013907000c020803403034104141c0b0324180301241d5082c140240c000d6224003a00540406d0000c5001c00989030b0304054000d1001c208981c074440080c88603685a008000445e4900c1c4006400300c3c52620410340081d100750b00406800c48011117184001a0a80102d0f103240c00c101d41c2d0000030480041480140750b0440b505903071110342450030302503403603094085d0700035802070940c014105500c501242a569806104040010f00700742c2d41 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 9725987 1250 9724737 9724769
    0x60409150504020315010201060816031106090418060509030a080c0304020406090c020c0414010b03010506030c040312050a1b0206090409080d050405011b0e0a0314100c050301140307080a0b10 84
    0x2d045c01d1030392032010602641c60318500044400d40450b0004854a02da6426640d907861a103400f103940808003d03c5521910400c081005c130364032072081c0180d0780307100a04a07290f44450b1074464120382000e4030390015584280211101c02c3e81c05200e040d81710704884045a160b40391032001c0740184c040d641010941908105403080c090b0b0b4002841291100f045506110582c850703400c240c060b40303003805903200403141080144128208035000316081411070441514055998580000e40d00f1049040c000041000552a6001e58000c40d4a142d052182800008501a507400580688100310140d4000c5403200007038418403000900342c54444020032024044c5250070303c0c104d8001d000c011481003010488241e000d84051083c0b030700005c01c00c40945000181401e5884a60100804074843ca0ba01c1c416079071100e03550038a40c052119024059280c583c0c0f41c0d4106100240d050341010340c2c50b4080d620101003009601e9000854259041d04280c0458507034903403140780c1c00380c501c00e03801c08040408040742c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 9727237 1250 9725987 9726001
    0x50a020d0605060a060306030b01050d0c1a03040b01080105060102100e1e03030106080106020601080a02010c08090d031809020f0d020702030f070305060a060b09030c0f010905040f09050105010608060604091505040203 95
    0xb01c544a050102c0310320f0b071410740b100015801c50b8054000584560301c0d04005001c2c2e801c0030740011903c14000c9080d002c03c145c1c0c5038ac61040c050602001580320070004006d100400c00c0420007039024100700c4000307004134a0003d0000b9aa40003200c2d500120036220106c580502e80309011071440c0030198070101c1017200c104e04a603030b030f42e0f40203202d00b0002911300800011040e20204065043e9101d07980035000d038100381e40045816a48401b0140c4140c84204510758041c0d40f45040008424070135155820011001c04030481059920750020051070700400c2003c140d1280c1c0421240c445007051001601c4504a0001c00c0c13810320360b01e0b10360426204410010050100000d0480c0c4030b0031041905100b09c546864200c4402d016448980f42c0545c0078421445052400000c2c1c14610030b0103250140c040e03551680020142c8030308410f0f080d20301d0b035910071ba801804420b001e91030260030203040400f25802c1c91004035510b84524820442031940e52180000d180003403001ca070005000040c419500ca0030004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 9728487 1250 9727237 9727241
    0x50c030408030417010501030201080c031009020d05040203010609110a05070507031a0a0606020705010c08031807090e010f0606080c13050303030a020301170c100318020d050c01120b030a0f050a020d06 88
    0x4004d003502500548202040d001050007410305881d81a9544003c40d1645c9048140b50b804c01b44c41d10910010482c2c0200c0c0000552000e03002e0721712602004640380c24140141401c650843d000400b4880c1401d07048252100c2e10822615002d81c81e00e050b0342d48510504140c2d0170104141c200400c10706d503401ea1320100d0403140d0a0303240100319058080102c2981d502041e070b0340d502c59104050108110200240204000001655000c1c41d450071ba07044504001d4401800c240154000102c0c1e80d139200c55081080009102e8036011161f400c40410501e410000050181c0000070000d001000000440256514141d12480010503010301169264105201c2410187d0805d0107203209929200f200f1b114407120000d45500c10140c0544044880401ca5804a000d0800d6250b04200041803149080040c0c440c0d00912041501800c081d1075041c0130b81000405181c018017002c050300d400c1191300c0042e82c0c0e001c90501202a030010240c905481c8a05d0003508000d841600694030407000200103051101903 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 9729737 1250 9728487 9728489
    0xe0402070611071709010e01030b031509061602030405150f0c01052403150705030901090203070306020c01050c07080a260406060302010807030903050d05090703080301180f060b0307030c050c0304080304 89
    0x402910404442011550180d8003e5001c540c6c0000c280000f0207650394020b9000c0e209442c400f80030f450544a400c043e0310641642034174881850f60001c8100219031145040c0c04528480502c045d40c9005e1a00c40000c0800c40362049a034940c8100041c111a80d0700c02d5801c954030315210400030311041c5000e402803008202d0702034801400c5051246c084400e40344c00305401249442403885c4091a46840300112860b800023010140b5070741d03980e020140969003c01c0b4040003544620780240e85d900c0d01020789400d5032000b4060580002082c003040d400515550291101078a8503d40800320403075440b0481e40c0d02208003041303050100c418060000f4040c003500a401640c3c002c0e2221000368459881c1241140e10b0740302c001d0700013001406a6a00004940c02ca503030008071070b8089030300c07460f03c0e07803500f0520394802c0c1c0c014040444c080c0040440700009005240c103480c101d103001c011080c5444154022031000400200030541e03140c4c07060210074000c07026912422030100450361a503440e19821560b90f801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 9730987 1250 9729737 9729743
    0x80106030b04020306030a0f05070503010608061503010b01020601060309080405060a03020a0f08010f030b13050f0303070908070e1603060b040801020705060604020903031606090506040b0402010807020d080105010e040207061107 100
    0x4294032180c0a042a000304e03401904042d000780000110b644030903a500350000f208440c640240f0340c0000d06503509004120140006501400c003a0814202d10b1000380e0f04ca500b2070b40a0b90601c84c8201c85070307802203840e81c1192802e0902092004941c0746c82402d07840341c0d81281381c1c00781c1e0110750040415410350103004403641c6501c441c0d020041c01038091340c040b502403180305042d11004000348000785024060580040407508017105140c4c0c1651407a051105650000c11640c2c004401c000e401c0b64807051200050111102510f4100d05184289506560080902c2c42d20b130200b04070006440c2c80303035108000501d216030010f500c03542c85d20442c0303020390700c020004c0d04e9902c03840c004500240707040e01c00c440e90040d009008501e04100e0003600c9007000d40c0c04a055504c03aa82c3d10b005000b01c6c10a002d8103110301e105418010300e91500d44009001c085000d8581c00c11940407864a881454100480605644090a214079002d480c3c0c0005000f902c10044002e1106080801b03c06607407030380001804107184 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 9732237 1250 9730987 9730991
    0x306060f03061d030405060f0408030304060e07090b060f090120101a0607031103040e010326030601021b13020d02090109050121021303060903020a03180503150a0e070608010603 78
    0x60344071024203d4264040716107075641042004000c86e2038080014880ca503e074500c0d01d420107507203080045c21600110381c26a80961200d10341c05451005100758400351440720000c01c03115010740040740a83c01241042070f1a803000080d81d44c0039038011030045400f03408000e441c5080044c41c0c40b40540711400760410360000c82c1060700c80b014000810481080a900140c452030400009031412100b03c181850b00b0724003400104804944d216018111901950050300c0c158001e90729030054007012003a50440c2d90707244409009010050b039011510300c44240d001e4440401e01a10440020a01e01081041314200c0c0d10000d07120003249400d80242203101d509072603420980d030380c0f00010359a02c82e409a02c0300142d540300482008a0113641d002d440000581c080c01805941c07241d40e107004a42c400001500503a115402000070075520241411600c0b8541c4075045070700b46400c0102c1e80d103607240425040d4102d91000062401d61103607101078071206040c400c07100f0050fa20384001d0b01d001c0003030103030200185c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 9733487 1250 9732237 9732251
    0xb030606010c020609040207060204080d0c050c0d030507060506040b120114100305060406050a0207060903030f06050a14150f0a080702070501080c040e060d0203010623150909100306060f0306 84
    0x9030144800544581c3c016221900e0034018008200096110b0742003191881c0d802d000100d205541044403000c0c0c40384e162100904024941011480c0c039aa04000f54450801031103402d00080c0c1c84801d40d04169407250010503943c40c4e400006002e403e0000301d80341c0040c410038a0303240180d415007000c040380c0c0c8440c04100311900e030100140d02c542420300002e00b9584c844000324002030004d48c17110358481580302005051450030b135508801d89a600b0300c142c0000c0c0e2907654203492030303100f881240300400045031070301209450041a1018116514503182c070070708182c00100303110001401100c41134203061030b002d540e80740d4106019003041400d98000005109242d000f00e40755014020140c0641c0712250b43d10b0406290140304a14403074010802c5401864005441c0016103007400344502a12504907a010300300710300356560307000d0354904501c00e00c074a041158004c08800008101c071583c81c020f40d0001915660752007907811012003648001c00303852800b440010f086035030745c1019059a1003000207000d02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 9734737 1250 9733487 9733489
    0x80d0222052107120b01030b0a0501030203120703020709090605071202090603060d02011107060807030e0313050415030f050307020909010e0d0e010201090b0a0603020f0a0605030a1a090702010b030606 88
    0x39888600425810070b42c40903862521002800500c1c55078101c410403208507507100c40c0c212003010201d0f0421649001403000620800070a1540342d03a0180c03840c6c200300f11544c51078000982d6008401011440c00c003000505a040c188213001c840c000d021149014410712003030b464138030020030007129001c00085100c03000c01c1681c00c140c001c950072990014880786c1551115020440341e641c5800e030032410300083c86403429804900f409208010700c0c09466200d0305103854040641914012a1794460320b400c10040e01004612082d100c6094a00980d0b0002d0a00401042002e060400382c00c0a45515010007200040040000040110318425140041d990b01c41100726420b03141c98419403129070f08081120840f141c803814503180c96400501c00820b03d800f95840d000c0d111041030320030b400310301c2d210f11081c401e5040004c00402102c105031a144503c5142603002002400090102c00d8105d4075900e4035106150303000000e02920758000e2080750395041400c0043c0c0200040c0400c42d0082c081d0000050361 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 9735987 1250 9734737 9734797
    0x50c0108150f0a030209040c03060c050c0703060b0103090c03080c0c090402090a0c020c1002071508010602030307030e07030803070201020a03060905070905120f06010b120901061a07020409080d02 86
    0x14841109118507599912040121410220300d240d60030548808001000d681c55841c1140528010803500b9400c80c15030801ca019685001c1c81c0f101842010040942811000100030080f42e030000300001d090106240100c1c0030f84241b0301c1c003802c3c0260b03d81011051040d1785004066a000b0001140c844160040500040a008440195200b15031100207410740c00c3c1074100c40130b24069071041d6040c3c000c95500290030000c8c10009040143c0c030694052117600f0311300f0181c103911102d038100140310b90f143c21030082d81d03484014002000c16454038002d80d20701c0001c01011010b503911402e095200d1900c0c8078002c0c000d4010600710703070000e420128000381031007103440f41500841d0f4503038481e24441d0405043c0449501040d900c12140c1c495039400c0c2e1010703201804079a01900c4404c41c2107903211552250400d81140150000040c1c0e450b110007040101c0c03204500c1e0b54000c80700010a9114100781c00010003d10304071300083d001c003600040d03941c50a01560b0003000440c445004501850300b000c1c1041038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 9737237 1250 9735987 9735991
    0x60e01050a03020c070b0c010906050a0209030d0c1106030109020306100c02060a050f0906210c0903070e09031314010314010e0f040206040b040303080403030509010c0903030f02030405040501080307050c0108 91
    0x10115104110711000300380b09070010070a04405108070b5038030b2030303072103001c0400340d0f110380d201010b40c0c1d54402400c4208001c5004080e00200d40210a41c20241c00e000007945881c0e0b000a000188488040208104800c03240e0b1440001c0c07004020316103d40e50303a00090043c1d03108603a40c61040404585e00850280aa511a00d003140c02410131030400110900035255640303d116201921801407140c150299034140c01840798110748665040b030214094501040715502401001d0140340500c881a841e490015071101107840380b10140384251142c0180c00d08610442e0040b40100701004000704854800958042205a00f031340d04001c420b40c844003c5115640a0041a181101c017602062a00809464854016000402c214981a0380d1840040c40b41d102c0d038403c80108a0345801c01003410f4051040c2c0d90300211001c024012640b01000c0144000503c2c00010148121400000b22203031007081607802510014004010a58440b4007055598000d00da04542e00d00c21041c082c080c2e0352241c01e8042c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 9738487 1250 9737237 9737239
    0xa0b030a0302150c070602040b04050a0f03080a120b040504050705030706020a030e0409030e030609060a1104180c03022101090507020705010801090e030702041a041116080903150103140601060e 85
    0x401d000380350400030300030841c0140004c100d655042c060312003c1040c0307100400040c4802e0200503501d41c98507080c005203a43c55030040c004032403000b4080000c96991030442d610801640b41403205c00002c240070320020001c003d1003540003450300c4100b0040200024440080e560101c04642200d40e8034401244d541a20f841d000f400990000195580380c01c00703030440c0312014428100250045040307000309180c40030444021000d6072050040c01360010880c40f03088614640310358868038060614921000c2413040060002809aa8010b050b4280e803280c0c0c10b64101c0c4484150700140056aa5000611740c030f020b003d0020103610300008240e405000041c0441160700c182c4401c0e100f03030701c2c194840000302108540900d09010400460005a4503031252840540310b20710041c0000308460240400c54120113000100310804101e03410343c0d2030500610790602035200007020ba0318034030000030074280b0b50304004003c0c85911840000c13082111400100651150110440d5080eaa8503001101c034901c8000e40c00d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 9739737 1250 9738487 9738493
    0xb0402030c0d0504021c2a140d1511270f060d0e01020a0815040902060301140301020d0501060509100804080702090a0209100201020406020d08010515030402180f0a0b030a0302 77
    0x5800b2000e0ba90806907009000070564082142508846c441001c402c013002c8415118001483c4068902c0e207001065001c50b0a031162005420f04c054003413900101c1c10050301c10000c42915000f0444802c1405820745c00403401801440c541d09a5400076400000c40302103402d08640c11408452400c0035441107081c40104011110140f00c41407000c254407840714100d803ea00c61102c8030304038209000411810764030b40c1c0c40428501e01940500c0480c0360a140c098490790420101c80d000d030fa90740341640c0c151040700990b1441401c0010003e40284514410005850306003800082d83c26000320240c11072020549441c68042c901a404403070200301160010043c200a20100000d0300706041003950114100000624001c02c1100080b41007202c0411080103030340000c1d00740140c1340d05121000100d50700d03050424195040100281d8030742c030303045d1051041700804400074081d50303100740c010b00604040d511000c0075030600403215084003004450b0050500e0130440c4404440c00c0009070020315541660203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 9740987 1250 9739737 9739747
    0x304140d0f02100507080301080c0114120703050a0204050d05070504060506031e040f0501140702010e070503030702040f061505091005070302061602010b0a0902070501060f0f060e0102010f0f090201030b0402030c 93
    0x3c2154060100c22070404000007401418002509100114040c20045004104007400800010501c001c0c1802c00d48022200303000c8a95444440030295400120500300031481e0b0740e44810110081c000c95002c2588003007601130307242c01c1c04404030f00c90044c0c0b04103840c10701c05a61a4801d01c0002e02c01556003890b14103209803511590368240c040303650460b00c0344c1e00301c02a00c04641c07034050a6800700505003013002c480c002449040d41c4c0900c82c1c0da64110030f51018103052880e201c00607490317008030700003e0301454403030240d100c0c1d584040d4071880160001010308044051000e40c020441d4100410700c0d03003d044000c04801c0c07254091015680740642c0b65006080c2a41c0d5900c0180d1191240341800003035640307030071189540d6a5026031040203080c8840c0010385402842c24414255581940702a1018010f28010701000c95280d41c0d007004e558503820908030071181e13000101e004149807a0605060340c5031400910300c1c280c0d240c001890850003640c0901c40b4002040401003244001d035125400d41e50304010b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 9742237 1250 9740987 9740989
    0x10920040311010905040504080d050723210c0406020106090504020f04020d09050304120302010501050d021f0215240108012103050d1103040302070b0a090e090f010903020304140d0f02 81
    0xa106040c580b41031410990b503030b50b01c01c0404d0603a9002d950896000c9030124004a04503840e03ca0343d603215850346048100c0d1410b01c034003000710708407007170044420070380003d406203032000240105601446220a4080103241290f406412031f00180100d00055003004000110841075020b580c1c0140d80040202100d044217404110007035206000b0200703901d0301c030035101e0041001031010b08018002401c51070441e1000d894000d00b1280160042071260218448030340240e1904e4241440c0c0f0384556402c12170410405a081e40b03040b031102c04a050764070b80f480801c09884049035018021208012280e049804010300640d1542801d01881184014890380b03141360002680714015820b0090a04a107056030340da10303003803e85004042210154500100f07220405a04020010080c2090000fa5040100c030030300040045035144109103007800c403034022403858482480503040b000f1180c00204020052894080d40307a81261040211000703500742518143c1c18090036804010340d00500003c032100040e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 9743487 1250 9742237 9742253
    0xd0905040b0102010e010c2001110301050d0309030f080904050a05060f010302130b030411031e060609060a080a12090f0503070504020705030f030109020d0f0e061605090301140109200403 82
    0x5a070328119900c03215801c02121007032003901201d600f55912020440f041300010300408110988400382c5a04d00354010030034140b104141c0341941e008032004851403daa0030201e6900b60240c10182c030301611000d00d8000c115820004028422081c0c5003401030b81d0300c00030340200701c6a048842e15045407404c203100701e0661280d40101007130085481501000b5480d502c14000301c1e00112000c0310000b030051406e09051408004000488550741202d6858204610041c1d45407080900228040d201d0440480c84650f1020888000341c940301c0c0c111204d1000f00d0401d184110000d00c01c074000b25010390303030101301c119000b00008150b484c0a00100742251a2400f808020f5200440a0720540000d01c1100c802e1070380400210f00070200c010700540c651700080280c0c421a4156002c0c00080761800c2980300e6500004240c0d40d42c0003034006541c00300e514040c1d40640e131910034460529415441d00f00040082d15541811a05039180d448080040c2c40000c0f1011803102d01d0441c50880101040c0800c1000400c05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 9744737 1250 9743487 9743501
    0x30c030c031e0e0301150506041406120a0207030905010201050108150903040b0a0903030f020d08010302091008030d02070b060d020303190210021603020c0a030c050105070201050702030703030804030206090d090504 94
    0x240380020300725020400d1106a90642c854000000b0000e00140b00320f45824001c5080840f00001c1150315a4982400100039101d28807807007140c000504200a6140e441e6820f035003030080315070f403a1200d0b49050402c40f002988520340c120302055484502003081d500c14800d01c0d042e96600001440700f0030b201200b201020500402a5607180300c200000f0460304a4003014200040281d150f200100e0b003140b5020348035030800e0f54a9400c542c0801003942246a21a12641c110b94041d5405090b075100c1030741816101840341c01040291000055804011800d640100b502e940076803014032064a81a04001e11940b0148000e903240e4014806501059900304040c0082c42c00b03401220044100310140b041a42c02c2410207010030503623451030b0000e240d01840130014410040322180e201c5e5086a076041d0000c50a80a0319040240106043d030440e4080c504a4181c1500102100d80c55036507031030000c0410204030f804030700502a090104d01d1000c0d000800840c03240c0e56031981002141088180001400d00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 9745987 1250 9744737 9744743
    0x9010e0a0f1d010605030601020606010e03010f06140f03010b090c090a0f030501021c0203100605030709050603040507060212030405060a200304050c09010501090302060915070b0f010303030b0a03030c030c 90
    0x440d8000060840000c1c401c44010940390100d5000c8038000e44000300740310070590108051140805c03c21010780c0e40441d460382c0c41a000d08060b000d104055010a00602e414501d0b00011850700301e0200b0590350705800b1030318582080b199101911801010f16098035078142c6400c2c0c11004400200d14002c8480016017074611024002145540c0d90b00009682026680e105481c1c603540007031010b015045040b0501103d4540c03440035495820a030110540400d214441d0030700b08803012010401041c803c2141c4401004000c0600e03403a81024280180c0703900c002c0c400c1e40098803c1c00c4542441000b494143c038030483d0004017074440f55880e040440c024043c40785031031104028404410701090054070196004501800081804001c0070040c0000d041c41070300041c0c140f00b0320840400059450408845003004140ca0701141481201c0c04440031340a03040004200400c01001c10695040025038281200c1c065501030041500742428403c4240c40c500000e40003920b030403004000300b8003941040d000244 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 9747237 1250 9745987 9745999
    0x4060e0a050a08130e010510080c040f08250303120b01050d0c03050f0c270d08040303080405060a0204030c06210e010603030809070605270303030106030506040f05040809010e 77
    0x100d541c0d4aa00709152403004465a00c004201034168180f82c520f0400a0031a0000c24211541850001441c40301140e040e08100304c060000103403608110000e03100100f100c1c14403205526142c00c285a11403009414107603803c2c0c146080c01e02d40c10075085940c0c0850350140c9a000c0d4403640082120090002a403010b0305101041084a1090744d440c807402c080309a00c2d40e0001150304200c10895075125001d0034100b0b080c8001c1c8aa5690661a0700318200d801211002e4000c0c4038075040042403548a02280c083e101ea8400b06002091613003000c0d0325417044d0700c9507064070790940e14821481d00300d00843c0409003405480b2501480b0840c014650504141c010700d101c4c3d40301e03140c0d00d6000003e0340c40651f11441d00303035194142001010313000003404d604045000c0207052003030300706900248203021720108026a001d13038645504520003040c00c40d81c0351060180c01d4a5070f0750703150b05002e00544030664541d40290320345a0031303031640821840b4807401241d204407001c2c0791040180044440d0394076000702c141e00103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 9748487 1250 9747237 9747253
    0x10501052206030509100506010e0103091e03020105090706020703050a0308070309020901080705040c050c0a030305130c06080f16080a0b01050c1c0206060d050d0804030512090109110102031204060e 87
    0x7003100e8006000401559601090714901111490708108560f002c2441c20750400042c040c9585e00a100283d01c20000e1030005050384141c1007482d140a82091600d141c0060030b280d00e003d01d54103400c118030403040303601203942076540d03103004036640c0c091403102030866044000041e0000b072054032400d400c01014a80440e003811641c00240720042e00b0780c40300e80b51f90320494041003241480c2c003980c10684c0d80f500f42507091681521b41641c40b14285030008080603929130010f60801100d103c640d090580000c2590303000343d20f40300c0140402009680c1c004410b02c007580090325008900c000800e40c0b6549607a040c882d600c903120300d5009040e943c3c4e001814418140250b035000001003051301d5000e41070020030304c00d0342d126040c041e0500360040c3c8002d0145241501910104034005001d180206441c03400303681a5880f428111154081c001c4902902e022110501000040541110540600540c00d10349800012001aa520720500192200060801c0001808250241d2100208185050039113200c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 9749737 1250 9748487 9748537
    0x8040c091d0105100306110913020c01020c060a020306090c16110102070503030d05040b06041104030b0a0b040204080a020f030d020d03050903090d0b01140a0b030a050a06030b0c1b06060901050105 86
    0x7440f4202c4540d2130300704414204005100c2c403401000c0d0b080d2400c03e55645032840e0400031030b200304040351000844071740000c1c0c3c40980f00001d60441c1d003081120019543c0a003841000200a940256107451060081e1008a404401120100c0d411948600225000707500e19a480c94819011100c00381e0641c01042c0c000203103030b101400140000d1205d0140002d00303140c04d152003524200c010342582e01a500c1c01d0074a0417070041c3c5e28101d0701a20380010131048030380e59408040e800740007040c0d00c1503080383c004540042e022a0014001e07091a00c202e03100790141100300b0070315a0312401c0d20200001a03000410b450301c214001c2c0e110a4000814400b40c91605030844082181c0c16101c0d6011510504c08000400c8900d050700222034011104803a10040c1c03a1905801e510740c0c0c003015280e03a0071142c0d148007081002c800c6501140040d035114040d801549042e01c0003841e1070b000014111035080e40603020710a12003000c5070444c82410010000f0410b0790074140111015080042c900e071400390045242109 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 9750987 1250 9749737 9749741
    0x6051b0a020d17040f02090a1104030c050127050d030203040909030503010501081321050705010507030605041401080717030f2701020109020307060305060d15050601080708040c091d01 81
    0x400c140c01e400a20011045a4005008182000c2d20304900b8041000313000014410b600c125a0654040300c240d040398580010440c002c092980c1a03d9241c880090300000704040d803040d0000700d560988640414280d540e54400e81e030300c561020041051680001030181d8070303081c40c003030b0451070080c8103c5e03081c65121000760086a0140300c1c140c02191010004004940e4071100841c0d1000d120075000000070301c259940501e200d003000001070f04d981031a141c000054452025681680e81040090042d0309041d10050000c0901c3d000b124051424040ba00c03900b1501c2041d0035040310300500080406c41e1a044080b40a941010740000007400b0030070440082d0052540074000d1070000c1c9407182c4070791020040c410500141d14000c541035905100100c0c015030b80100d4030408503003070381c01c005c5041d956074130009464102c1c07804000e01241025040710780401c040d500c0a03104e12400e88550340603441d404401e542c0002c0c104c500608010755030805210327005007900010080d1840912000e40c0100902880b42 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 9752237 1250 9750987 9750997
    0x709090506040b01050102030712120b060d09050105061c020f0609030d0201061e140d03020f07030c140612010311010302070f030c06060b03060a120c0503150109050105090c0706051b 80
    0x24181c0c4004180010b0100021445006200900055143c920aa5a20450140c0c000100001e0014559005194141c44d0700109030400c0d0041c945030f0350b0551607082c40e00504880f0815a565031030b03c4001071030b60400200d00e02e0781d9500d00401070185442c0303600f04020b144190030490707040322041c490a00d09450400034118824200d4001061050420000a54400090050281c030305100242003154203400b42e101d4003098400d640d0910a4803080c1426481e0084014000b01d40b44199540001800000c074143c01c1500e00002062100f820b005007000b000e40540301d040240780103000300400c001040329802824001043c1009400c010140d02c0c2c1850311011403505a0100ea540c09580d000c02815205e2203000e0402800c16505500740b80c8042030014a56000c0c04c1c51441e069444402401502e51112005240090444aa954400e034013074019060078450290b10a041c100003041c14504a503040c0d21980c003803104070b0f05005160f00d03160007902e0090b02020b0008940d9110542d00c440ca040280 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 9753487 1250 9752237 9752243
    0x1812100e0f0606030c0d0f0c030210020102040f0f060503010509100504020f0a02010f05010602071401030f0f02071401020403030c080304081605030a02070603060305070e09120a1805010c0b04080a02070909 90
    0x401c401454050007801c224004145501c680c00c4141501d10950303484590308030300c5400c40c04490301d03c01c261400156507045074002035401b800b0342400001c0503905400800644101c0c201c41022145e8409048404104038019480424400c1c001481141808103540d54031a1140d00031881e100c0d82d51000c24100c1c3d000140030507000200041c80c0e80c181d90240990064111217000c00c100961614100940320b1002d40600b4080f00031107524064660b00c642c00c200c802c0249008200100c811141d5950002d510020701210b083d48101c003010072512045c400d0310116901900c0700c01d8036004503503500003107510041c01120004400d1211032440e1f00318680d80d0b90b0311840740008503074a50070365001070700d4030304154444020182002c3c1c090002500c0801e00c40211106074800c070680b80ca030f03e0030300750400601406294070404041004d8151643c40750494045040080005a400751500c00456030b84880140107170802d1041c5010400117081600200441c06d19881030320241900c682d407900680d20100d60903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 9754737 1250 9753487 9753493
    0x19030e0405061e090601030b0a0e04051507021902010c050102070308040c0b180402090a15050405041b020c0d020f0307060504150201050403140309010b090109090b06061812100e 78
    0x606280c841d9507089503080310751000c162038140010390700d0102c0008050060081308003064880c0d0181e000540700304001041c0340701c01030300c8122140255008442c00c1d24940701d03ca112001250034000380b10300580c120b074007401c1b41580243c04501c26640d00c06040341000700403c20074022034000c6c40a0080d20740300c3e5035209103900307080c1850351155069800a0482030420051104107011541d250100340744160b0b40540c40d1078800b030005903002040d50101d80800400e40440c1080c641c08401003056550884040013842908050604028902d1900c0341c007591220407170030901d01d011412091b81506c0100340030480c1c400340020a040c544294015004500045024007136a04401610010302110788000c220a24040c0c0f402808500e2000000c516402c00001180022000b9007110029900282030780b6555603451100d0720003000f0340034050754512191001300703c1520b003020417a80711201e00e055a10341c00001401b003111411219019100307030700ca0903281c0b000c03140c454015049664500009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 9755987 1250 9754737 9754757
    0xc08160b0901052d100306050115031b0c080903011d030703090b0307020606130b0301110304060c0e0a0504021b06040f02010906090b031302060c0a1b0509060603010b0c1903 76
    0x5110300f510340160081a00c4981101d000b244c0d421048480c0300028000714070300c1610386854011400c800096013010341200c2c140702c00425002042c00414600048076503040010008205041032090000603000000941c02d441c0d0102151a03000641800400240002040070300d0351701d6650598102d008000d0030f41c1011401006041e048004d00c00209422641c2610b90710b02020002d45074a0014410b81c420240140e00071403501c0c4030340c0b114044150103002041f0320151701200c040303d0303041140c0403100b4508104031280d10a1080340746548404019240049450922042101a401c400b2202d0704100d078801c4c0710400450304009460080340207100000500d801c80c000109800700c00d8020074140031018004122280010b402c41e0391104da80300d50003c0440c224030005482d807140c290b100c051882050452030030b00452084810744501c1c84203140e0400c0740c0d90005e1103e010300c200d650035401441400100143d0403803200500c4114890003e4407046d54415062000100c50305400745d00040034a19 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 9757237 1250 9755987 9756001
    0x3100501091b090803031f0305010504060603020a14010903021201020c070e040c0605040b0f07030e0612061002070806060607140706030212060a0b190302091201050901060501030e06070c08160b 85
    0x9041031442440f8030744409124140f004e070554030312010f450740000c445030909842c0f117446503581600265621000900a07800c050403ca400f800c00c50000387d01c10007000400080560001581301c003140410f8442400c030615580802850f41044091070b07070155004c01506200d11402d003d0764001d130002000e045c4035402c0508100624030556000342046c007800704028040007100d03000f601c1d0150b0501849542d11700b05460304a48240c0c0303015100d5081031001c2a8401c2c150090011984140c00940c0c04100600c1184404c07680d82c05544190600c9402ca00041a02400d0003801000c030319000d009036054895003c199649002010303880000001d5001c206440b40c0c0314015100c540141e0115501d03d4683e0810745004c2440c0f0480580c4043d801201001c210114000e40548140840041401414003201100140030300400c444080240d4031f010804901580a480703040d078858041c100900b92960342c0c10307050f10408001042504e608000303200107546115803010003903c4600c1b50304500c40c036003800e030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 9758487 1250 9757237 9757271
    0x4060b0a120c02030307080c0a0210062601060609050105070203010e1203160e0901090519020307020f150103030801030f03020703050a0807030f0207032d0f0302030304030206130804140310050109 86
    0x1400b9011500300b00140919150f026220b5030b000440201016030f20810100107924200d03441140c14844d50030440000f44038550840101c00000803030003140d4141c6a40000d06080319030a001c1c940103e0f440010600c00c030b51040340504003640c07004d000021a00200b84803e4500b6121008040c8402000800c015100706501440fa0008201d030034016507440c0c41100240811f0360500880d121356554000103102400342c0505c1290022132550115503034241103500035240c0040c0110300c24a48181c55840103984008140c07207040769090b0b070f50315a90b40d086a80710142180b07610000e86c11445415004030205d4018070038400c1507482208400c1d0385241c0e034a0080d0040341004400b10071341d001290f04001061440780b103803003004209a85240320342140c2d11042d018164000000d00314808079883c6204154002005502650180c0c08607815551950b0340b0692030313519800000e005000a0000300089200c0104580d000301e40213060ba1141c244a0796a10121407099002d01880f40d100c4501003100d85c048 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 9759737 1250 9758487 9758501
    0x70515070320010f090b0901060e0105030303070e01020703060f0501050f010503060d03051b03160b010e070504060305040602040e090a03080c0c03090909030708040303020106060906110d080604060b0a12 89
    0x41424610951005451500781096460401e2408000c0700c03001d0744294061300780c0c072803071a2040014a84600b81001c031124215601c059940c40e0420120340d0b81216180710b0b0498a0040045180d42c0d00c843c41291306640c4092014154890004d0100018065000345603140c8841c040c0020558902000c00c0b01203001403100760305100c000c00c14003050303883d015452410260142010750f036918004961181c1c83e041d5854079041d0340004560400c41d039072410303804440c6c540074074205c94003640c0798484203a40e003800740c07009008280c081004010b2a07029400c840d40c0b05014a10050919586010a60344454100d40300341c407a4021502200c00c03d6000301401c0d4014440117100c904046501440700d5803440b520301d156215626180c0000c402c43c0042041b2549070703038449031080c0c98503520b160107406844940a040d003c0f40c4040404624544103084582c012009800288211901040e00780c500950140405800a48500d40800c0220050300200a10a41c580c1e074103c82e0f00544003032504494203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 9760987 1250 9759737 9759769
    0x9060f0501030201020d080624030f0604060f06030c1704050c090702010513060f0605030f060103050705010804020d03030e010f060609050901091112150306040b040b0603070605040b090402120103050705 89
    0x5040c00500150741d00054410001020341003032402926007100164031b20881c8000b5000039a00e00000b0955400d403000034600440341d50990746642d032280d800700b0090718828001d041c1003400100f000c00c40644a41c100400d0820303a428509182c0d21038000e07000310710104441c01d0710780d58008080c0c040c00b420104449940241715200820031802c02081840e42d0390720031200903103241c0d00d445240c48a180281e10200041200a0403141400c180f0402e40c0e84031030342480241d03524007503544002402c1d402809800e22681d4002c02d00c1c1e4040c032142c1e44c150000c019442c10b0350380d15940c4400340b11207000075114980c090851600d82ea800035161404001000105801207004076083c403103010300b03403086d540c2520f00034281443c2003242603a950f92040c080d2180003071655810303c07658041c40705104200b01301c4d5000d64080c1c40000f030596110001c0c965290038070310a81c1c0c0000e00400082005003075100150a41020003032001d413804043c81d240b952412020381060314550000c40041086141c444095299002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 9762237 1250 9760987 9760991
    0x141c0f020a0b281e021203040b010302030607050702101d03071e0605090612040203030d020708030106090503032106010203070606030602030601030b0a0f0302040902010905040207060905060604091e081c09060f 92
    0x50b07007540051a004078464130f11210b4011300c000f1030126000384400d40e01354903c00c00c1c1c10384174605410442d0f1020402e00c41039000b40104c0c0041a2403d104404031100c540c0c000e040c0c002400724400085078801ca1082c0c07140e10241e102c51500e80a03a401b441020003c0030808030a100d500440e08684809280d5503000c0c0042c0310080028268a440b248c1c1500c0914422600c02e155a070b995001190446c441c12107280070b031510000710034040012030005035040c1d0341141c1d600003800e0b4664080c1035482c03052a5080d00c5140d158030180040c40b00004580e03510080600c10740b42002c000c0d80e07519098418940080382c00e00c0d00442080b419503811310074002c030303801c0841d40c04148520741440b60700440014003000e4003a42e10f84404c4429640502e6445004140103081150344038000d0500c1c07802130040d003404840b203020f03c01c0810b22074030349401200b41c1c0d95003020b003569044506008409c01502007800845106806002d100800300c0c40030b10784440206000000b182290a91074010104d0362000b40e0508014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 9763487 1250 9762237 9762307
    0x7020a03030e0a0c0b1b030309010c0905061c05090c10080a0b0108040201081501141801080a02090303091c020a0e0108060603031206040924020a0306141c0f020a0b 72
    0xc404000550454076100e10260752031050800e80b0820011b5000004c046201c000103100e41540150310604000c5966a01d81c02c030180c48408110301403103410302e681c3e40c030b0000d554003071081102e6502503904441b145040b01d2441c6802c40100f44040085403e0a001c0354000080100036429401510200c002c00d1070091020701d440d030b001030452480545017079140301001c0401009640110000c1b103000c541d80301d2050f11040321007181c041e565980284240050310305000704a141d00035000703442c0c04400c020003039401c080b02d404c103010b245003500e031070610025400c2e95000c025884e84807820019204204248400b581000c02080c035200010342402d003c1d074001c00412580c0c000d90000640c002000700c42c0410406805e05000f502c2c4d1382d4210072007000710800f28100141300d034141d0050200780002d440900c0416640d881e03805074036016166607500100d81e900d01d907000c402e07203c070741c54643d6102c1c070280700010301c2540116980e280d06400880c00d880340064001c864260001c090040000300807c504111 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 9764737 1250 9763487 9763493
    0x7180b0a03030516030c0b0a0207060c020705030d12060f08070326070b0601050d05010b1308070b090616050601030309090b04020903070302130204081c0f1106060603130b07020a03030e0a 82
    0x41c1c032400a8116060b0010091501014800e81a1200d0036420083c01f8040d800c10210100007544550000c42e0303440c0c0743c503000384800350021507010100e810090260680201400b001c1d240045d81d45030060a0f180e40f80e002240c052200031060303000d080141300500340c0c1c40c114908043c1c00070b20040c03000002d00140711102100b010740c608640740f040d44a56010b00e02d440d0000181c616028030912580c0c05401c00b0300120b440d82064001d081c1d0081044010351080d565031031003c3c3c44220b02d0042c104008030800c251040c50070540002d0410380c1502c2040c840c00c0220781c40b2242800030030f810840c002620396204001401550050080e083c10850b021441c04000c000000d0391503a1900c80240103c030b110540d000079002c10750699008280d00400e0321820088404517018030003c11030640040307074070110041c403014030076440c0c0c680f40041d80000300311503120142008407a42004001521840c0e14286103c0002d010900c0300c3c0c01152190003c1c00c0380111490090281c0e802c0000021140d07101404501c08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 9765987 1250 9764737 9764747
    0x2040e0702150c09040f0915050709081002032206050405070501030e1b0616030309050d0306030305040b07110616030801080303150f130504030203040303080a0203060109090b010c0507180b0a0303 86
    0x120364900d084507a20064130021401030628074880300a410b2424446509000c18011022220521038130100301130368600d0001e456480e150b0107204103940c840312815103a94501c2d4000d68000303e12468007118134048088d12000b42d9030342c0c0000c5459586840503c03040003010403441c000b07000242402c2c401c0185204540b580d51001051054512000034aa02071f151111400c45000010b28055001e01c403400e070401501900b41c10303104031144c0c45082003801016110f40725840a907903065590900d054030b040f107100155003010109488580292030500070340e544074030007401c6503000865100031340482c81c1400740c62075034164008140380d0010420011191610081c00c4c00d18442216000c1c60782c000d05001c07445445400103c00c20301481c10060006250b0000041c0089a1003641d9002d25030b610348507240d043e80410b898083c0032030140a02030010003050b42110801003c1854080c00e11040c985400d0301e0b110303050f4054410858082c4408164031002e01400781c241c0400d4030b00e405024515900144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 9767237 1250 9765987 9765991
    0x30417010b010c08160b1e0f09030306090c0f03070e03010c030c020309060706090206040e06100f0e12030c060f061e03100213030b07022404020904120905030a0602040e070215 77
    0xb4007200281154103031180c404a002c040340c001b443c0e0811840c040140d44052481c0030a152005220b010000317640850006c074503441040204080d600f5904c1d20018081c010b50007502502d042c840900c400801508075a001e10300c640c5107070b039403a0070b491907440a04d030031a840b400d07e507400c0500f030606051215030008129950892f060300c801d80d6815090600c3c0000388030f8407500031761214000500069559001140d0350250404881540d4101548203041d0754642200b960000495a17480c0e4012140c9030202134600301c181c1c081c01781d074a030010310390050303007880300403249a6051072851051101e0350070306001f0a01286001c007610a0315a4000001031f548084203101d105102d500055540389160542c0381c442c0045512804401c01418075080c060345805011200c0c806081005580540c2121744800ca1401140c02801d02c61043d190748d21170001c0c1d0b0348000019020300c0030307400c0001200d0f00c04000e00007050b4000c0f140140c0301c40c10702e402600f01c028068414402c40d071020380d5504090f030038070442c0c030f0f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 9768487 1250 9767237 9767243
    0x3060a0b0904060306060e0a0507090e0406090f1e050c03070e010506030603070e010605040e06040603020607061113030b0f0901060b03070c020d0605070309060507050f0a080603010905030408030417010b010c 91
    0x380d114660003002502800329600001c140da03052203000030f914800b42c108030380980c0e110f00040c0140d40c0c0c3c3c0301041703491808070b1040d019442010408580810000d5100c0b40c0201e02a01001c80250071540300d5440c0044103d0540603184443c2d0212014042c0a22460042c840200d001d0a0f00c80e01d0203d40655101c418003e061084000201095550f941040100000c00c060440c2540d0703903948000161107900075102c0d05020000c908000f44582c501071090741d0030340c0d50040c11242006c0194070b40708010410a9140c6034444820098000c064010b0f080d043c1c01948a000520b071780d0301e05150340c034410100180990845a040070018010089420140c0f50700820518081a4511041c00041c001c0040000c018200d2071078881445192541600060041030040100744180e4607020380803201440b68441d46403454106000d0410403e03c10484070390080801400420081d8240d1907990842e405503104490b20381c0005410005001030510496884011000030403511500e080081c00c0c0b410051401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 9769737 1250 9768487 9768509
    0x30c0a081003170307030506060405060406030203060d0212010b030f01200703020111132102010905040e0313060e01020f011b0809011503050309010e0d020a050d05120a0914030303060a 81
    0x11203071040407894000864209607440348076025840460190344c0190385074000a402c2000007201400c240302141c081300c00103020b07585846c0c90544100c00a40001e400e40360700c030701011381440c003690300ca194a890281d003000001070094034201c20149411601c00c02d4070f8299040144145000d8024024600750380144c0b4906951b407081450100d005214a0708424000080881c00021900080c4680030540740b2429454110495500c1c0c000d24400c1c01807402400100f03400d6051106080580000c0c0d19078500000712420055001c60a08540d41150020b40c0069038000d078400c3c4640c0c0c10081484c14401c1c10300200482d81c4c0503c882d02c090f01e5070705052000c0c009103001192020b40258813401c548080e0400804001d40c50f45062070316948804a02400500401d000c0b00340c0749880b400d02401c03140e004223441026882c1c841448216a105031080d10540102c4001c5007203040660024008096560b0301c8850950501b400d00c2203032885007070640c0c0254414000c0180a466141c0308105981c110044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 9770987 1250 9769737 9769741
    0x120b010308160602040e0105090c030f01050f030703060207060218060705100902060c0115090e011422020910030501050109050402010815030c030f0709050109020c070b09060702092505030c0a08 85
    0x200e1218100ca00800526213480002c0c00145000c41c07102050595100715403500d0180c5685810304424001501c0e441910069280100f19500d001c5507100c10a1030701400703548140d65a81c60740000c07a0071000c0c0035640715800242600b424000181c40d0520000300303c542905105081d1038031961101c0021540c519a81c1e00d114210940d554030f02540d800c80c0320380e00240070340101c2c1080c1c1d00b9208207074401e100041d0f0508030b130080c40403c1801030030400c641c900034000e02661054826001410710005d011003e0704c010000401503211004103612598560300c0f0180788078618600a400c5a00c140c0c050044e45140c4000e000050780c2c80100b0542001c0e1031840c01030407003035590000c2e041241d102b101c598035102d41600e07101105d00101c2d416048541e20801000641c1e41d8101c15400da2051074000f40702c0d81c03c10a010b110303c02040f806004040c502408503800d11441d0741c00b2420402007960405011511804a00e03900307042d180040c14122514600f1030b06506100140c28818001d4000520621204e040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 9772237 1250 9770987 9771007
    0xd030c030b040501060c030806040c0f050906040b0a0503041707120806030715020a050105060306010605030f0901061806031e02010e0609040905011a010207140603070503220303060807120b010308 86
    0x40703210308081c000c10411180d40d482002425650522034114085516040000d286207403d119400750440d544e21800042040e030035040300d140d40050742c00c0c0e034400d100b0b1001013034080740c1c50081d01c103450054490035928103260414200044071101c110311120000c2111b6400580000c4200306845032030b00340a4100d0300d980000900740a041d8005120300e00d94050b10307803144d50340001c0c00346480c0c1c0203200800180d1100000d00d5102c0c1d07024014400841c0c0108049840445491004c0e1b81c424421000001d010391240b01c50b018107000c120b8100140d41c3c5603101841030005040311145c0e030040080c100380081e6116400a40700501100389248a20070100d13075841d071038032203800c141c070856401002040750014409038141d640d40c030038a0031801441507003404038035012024540c0c610f030f200c002c01d95030550780c0e80f4038200c5880c2e000400340017810210a4004020802a02d40f0340c081c140701e6100400d00505100009207001680c2d4003c0382c855082025400101700440d0b0907905490700890312a944007001c0c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 9773487 1250 9772237 9772241
    0x90e010209040c030507030f060b0909040201050c0615010f0305060904170c01180b010522050601211a03030a05040312030902130501080d0e0f01110f010e101503050d030c03 76
    0x201d5115000341c1001d011503211070703160340301038401c02880d201049120b0361440201c0c01c030b030140d010b148070010040102c0c840328903241450a602c10300c1454443d28001104c1d0036503003014000d680d040c06199a60210720082c1da0042c0c14016000045c0c40c00304414904000003811082010340040c110700059100c81e50805034150480d20440c101c00001d00880c0f11030b400c003000c811050401901c503c400320340081800d160441d41030f19000744102e40c09160340f21040c06100144009000070f410301c4121106440da52581c0d6140c0141c210569000040002c6501c042030507020014844601c242c00400407102174580020a980980c3c0d006101000c408141c8202a00207212860b8043d501c10362700d4070900e4030840142c20450503100d01c04165143c01003513220a03580d002000c01d1040e404012000c1910007548955600c0007040b401c00b0480d240108400e41c40c80c2118030010003444560002c0c1c100071520b982e18040c041148101c00c0412100500e161100d5031510184d440c0b1104040e292182c0d241400d1003a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 9774737 1250 9773487 9773497
    0x20c010804020916110313150f0801090506030102070b010303030b01020105150604060503150604030f15050105010c0f170a030204050f0603040203030f031b040e060102061b09010507080d050405060103140f0304090e0102 96
    0x2200882c3c0d500c0140c140f040b001c1e11f080b032081d501d80300440c080c201800c40c8a40711261843d12243c449140326403e000e03c1c01c018120040c51945c05640c248004008200906d03841c500031402501c000515a822130002420340d4801801c41c0d0400d541d03e5103030009525014100c03412110140b608503240c0d1140c01c1081c1c03a4582045030a07510802c041030110030302c14a07514818803988a6a0307282007451401d1002416604244115804141d1a0030841c1c04202c0402e01c1415052099081c1c0d10803504440003060950407041e01440080c0e800720b0284401e041213445085d1541c400c441e494150707d42036002075601c1c801c01140d09030081c808070200789084850400b41d2800e4440602c003c2d01c2e9600c41d129458800c01c100c41d0f0500600c40c141c0490380140e080f600c007284007408402400c2c030f4515108019190b5601600048031000c004008500301100700741b0076203029900c50400b40c5640e502d54145500743d05280248400b0b10340109080c0072491200204a1781180c0501c000460020355200c0c0b814024020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 9775987 1250 9774737 9774767
    0xe031605150c1605031b010f05160b04060e0c0d120e030a050703050102031012030e010e0a1d04031e020606010c0c03060905010509011a010203030f0a0213060206010303020c010804020916 82
    0x50b00003c920310280c0b82540e4030a4940640440c0c050050201314442020600d030029408544030f19145400d00d84503100071f02e50407a0401c24045540b4443d42c3c0c2c035803460701c200d80030340781140d0710a410842c4603001e00035160905000c4405011590994032400c1c4105281c0c24094203000d85403400d0141ca480501582100c5070b04102501c40c9282e072030808038042d5001321070221058000003004540355015003946070b00745405607200020181854019030b080008005401c1c0c0c031550302c0c080040c003143d076842d1100c0b002c481c5071800c51441c03c040c41d000c5c001d4030000d000d03560b1014443c04004011a8002241a4403000920300264200700e6414003e48a4400e500301411881c14a48200144103054011138081c614580c000c02c03401c022540190040481c05940741d005030410130103d11140308441100350045920f40d03005140c13180803500d40300ca5100320362003d0056000b0000400c00d150301840b400c60f0b01c80c001e0805d03a41d50f19240e070018114800080240c0740d07201c1e840310100c1420388a081c80c0051124 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 9777237 1250 9775987 9775993
    0x3080f150a080102090a050103180f05010b03030a02010207060507030203010513051e04030c02091012150608030705070e010e1909060b03030a03060e090a05060c0a0507080f040302010e031605150c 86
    0x180b20711815000c0e45c441266980940f40c150000140c65100b4420b0360590b501004038840b00610b07542c2c5000703441502100641e61036494503407611040d0340c02d10040040041540005a552805181140546200802c000e05252043c001000140c682c100001c03405039018800040c0ea6803808a03a1401d60761100042030001071072801c2004154002141401d454005ca5440000f95a07140c2d001d101c04016020700d4200814001c07480000512440991240646552000c0786942d142c1c081c0d1861900402c130269800d90104a040140500314007495000d00f03c04100112039141404407841d03000e9000941203206075a8a29600500400380c0c0083d1180d04000d080d40c1d618014603100a0282140340030b2203020764882000700c0e00b8104009040d014203a44171000d01444e58a91600311178680080c0c0c80c8005200e0100840c9001440306802040c10b2080d41048645480c19070000400b1b0284d0008841c1c081d0307210701c0440810498008406080700c1c82202d02c900600e021403108141c0303024007150a21984 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 9778487 1250 9777237 9777239
    0x61a09091f170a1209030b0f0408190905060c030301030b0a05010501020c1002010f050406020901020106090b030c0d021203030108011b020109020a15120504080306100504030b070f0309051903020708010903080f150a 94
    0x3076205e03500c0c1d811240968006171203922038400c0803009510503030340140f03458000c00841e1000e1103003059001070066a0f0030300b060104d5984010074015072200e4809030039900004010700030030140a44d643d42090210b0b10400c06517042200103940c40b260600d11030b102e00c0902c102142c000341301b5008600f801880080070322890602c0d28100300650800841ca074099400c0800200b41c50040b4480d451245070002c00520b4040c01e09400c0c050080030b12074040c0c2c2c04c00340d000035800d0360500800045000b0400e25000180d81580c5202c44000d14459050610459041c07014120140c0d403507090020030348104800031082444d40480958540940e00400000741c0c1c01d280c00c02041c810000c0c061440764206640d10a40e444182204986900c550300000f0801c030101c0f000700f059540f01e0060f40d0001c41d4075080009601800f605c0c0c691500d50100001c48243c00d152080d2010194140b15540080c0313001c40003440920110781d000b8180580090505011401200010340c040940c05903200c03018001900900c001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 9779737 1250 9778487 9778523
    0x21302091314150d0210020705030303070c0b130f1103160305010504110402030610030b130e060601090f060e01030902030a0f080301170c011b0501061a09091f170a 72
    0x50302c041868001008880307000244042c9242e00c504503201c800805800344c03030300d1907802c001c079010034000080210312820001241c43c1d242080258020300403511a0003240300c0500c0d000d0401c1000410403003a668403a0301d820001080c0c1d8040c41c0c54039034001c00d041d41e010031140102c4c1c50041c0d42c00c8440e100e0600c8040010a002d01035001301c4c020f900800202d0f00140400051009074407080d135009400030306540c411200c10f8070a5000b4034409400400704e0040415410800003620140c2000348c3c150f8100380140021903030040c01c4803004050b580c0b010400c00385442805444e010701071805606154a0b0802310045540a012118900d0340c8111405032440b254103007100f07550401d007c0d94840941401c408000600006100062000144e5410b58028070000301070502d505a000104d405648400d000b040f0701440e0a030050103100101e1046444030459410004113030700160104034031340f1388042c0e403030030704403142d41080c0c00e6a0441e0702171b1605c0e4504007809403404e00700d42009018441701401031200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 9780987 1250 9779737 9779741
    0x2090709080114130308070302090405010b030a0f05251701060201020c070801020903030711040e0d02030a02010b012604030507080a050406030f0510030b090109050303010e040204060e0c070213020913 88
    0xd07603005100030403a46503024005a9007940a03140446048414070411000910644007a5441901da14015040c040c02e40d003c02c054a400b0f81080e140404080104010042c00348113003d5400c1c2d4a0300180038038102550035001c0d03003002608100350202005041000d080c0980e10a02d4001c103070240244c459079490340001c0c002c0d0080940c240c958084d4440000d0303004014001d49e080c8c0f1130000e02940c90001603642c7c0f5120366100110b019017107a244c0c13002c420001001e10525445880c1a0091640d68105060003401c4810346040c8905100020401c0c45070020940500c10204c044800c241c541030f10740e8203041d50a4000c00c3c00007040004002075401c6040d41c05005841281e4884c0c50500024644601180a1f50021210f017100000c1c3c503801013000c5146c040450b81c01c01212400050068000d0b114503080d40c1c8241c00040846010740c0a220440c2407a100d004004c2800825840321401c100c484d501c3c0c03a200e0700d04041e1003401c0307140c945100c4541c0b982c1129140c030002840d221031070303c082d02c481c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 9782237 1250 9780987 9780989
    0xe03090904110f12120a111504020907030e0a110f030303040507031e03020312040201120603060b0901140a06080702010605041e0609060f03080f04050604030b04050d02070605090d050a02090709 85
    0x20003440d043c20000094244035012070703904c006850141c84500711042000c01079401c004550010051032003200b01542c0410700044401c3e44200804c0361280c5014018024509006001c0d03034101441d216108800060100f40c0e03800ea5a8048046c140c20408a00007410712103003101166031501000040c0300401500141d280e0803240b103580c944400301d8689910346100e040d035800240258204004c503000d4008500c1440380d01174814144030095901041c2844205c40b915041156900d07983d01019005151811080d4010804c1c0d012101c0c3ca06035840c0840e060001d1846190203008180021a11290003034000b9005005d01400802100792000c40c0415400c030f401c2a43c0c04220710b4800c0106a500c1c1701d0084906850680072044165171569465280a0b4004054104060f00600010641e5601e01c0018402580a0503c505840c2081d0074581e0400880904900556000610411003290000244c0b0308826007103803030800d40c084505103a81032260940c0c000390f0044141c810803a507540c1001043c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 9783487 1250 9782237 9782239
    0xe0106090e1302090702070906090e0f030c0c0603040c12030306030209070807020c0d030201090813031406040f0209090c03070b0c0f01051003020405070504080115090c02010b130e0309090411 84
    0x66503030741e54030210010400c00340c0382400100c2c0c6044070000907003014281660030000d01c1c4102d504a03642d81640701c0440d6442e8002401103030300c1e148001d210140c2000078110302808040958034240078004401c1d6140078205041c1e02907080440018244090840854007c0c03801c40720311102c40e0480e1030300030000c0071140402c13489520580082507105114140191050609400074140c2021110070005400b1070b002c0c08604543d01d62001c2c40c000341c0004090001b04031110500920f09040d450315010000030504180302e140c9c40b00003080089400220781c844429016180350100c0d484400c0442d0610240d900581c0d018071039038000180d0721500d42c005105403881e000c1940c4c0702021100c08542600c906275240c220403610600140b025181903441581c12501a050451415582d610740e00d0943e0302e86030700c2100ba1030021504000d0001d0b45d004190809000307200801541400ca0001442e002d40790100c000e059541d0502e12540b40301c10021a050401c00034116082450180b0b4011700001c6105011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 9784737 1250 9783487 9783497
    0x140607060f020901030f02180103020c1204080703020307050d0809010c02010521040b060d08030402121e06040b0106080108030315010905060f0403110102011e050709030803070c050d05040501170615040e0106 91
    0xd2100001882234544c141c0a40b08101e45002c0c0c04030046020350400c0c001c0c0411070042c20b4207806001c4107600240018042c1e003020b441070502d5801007609150090380700d540207004004000340051440421201c4e1914242043e00b051800c41c00100c41901a03403208240440641c25a007078907080c0c1281c2e07a0711aa21542d01d015440d82d4903824020403032501c070001040c3d258140041401031805c4070011401d0b551090071243c11048100c15032141071410945641d4035001401403000b0300a22141d211f0143c002c03401c01c0542549040305469aa20000b040090000719860035400107030320944000000b0500102580d40311505032111007527950180c40f00f240c003c2d22440ca00b1a5650041c0520300034110700c0e540711100000c820518a020f003000400010800200301c42c0440080d40190245000d241345564100c15101d441c41c000c2c1c82e15040b0410001800000e210402031030ba07100d480e0111040707040c1d6071904030307494030030115245c1d0700c40c0541c0c24910880400c021402540c00041103040b142c581e511 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 9785987 1250 9784737 9784751
    0xe03040f08011a2b08120106050304030f0c110603060307030b0a0b01120903020304060507110d060b0f010c02090601050d0605030a0302010213060302040b090609130f02210907140607060f02090103 86
    0x1000244c0200350305500c15a0819842c504510f265215010380c198010090f8a180000c0d0810700c56400706e098100e00c02140d00030080c01b0a1541c4040300070007030300850425810344c44284d115001217140d2550b40c01d1141c0c8001002600984051000b00002c540c081024002d030700b00301d001240a0b0880700c0316140003c0361a1001c0e00060664000c0c03401c0300780c05d03401862809042a2044800c0d5201d2141074071800c024000d0301c1580e8503400c0c00c0131aa1802500d00051400d04401042080314444000604002e04c1e1000e190169440d4500c094104000b400c0c05980d45440300303221005130030740b40e100e5a0700d4000e005507001499019002081c021309143c0070801c034180c4800d4242c0883c0928002c00142180505c050019401c008000700300c080380c014004a20450750441040039a20f4280400645c1900031800500d030680d500f03d004044038080c1804d11803481d219400741d907545502d21a194651800c4401212161540c00071146e80c140c0250061210309035000100e0065030080100078002482e00c0700c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 9787237 1250 9785987 9785989
    0x103030221041a03090a080c010c090509090607050d09060908070b0106140d0b0105040b1b0105061e0402070611040b13050d021c020a0b040311090a02030903030a0e03040f08011a 78
    0x70440b8107440780c0c1450070321500001c0c10711620b144c00041c0b040d0540d104910801c004103100f180035104540c41d100c0041020a1080303001440c3d14110740c4a00d0240b405041030001208001c112250700c80986c0c90441c1c3c403a02c51007400b0018211045014091034a03091803d01840b8a101c008c1c0304450140348101c0c1c4690343e81404550843d82c0d03040c560101c10040c04071414080ea40e0300301c6a400d200500d002030500b5107800b408000e90b48409014401ca16403240c4c40407840306e082c060341c2da100f42e0807110710045081180302c6070b1814808540c030b140b040d5400118842009007071f9002c0041400f900541644542e20746007490019801b0048003040030304500c40001d400d1500000c0b1400c0240d000d06103c0880f140000200c408140c4483d0407039000106003000300c3ca40004502a0000f1030260380c04c0340c03a028111003400480c0d0350190960204500400800036030030341c000f044a4004003000c000003020340501030410700318001c81e086881e44d038100d404005412501500f1180c01080200e2030006400d2031a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 9788487 1250 9787237 9787303
    0x30601080a0807030c080406020307021002071a0c0109060905030c06060307060e10030b0909010f0b0402030105061905040503060709150207051f030207050f03030403090b070b01090203040f0b01030302 88
    0x11003800ea080d404030a040d00081d0311070b40903020f41480b90600001c00705a56488906a400503003150005a1021503500c00707510f011200e451110440340090100c80c1d05020001c400d4008450b50540390300c00000d22038035140b00951122032010707000201007001911501e065038890f8040d14250050b84240c1d800310341145000316aa60440300c658407504140c05038032080c040c95401c406022018107036200c90018072501d481d0a0345115009050001a562141c111031800302c961080200d409144148014021521218105c90074217038090700e10400078107880030842c0e107481190000d46e018001d5000b03000d0b006401900400a60b40b421209212210000c00b049039120014403d01c5d910a100200c0c3c18801c009210000e80c01031a01d00c3c015141140c80d4480c0c2e071130311041c85c0c9491040ea200000308018158000c1980025002a40a8914003d16500c524400e00e0040c0104542c0f04d81c0000400d00301f042100325a940568440b100841c20360396420302030b4840c800c0904580c0c60704942079070300c1c2d00e0300c1c401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 9789737 1250 9788487 9788489
    0x30801150507170d060b09010f020f1002070213060306050402040501080c010c020405071b050a12020613061e050a0b03010605010509010203041a07021207150c0809011d060a080402030606030601 85
    0x7555002d04150382502e6942103800700e4070058048900c1040303091480381d071500a01c4003a2003142c00071a036540e201000106905400c4d1001021504204255613030642c002c03413040344030070402c14090389400c5240001090b120100c0342820140c4c0c82d0101c00000c2000503080300c0d2040340215801c0041e40e90725540320380c4131004418100d0015008400101c01482d09900c45504100c9074a000e070406425444051a10020880b041e44e644d03001401520400c0310410a0500c2c4100ba48003519440c10945058480100d00d40802824243c40300c1c1080282c40252044411050205100b440542891481c0500920003030551502950a1100c003050b2035010380e08490640750107900071072800b8a040b0080011050b9900e14038003401c010030486008da6a0b50b4a00142480c040001c1d1100b40c0c5048030388406000083c20544c01e120fa03e06148020590341003d450301e0300f4003801c10031201e074460b0340c0040e1009081c100e01640f180e0040703641c940d2a980085128880c0c1e200b0740c11a01d080d224401019a60902 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 9790987 1250 9789737 9789779
    0x20a050d08030601110106091d060601020c090a020703051303030e030105150a1a04030501090308090105010501080103030f031a03070f05010305010b09030a0201120b03010203040f05060a0903051905040909050a030801 95
    0x108201003143d951044608180d04010b2500000d0802e0300ca00c0c1040c01d48600307240c40902079680b002030170394000c0280403054021000740014188070b01c0c8040071620300c0300020401880c556002c51000c09140c058800c50320110240a51044da440d22407070040c000c0901d81c04090700075031030540020000e42200d0f69000400c0f2004240120f400d241c051071310b5018081145220101005020020002e4001d01a280c140e9109456880701d600e011042c2078219003059000d541040903110042011940000c9440050295440c001c240302400741020f01400070005441901880354010010b00300005070b100000390380c4240d03400d2002d0303640c91a0881e40c0c1e004800c256540340e008a0a1a0b0042d8002d050061403400e10304030204481d40300900003400c9030070484094812100400307403613042000600441e6030122290000b007001256588004050303000d0169948200c0307454010f03c40b14203018005030b8004006030f280c01d0000c2c0b00149002601c4618841040313011984002c000315070710001913107a02000304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 9792237 1250 9790987 9791003
    0x5010b03010e0906150607060908030103030c050f070e190b03060906180109210212030103050604030f0206130201180305061e0112050d0c060b03010213081b0a140a0e0a0603020a050d 80
    0x1450f420846e0590089804071680ca5031000034030b00088034000614021402501e610f03041d0406401c1007814000480d0a110380c1d07401003030092040d40c030352850003a007200da50b1414000c20b5503050040c1000301400d80203a03506120300e404003d040940064017511910440b2201c43c52809200b00150070f80781259001800c820152800c840f52580750602c40c60507006910490b20b40304400c0101d544240d00c20b0300141c402c0d801c140200802e0603001901842616002d10080085280007580c900001d401a40700030704200036005500710b1f01e0008840d442c040c64012040c0c603a141010b10007040714580c4608145030300d040c001d00000f01d4240c4182540e90701600725002d440d10714444001190070501e000c00442d541582c651090440d41c80074805840000303400c80081c52141e0502104c0b5160100b0039420201044c03240b49c80c00e40640791003206000300da52440b80060742244d000c1c00928441c2c019044142040d004600300807403142d5a0300014112030080e0340485403180c0302d01c1403110040c20181c0c081c003424 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 9793487 1250 9792237 9792271
    0x10614060d02070501020415030902030106050603010608040b0709090c0507020906090402150c01020412060903021605100305180d020a0309050102010c090b030901090506100504060504020403170f0d05010b03010e0906 95
    0x76509030001c0401501c160001842c280e10350801d0b00d034107510103090350b00003584d0340703c448218102485914041c00040341c281782550300d4080001c01d0050001d1004107020159000318a14030700400b852409000c0c0b1260610200644c24001045a00050016481001c400021030110f0030070441d443c2c0240d8010b440001c400e180d1510382141c2da4010b1100070740540d401c00001951000000d00c28007101d115080200303000041e414001e19028074000e10405041f5031038070400c059529038072510b400c10700c1070501180981d9030f0414072911604019050400303009600484150681c08540c2001292082c1c40701a5a11b89070001282250764070b00d14000031a201e103005201881c590000346502c0303604a0001324441105a035103500780303141503a03c2c1214400c01a0b00340319500e0b260040324082e040c156411070800d403031030700c40c4400e0110f00d41e4100c50001c000a45030810200e0070b01103d0312640c8034202030140c0c1d40c1d00d414180082d403091040461108001e030100d01640000702d0800e004034489034030f5031400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 9794737 1250 9793487 9793507
    0x4060e060d05070515040602060603010b2112130303170603070905090f0a0c0501030b030c0303070201050702010909050c0403060b030604020312030711010501150f0503070f050706020c010f09030201061406 90
    0x3100d0040001e03202c6120301c210005459841010756484403000508540e102c1d841e01d01e010740351410103860700d4840d07410121030302015142e41d240701c65102441621a80f8005032091007604000d0003044900c0c15000c00590f200e00611343d078070705000702d0780300ba91f0344502e0310340049820341441c0b0113568039645900980b0040159038010b42000b0f4001118800343c90355040400955031500710180030494080803401c0040050b5a050f02c44d100c9565400d034081c0c03d41424400c00607480b8031885000a05000c004210701c4150b900c030f07041d03103009042491780802c101d080440c0c0c070311501e4006d0710046071040d050180035106410085100c3d030040f540540100080341f01003c482000d504020034460801000381018040b00b03409000f100c2c02010325803080000c1244800d0028142c0388405c9000051010410501c6811079000001205240031454013507110b8200f407402c00003a101c1c2859400c555030034240c441620b000300d40c5c000c42805100c0c0e0002c000444c4d841246000940c84a00401e5002e80d06104140c01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 9795987 1250 9794737 9794749
    0x219050a1d01051204030908120a090e1b160501050a0603050c090601050c030406081501050301030b0a020a0c06020414011701080c01030506030c0306041b14090a0b0310111804060e06 80
    0x441d100c141020b074184202090311100002049805400080d82d104080010300014030503141c1c4c91540010345494402001006080c08260340f042c91900c02200c0f0002c1c481603520a05412052040122640c0c2c6007600304032031080800351601550b141d480c2002143c2040800d00c20002200d81c030101030424100000c0c204048031030000c0089050040402c2500d4035054148010006010300e0307201c02d411801c0801d46151891103443c20300c1d040c00300420040c0080351080515130f501060404008d40d03103a201c4030301110341c0007100000420490012801068074003601c0c040080341e005c00c3e81c884054181820048501e24001c1c42001d003036030001c54192496500c03c0c0c02c501e034001d0300a27007101c4500d051000428648041180c050f200307404c3c0e1440c100d500341c0c00952030100420f102d103900240140721500180c1c0c024001fa01052903265110000d41e500e031002c1c05085064084000c1c100003a042032078450005a01c20401000c40b2002c400c820005840c103440f0318825107104036075a640a40d500018402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 9797237 1250 9795987 9796037
    0x1090905040203011401080102040305070803090a030f08090d0c05010216060f032c031c020a0f0503091e060106030b030102040b030105040509120f13060206070210050c0904020408010219050a 84
    0x1e0107548503100d034448032080c10b0017207000700006800181d80b9451410210309080c8280c224481d590400c1281e04a10b5450030828010f884e001a03074080180035034a403002051013052282c603000032032850744105110f14009501c003100d0081c3c090300c2d0640c21007071441074502068081c8102250592100d00e1b1100d1180d03000d2100158102c1c0910810a00d031240f601c0c1c0c07501041c407518020307070002034150380e0268405914581c41e05a135a0540c2481d004581c0501120800880c080411101100007075040a040001146401c054030000d80002403821500380c5500b800d000f0030f00403a051030007129090405208540444400d103042c10b0030345e401c180c104409048040c149021510031181030005655001009000c80c818155115940311050316039800c007010b65520000035074000504109913680c0219071050a43c25808000815613100b240000041c010021120f41061000c0b03404030311a04154010251040000c0c0d100265034502c0030103c2d0580b00b00d045500c000b529170010f80c0c1a01d144a5040c1d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 9798487 1250 9797237 9797239
    0x108060d03021209060409021b0c0a0f030b04150507080601020c06041809020a1e031115071101030608070602060405011406030706050a03181a0901110f0306030705030f03030703060503060105010909050402 90
    0x918140d41c549442c0240e0b04042c2e03201c0d40f80b9440c20382060b91a0b40400c001c03022b411007034442d1540035282900c4640200391500c005010110880c00140330041d01e0ba004108443e6204002c2082d41030443c4000c004040498040b8003522036604110140d24100301990115280c491a075003442003030340c2e0014090300c1540302c12a044100c1143c003107011610500441d0624000c3c10007034007030728610300705250704085840d8054051150886200c020107100d000b110046500312404400202100303004038001e00c50307a48540407170700078074102042442d40828a1401607005400070311841d40e00c05e0401c1c54240341510035581c1035206010401000380264060420f0f041c40f4140003605402c65080044400c00ca580102c682c02641004640c2810110308960f03002080c0030000c00031500e070185800c250340700b01c480360f0b440d40f400440060f110750340030090240038203800b130140e460204c4c5000d286907680d001038403c400401e082100100b040e040000702641200c805a4580403003078034106a480080c20054001c0e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 9799737 1250 9798487 9798499
    0x60f040b0d0f0506090118030804020105090a0504020c010c110601120b070201061503050402030d02010e070b1602030307030509030717060a0c0201020d050108030901020f0c0d080a021e03090108060d03021209 91
    0x5070010804510320312030a1070154019082d24030f000e076481403c440480f805200302e01c0520304200d000c2035010500700d511070741c2030804c07503a20100b2500282d0000c081e5400300764450300002d0010f4590350b06400104c100d00d056100c0d40300300780f00c8182480d100c0d102401046131560944800304e0108800d40f54840d001900e0b80000118035842d08183c2c190100780d281582d01080c0c4403010701c021404c0400490065299520007040045030040840303460340410311880821400108249240c000c510b400b24241c0b80d8000c08485ea601c44a20300a856034020580007032082c01490000647d049403084089080000c0c1c1d406010680e4986007054010820803018108643d1b0070700c46c0400d52150391091078046c244031002143c0b6996000c00080c83c10790076441a801d80d80280c2c8449085403140007141d540b5661181060b44c641032403500407845c060715128006d030220b28107202da0203da000440100b44103442a44d400160b5511002401b040344a1003074020300580c011041c100d6103101040144c640e481c402000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 9800987 1250 9799737 9799759
    0x9010503061c1b06080411040509010b04020d050a0e03070308010302040203180f070e0a0216080a020a12080f0a05040b07080402040b06040806180d090303050901050f07050318010206060f040b 84
    0x4581d40d14104040b046500c0c80c0750f8285008420021420034004043d1890100001d10781680e480d80c0316070130b903000c0600498589010944468080d04078249180d0701030411926440c03d00d49000c040d19040e1295030440e80f0340b10b94584224808002c581041d60140c603982c5d0720741d19560902000798401402000c40b4005c00303008078540c1105000c1040b1070a10800180041c070708051a9550410024045070315540c81000380d85880b071003c25414040340e4120341196141c4220703001c1641403100c03072030740100002c400d40030240f44940c0118056028002e600d400c00465944c40d4074450444005031006402e000d403400004070814800e03616071307902c240702802c0440e4103482e0001088542d0040e800a00d6590404000c020521a416010007148040030000309110311a1500240610710b29020140400600041e401185d0f40120103c2e5820b4000980c025130b52413031303030400540360b1b004014520500304508658841640c4006503440c0269001400c1c261100d4031141008001c01d40034414603080701719420 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 9802237 1250 9800987 9801019
    0xd080c04050d060f050603070f03030c06020d02040b0406020f01020a0806040f060b03090109021c0b0103030f030b0306010306020403030f021f090204090f1110140301090c020a060c050406020c0a0302060901050306 93
    0x20302d429105120341c00109034214580c1a000c1035400040c80d844c020b500050782001545440c1500e0005c403501410300011400c001e051044c041c0c89411004200540001000505500303118010b10032541d06600342c81d0310b02003a20b281400e034400c1c40784000010383c000c2c4c04140f291030703c1d0b88081c01d000d20041c000240743d940c1c1d040011442e042101c4030f4000741d41d030340842e0b0b0641c10310601d6403034005d940c07541d980d1802816988001c0e0120041c04081c0820150f5511040301c940290301803481448000c089810315a507e10b0280003135401400200c1c002003180d85c21842d4680002005d010740040640101e03d500700003483c6c400200542c081c240e070700503142c003041c1c00421a50070003988018004e014521551540409020703107101440100c0d002c2005481c0202309404040c010380341036480d00003010610075400a02245040c80c0c0c1c420107072145182c4003075801c00b190040010001c80700540c0a03200c0844c0590304200303180440740b01c081d4001d0003c10074a95158030540c000c50784981e00500001004100403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 9803487 1250 9802237 9802249
    0x170a030504141807180807030503040e040201020312011e060302030601020705061606020d0b030d0503010815100b1c0f0209060906030a1d01020406030f09030e04050c090d1505060a0302030d080c0405 87
    0x113504000418200741d036422005004043c1c07000644207000007016841e141d503403040e41c2c9100740d206400001640c40301050443e8402e00840d2211410780d0004410b075611054046044c18a080e02110817402d5a1740004019000c0d0007900d00c41d1405802502c01e46107450240001c03584040b0348008191140c048110000c0d004d880a4104c0040f85280003880192407804e262070b0900c0000c0c000d060040500041045600004c1e505c1030080c460510140d01340c9509c41a0303114a6016004070030882c0000c6092055910084409256030803100010300c040109018076900300d100746041950808000c2000d880d007403c2075002160030000c4100d00180d2043d00012990482d00c007405265038994001034104011070385401015601c009800c4100001c410550340645078800d805000b40c001d90304c0384000b4a04403204070940f4881d600c00b07041d90022410720f160020407103005000059100c0c0ca8203020540d42d05003a0184819130381c0c003500401c4445566002a0340d01ca40050a0050403202044003151645500c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 9804737 1250 9803487 9803491
    0x20d0203030c03040b0310060c170f040b04090504020405010e01140603180303070908010605030601050603060409030309120302090103050f0702030406110304030203010f0905190507090e0109080310170a0305041418 94
    0x120101616030920302c07d070360300342c80c0d103940300004211705c0340009000729900c0b003200c1c1c0114050300507180e0b50360780da076014610600413540181c81d1100c002c900054440040d400a6101701c0c42190104520780c3c8404400070341000a00401304485c000e41e006180b00e060610003117402001c409a07250640c46a0015039255510440d449000a80c280c03d0801982d2000d000b00c401400c012400751000e50305041c040707600ba0000402a910550b150034686043c0750080d88005104c50304540031080c61550310f14050007035072041400c0b90001b450a4000740c1c0328044d582c41e66000d0f40547c0d01443c5080e142040440d034020310f00f040c028031800704102c000010fa6017441081c113100700c0500c010501e507415050007820716014692041d040304074200280300007a0042106c1e02a40c21075140002d900346000f03c1c9900410480304004c140110000a02080403d180da0340700450703040741402d50702c0ca800c0b55041500d400440300000c010039800d0005002204102402c00481103016012503107444100501405038801 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 9805987 1250 9804737 9804749
    0x11040510020f12030702030304021c020d060b1306080a020409020a080709050709080a02030c01180302040e01020711010c1e030c020607031d01030b0102031c020705030c010f050a0b030a020d0203030c0304 89
    0x8204070718450b0000902c40c1c000e030f04030707600314031421031400302e101a40364400104001d103d11180000e419000741807140f0303e10f04540251103050010712a2034024000c1c482440c9103403003444510100840d80c44507000388019100010064400c07075220340c1c280720140050000403a44540e8185000c5060304e02080030360018990311402281609003008040c1685025401c40d42094110203038580258a00140d95010310310300b07207080e0f02940b0300d90111070b105100d580c00c000c0d4828144001a0b4178940e054024144150003401c22401e241c00350001502c83c074801c030740018100d042151410400d000e41c01a880f404500a00b04040e440358968005079141d802400308a01182d4203140740c0e140080030381c0c0000f55001007030030704206040004001030760380e008040001c1d00f266861802c0540407402601079840d21307039019045a0311801c1c0e580050f4042c20305c40c6580e001b06850000043d09100351070080c032907036010280c0035020101043d02800402e5a41100030398040c4800c01075401000408c000402c01858 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 9807237 1250 9805987 9805993
    0x3080c0a17070c0f060804030f0207080f010b0906090106140306040f0c021006050105040f0e0603010905071d0a0204050a0b0304030c0c1401020c0904030512040c09020a050403061b0906031104051002 87
    0x124a440300d2044020341080c1c2c02c1c3c5240c00000d10443d900306c0f100a0b003190709400c1506c42c1042510040b0f15000c0303240c00c525803502828507084d0340d0000541240320700007411126a100341da580700922070051404d2042c440040d08408a82292101100040da0807410140c804100f410714040c500b01030b44c41e0a6003a00041e80252000c01965540e8481c2002600d401d180662a1510340805001600080e0286e00b13000c00441c4003140995030b0943c40100303210740c460141d80007603503903c000c031920320350300c1101c2c000d05059100003420f1801907208840a542c3c0040058901c2410040c4008054000400460902401c3d0180c0381c0030888414000004010b803000a40a400c044c0e000242004050214680100c00e003005020010303401c02c05540e00321a0ba42e201700c00b25502c2d424007440005075507002c0311001e480020280405070340000140140c030b024400510cd241340202d0403001521a210740c03000050110041800954800e4029141c3d91304945a003a091a403100d00069410600080d81c201683c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 9808487 1250 9807237 9807247
    0x5060307081603110904020d0e070e100806070f0c0204140108010b120a0b13020310020706020306040e0309010903080307030b0a080c030c0109030302060f1314060106031508030403080c0a17 83
    0x40c10308038905207811403d24007440f00300d0b0f8200d0700d146140626020389104980200300690404400d5200300c0d521640c076012101540e555a001510060081c1c40701148034110400124990720005201d601a50b1a9030f20464006850201101c02101c1140c007240d0064541100741d048144162155018080400001175415000810040c400c1c6514a2005081c1c1140e8050700107e0842c02c10340f1340c04200e6220900b43d504507840041c0c1455000b14003289624400303d00a4240403955010b5803107010107980420001c0c200705040c5589005e0500001d0004400000510000700030101943e0401c85d075003004a8440c0d04c40001a004030b40681002e5040e51280d910046189803c000042e50040282010880f090039030310000c0d21100000c0020a24100c2c0c031001c105180b924041308040e02e904101403201e040445050162204802c0c841e800000b800e0021040e248141c0c1d481840446055100652806295513079110302500004482143e90180441090119040010308841080b1084905980c0c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 9809737 1250 9808487 9808501
    0x7030605040f090809040f09020613050a06050405100e06090301090b0a0c0513090c050d05010801050411060301060e0114070204231506030414100e07030b0a140106180506030708 78
    0x1140245410140c2e107040c01500004658050300b01c1307000640603580419100c0601454801802104030000d401c0f100004d28040041190f840d0b1030b00340e400440341d06402c5a6034680c111901d00542c0146940031500b5200d40d03c10b00c0c080c1c058a01450009031110742841e050b00006800c40d04a902e00781c510b090178504210b0391410522401150ba00035090443c00c29a000c52014482c1456011f4150095070b150180002c5074081d0041d40c20300c8000034801d004940c0c40b9090329010703100c10b980031030308441c5000c81e01c241c6151401c2585d050311415507900c2d00001541e40111500d1002494000013040c0811829025132114055881c9107029200040c0118040c41002401110010040c0c0c00c0c18034480d02500c0c090791044203d0350810f07080145400c4960040c0015800e0604602104c1841460300070040d01a4002250403811640035003c6540d4560742d54217541c069902c00e0100b084bca62240c1d0050003240c0c060703201c540c5003e07c08150a0a240c3d2030340041075803944142c50b01004a5072143c204001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 9810987 1250 9809737 9809741
    0x30a030506040903020c060304060908160501054005010204061707030b01020c040902011205040c080c01050301120b07020709060e01210c0303050915030f0f07020d0219110303030703060504 83
    0x200c20b45080010054545000791242e40b194081ca1158100001003001e110158200e001d1494200102e03641e141780352140e00740440d02c0f0100464080d4200000079802c81840c010031880b40b4074005400b0510038114040c010311003140030401101e100b42401d0500030501c00d1015102800c040c4d02c41400003400181400c0d61240300400203c00c05040280070f203180e9901027840300246000345ea001c104800c240c80180c51700041004a0005035282c00100820b0100a9100500b116103420941e5503644981c401140c5611090140c007280700042c43c5007800040b5500e0203642d02c8040f0784192440241c84540c0181507601d15070098451401e10300c0180b02c05060141c030f821183e5030810300c00000e0340c840d80d581c0500f010548000303020b120012a00c10044d4941005825025000107142d40c0d4901d0164220440c000095130040f445d4010b040014105a000044181081d41031760000c00c088260300c000445820503290301144e40c01c401c0d5000a226031010806140030390b416841c0421329034148414403003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 9812237 1250 9810987 9810991
    0x3020307080d050708161203150b1204020f030c19080c010305160f090503030c0109060b0303030403090312030f0c080711060112030c052401080f0d05090d0f0212030a0305 75
    0x2070540c028807010000300d0342040488a11660000285032205440c880c0040005510103001e0a40d075290141308604551580c011540304214416070060341d40c40302d101c50424000e62140030382d4a01e84001140151404005d80c001488004049881d03494080300841c90850f003030003800c0141049800c0510130440f040c0000d0355955001c0c0380420180ca000d1400b580080c2c40089200d040c0400400e0f50410701d03100e01c50180180201400700d9688407083c0070018000d100d0050180e81c42d915100481d4281d20b80401141e0007a03070141c0d1100105401d68560b02203e80308045000c00345942c8043c0f24802c0f00ca50701071501400110b84803815079190040003c4d046d000c0d803a01d140001d41000d00140088045040380c1c050841d0503152402c2441003e2400ea40360811818020301c0d80000c41c0e28210360740c0d4010b09400d068030701140c1075520721700203c030f840c41c0c1d5158102c4100022401c18400c280403800c0c4070a8500109006c1c40050060519540104680506400700381c56030780c100041c0260203030b0309402066 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 9813487 1250 9812237 9812249
    0x30102090105030a0b0d050601080f010e0a0803010b0307090e010b2109190c030501020309030712030c0e0d1104050703320103020103090309080f030a0f02061302060f07050102030c0403020307 84
    0x589050301510000380b0310321001345070108440d0f03913041c40a100d803211200d49901e40d0303003d03003101d10310350f11082856610100c0d5140c02d0215030a2070b006203000700380400c0311000c860388031009078116424060b043c40c1540000b0b001c14208403071000b002492214100f07a003030082041e003101c01d607103040000218072030000301403105a9420010061210b1110001250642110700c4001104090b86510300300044a0144e03001030030560012041c80744111000c001004224811204010a141200010380513a030100802c100850a00c07000440c03079003041c0c0105030240e846006543c214003912000241140e00030b0740c280002a43c0c82da83c06c0c40341091061080042c209c20125501c020b0940b1328503c9580205020003410941c5604400c81058050000070024018910680d200d031003256030116542d400c4010601c0004e1441a05501001d0001c505c29000d4411180e2206c1e58a050341c0a02c08907a108511240c1d4003c010000d09010031020f05c0618026146441c40b41c2d42c40b4a9401018075100058100d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 9814737 1250 9813487 9813491
    0x4030b0f060d20030a020d050106051f0212030c04050402070c06090801020403050601150c0c060509090f0601050d09170d02031b0906031501140f0c010e0c01091205010906091202010501050301 84
    0x2c4070100c1d041290407114903580c05600c2851480f9100400d08060f15020003c1d00010740040c00001c0010640180701500d00a940c0342070000e0196440d841d4510000c514000560002443d003041c1c05d047c400156804089903250b10314169540e008141241d00c00c80003171710b61441d049400e011070b56002c13100b540200b41c0c2030025400d250541d29015241c41042c0300b4081e00148001288509600030106008130320f411060000341d141c0c3d03505c0003400b1940408a114450345103400000d40d24001d4842c0075004010607540c0360304120603450740200404032401c041e0b03050f02e000b03454400c020380004010100c01c48502009a16400c001201605031482c40f04441116402400a04184c0e2101070981e94040c452201c450b190000c0400165104240d417540d030070b03140c48000749c505d00c180724900041941c03d401c10000c00151100031503480d1a0601b1082c5603000dd1038045007000051042051840120f006000002e200746640ea00c0400301c40310030004039442050000c2d9146200e030284590742c0100000c1d002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 9815987 1250 9814737 9814759
    0xa0206010f14091008060106020703060c0207120809030f0706030b0f0303090303091e060406110d020d0210020a05040503030a0201060302030d02030405010912110306040b090106120b070305180304030b0f06 90
    0x30744807035503001a41d158040d81d0108001040201d803584c01c1e03401420000143c504958480c04002d440d0324141c04192442d5092958040500d440043c0100c11620b0032180114007844643d981c00c0c1d280d000b0031204d9030501c5010001d0f040f0100c14003800d8000d03c8103403000640c61300d2402c2845500300c0701405461280d013052020741e00c00e45010044514051046517080561003034001786080b80b5110040d2f05400c05800b0401007030180c2c22140c80f494012140c4100d405080c1c021400b260317141001d40708900141c2203a8100007804d0621b40103040303000d0140c00d10f5410517484002292441e0440c29541c00141e445120400a506050000c0f806152a52000d18581801c040020f03001d100c0b40d110306903040310030f10380040c01d0050002c4044c4580c0e40041c00d56500e0b08103800c0c50101210103945054507135107480320014004000f001d460590340c0d40401b85031002c0d910100c0580040800030400038540c0c488865102212806000030b20186110326180c402905225a10b210b00340c100500e818007503020380c81 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 9817237 1250 9815987 9815999
    0x90e040c060509030709050703020714010207020a03080d060306090c05150301080606010f050c0102280302070506040b07030908120f010512031905040b0d020c0c01030912140715020a0206010f 84
    0x2001109a0307005091150ba03038001000800d1602100c1c0d4031140c183c82c90f21092203a403681c550000c24201d40504028045461080c41d030320700300e201c0e0480003584440140810000142d00c03401402c15000c0340200002c60a81e2a03d540090b908500001c41d200309100384180003620b850707481c500e510034180f03075801c2c21581001d4040d651804080d00d2a41800740713039181004401e04c55001c454520380e10701c1c001d544500020652840388114a80c1e101406000700050031021440ba100351002590400c0040c4030740d48440d280c859070540301808000405841d00d903808007090b1020001c014100c0d02c3d05042610340340481c41c4003c88501070f00690710440c1a081402c0d02c0c400000103481c058038035030301c00da20024412081a201403099510100312a400400c1700d060079422a40a09842075107074040d11480010140110111b516224005102460044001520500c60b425840c0003d8041340d800380307170040c95210040c804e46200c05034420590009114031000358180078540c0140440d00c02a508942018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 9818487 1250 9817237 9817253
    0x105090c010f0e0a0306060e0405120c0307030503100905010303020609100b01080a020c0709050a06030201030608030f030415060e0a0c1b050706050903010207020a0b0306030d05070803070503070203090405090d090e04 95
    0xb0000004100035940010482e99442481c01c009650080c400c1102564031260403100342011681a0303024040c0200103221903007860112a28640b158000d1450014035940c182c419400250030000070341405540070400e50242d12816001e507009400030b0101f482d0506406207001d845040d113110380782c202840148566000820607402400400c0c000da21000340720707100c519005895210001d501d06003001d00c44100110f034801c5095a00030b030784c1845410303180c02030140c0d280b10350009007a0f840020000100405e600c800703061030020408101013000750740c031100c03100c008105503440e1035034a0762950303c41700c601e82200c038103900c491f5003e0380d101607522580c840a49a64071031040c181402800980d00ca10740e6020360440c1c403025030007811840c504d600c03403002d00d040360001c80700b0600030701c50b000746c0c0e10300640540c095840b0399601441d01451a0341310038040300c031a0000340101e0150320050189140c1c540d00c42c00760900c122000002006901c60f480402840040d0a501c0804600011800d20002c1442c1c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 9819737 1250 9818487 9818507
    0x203130909150c0203070203011b0201110309070306020717030c121608040308060d0b010801050a0c020f030d09020d08031f050609030a0204050403140703050405030610060206040209071e02010e0105090c01 90
    0x4810001804110f80c2c1040e8158852540c000b9810b51030045003902e021400c415000d00e004403075000300728290f00d60064201c1c603c03003546c4e060300f640d100c21403c0000842940050503a1845640c0b030b03d4249004c450075180a8000355407803480c1003008103000c2d5500e400940b445038002040304410070032140030031000d085084054005010005214000f4045443d034a00151060f03902800d400d40d07035030790382410b03500030401030b03da8200c01c0341803512040342d580c40050921310034103203080658030b02001005020014004080b00300d8011080310603d10209070407101451084141c24504400c02c2c3d0350403c09103600c006900b1440c0700385014820039200391000580c0f42021a410b0750001100d860f20f08003a6128170058107030340f44042001511408056010016000b01e03002a41103500f0f07512071000c80700c6a02014080c1c2d10040c0c3c064400079025190020305241c0209090901d1020442c074003800c0d00c070ba0880c10003100c015079111000e20b01c80e50000d208003a8803042d544040c180c0c0d8442c00c000240200a1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 9820987 1250 9819737 9819773
    0xb1c0207120e04021903020d050901090b070f030b0409080d0b03010203011413020702030a03020a03020d0507080307080709030501060609050307050901050d02060d02090d060603032303010611030405040203070203130909 96
    0x5240c1c2d0b803001c0c1c80d43d0341242c210200c0c070201d1520034075440704010040e41c0303d05c02c5241d0041c10440445d4421005002e21841154402242402a900c48004544800c0b226880704c0c01c25481e10f0b545000c94a45200307000b4190b005048003075a80c083d121103031003a2032081d60303128040d03841040100000c0100c86241040030900325400c11040240102c004c5c0a4015904043d516006a07002802015000102001201d12076000d4a2010100c4202075585d0700900c2c0c00a042e82008000142010f0710901c1c1c00e035070003142c0d41455000c940d120780700ca07400c4498681010300420401e1100384114941008a200104403c8521130915030511011807495002144028003038000890448203000307060301603c0b28017101500142c0740c41000c5c2807040c060300080c40300746c012903050355141c40d12002c103d000d0515004d880000510b16481c100044840321f038081c080000a009c20b00001c03415642e10b000550082110364015600e03480a0b03039215941000c00d90020103064580f1885100044000178010300e01c0d11 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 9822237 1250 9820987 9820997
    0x150406021b13090f050102040603050f0a0501050603070e1f09090b0303070804030605060607140307020909010b0108060f030705040f02030702071205070513090609060905061f0314070b03010b1c020712 88
    0x122034a1300e00005180e9040c001c142e540081000303e000c5600d68042e074442d082c1c1410525150321350840a404941080c041c8581112080001840c035501030014174800410160822007051070b04d00d2034012900340d05400768000750200e03800b0070149485000318248480100e01035440c007040c0e0f68502c0603910a522008200c2e5858000158260303407140140c0706500c1d003001d200b000314200c441d012916540b011008a21581c201c0020608400c01442034101600c03040e12100c050351102400c0140800444031480d82c18032401070082266103540c06450b03802c1011000141c1c490a051304d02a0810005803c50706203102034261240201e100040ca00c0100c83c2c0035a840101c2454210000020303086004018049070b003030002c10010005c155101c454014081d90030f4484a0f11500303107103480344146c1401e0031180350741d02d5001d01c0810000ba100c2e15008c040c8108030b892856451044812a800c2640690304200c40400e414800c0449422002d041112a150842c5404101c2c1c0d80c007290b02e02c40c071101104100c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 9823487 1250 9822237 9822251
    0x110f03060a090311070609031208040809090402030102190302030a0606020c06040306180204021b06060411070314070c240302032205010e01021305040e010605150309010605150406021b13 82
    0x103006050712036a031341c40301c410341c0e0a050701c885000d0000d2809100886420b045142e83c1700b500c1e4841c2c0e1004d4001d070341c0181e40302d2400c0454030803c40c820f140940140c0e031555003049900700c034800443e40d880300070a035501c0c00340c2c8900e003241c008411a0313480e51251082d0f4001000380c00441e41d4680894041e00c0d4030800000fa503501241d08900124200304000790003a2001035000b08004668a1440b200c2100100301d03101555564140003e445000403820f95001d8280300c014002401410110103d80041c9841c6003442155150065038599640c0141c581e46940e00c00325074180103004060340d159006090a52550402016800032a030070b03142c4444d580182da00b050b1007040401c2d084245c0040c0b2010003592070b034003181401d601c48422840b03614030662078140c05104040040c0102d00c2143d500030851564543c07a4555024079a1008001894955036103001003103a80c1d03012492486160a00380b001d032074508105010b443c0c03030000c248072072100702001c1038000e00e0f9513031040040310100f0581001c0340d10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 9824737 1250 9823487 9823493
    0x3030609070201090b040b01090534050913060f12020a060f020c040f0c0f0306030b040f0215030c091c1101050c030c3403031710030204020c0a110f03060a09 69
    0x140110721008011000c80c0e8280011301554171f004506030b91954500300300c0b136103510b050040d5003540b04200441107190004c555401000c0e030015595100030710700b0018944119071001881d24403000503141501555200180300760034180380c2c0700020313120300040c515034400c164000420800c0030340310708003c00c481102c0203540907100340001074040101501c103120340c160150410300901805040c0800080c804055222036903c00e018460449410510201030b0341c6668541010411342010b059030040d181c1c04141056903030400055104012074004940c03030301045070811081403c00f40c5900801a60b41e4180c2c0046090140256260307082400c02d41d90b10502c2d0750744c1c141540113520300000b40380a248014108100303050580c03120301c042100000e003e40040054540c05058601010b000205016444070907050300500c255001209500d441a905a80c0d0380000c1c00c0e42c2c80049140e54542245400c80c0410803104100c960032882280c5181c60080c504000c2503550400525044544c1c4e02d404a410038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 9825987 1250 9824737 9824741
    0xf0703081606020d02070b0108060c090108010306020f1603030902040f05010302090a09020f03010207050c0f0a030812060307090f1d01021c0203040606050901062309060301050112110a091805010803030609070201 93
    0x1d2130100d0130003035440d02001e042c039104209003489115464011100000e01c0042c1c48000c5a2004605840340130b00c59080d030300e804000b90800c165001c3c0c070790703004c114000a0b0700c006e24502032198800d540c0815802501c1c41400143d070242c0403003480c0d5909182c010310050fa03440181903400794402d90006440c46003800040c18500300c2c1d010366038155100159070405d00c5404154091410f42c25104078035117021110070310880f45020b1002800f0b80382c00303005904005907242c80c4542c00981c010110342249448550207401c81c0c900d50244030709aa503400307082001e1110500a40804000e0000850508000305941380c004201c1e00307c84018030340c4c0040001c042001070f51205010303050181814005607180e040242294680c1013041d10f40c0300c214030308150903081c501c086170005d900191845046034078200040d28150180f150b80c500f690b845900e406080d10744d51018018a8205075150320002c1c2c644440100c40140800d841080d2030308000042c00040400002c698020b607080c0c44d14400d580d105402280 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 9827237 1250 9825987 9825997
    0x50d02010503130b0903040518061c050c030102030a06090b010c0b070f0302040801050c04081204140d0510110a030b01050301120f0804080601030605041a0402010807050f0d0203010909050f070308160602 89
    0x900b074072902c00c0c4620417400201400030740340107651b06000c4c8000c440c07801205c00001c851960b805501c2903c01c0034603600b01c0ba4102c4d0900d02c40c03001c85840406180009080e81c0040351031800d880d81d241000c00260083d07000302314240c0c0084c200740d503071030744103440c1c880c251000145070405200c40a401c2d4502244641d0458000b49403840c002c1207141064051803c403944180f2408601e8814040740380c210044480c11201111002c0c01007802c0d580e5000103215600a10031019036941c0249014490341c005c40d03015180c1030b820081500c44e41c550360018007804071452601d8041c108a424801440000380c4040322007c03403030304003040610b02c580525144000d403190f5040401c260143e6000001040059041075003d00c2c0314000080d0381004114400c40c080d40c048a019001401c80f401092080d4000d400900321010070781031302c41c0b421840400ca4401c0c0d0380283d100707500895940600c001400760030300a41d10304001e51000350000520316240c4000740c1c01109071704103064905c2e500b24800c110305941107131 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 9828487 1250 9827237 9827243
    0x7051b0a050106030302150c090409020d05030a020601080607090614030c04030206070b06010801090504050c01181a030402090711250f0311040b040203070f030e01110f040305010c020304050d0201050313 89
    0x4a031a20a403a2440c00380c20544000ca001d84103050010204100045072140f15204802403203080620340e0381084090182c1140684c0c01c0044403200c0c001151040c001170030003551940007024154546000c2610701703000100200100a034111081c0039469102d014030880030207040e103450716512040e1807a20383c2e2107a54402035106030009010000c02100c0b1003210310800c001d8031203404036130741d810b10142910340480d0b00811a41100c42840200c0d802442000d02c0c100403070003070420044e03c8401c092060150501c00d40b545900100c10881149802440c060b1300480310300c3d02c140c04011031288199616251843d2401d103640d2039403a5281c149e096154070f0000d140c681c40c1c3c28012903982c117041d403035141c0d990311840c040c500f4401d5660650134180210707401201c0940c1c8400b00c5286500b000c40090050480d040615503d400140415231808005051566001805035a450b840c5141c5503003101c003503140380c40c00d54009001c20811030359840303d0685803170740a0824580c0c0b9641c6110b0b442d2055200d190007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 9829737 1250 9828487 9828493
    0x50310030f02190e0a050c0702180411030f03070203011113050d0f05070e07020f0714040207050c0d030201051602010501060509010815090a0209040c0201020f0702040e030706020a0c06060501110607051b 89
    0x28a54000e40c981d41c085c0300080e02c01c01907910703800c0d800c8080c2c1c41144000b94104400c1500c10140c07001d424030386588617008281110f0426101300c00070f420030080380e4007045c050b03002246800640c9428494025082181e4080910304070100102900c003151501c1298407408218406c9024004856440a81d045d807040035502c0f441d440e84011404240142c5542c00148107401a000042100048220542c3d40115002c401c2c545840c0c00c00020394000502150b8a01480741c0030206e0f512007007031b02612180b1a400104040c40c0c681000c1010903204050001103a0502004000050304401241e190724020310785a12140e8402640c9034074500080714680c0c0042c82e2000700041341c0c0c5a61b0113040e120404580c140500040008224281c0c001d842194403001c05c200040001890316512541d80100d0a4081e28104800c03501c03580103d801022641002c2981c011001007000001d100c0c50000c0d0000742464004120dc4d48600b9944910003040781c0d0a0210000f284030b140300350802c11807004c403608821 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 9830987 1250 9829737 9829739
    0x50907110f0d0f080604090302100e0f01050408030103030e030312010306152607140109170a08070303020306040c1407030305041e03030e0708010b0102030f09010509090405061006050310030f0219 86
    0x4001e00007502c4000306000211380d0381c0460600e260900441024030303007541c010120034405142c01401066001503a0a1500c03601d4180d8101e8842806000d1145008106003500ca6140d410080c205e50051036005204e40c100300410326031402128502c5040d66000710002480c2404c0e5009500743c280290405140c0350b1000c0410030161020310704e03c88a0035144815078640f1941c446d0002120300040401ea40400e03d11a402d2101808151004240c01010821101650819101d8040302c1e80018401da00080c3c000040140714101401481104c0b0a9840d000c5c004035410f0380040c1044c041d40e00e0080c01c150f12400401c0a008011005483c0b84224421040c030079411403030b0107002045584421100c0c0d00a507400000c901c4d50600c1408002c18060f00078500c0c251040203151001c0e84402c440d14107000c03082c000045107441e1340c00c0c403a1103075209500402c02414404481101e50080e94018410000c003041007100d45041603018600302c0364410903980c0c07544030f00c0c40001c6242901210254111a494070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 9832237 1250 9830987 9831013
    0x20f04020f030403120c020a0206030603010f0c02030301060219030f0c02040603050106060c020f0a060504050121020a0e010810030305040b0c01091205070b0c0403170306120f01050106020c0604050907110f 90
    0x80114010741c465184c10600c005d8284244003500c05540c401005a00a02050700260800304010347d03200344010b00000c1c0255440500e1801c5800c44544036006900100041c00b44640401c8040181e50b11855600b02c107140c55a802080b0407003040303c210401020911140071034555800074000782d58446c4c020300040d915010b00801f07007503e41c3c100783d1107880300100c940d68500303184d180c03a0142c0355540d0b03440d481d180c2001c0c0192001c40000442d4092019a081e4681e040d401a1000e096401e4031555900c0d03c005000c4001414400d020b4446006102220b804000003904182200c1c00c070317140708031215150090381d0300d031034010540c00c0c9002d003100b0f04411026144076440002407903e9880f0b501141159210400301210320b000728000100340c00c84261000b0003014002000c1c40e405880200b01d0642d848800e1803030345c1440580e2107148200d039164801880310a405001050219409445950a0500d001e0000d45071000160074031049c401c6040610184541c00d21203809801c140d18102c40d282d084140d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 9833487 1250 9832237 9832267
    0x9030406120e070e071202250206040e01030b04030f050310050f04020903160305071d071d060a0f0905031212040503070c080a03090501030203040807030f02241503030403020603010b0304020f0402 86
    0x5c900b0b01c0001d8162144101d0300c4e455100340c0d424240c805003601074081e10340d0201e80c1500340d40383c8140d0340000c0c00c0c040010b00d000f4180c0907034003845c894100c200140c100340c40d0240a0f80f032010111020710a0610030403502102108002d01141e00c1100c2e210030144002012400034424a0260b503018045d21440e261030401d51038400085a105000312071031a43c0e6141c5009407080d125046084000084010a10341031240e01c0e0303c0d02110004203007240c150002400100d055220314610004130700141101c00205420402c6c4c400203107800d9004e0441018000c140c5100c1e031064400782003418404001283c00c0c80820016250500d0740700c2800c414098032280c18541d54104110304400003001c0c0792010032254400d00079640901d50050b540c03400d1294580d42950042c1443d12018114807941c180b21030910030a504071100007190718014109403d00c401e08141c261501d03140c881c026031081104000584520b002c40b0304540c900094252a62101d1000521041103600340d258043c0c008108804000508 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 9834737 1250 9833487 9833491
    0x10302040b0c030306192607090c0e010807030c0c0f110303031f050312030a02090d1e030806030d09031502160305040806061807050d0e0706030b01080c0309030406120e070e 76
    0x200c802c601d038074202546507140c242c10b0740185041d800c1d284212411481c0385100b80f201160241c004d88e112541c85180b84811201301e55180c8000402c820a40c490650708102d400e500031805140900036804000c201408441c42c0442c010000000e0a084030306021544c10f2610031400014192540da04000304949500c1201613001d40d02c0302b0b40b12000290a2600294000da44106120780b81e0655071000e80c2e0038000d4001303400860304519400c00200024100b0450400352040707140440240d8442c50400070004000103050030f0103640011041030702c00d500100440c0840703521005680e405c1d00c0a24054011f40140c5103032000e405004c00c51002050703000700c00760040c1c41c11901126110340d0782008010010168010400040e002c1c0b2000c0741907148100010b01a1101d01c803404144560b00c007482500c0c10175140c1c480b100090740e4013241e0f20a581d2007071141d6008000715007600c0c211304000803000d40302d20a070701c0399009100110407000309000c0756030400405101e41e14151418a90340d050460010101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 9835987 1250 9834737 9834739
    0x30c02090901051021020406090f0b010201060302030c090912030901060608090d09030209091608010504120c080412030e04020c061605041202100e0d030309060f020301030203060f06010302040b0c030306 89
    0xc000014500c1c041c144200c82c4200a040c0059030700500e03050355490500703403104104445103c5002d511015895901502c07000b04204000003c1082203801074404031f446000c5290304690500c441040581c1d000520a0713070b0352808407441f81950301e1340304030507142901040100c010020040204241220113500c101300711001a1500c0200d42d03640d81d49203444403c031164084c0868ac42c1042400981131885003154040050411201c2820b45144014881c100d070703a00c0850b6a070345070801c100803c0711000507001080c8150901510014141c1e8409030b583c01580109108941c001004c20181441031081b256400b03009082150340e0448116041c0c0c80380c004a6810704903142810910440d43e1041c4115012035105452460240e24103508104e0000510090f82c0c04000c01d0303004010850b5180c0740300510091107074a00081e1810320f8580b00058a1071051190300241c8103000410250710040b880f103501002c04140003541e0b544802c0160000c4c041ca4010071042c0101148900e0070b4070002000354007487d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 9837237 1250 9835987 9835999
    0xf010f0b09010b070605040602090d0606140d03080408070206091e09010e070203041404020903010e030703031404020d120201090c090b010905040207170f0f0f030105040f06030302060c0f1303030c02 87
    0x4150014030060740401c1c03081000d04142049604007240c0d080d440f0503000b5110322009868928100300081107290700540035505036584900801a07003041d90140001001c040d6940922100d46480261441d00700401c06891a03000050100855551070b0480d41821002008003205621080c010520640800003403402284000c0020810034481941c8a22545040d4015071901d800c00c00384c400c10300c52044000d500190203009290b8181e074280980f1300d50031003000045443d681e050a004040e14a000c08030350074945001d0500015032115601500041e801002586071022030030700403801070104110240030701116081c04545200d454101958500b000d9990300302c0240c44d40d0402007203205081c0b0041c9107504080101c06c00308a81c1c00a041711802c8801160309042c01300c1e0301e8200b603910034104811000e40000051000745440d1192180c00d03070510204215040c10b60380c0c00380d620b40c009040c103040070a01142100c1c030294080d0884d252140c01c0601842c10701d03135038034007c1e01c990001902203210356 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 9838487 1250 9837237 9837251
    0x3050a0308060f01170c0a0908060a0e0d090602120a020c0406030503030720060a0b011209061401060302090a05060d060504020f03040515090d0f1202030f1503011104170106080f010f 80
    0xd80b0a0762012001044e501c90a4011b4551001099480c1d101e440c280042c08900303000000d03049018000300d44286c0042c0400300d04c0c201c1203000c4038107001402a421082c04200340050041c5a0b0024824507020703805114142e551122000903440c0603480d4000c168490304240c0c0200400501002842c080d40381d139101c1c0c07061030341600350320314002d190401c0600307c07603020300300044242009401c80006000d043c141890804800c0764080245c1d215150140da0498070b404808280309000c008950040410340740441c00e08620a000901e00301203446160701c15000804c100c03035001a02c2c2d00c901e00909005104540c1c480b0310000003101500112001d50b807500a525051000c5088291214410780015000d403485404160742900e1000c441e1900c40c0c00c115500074044029003c1d440250302410511011201a141448807404c403010250409802641800c0d000c44002c440c00064a0aa410b003100c041221054560024018038081d404030b03c1038880c148105a13029010f51103020004041c0c8001d01c002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 9839737 1250 9838487 9838489
    0xf090d0f0605061509040b0d020904050c10050901120506131d070515070303020a050d06060305040c05040606021f0b0402030f04060614010c0b0405070f0b0a020f0105010b09100903050a0308060f 85
    0x1440c01d0303400300201e80904100c0c0303405c280360640c418180000001c0500404900e0354003c200800021142102d0701e500446a030328851601c5e1802d4207054440c1e10380545400e41b1200020071030440d4800e007001a6480340081500c5960b40342640c0030136046d41c0020400c25180d1500100040c041c4101440f0a016020000c10282007480b101060070220304541483c1c18450341e400c0b0000e5005802440c10000d0500101c01c0c03420311405054000c054643e4042030b42d04180c1414201c04126600c814030075071400904108098010030780b02095984810035030300c20501c0c1da503844090311041000300e0b4050b100100b045201c1288451090042d40915010006141c03500392280e030092002c20540d0100380440d00e8a400505680d0100768000d120318181d80b90950b440d04d202421b02019004904a0080418100c64180d0304118280000d45024000c0c481d9501d4510210710034400c04020a00900450000c0c02e2414010039002d0000d41d8800111402c806a03400d00800801c0c064406600c030303910445003c907503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 9840987 1250 9839737 9839749
    0xe0603070f08010f032a0f0f030b0f09060a09020114030106020d08070203130909081303060f0e0c100c0507080304090603020a05090702060a0509010b09040501050403090e010b030106050f090d0f060506 88
    0x82d6130f48060b0f203440007105000d0405604031904981036064003090741c04640c036195a0310540c020908540002c8e0014211319003c04c0b003c034010501a2052980f20811a0b84400040c1d81c40d00a941500000b07440101800100e4038400f2202c01d80092010000c000a0703810380c0000c4020081c4a01e6a8916044e19a00001c9840b44200d03001d001181d41c0d045400d0003008074035400070710094403c3d64050b150805030301d0325402c510025401941c48035a40c50f101d0704510300380c0c0034543d0f801a240003d4208081040c0000b524418082e04032003c000b41051040100002048000d0180c241c0400326502e4070f0780c40b140c00700a0141c0d80003c07401703004042d800040504001c410140600a0f94000e0181a07444444240050000400c000034941d2944002d06a5444031500180518003c00c0041030030b00e41820f0150802d40582d10414540705650010804034600c903042d44e0646081e481c000e90741d01c42a0398824000e001c1d2003042c55000301c006e800501000b050001c1c41000f40d01c00c034400d006903a101002c100b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 9842237 1250 9840987 9840989
    0x201060602190305091c03080901050604090503030c180916120207050c090a0204090905101104050105030f09031b0d08010602010c09050d0c150804050c0603040807030c030e0603070f08010f 83
    0x2d002c03161464aa000a0140c0040c1002d1100500814800070041c00018200e262911080e0301152804083c013000c64801c0c010703242d220384250707024000c0136816614650780e840300416070701c0800d40100d0041c1d2880706e4002081103894009042c83d00505107000c120141c800b043c103680022035041084050100c4640c02070752940c40d0031070040c2c0b5103041d484040c03040100d00188400c500035402c00c07011402c00f500344a07029156000c0c00017001d0500300145d90808603070328a08405194001070004000d542c0e408411a81c0c842d88c40c2c44a2001030711100c034482c0c47c1d40074800d580401c01c010b8641b1303212900c1c000280368100059554402020340d0b0b8400b800d900b280c038028003840004440e40e8051100b8203200040e0342c0104d02c039201c82d010007581c0318001c0c55216508441080028000720a0000340001003090413907041c422941a8514140740da2003000510030030720020300b40311061500c9024180034110a900c0d404000d4481ca40e00e20f401c040c010903404c141d80321070b0082400c0d000040b581040f040c0c4400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 9843487 1250 9842237 9842263
    0x6040c05070b07090b0c010e1603050a0f0807020406140f0f0f0f03100e160f0503030406031d060f27030d0203040c080111040510052a07030503190201060602 69
    0x386403401d42d403201c1401d04001407100091181d11200020002c00660050440c46183d20000078034500710b10550342040900b03119810411007030700050010031008100d500000790b002e20003800420484ca400c2d41c1a00840c2c001030751081c038010001a0010b00c14030410f1048100302c078821503d080c04002c00080d03640d50150340d5080088500703115410308042c01000d14036072000742201c42d40c80c2900721040030358240005241c00d1f900409010a6031480c20312140e00581940d005003d0520700b05008240d6034040e51084030100b686400c0040c45012060b4a072045181c150000e440c90b40c0b41c80d810b034040d0014141c1e0541d000c141e08007800c250a6030041c40c4076090115042c041e620340145030b08070101035000a031007034500a02d40b90001580c1203091056210742410075820301d8480c0d180100704040e180c0303540480e07414860100620b40c6040b408031b028940030304613640c004082e80804010586000d50070b0b040100b8900c00065010741411101c4c00d04501c01c44c080e4028403403a42c036000201d07110a0146801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 9844737 1250 9843487 9843497
    0x60103030e0303090301020d062903070804030525150204050a09090201090f060e01030c0e0f010f020c040207060501050a120302030f07021503010303050d14130308190501080601080606040c 83
    0x50000030701c1034038194101c0318000c08407402c0000500001c2d08a138404451900c03501c0e80c0740001c04c010b02d008080041210004400f0717074032010156400346840d2000030094010440a01d00190406004078113845090b070403060a08162a5407600d69491040f14803404e4500090010344000258014000c64041c3c1d140503001d080358a140169103005404200c81c02c0b17050001105000c5003140e5402e401c0d20041c40715594110380310100d034002400b2104003840000c108498409142e4294a0706007080d100400c0a1038290b41b00905540d04134240101d0101c125802400010560f040c4695600071505940080311036602c4155203504001c071201c06e191000b005038005200020071004800d024129103400600b0386450703016001046d00103503100f42c00840110384042211801300909101e801c6600040c00f070510517500b020404400e03002808400242008240c5c00020b82c4204850340c1c054241800da40140a030703584502d26035807968003d00851540e071045200060701490280a690b001c6200745d01c0e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 9845987 1250 9844737 9844739
    0x207050d0602040b07030519020105040201090605090103090501020a03020a1107050312030a0f02030103210f09230d050f240a0c020309030a05010b0a080319050c07090c0302040306110c0601 83
    0x10300c00800000d403000d6034895400d020005036000944001c10f0898426510150740d40b080300d0a0400011541d0080001c6a15003c104030050b40c100a440040d41d8450034242d40782c801c1080100d000c0c100d280d800030030f55400030416840c100c0d0503401500d0b00051644406074003552404000c1e546090a00c01d10380c1c142d0141c215a008003002200840d04510204404a00305110101c0c0005a901c01e0744110b40200503c07482000450140304020803419031842c08051405452200a20398402e40c003c210000d25010280b9003884840000c911500e003020b003180e181007070396040040c1c071205416824a5240110000d62140001c10081209070340645a5607546a8035810800b00003003402130084803e41c4010011466076a604101c02a4460b102c3d80000c41c0201500c400d1240400850f48420801c0e80f042c00604200c80809400b120040c5480c42c040f500e409840340440d10302401640a0543d0900e04001d070424190305800400c19a4011a018055280d0700c50b810700310343c45421014078560b080000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 9847237 1250 9845987 9845989
    0xc07050d02031c050a0e04020a080a0209030106080a140d09060801031b120b0402040b010207050102030f0702030a0f05030301060e010903020d0b0721050609130302030a0c050709090501140c0901020705 88
    0x10034080c0c040d002404540080440e9004207058803c0c00c40a100420350104003903814961120403115055010b503015070074044440b20180c41901e001d4480d010068010400d54a1920250f200e6070041120804030742d0b00440604002d90780f001420b002005038019042d4106015015184d4241220415030717884000381e10350707110340c011000c1e002d10b0859030704060b6000040d0500900070b981d10040c011403c0da81d00341814810032040701e01d0b112040c1d040d9044220100400d030707004020346400c04041c1c004281d407107100b440024201100030000500e0940d40f100a5018003400001460589400d61901140980300000540e2681401d20000f940030030f456800c0000141024015900040e09081903004060451520414a0442c001c155040ca0f0740b1000c11402e0314101c7e44103074210203003d0181c00d5144c4243c074001c2d200d00c6920051014040e2101c031382e01c1002000c2000c0c000a01c940901001450201d2900c240030301070b0a07a804855980e01008078800880301011500c220360160000c1450310b01d000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 9848487 1250 9847237 9847249
    0x60f120c07032102041511010608010510030204050402040204081504060b010305040807120207090c02010b0102070902030c0301150905060706090209090c1f0207030203030a030b0312041206110d06080d0e0102030c0705 95
    0x500d43c1407620340038400080c0745100782403105010303041a121505c04082072440203084600c2d65108560b1a130401e01800f0309103d2140702c12095039019140030440c1d58550011170041c3c417440e40401170b24800d0380c0114040342030104450740109d2141c502400038004800045054410541d40905490070402002001504160b8803000001c1e0500541d50303d43d641e442010200c45420540c03d0150b51200402c00301c940e4103005010243c260011b00b14210700701248090124001406400240c96010000750003460007120088014940244070aa450007180740c4403000c1c04c070042d4102c1c081c0c1c00c4400032414000000c200351600d51000752003c0e010888246070460402c6912140b0020341c01515004000b50314180000d00c0340300200e80740402e00c40c103828203140c500258915000103e000520090100203064030041070255040710780801e0000022060094511944c1002c0c4405443c0840010b03202030b000c1400078000c02d07103440e0401100020401a62244240c40e40006a900300b510140621300c1c0076 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 9849737 1250 9848487 9848537
    0x150b0703200705210106031b0b0c030301030609050304030c0f0e0702030717090103140901020c060106051806090402091806010f0e0117040804050607050309040501050f010527060f120c0703 83
    0x74075404c503482d01d9021103e80c01c581064106440e030381c40c60601803c44042c942280da0007410310401c0c4504c0c0c2200300d034282d0303264081800000c00c4e103a144d50f401c50901c0020002d56000e1038000801840c507550b106219018442180b1588080702013505c0001d82d104e00201c00d840180e0b0b0404036900c240e1030309030306000c4075610080d40d8605041c0d940d04401c5080c20303000c0c40740c1d00c901104000141d44030740740c0030390030f1908005a00890401c0f6082000701c003040c44407204499141c0054400a48070210440003c001c0d01954000300d40002d5030300b044241405100b07100a00881342078882460004191504580407010440710b40c1c00301e8600ca51300304010300d044102c0d40d4080d00400240b403e1540781d0001039902d901c0030030250341076403000c2681865858541b04050061004680c408400406900040e10701d020f840d01c14000e40f04020814034000d104440ea0061120006114955a0209080c40c1116400c01d020f440141040000010b00f68500d480869107103d801d51a940713924140844e0608424a42d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 9850987 1250 9849737 9849769
    0x9050c070b09100f05100e0402180a0f0903020a1103010606050708070501020408160905070206040308040809030708011b080c0708070b151806011b03090513150b0703200705 76
    0x955042d10f2824041403040c2036031a505404081460b04040e0311103e0190f21640108040385040c4042c44010380e52401c17992149200c191b80c0400130740e03071100044001e25491038942001c5041040d680708040c3d01007883d001d07a40c465400858441e994205040c22a4224021000480c3c1c040001c2000b01d5030990180c880780e0b04c80c900140ca0513446251f80c1c1e090254507500a5010140030700700784040141030241e941e102e4910300c0140700030300d0581c9000f0018a00904064400f07080003a203140fa9071010721003840944001e00080c0600c0003400f070780c0c0c10850081d07611803000482000108101c014160120703081a904860000e0404009407078950310228050800c020708085800711840ca40c5410341004035440890380d03d600d26107413038000035200d0350040d070346108209044681d0f030000a80202c0036509841c0e041d0f818240099030418640000d0a4100b0310014014046400156034030b4184000c1060a01c280d598140e01c264160044a1400080a54010170b0700700150034412420030620608050003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 9852237 1250 9850987 9850993
    0x6091207061e06210203030307050d0b10050d0b03060c07030f0c0b040c050f030105060a090c050d0e1c090605030703050604090206070c06110d09030212030c030a03020403050709050c070b09 83
    0x11445a904640b0500c218841034025103e0720100400b074108003a1007600c815052444040740404d500090b102e00c80180304505018020520903c030b0200365001140c0780001801d50489003600a02c042d1241d01301101914480782458060842030a002c95490b010354010307000c00e4103001240d038040d1000740700383c00c583c0200b02d0550803900104030300d8141107024501903950103201c54105406e001e17103420760500c03250081c0c2c140340034000f20340c8070040c006080341da0b00da00c0040c1184804100300c98074032502c1c401d0f0b0f03062410700700340e0280e1540104101201c900f20080d0008458010342c1e0940d1152114824500031a40501c0024140390298200d80d500050080000500042950000da600d403c65802501c00c03081d141400d01110b5000109138541407007210080005d1b02d0306000050601416000080c0500c000c075600e024441410003d80d0456030044080d40d85402600b04018000c6d0020f20055030544a4440c000a2500480c840c190080102d48030540c40c0c04441d40720b41604a0001c5e050700c180784 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 9853487 1250 9852237 9852251
    0xd0915110a08040806060a05011b03021f022101050901091806060303050a080c030603030a0509130c2a150504020d02100507020a05030705010801150c020307030b040b090609120706 79
    0xc00d014a4070740034410300d070294071907003085495440c0150003070802e406500000018007440c1c0e00300c40c0d126080c03c1d45c081644001c4419203012403c005550307080090544c0d06504980e41c44070030b40c000d02130070030049107405002844400010704804c001e00c00d0903004600c680051141c08410b41008282c1034522020044840701691f0755021901207134405e030300007400419411030041c0d0010394030303400c5a40c0e82105411401d0001c002520ba109009441d801d114001401e801c43d81c035420200c81c1c1c000d0b0742c41c40420036503211550140c504410701d14149000c58242ca0b48600d00f456010048082c150014004800d940c4440d4046006010141060303a01007001c0e01040b005941e01c000250900c2034641e00c598a60302c140c41401504142508081d04c1b80d00040014809660300c920000d0440d00815004541914440d2041e0307818094680003035054050100c02000340410030004900851040940282982c0c88802c110349912041d03a168486820200300103010307403803480191241d1400303080009411 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 9854737 1250 9853487 9853517
    0x30603050d0504090e0106030201021009020102070b190906080708010e1519090f06150c21020102030f090303090706111006080d030b090907030f0807020907020a0203010606020d0915 80
    0x92900c03070204000400c00502486101ea49008014030681d41700001d004041c110f0380082c1d00e03082d40210400c0c040b41c4c3c402120f03040d68400c01c10403000705922082140d0b110b20f802c064a101d210785028450200d06803503000030300b40307104026980c4640c400d603403070703540c0c6908086d000f03200c1010107809101750329403c100e0203d999560010000d03940000205600d4031300c0c50408401c00f50742100c054510707001e1070120100070102001075400e400312647d04d8840070740385140c94201c01c070740110724086604103c0002c0101d40c0c260154000c6001c3c9010001c003c0c10750351410700d25503917880112505040c0340c0086c2410060540560072807065100220160b80080c14030320f040b142281d44540c02401140e0019a104040ca42c0520490528000644802481e454041c8102c1d41d01e00c25803000038500c2c1e100c94440703001c0c0b04403c01034441c1e807075005101c00a2410421002903444048007000e0b4469441c00000003012400091001c00305d000b55210341d610b2500c1d00007031760964241c81041c1420b00c940300c20344d41e002d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 9855987 1250 9854737 9854743
    0x40507090b030709080106080d08041401020c03161502041512020c030c0604120206070206070c060b040216061406030a0206090303070204050108070303120b060301090b04060e0a0b0312031e0703060305 88
    0x124152540d60310013040e181c5500c11b829248039a21410b000e400035510045070552180016901c15001100b0400e20781c0121020b60086c8141c4c03d6010003804003242c400c1c468158180c5084910340241c400280026010108000704d204600c2140f2088100f081c2c016001390051544106aa403480001070503d0088255503095a0003984400d40d1741e0842c0b0108010003040b030080084802403480102050b113418038029542d0b0102030111001e01051904880c10010260002414160007600540d2103407202c444020502980d180c040316014200001702c10303c00d803440d1113280b1620000f4014045800300e6005d00045910002400ea010b0104100780000b60715907010304c0380280011070041c10070501d5800c0007007201c0c134002492006c260800c3c2480c51599554000d90341035603044030b00014250050b900150090005900001c44c00d102203080251401d6140d01421080707109500340c03100c2c10014202642d89100842e14981d45d0034850703000900750b10283c502964020030300c5c10000b1300543c07251038540c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 9857237 1250 9855987 9855991
    0x30e070e1302041107020105030423030a0801170a020604121407060e030d0807090620070e0601090b0301080a030503100806010306050a06050d0f02090c09040e0109050106050306040b06040507090b03 87
    0x10302400c074080303400b1801c0520402c03081d0720000c2d28441c1000d0450340001c0680c800500302802152481c43c0100004038540030700c28a4076050b804595444880303d0000d887d02009106904885141c01007040c0c18000110f807a0440540c000c2141d490310341042c0810101250104003960482c08090f0114180c00042144070094042a292620050b200c0c90403d444c1c011103030702d000c04200c1c61380d080c0a5080e811041640c207881c09802e012040d00c11506601c2d0054044450b094254810f04200040c120400c0900d075010b50400ea0719080c2c40780c3c4841000210744420320401040d68009000240400e200c6c1b8099508000f02503204404e2643c1d03154a503207003141c281c0003554503903514001d0000c1100180300c0c0d0801020b0598000101d02815200d03241d80c40710048019000750001000585070091000440305003000080081090410710840103008080180d0200c0e181e40c0b070f060010400d480c00090040c410b03640850750004503a40d0405003c00b500d40980104248510b801002c10b4001a40d40514 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 9858487 1250 9857237 9857251
    0x150207020303070c05040501060c170304020f0405040c050102060610021213080304080607031d060402010c030e03011505040f051b090d0606030305030f0109061505070c03020901080a050c0105040b0a030e070e 91
    0x1016a400c040403c41241d106034444d402b407001040340100041e015000c80c0c0f03c46c24803400744584903a203e00102e00c3c001c40d600d4070130780d110740ba00003000200000d0442a001360381c1c003a4216480342d9941414801010343d80400d4401692092044000d50a09880244020745440c0648000d6aa984120034030359013080d001440550041003c000384160705101310000400a600404c1280b090310700700584640000e040a81086071030404442030501401c030212445c10042d008015440c13440600880101c064010144a0f505010400360b08289a000d2607007d200e0641c0d0200381000d107a003142410703520480c0c40703035040490012020003092884c1b1074103008500984406940b4640031465000d6801305030042104103103403140038810140e0403e820800f1170120b081c21955013005061501360300d006075000942c001d441000101e00b400005c92a84821440390084030001400c400040d11140070742d00416001ca40180b12044142d842500180031221049068624131615a9140d10700490212856 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 9859737 1250 9858487 9858503
    0x4050904080408010624020106030210080a0b03030406020a060e06040b0606130306020310150c0b0c070f0c06020a050d0305060303030406050a0b1f0e0d020a0504020306060c01020c0a0317100315020702030307 91
    0x241709105403078204460301b2520780b00030131a09085500046003128008265020465280001035008070198417480700c19900804680d12983e445000945d200b22080c0200c8883e030801c28254545440040c5190055511100411443d922041440500c0d0004082030001e41180b000c00004076a03503100640c00703000e0805840741924200340c0301c00740c10542006010b04100c038411507800824042912180c2046110344000da030703103d807030500143e0801e600202415806d0100c000050140c2c0014800580703511400594403c2c5006403026000c8440490354190103800400000d00050710640c02a64001e840d42d4002071031507141c0c0b01184081448038243c2d0203040302c1e110800043c42d0410420381329541c0888080055101030341c0860800559446545d0059401201050359a63750b42e0589000e660740c28000c5454440c4580780d1562064480c106801044040004480b21184007070254415030141240c910703244e145545010a500040900650712036080c800380c4016603041c0000d080c0a0f001d0000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 9860987 1250 9859737 9859769
    0x110f0d06060f0608060603100603051302040609020406030e0a05030a030c03091407060909060506090d03050405030604060f060e0402090412030605061209010606090510110c090405030a030b04020f040509040804080106 95
    0x4084c10075040609400d1150801344100001490b091400c24159021403401041a0300d44900c407180608140301c00035800340c10a4000300301707815550b000d03104440c40c030740e0180150003800480d1170b245c1000e104060116013040003803a021038080c0d085134010620610f03001174000b40d00e4130342d0105602810010341040c0c000c420304200040d4008007240281c680d44000700310603840c0c000011041d125111446000b90040c041c00c0090501920680c0d000f4280941581d030545490301d007110060618160210f401c900d40000403400445646817a4425039010701610b010380c996031545101ca48500851100b01a01d035a008600c545038000a818400c0c039845c40b40d0180e040c880400f0742074440d00e411070030804c40c1d80c00d004c00a5a40b100d07a0801154424180030040e48031403000e06080112081416812005010074401005400001011408010f64082000e0400380c0c00300810392003030241800e050f200c240014485841c12501c1d981d085441854541d107810703a40e2600a09441841c2d22012000d000c03000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 9862237 1250 9860987 9860999
    0x412030c02030f0303160804020a030c0602070305070e040807030e030f0111070614070507080703050906030c040503010e06010302240705010e0109020108010803040302150318070801020d110304110f0d06060f 91
    0x20000703c10f02d07a070020758103501e4070501190783c01000e49200b6041100301c0001c10203645030440003070701558010b00b15042c2c0035145c1001039135030152440b00b211035105d481000500391641c0c1c1c41c51401181d000421900d880f10548084850741041d2180c1640340c0a1042c00c0d82c68010244150b190900007000001e884600c0340c00c20004450041905103200f410401c1044015507000c1c0817158400d60001c09592540b140e42412500c2d80552480641c22620000500c000a604034000d4801c84104600a000100310149075549821003848001d400c15240700b0070b42250106801c2c141180400b0704005410005940c40d4642904c02480806c90340d65598141c800543d603000e003895000d00b41d0080110318007461070f804103c90130356500e0103040800c004400315200707000f50100308010300c002104445c8602d45a10380d160007548540c0f401c01c0000c0c50300c2422007001e142d90094034440d41c4c101c511a0702580484042c030148102c00324155a10032004188038002507803d12640b00a00301e103075803004501e81061 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 9863487 1250 9862237 9862243
    0x180403030f0b0d020a05220e030304120215190b09010e0103060b060f09090a060b031608060109060c0206090604030b010b040e010603020c0c150408030a030f110403050709110412030c0203 82
    0x11100b601400c0411034410258442c200a0781c119042034035211605c10300400c04004401c201c034030b0360900e282451091032070200d001000d10702460240e40d403058002c001d41c0d01a03a03500703068802d102041c00088001442080c1c011801c032843d078141c07000400c41401c02c3c00001c03c248401d03000740c2148a4511b0060051228502c0750040d200c6040c1c0d81103207010301500000c1c10300d0280440c001d1142c0c447c500000c5c0314130215000140204143c21302c0329120b04054071000e60f003541604045000030f0480001484940c1701e9035042c011203000752107024040c030042c3c01740005075120400b4140c0181c000c10000000450400e0f085000307145106802d61241d042140420708100103034810001c150052140d00c45007507012400705c0c88864101c40f581d540d0f001200c584032950046074825010381c080810700e03034038264040c0c0003000301d0650350808102c11000319484802600a82c007000d0103d503c030440500c01c00100c0d60102c02074203240d65155080642d118108607015040c50000c40006a0852881c0c0441c1020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 9864737 1250 9863487 9863501
    0x408030d09050106080601030305070f020303120108011a0a060507080705030f0705070303081b121306020a0c0203070e040b19021c0204030524070e040b060403050708060c040b18180403030f 83
    0x11720f019026030351458a0041c0301d0701035990042d103883c0003859404119501001200d001001480712600350350380d03410307081d40240807051441e210480c0024401c01700d4a002c480403001d5690545540342880c450303840303114194000010881c2d0610040280d059074602c4540a80303550ba100c1c5008140315410f40c600206440d8000c0c14841d0b04541a00050700b9150108090780d4418080c010146942c3c1e54050010710103031101e90015050501c00a02c01510302c1d8030480c045c52a600076403c43e01096503903180c060940c0c400322005800c00c40708a02151050f80384480824003266500c41c09410510030704981d9000c458510b1000f0341503540020100104001480160a446290311480c811440e20f00c460380b100c05401011300e4208041c1000400180d80c1d554000e104981c0007900c0b0a441e552281b030704a56500c1c0c14002c02000d0f225040004001410000c100c0341990344000740181400385800044840c030410b4002d05074404035051100d25100000111144154002d9801060101007040340c281140e01d0b07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 9865987 1250 9864737 9864749
    0x60a140c060c03040c08070f0603020a020c13020903010c050c03070b1e07020604060606020a0309030201031e090803040b090a03021b01050c010f0507030509070501090b03040204020c06070903110618150408030d09050106 96
    0x12141f4200002c41404519100311440d9003800360f034070b50503441d049050072000452568002583c803003451444042c1d90150180c05400d80003004000c0e00c920040d2018010482008a181e0042005100081303101c000760707400411307200401c1c0380240c1c2e041e00308640100c112185070060f40500304100038000c007401228000c0486002412400304240c50003424842e960201a050584840c2001806000e018070b40c0e0220b50900301c10008070380186480003460340241c81c140e940d161058041039143c000401d0944029605070010400d400310740034400c50f01e02070070130113506114041c03102c148481e400380550350a5504503840001e242c5484400a81250806054000d076079028107424840d50341c12442c104103890441030b5050b12035075984000b801901c203074004c0d0f12890140310140190f142d0041040f0007030740c0c802d09080f40c040c000101070207128010401c41c01c55004c080081c80340c007400d02500d445000e100180c03c641c503142d1603614142c61940407150305100b5a680310120002e0100070301c504805080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 9867237 1250 9865987 9865993
    0x150c010c0801030b040f0c0f14030106080313090f180501020307090f0503030a05030a060803070302030301080d08060904060203070c0204020414090105030102280507060f0903110c060a140c060c03040c08 89
    0x410f6482d03804044400400040c90000d4208866080c01b4500384204018000707100c03080b040a46032019038000d20380c0244450b00940c01c010000c2030140d000b105464010340717004004c05442d172400b00c1e2400a48007035403818200780c0e036400e880c11145904100e050709240c01400056941c7c20101c100900d0b50850754415250110b1841d4103200c2580c0110071611010072070703c2d100703889481e10a40c1c00010480c90340221060b102c0018890109a0003101030340c100c607078030014ac0b40e4035543e442054804442c200d65040c0e0104400c1d0000f00020540e9010b0340c0c000c1c0d01440d2500720b401c0f199021600702da01a802988080550036003040f803d10b4140041303809424264001d500f440c1003007030400c01004524040d86030340c450001240e0805131113501942c000c00d4106a09112505294107144000c14185c0d03425400500740107862540ba1400041d4020200f401030901ca00d0701504400459090140400d1500c0303880c0300700f2084021100c03c00405009842c0c0210b1540d0b030b03050501c1c111409414070b03807040840303030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 9868487 1250 9867237 9867239
    0x103140105010b03060d05010e0d08040c0e13080a0e0406090203062106040201080613060e01170f060c090109090f051609080a03080a0f050a0f0b0105040b1c060302150c010c0801 78
    0x100000f019603801100c00d039203d000071039043c5860ba001d0451160021840d02c12102c0c0078040e5135003c40c1680c00b8a00a00e250000380f1380b41c0d070314644144000c803450300007074103140301c44400120a078004200b601c48038980540030030015800982541c100340e2040003080c3d00401480b045107400c41c400004411b0f9140d440e84003480070018141c9612000344064180400d800c0040c400d61030341d0040740349901190008004217a1200d400001c451403c0c0550056001c1d4100390254145c0002030344405450884010300c29a40c1340040791140e80e0214890504010030700d00c0001c1c403458a4000c10610051041010602d032810059034405590941e008004010080d0002c01049601141420585405240440c600d550b42c0046402a0040c0d000081446152000b0085181280c2d400f80e440642001c07018804413038000011581401a4000d441080904200114080400710481c030200013002d0404601941e4980000e2480d0200849400a1000004040030241c00030b11a0040c40340c41410900401c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 9869737 1250 9868487 9868499
    0x50106210504060204030b04030306030506070516170903030c01060317042402010207020915030c03030a090611070b070b01060809060408040b070203010608070b042303191712010314010501 83
    0x36040403500a00c09696400810284500340d01154060b540280003261242018a401401491a803000f40d07601e000e40400b185d5058031400803503282e031007049440403100340320791903450140781e007016603400c2c00000700300e0018640c9050024000850400380000303442843c500382060000700c10071803135150900801061041c0d100c0400c0720f030784100e205c0c903541c480300703c5104043c0c1c02481010303000707940100300004111810801d02e03281800c007101902665060400c0400303140e0341c0e016111100c008a112200180500c0e480365660384400c11108040300e10380c95072040c111680364402001561a141944014400742c1c0e00440c41d590002d6140d4018a40c92030300380c980e400c0300e000f107000303c11502000103001000c1d50b809401c200040d1646d00d0682d0b02081d9919000c9885a00c03500c1031401075210990809038905070118031a01d00d420203800b4010004452003010400f15080d202101c04100581c202c0040c0110070003e85048901c182001c51194158180301403040440d1040c10301c260b04000c018000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 9870987 1250 9869737 9869777
    0x1104020a0c0305030403021002120603010c080705191704030206071d0303040902031302180114010305010e0705070311120315030a03020a24020316090f030309050105071103030319050106 82
    0x144540516100d03480e0b46443c078003281001002016054401e0000c2603030ac2141e11010225405803508400070844041400d03002e84107280211408008a1018005c00d50700309038565a56009090a103019095004104840050004161800d800590240c0c00b00082c0c075400030034601d10f0b9001e81102c0301c03e0754061000240e5074411409111012a00030020601c42600310003801c0c4000d50050405204204441c0a014200400d20501403485850111201c55500078410b0720b050b83d180003452030003030340d0f000d800b42d0340340d030004800f14100004800141181c41d030501020650b0000780d08400d07620f00b060402d0342c4084400b812001d100b1703004500084002f0307800203140c1241941c0510a50f00000c042102c6080d10500d984403542854000030400c440844885000c1c400c1d42090740f6801d030f02e941c0f17030710054141ca0540d000c01070206081035000d00003507014001510650b44140b44402c17518020501190035070300140d42030707203000507500c0140e038803081d0071300649014004500d02442d0002c02100c00c901 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 9872237 1250 9870987 9871007
    0x5090405060412030f140403020106050d080f03090a080403060b010807110d0e0f03100b1201050108070608091903080702010515010c06110d02030708010f060905010e040b011707020a1104020a 84
    0x48081c20040410264a001303030030034040031881c0d017401c1104d50000c500d00b44540c01c0c00c807000c60041d440c003140031580d032801e2a01c4000403074015407405d05100c0c1680821070760741d0020340705041d54440d050540000801031401000518425400410510b00040c000b44c1400005040c400078024001d15180d44010001100d5041c3c01c186d1400400c09201003010542200c07040007600e826020342d090390303030440c4940d400030081c11405441c450000c00d16041c00c6805c895080c00384005a800098080011610545000f03400c5040001510b5039242c1c800c0044054000c940c804502040318082080f46c51502881010b90210b95030565000741c0c840c00000170074207040c5000040c5665600c00b0a136504900210070345210300b07025001150f4a0800100203400d040d404d1080302d405a1030f0305008149075114040070300450324180c41e214400c802c0d200c02c0001a1080b501d02c141000b0301103100724500801e0408144c0549650f40150210b01d40318180410100842d01a150286004001280c06540c3c002c40c0c40d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 9873487 1250 9872237 9872243
    0x5030d06060f0c1209050316080c0f030712080405031507080901050402150d0603060e031306030b061806090915040606020109050c01080912030106170105041a060a05040e0c03010503010501050904050604 89
    0x12801300c0c44040a0b00c5a003207a8008039090303c14580d00c4000031074000603090903900140c00300c425450440003001174024100302c410390560000441040341c2c1c0042240901014421032a1600b041e8481e40440d02e888504115143c0040e006414449500c0d0410032440e00440c0401c002c1c8460300c4c098002c68a440d8034002c40e2250180c00081c049021801c9030f1000014507844081802240522400150349400c50000b100d6018940c07000006e115020380301d01c20395007501820460078002c84101030080d091b0b494031515002030040140c18110b40d1070000c4984038200c1d81d03048620071052841403004448d400d4214206580c500a0001d0205000041c0350031038103401d1034804420f0743c2c1c581145040030580244100110008000454219042408407010844c000600e1203c0e80e039810400050303800c1c1007070001c40c0034140c41180b803ca00f05000100b0310700d0594100f01e0702d0181e488010121220088820220650000c0014400c6280a024113401010f08a614218505040e100e694403610041c1c402 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 9874737 1250 9873487 9873503
    0x1803080a090c1a0c0105040b04050d0f12020307030612050105010e011203020601050607210c12090605030a09170d0501080c04020a02030a030905010b0a0b03150108090d0302030604090206030405030d06060f0c 91
    0x1280c43c4001da0000c40c0c80f21180e0b403009004c182060314200041e4403003a03c0484850185a208184591141100d4a10111103aa800070340c40d0800c02244004e501c06000720b003c054840c070001c140200d8180d51004071910410002030290b1400074410036041068110800c00c0040120141c0841c2d0700107021415204101c501c1036075050186814035030325040304aa0320032502030b440a07070038042c0c00000b6081c0043c0a00e04102c0310010103242280d1000d19802042d000c12014404200700343d801e130740403103142481544504072082c007a0102c900190000048107000781d0300c0f080144100031080c0231108020070255000d41c105550910702075200d010380d1541e8803c05560b500380c0c0c81400800d42052042900c040d1075040c1c0340f81c89100a0722290301c110742141590b0404584075041e940709410b928414240760340a4400070302e5044080700039500160134079500c55202e410140c05a521140154005c600c40e000460352070b130b074202c00c080680c1c1d802d520140501641512a8583c26000712055058039840102 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 9875987 1250 9874737 9874769
    0x61202011202120403050c24040f030c06060f03050709200c010204050a06080a0b01020706050904020a050408010e031b03091309061b0801050109080304051305060102101803080a090c 80
    0x300e0070090080320812110180150180000d042e0003100812103000782c9000d4401070031140307a41c440e0b2586901c8030550000260000103000c00c1c02c05003003005651003440c20384d07107042552b201c501c2a100c5980101c48480300d070140400030404100240001081d10394000d0164120a4131080708a061032044000d0313503500091751031a1100c082d0304a901514004010605071030721440c0003800c10400300c0300c0702403842c038040421843c1c4d0700020700e04044034295036445140482c1c40080c070000e50040e00100301407041c1070002113501d51081c001c0560388014800110380354a09960300040000f0340001500c07054208100b861982e4803040071406041c0010031022901c000c092a0240c02004601c559000019204c0044030749a07900081550481c0c0c1c3c260f841401c0305484550243e01da21443c8613103a800681165104510174172500a40d9205105005483c4243c50309580e8000b40c0e9403000c94146181103c100440405401804c19608000c1c00d03901004039010035541c140c1d0958660040349114000526 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 9877237 1250 9875987 9876017
    0x20307050106030809040b301014070206010e010806070309020a030b0a15090e10090609020607050d081005100c110a09050f0604053706060e01020105060406120201 72
    0x211191568848020810540d4030708040016400000321244202c1c10016070b00042d2505090540e443e24030701104120020b0708ea901201c9030300500040c9020350003041040110311000f13120711000f401c1650008041072500f000002d00303004050b04480748905030380c40144600d0800041c6241c0c484601d0400180c108103070300009500c000c040d480104103d024400b00010844070b50415081c400c110152034400588800c1c0c07290680e289484282440e5014414450f05815540c101300141c0e070041d140000c8508031038002c98015403100030305540d15403200d050b542100740c0c85001d44c0c2c2d1141c201c45a0402c81d030b080800050b00701002a040d03108000740b0440d00404e11901c6020001e42c108010a501d09440c4e0b10429103001d0a4211030410980310280000303112424207000f403d00c28101c5030305148100c0e4981450344070519a00b0b40f4813001010402c1440880c1d0320318442d040c003402407511202c11481002000a0035104010311250141d42401c3c01040884040c43c90641c01c0b641c2401d040b007114203004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 9878487 1250 9877237 9877243
    0x21203060307030602180a0906080a030309061103010b0c0606010c03090303080907050301020301080d120c080c130909060e0f0d02070b0a0c050304030c030201090902040305030306040207050f010e06160201200a02 93
    0x282001d0084d41c4000f8081c1d841d000d0000500010a109403120740026075180c1d030385422900103100e00c48807500803c40300d0001910947c06a2045071180b800092884541090210301e41c01c02d803c207810007140007511204802c010400190b11103c00d2810810400c52541c0051172400c8601c4020300b80b100741e9010540800f424880f60000e404050000c6440707607554121940d41d222160000004140b030340a040d0300114050145407142140f075114070000e6100c0c6d006030301d180d61180440c844000c04014001c03824003954004c14242c58010013020800300701401d40c25041003c0000e20011951149070749040e5190081001c2c0101e03242c0b0320f401c82c1c5030561041d00340d6003c1c58201c0024a6404009408070402c440d104849095a000307136510050b1689486483c0d0491044d4000075145a0040c0300040030762a26800a008191151095800f10303e1605005400c0d80c0c2e070304031f980015400001c01c000003000d0b0140f00103e2800301d44000c1c00454400410202404409021602c07201c0c400070701022a41d00070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 9879737 1250 9878487 9878489
    0xf03040302031e040f0801150501050a121503020f06070203060a0b0d0c080102030103030905030706090b0306040f0212010611032701020a02030d03020306150c0c010825170610021203060307 83
    0x41c01080d803608460030a100d8444c1e0043c0280d030305200301000046403500c0140316905442201e51a02c041c01e5080c840103440c9500048451070400c82040100c0e01c07801254081c140c190202e880030810700364254410041080e04a000c0701d8000e00d4180710045c00b41e90000b803240c0d0021203079800000c0f05040b180125607580500d40c800303401c11001c071000159102e03055008604a0303002c0d07550500304580790301c2003645808051103600001001b41e1804e10444045100a580084005000180304007034440c10360180d80040c15411840c01c140c0c0300410485400888600f20100c1c0c0788040c41c9490721ba0b0340b512480403603460540311107101c141800d01069008002101515800400b10b400c54014904001d0103944115030f120700a440040b544a503010116090307520601810000e00208411080115400d420040801e0a000e4182000408103030b00da91003403000004580c0e80d42d500c07401c84c03904403507040380c0606040d000d200303103410300c2038800d50100d10f000d00300d20040c81c195980c0e2a11000a0310740700c1c031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 9880987 1250 9879737 9879757
    0x307120e070801090f02090f090604080d20070606080d0c14010b061314030703020105030403030f09080f0a030506060c0a0b04030203071211100c02030d02070c03080c01050f16050f0304030203 84
    0x4e4159904144100c00c80c864140a00c00c0300d07020340703664a0b04080401202d00799008034090340408007250010317440030003400b04003800c0d00340051805150440e4a40000340d00e950340c2148080082e80c2e50900c071841c0200e80203400701100801c0d80090404c070003030002c0980d6201911072115a0440d009a1400b034210602e01d00d0010042603c4544401301c188044c11607101c2d022007200200540d035024100810340d10b0480380c0584a00b4103556840d00c3c20ba005d8503002c3e039a000383d01d030366081490025503c10080c00c1d5524a10302c206864402912007d000c5490103001d01e48142005d200c2c1c101101000607841000c250300c0140e120041d166480e0591841c007900320001e050002c00040c00c44116442034040103103040c04400ca07000808001190400c41340322008a10060304208071070040a02c00d50001d082e410300c1400746644084c1d881c1c44142c42504503d85404580e5161418464415100b2110030341140068091030018100c040015000b440b0340407480841c0180440007900707150090040e102d5841c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 9882237 1250 9880987 9880991
    0x1060e01031a09010b0d06020c160602070602101505060903030f0301081b01030b030a0201080c040305010504050c04050c0a020604030c020a050301050a09150603020a050f040e100207020f04020307120e070801 91
    0x107140d00d4100100c030701c0010310b02003101103540040c0b0740180501440c0c903090006040204030141c55110003021354400050301c2e030144281100031000d40e01c5026004010321141d8081d04151342040c4001742014003101d0300c806040e040050180404007d01c000204407102142c10540d241c4030305002c03074154001c00c14a1100d0400201c000668054085003101c40c4640481c004030000200c9001501100c00c03902030560558041205040194010b8a409030003010f05042d180c100343d81c030760300d1500b13440e4204c1d4103c4a50704803031000c035a00d0409000b1340b5000700c03988403194280f40404000131354949004102800700030015101c1c0045d5240c1011503405080054000d1103d4600403507050003822060f60111040c4280702440c50100d0101d00c5400162540113100c1e02d1410310700070803c400f00a4903090f00341d116030b450540b048034002c1000f5010000d4180f001c0540c88020303e004101c2640344041c8a203010300c0c010400c004c21240c1c0032802c840e10341940b100015400360885400d520303104840e00031414942c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 9883487 1250 9882237 9882239
    0xb0a03150603060303082d090c030a1505060306040201050a03110f070303021909150c02120303040c0f0b07030e0418050714090c071a04080903010603030f020609010e06060105090301060e01 83
    0x9902d5046401034030300944070012a900c81252044201c403494442685040704400380c86010200441010b4014404c0421200ba004e00701c00000d0501c1d9400c0c0e412181010107807411400600240079469000c80114017400c490725003500040c110b03108071040102096034881d000c00b1310545220940c2e4030268095074958550010b841c000d402036111014a0f000804600d5841902d00e2084000500b680c602d4120000c0c20390140740140c03980220000b04992004a4035019080c800303040004d144145c2c0601d682d1034407189850b00f00011519036030048540c02c80c0400525010a8110380c0d90341d02e4038010b8400181d5021110b20724802d1405030341380241035000354080010242400645401e10701000c0b500800c550721901001c42880c840c08030000c0c5110740040c401e409480300c2590a81c1c1c858040d1010760f1801c408880001d00f140c0c1503030011408180e11100601c1c02541c10044194000001c0d0000c008014644807201d41c2c41d02c00601081c100300000a542856031000e40090000341503140b8008819 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 9884737 1250 9883487 9883499
    0x803130506070309050c040504120c03020a020402030405030301050109080312180a0215030601090501020f0c0f0a03080a0203190309030c120903060e01090201030b19060c111c02120708070b0a0315 86
    0x141c0701d034504c260b070588125203a2280c10301c0c2c28032849004a038040c0344845500410361054410303880407441602940180c4103020096101c90004500c070760301c501c000d565a07605200024210044c00e80248115510910000d03140134032000c592034000d400003e104541e840c40001310346c54603030414002074109168070044c0000340e100f03034080c5010b5582629100c0c18242c49100483e5140f18843c0814100d50010000314058103050000a000700c05c042d04600205840c0c2c0c0720b002c2c0c0e0740d12020000005900014900c0c00050041e0402d20007a019854240f16842d0366485c014041e03410f840c005003039500341d44091000e503401003040703100840c0d00031000e20001c0140400d803802000095410703400b01c1d0500d42000460f1810342482000c1503c01740c5542002418600115010203030300c402194442c51100000c291079481d01550142e148a101c400b46920115206200d04008100450405540080428058211701040d000d0a480d0502c621079202e4106003000c402030f00308189011489148501b0104407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 9885987 1250 9884737 9884741
    0x9021f09052106041115070f05010606030228050d09050a0c080105040519020114040e10150215060a0302120303100806010608060d030908100b03070801020c0a08031305060703 77
    0x44030700440304101c91a000b04a08000718226400d81011038000d0300016000608040d5020341d070030b0002d84040300711100c40d904041540e203c14010380341462442005403c0000900580e0f0180660703180550500900301804141d06881030f0400103c1252501e0250210340324100b903480c1860038840034060132485e4202180c94110420003681c0c000c1c20800c020408c1c84050080901840c1d001e002001060314554030004540a030381c40c02c80c1004028035a010b00a40c4044c040c00180c2080065003005060000030081c0f81c4800341c2c0300d0050440400440c205150700412207110300d90682c00990610f54444000908018240d00b0003980722159a211034417540d4004042d40c400c0349d20301c0c1c2c1003102c10349030041d8941c1c41009101c0d210003e083c00c0000381083c100001c800108904c0b80c14003242140d201e00405041461340c0d070710404010355581e8154058582040032000405d9884021850712214590081e224602030310060700750080003011a031840d0505091212540d0068143d1728503060440000300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 9887237 1250 9885987 9885989
    0x20d0302010b27150a0e0705070c0e09010c0212040501210903050406020610050a05060d150602060703060e0103020a0b07151103060108060f0d060c030e03040306060f0602030a09030609021f09 84
    0x198070884040040c121340440d81c01d0903028080101503d02103440d0698104044000400440c10044103010000c00180003540c4040035150700d0801c12524582440700b1421035200100b461300315802201e49005d0590390700200d6080d00c0080c030b448102404100b503009004050186a0f46086190076824428540e000f0050029201607909a50b91600c036086400711840d020300071036a100c0d4020004001078034050380141020006a03601040101a20555890810107640001d0160304004c1c100480143d040c0301c1c00d005070290500e10003140d411034010401c00c40803406002d8000c1d0002500e5001c0c0040f04104500d4084000028800a00010b102c1146034009540c6940424400d1020034210314002e5001e1820407070107801114406c41079215080038010200201d42410380c1c411903002612400e00050014500441c008a641482c01d2a10014a2001e90040e400c6400500400c0340841e40710300640f0803a60001d41c0401c002400340001020194008944924034104034111400f10345c020200324 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 9888487 1250 9887237 9887299
    0x50609010509041716080a02010501050a0902040f0506070c030503030705041805010302030a0b1009060b030f070302040b07080a030f06060309050105060603010503030720031f050903070f020d0302010b 88
    0x14a41da0300c0041c81004401039500521440000d043c002205101c400607245a1541c3e040d440542c2074141c5031821185c0c860301401006035140d00061090f810420b28605c01426034420462030a07241c11400c4010408034050302e846610009920028404daa01e0803401554100050303903901d040c00c1001812540c42489000c0d020149191b00b01d2540b45648240d9040701e401030040c1000403210740c5c95107081c02d0000c203d150b0450049401188100b000c0c400c6102030508420215500c0c00c2054800a150400408a808050040005101d905011010380e40c140e5170002c5800c1c3c4810360f40d402079014010900b141c0951b54540200052001d9058010b0440a402071008100f01d8941c9018000188001d010b001c0e01540200303d000002071658000340d80d94250a041d00c642d0880c1500060b08040e4512002c0024500c580040503007030903144507050708030426100441c60450240d80d070703101c09036209502034401c1000e03002c0841418002c1d0000000850001e10f540f807031074807003040e00003000500320b451 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 9889737 1250 9888487 9888499
    0x204170609030a05071212150305010f02031003021203041a07060b010903260706050109020c15010302010806010c0809030607020714010305040b0c07080403050102030903041d0f012105030403060506 87
    0xc01c400590200464a841a050781d40619100743c944480c0f842049001001003003210202c1c00b8007505905c1c3c4221420455030390044d081052450403ca42541c15034164004045e104006203d40c164211030321008680c4d05440d0440b2105001010b14210b016503031080c200205040032004525003003030018030f00350f0b2190a0800c0580311b1080115144441400300809030701649c0c1c000d218841c20702c0f03038285ea101c2400141c40d10381045580e440c0244c590030390020309074940120b5410001b250a019030440c0001d64941101c166146800007020b10001170700382410301888070418824828250204c442c40000035040f2115030a221070020361b1450075100d0400c10408084040a42e90321a0017020300681d00004200c01c0398940c1100c0004d46e900c01c038012100b07507508000000005000707002861150365282d02460710340d840c2024008d88469109010001d141c00c04040141000b620b0b52028150782004405040043c074603840b5090701c640c0240080e140740f04c040380c0007040000f207400442c4110f90a40d20 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 9890987 1250 9889737 9889741
    0x50106030c080102120c03060d02030f0a0b010e07020316060603140703020103061a0904110c070303050d14061011070503070905040c0522020a020a0803010b030609090303060a060e030f0102041706 86
    0x84600701d000b181c01581d0140b05401c04605504084070181d43c204100074914260a0500d1b40003914080500840104603040008637100380284520f20900506070030042065518084500039120f124000000c143c0f0100d6028400c1403003015480403000c0d41d4041c06500303808041c4684580e5501c018032040f07001a00700000414022040d101001c03031a821008410304084c7d000081101403c03008005117007158003489800260141000840e0045002e525038555810980b4510802d441c124001518606130440c20f2150702d45038040d01500b0921203103020f0101c0c10803000ca40d41465015800558036126002d80810241c80503800750f4040ca201c0d81d0ba5003602582d0b0004d00007030000c10034103034503250031041c2441524240c64004000c20031880c4191905c22009542d441c49035042038000d8046e00c0c0c404010041c031410b2020045401c282c44800a44c11442c2110024800e191103005081c20020300e0042d29110b918100200944032680d50000c1d51602c1e201c0305110302290070380c0a4100301e4030403500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 9892093 1106 9890987 9890999
    0xc2c03010f110703020c0102010603020603130f0c06050c010e07060206010b0a02010b0a121406040213110d020705010506180403050d0b0607021002010501090b0a0e010603050c1204050106030c 84
    0x2031900c820310f90600a140c641044141c44c15607141610074809030740e800d0305680d406000c101400084030080c0c9402da01c240c0310b00780d0013483c100040f0070200e0b207141c01c4805842c032800c030540200b1078021900c034019541c1c0f40511803400540c00c554010300008801600a1041100c0c50001045018103000820814880c991006241c3c0c05c56105c007408000c41c0340010b480410044000740002c6c10640c000400c0b000710082a1101c02d59070701c0c880e02e88400003205889080c00b501c0011521610745051850207040c04843c2c291041402031401c00d110300025020380d0045400d83e0f070312418a8817200c1148020b2141e545201d5000c0e10505c5410300503035074503640710315214103540085071a514220f2440192401d002e0498464044080180729502076003050380c3c1181c50614010030584c03120f610407160740c49800c0580d1005001082000305000e0150044001c991062080705c0c040c541e140c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 9712237 9892093 := by
  have h0 := BRFrame.cov_init 9712237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9712237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 9712237 ≤ n) (h2 : n < 9892093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
