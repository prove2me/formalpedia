-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4641
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:16:27.790977+00:00
-- url     : https://prove2.me/submissions/93ca469c-4319-4ea8-80df-66f161e01a74

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 834532374 ≤ n < 834712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 834533624 1250 834532374 834532393
    0x9090209060f1b12031608010b300c0d060e04020306060405101a040f0b07030f2f0717030c10200301181a0607030e281d09 54
    0xb0010342c1003e000c800d50f01c00503d6041c0240903003070003a40109850029200e540c1c0c0b81840042c06c03408a92128001000150001000000307002000d841c9544d484900c030b01820313079255845806a0700403a110000440100040c802c002498000170620a850300c0740078840300f6078034589035580c110129400b07901034128100040b0640b40541c8215400f24202c9000707090340d616400d418003240da81e07594017500140006400d20680c41c2c0b80b9071744030003445950981844c0507210354000f44880140c0316000c082c0605e0740390800c52440b511000380c1004801d5900c2c01100c0099a0149948240074803580048440b0342e242c901908001000b2a078094410300c0040061840d003002c00001041c00c480f0320b03841c0c4515219040c269030514001076000704101d5055001100c0800000006c4a2459004807428051034440001c00e0b221741059621080d018200f2a2940c0c80c8000070611103180c40004200f501c0c001c84407282c00204200d00c0d41c041e80d07500320030300d44030007001c2d20f0700c81c20080143d4001c0e0881c0d00c143c184 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 834534874 1250 834533624 834533647
    0xb09010c0f02040e030408011e0507050a03110d18060b03010b0616060603170d0c05090a0905070c2906090f0408030a0b0a030f0515010f09230f01060909020906 70
    0x7140d5114400b800020b03d0400c0408441e06680107504500c7c00c0e40d440d018030a940344601000011907a901c000d0402550910310b80c042d10a108080424043c1a144c1c0400c0e0411074010701690041e5108030801d10025080c0c00c804031040c418040101d07140c80c40e05400d01c10a007414400c41e801030740090856490001d0742d90f41d40442c1d41d101c2008540c0e258617500040700150b0316603038801210b258051041c0c1c88212a012080940758082001c5040120510026000c1c0d91360315183c10485017008000149929140001c0354031618610019140c4036034481c0c44118010b8100d400c1640140000e0b01040c6901d0384000c02c410090160b60080d000e1111a02107400300340c10070000c503002070b0860030008035441d0100200e1140d5006900c180e44c001d10719441503003807080c00d0062090031050b071404040250f041c00b080c2c03060300701c0038020080303601e9988c4072a407501081c01003000a40c1d0b900c0b07490701c0b80c0741c90407401107440b441c42401500000b074103022000070003802c1d9001351102444001d01c4d444c142a0610304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 834536124 1250 834534874 834534893
    0x50d020f0c0f040f020a030b100e030303220b0702030406030b030c24070c0e0a0506010f020d03112a0d180303030c1403070c0311031e0901021204060206040303060b09010c 75
    0x7141a0f00a0741c807200800440c9140c801001d541c50b098402191410181c1c0030080e204041c442d07080188215131245400555000c0101c0744d0041143c2c1c010810025030f0f510000c46a090564020419080c040500603665000405441110405d65090000f64003c900f1305441d4100c031f11205420a824541c180b0180d042000c400c0b4402d5840340490f414038507543c43d03402da03e010319405440c14042c0070307050109034104c030302455034005400e08081540d80c80c3c2507002942c90306411000800c0558603d20896040c401c001160a41110403003c0c1c641b400e880900310410b40740f80c512110300d510600b222500d1480c000c5125404042c20b00c2d1000c2c0c401460b50f14103801405981c0d0780c00b81005100c07102c2112600e501c10145029110030360752441141c06914010b4840d00840402d4155540140811851000e09941140105410414940d242ca40c604010713442d100112a000114960204003c50581d44c00030b0340301c3c403440c0079917000c3c800c099586440111300d210360304105000902c51100312012074825003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 834537374 1250 834536124 834536149
    0x308041802091509131a0f01090504020a02010b030d180e2203020c0f190b0f0d18170f0f031305100903030e030f09120312070c050d020f0c 61
    0x80e030140c41c040c03003440050380702d80c3c420141d04003c0030003040e100300c181000002d01031141c4a00340100a18803095a10b030301c0c0c1070100794039948100c0503000c0010951f4441d6401c1e00040c00080c0055490703540e1076002902800199038807500074412407000c051524824410b400351044480040400036090138a502d5902034001d10b1072a02c00e61052014a00c4501510300d820894040d50142000c4813030380f0104a04a040032401a10030441c5c081d400e0b135189040e000074802c0318549003180769110b20390503038172116008400226103c586800c880d88141340c00880e0009180f441000300c004034416421050030280155500030480d0301081c081b00d112004180011500a586500440440341280c0d07202c0b032422101c070340034040250702c03140a5810107406020b110b40100e558000780d41091041c910054150184404c0503100700b04c16410b00807080c0c0d09004036155640842c842e0020b514240300b01812002a10308211002e124075090b4007030391840480c07260004d80d19040600620200d0030100f2441000710b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 834538624 1250 834537374 834537419
    0x415062a0506241e041e0f151203120c020f0703050106140414060103020306180405070513020a171906080601060f02070608040312111c15030804 64
    0x6400e8021410820480380304008500c501c000141565043c005081c41d05003010b4011880652a0801420000c0c9100c21020054a0028030341c901c0c4404490f00001103613046560500c1c011203582c24001076009084000c807180e00200240d582c41003050a061340e1481c0c06800203041c0015110041030030380095009541ca0301c1250345207110980c0450800383da0342d000300c40d103079580c3e2000c21240042c2010007640754011034040241500e10320300204040d4000348620f04040c0d0000014030140d079404040d09042809400ba0036480c603061400e2a134078035090040030701c138080c1c021800d10303400f01c01d0080765902c11107070340c581064503918100050a00c80240881c0c0484403820807142c103608040c420f08008050f9000200529458030101030180705585601c1d03000c41d00040001c2c000d461300500d14580003649460316890042d28503150714000c102c031032141840c2e0200011040400c0305810b2800800843d003440800160740410b91500c104005031100400c5440180010000c0c2d184e2601810b1003c0b500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 834539874 1250 834538624 834538697
    0x60e01060813020a080f07080c06070b0a0b0303070f060b03010b0609030a020405150409060b1f140304050304030b15040509030315040b0f030d090602010509160902180a14041506 78
    0x480d40c0150030036040c4240c800040e1f002075410490020100b20780032002c842070721803901d80725440d1180703440c450008060034521170301c8103d0658251004c10859400701c0d0084208102031486140c031001402441c0b10091080d070070071280742c415203401011070b021540003d0007000018815400d010144c00028071004504c502081040c3c59074455000e0041c1c010301c5038000240320004001003201c0395100b40500e100c54a01c0030009001160000d1440f0386542c203002c90385407203598600e0300901c1e41c841c03070304018201d00d189400d0101031609411131a1901008680c01d00441d070340e606400340d803400100c0b07a0215449a5260240c02c0381404e80c08004a05009480104030000c41c0f0042840d103111480740b500003404045081050310360a02c11103030810140805080e20295200f1580d0341c0004502595000b00e5002502c42442040d04040400e614405400c0210b000c0d030750684002c200c41d4040700c0c580614202a02180344003042683d0350182c600b10346446040065008080411000041240101140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 834541124 1250 834539874 834539879
    0x6120b0112060b0c1c0503040b15060714010507020d0207060f03060308070f05060703091a180607051306080618090f0f0a0210020c090c0a0201180c030204060e01060813020a 76
    0x11074060764010b40f003c40c2c0f10994a40446244624182ca001c591042400040f020031103c0c582c4001100e030026000740b01070000e0380b1183c441800c002040d20460384d202e01c0000381c8808111558a42e1081012520020022680c0721030050703032103001800aa01c01604440800e1005034003900f008002d08400740350024809440b0390f140e91165001c2d500070340d901c500e4804040b0400c01c0800045601c0b003894035040c0440c001558410450004509850b0103102c030000000d0f01803e0798041c1d21444800c400c04540040c10a40005001503100e188103044d42c603281400407032050b000e2a000750082c0300c0544820111119070a465400c1c402c06409180c0c2406001400c01c1c2d101820401403004440301c40240050141c80c0c07040041d002c42901c0d5202c1503402501d4240c030342d5543c4296941d03200e40c401e0602d5a6401c01c3d40c1c0224010000104520b01a001c0051000c0600400a80c00f9040c5d85c42950108181511100f600300040c0c8240b0a1100003101400050b00002c40316a803034100c64400b900302018681c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 834542374 1250 834541124 834541157
    0x60e06221113140f011b2301050708010e010f0605040918020303071b050d08090909030903010903091d0910090804030c0608040c170c0f18090703030e04050106120b01 73
    0x40701e52101650f50a0b041040503903140516015225410908003002c90810032080341c6800c544560300500000b0203071450303018826480040050b50394130f91008004900d001080500600c0d802c0c000c143c80d03a0060301c00403420301c2404052900341c61140e1201828240b4000b2030401800d1a0015015204098202d07840140c0341000030780001c521618400022002184001c3c0740042180d10040c45200142030683c003141c5120220717108103105840c07a014a54a001e0518a9841000100e541640c40c1c03031a100c09044d40240303103c06559050804884251b400307110b00500b0341080d500140650010000b10382d1400040d4020341016104112407030801d0340d2070300d990304000155400407010849450030001000302c40c03180400580030700c0200c80816145203c410355510701c2140454001d1810112003502c540d43c0d00b0440800901215100c940d518241c0b03000c0343c59030350701e100448c046500303400b0645151805016103410307104507980300c0d940d100d5800d10341b1002e0070300407030228140110400c4021840 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 834543624 1250 834542374 834542407
    0x4020a05060f03011503061401120e070603090b0a05010617040c090c080604150e15041118010f020d0c0609031e0f09080c060d09081c060e062211 64
    0x5050784102078403985820703542d00c2d44495030b40c540010141385c20010b1040b44230201011810100230301e42081c0807000d1001c16001041c0c590440003143c403881d000094240d600d80c0001c04010321a0f05a2441900d520150201b078038406c0c00354102140c01010811482c12074540c51759031080c0140c9000d050f60356a8074000c012940c0c00648070001030101010450141494041d00010000c92200543c002e80381c04825020758a020f48800e517081202c03111603415913610340056444542200c14540e40f0742415121403001047c0c404600d0100e03081d003482410107400400d134541c5540041d1030b0141c1d4000301d655208010f20740c0c80d0044050002005036020b040f00d104140031011417094031061400049c040c6c0250920b40c056115038407541c41146107810300c0d16030720280c03a603011007000041013080b42460003d64030f0058800741c0940d44000c80e0901e0f076051590700440c00b110450348c0403004588444090095100304640012015001929036080b403480c19030000c9031075909841c641c0d0420b901c0100c0c1c180700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 834544874 1250 834543624 834543637
    0x708030403030b0a150210110d1e051b0f070f140d0216210c030b07030506101419030b060c012304050718020d05090a0b010b03061804020a0506 63
    0x81d0356112500d9060901d030100201904100d203207007180d0040100002c7d99031108036002429503889a0000c41302030a424141d0300d0014094409011204a100100d40c0e00040e60704000742c3c4c5814140400c0a911041c2950410741e01a00319541c641003103480c105030b5960060700101d4840800f9116000480e0054030ba1145019481020f000760741c0710703030600901d04135007038a801d0700111000d0ba0400030411541c03030b070301030880803810b01391000102c5041004440c06150300c05000c200340481080320644d8160702c028844d1004803010510000404012031b804e280590f180e90901c4c00c10440b4490303000203900100008681440c020801c0c002460100e161034200d0355682c041d81c2e4450b080855250703a1000880c0d1a0503c044080500b407800e0f03200c05691303201c184241210140c00c82d0130304070801c19540403102940c6850307000381306a050803d5441d03510707000c84005490b0b004191002241c00c00005040703e0090704024242e03c0320b1203082207221002d007030140040745e0205040f0303000603103502c441002d03020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 834546124 1250 834544874 834544877
    0x50d0204030b1806070c14031b070f12020907030b0d0611090109140105071b050312090108091f020a09170304030b0f0c0318030d1a03070906140105030601050708030403 74
    0x2c00b8248807403407800100800312000d1060304280104100d40e0b85c40020043d030030380c00c00341d007000040f03030032441c207041d0703c1080d030381042c403640a50141e1381d80100020001c0c21600008030701051160386810394a034a070012000250700450380c0c00880d2290b8442d801401d81c140d00180005240e205554550007100c01c4440410305901011810107015070b000901a0000c010310100e0134005031902000030418410f04100828282c031031060603c03201c1e2030b80c90910181070058100d41480003400040300c56178000701d00300f6000840003000035034900780108420341c4818400d150101c090051041e004041e41011300f051081003035500300055601202e51019040c104c5c2c0d440910fa50f02c5c00c50400c440364075001804207100c3c0441034240101b081c0300c0000c5a50150400800340083d0351102100380c158461201c0c0c099401d030804038806583e10304800446c0e56000100c044408180c1d50341c0191003561070780d04c01e02c1010790301c428005220f9401140156807028052514515041b1180e4582240d50801c2c0e07020750 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 834547374 1250 834546124 834546143
    0x1051302090307151220030c04030605010305030d110c060106050f1c0501030b13030c030e1503040311061302061b0c090c040501030515061b0c0d0b090601060507020a03030f050d020403 81
    0x31582005104c50040fa030341005106c0010420440903072000001c03014045224000b00245035000004259400b543e401101413207156581d0400503540e0b04447c0980c4410380c90107007440084441c0c2811120204291405442c441e881c0c036071305490b19000b603100400b400104010120b550701e13859400d800501c51400d0005865411401c22094144008000c1141460034401c8d80c404030f900440b81130101070b03062400603403560154002c80c0b11510011640c0e103080340040244000c00d60022400c04d4141c0541c402c60340240e46000c0c0c54140c1d408010070181d00325800b04064900440c01e11503211030040003c013126060700d0040c0c0817400c900030032641d036540068041010700083d80d141c011280c21580c003641c4404400301c55400543d09105030b00701c03049144814000451148000d05c15040440401020428203840b03600702000c03011001c88140340785004420001c50b009028006a600803a0050805103c0c942140c0c1d0588a40310709107610014085c09000710b0740c0744a11800100091403243c2c0051 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 834548624 1250 834547374 834547409
    0x18111306090624051c020d0f0603120f021204090e010e060403050c010c080609060402090406031b0603051006090b0c0109050717160b0f0703120207050d12050f01051302090307 77
    0x82010100340561800c220080014405c010758103907000c014070716035480042c3d4032540983d46900030f0005000d40c1000b1401e218000040c000d0854a1000d040c159840b20a0900071022040f80c580342210075480c03001c0010301c014001d9800316070140098100c6940005402082401090318003071084800700c00184001485a28003042170141910209a909091180741842000601401c1c002000640900c4d40811280007a680b50340000c8000d60300130f0f0100100307064031141c11480d010342e0f00030140441c0c1040302142c2d00070410f640190031200959283c0743c4550410442000c40e9003c1d0306040c10564850340e040c4013141e02404100000c0101c541150141c00c501742c039403401c0c00380b0491003240c0168500020002c00c0250011200148039410070350742d4410b594601921741015100181000d0b41c4080744007010480e0010f20091160407a4035034441c0402c2c222000c0055610866201292000d800d00402440c1004c0d0700d000048840e2601c050300701101100804e00d09480c0354400740d1800b0312855030303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 834549874 1250 834548624 834548669
    0xd0b010f080d0806030703020d030302070215190509150a1106070c1a090c040f090c1401030b033d0e0c12070602030f0315090106050409181113060906 66
    0xa0b00c42d0041a41030600b43c0c0c2c545400081d49404440c400a801042e810b514081014826411a200b9a5000b03103c00d565034000141c5000b581c2120318501c10103090b40c3c0a0142550084017034449450f4003c20701045489034854034007084e0044440d140501c80c007440c09443d0503400340201c1d40310303d6032075903400408802424424031100b000381032030022540f880f00b8002c50070300129041d141d118041e600032401140015255000780559407018041c0c4000341d0f008968602a400540c2d09a1000d0380d0502c04400700500b0592203c003085081740300400d45034080401e502d540802c010048981c2c10300700031480b0084100a0583e0043c412000154002c1082c468092414804107210721411900a0640c04e080082c040d44d40e1141103082c2e400700001000040400041444200010202400c070b50640e583d200e4028240750032a0080c02c500d40d0800300044500000118550502508640030304c814054003800e01c400030304c411000e034180b0740d1100300104102c440d43c05024018103200e4008045440f26205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 834551124 1250 834549874 834549883
    0x9020307021c05030703110c120909010902031e040f0611031b0301050a0b0d060308040b0706050a1401140f03010c0f0e040516080a0e161409160e0d0b010f08 69
    0x40ca0006618600110b0064036809410f4035404102c03410002615080c00b11100070304d0242c800c904015201d18040724603040d4883c0098880c00e001a030740128580d894040344400d0703000c1121000c041401c1c1d409a40341c101100301d8a55042030107071001e0354101d54951941c0c019202004040f111095001043c08014440400c1000038541c081c54600e0440d41024001100380c841c5100f0070801d0100861100318090143c0d00c54402143e12034a0540c0c4c981d540c0014070510b0b0444070f005d0300d000c0c0c0340030f000490b030746018012044c5101010304140810303820282030110140340740e46100e41281c00e200b02d002042c0c4003403260900044003600c40c1d644031003404000820142080c1c1174207000e50308140906c0780d0440070740700da14221600c0d801e0a00c426620038400038020110005500b1080c400e035210302104082080a0b50195003541c04c02d8411000b01c0c02c144a65414103031906c84100383c01e50500145070b48910b40b0307000f134484020900e920031441602c5003100c1c1c00c0b083c0c0000220000f550001c0014620420 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 834552374 1250 834551124 834551143
    0x30c0821010e09060c03070309050114010305010903120b0a0308032e14040b03030d111908160302120105040213170105060913030206010302010f03110d05041401110304060b1206010902030702 84
    0x10300501080c40e001d402a0054080038105000381900c9e00c600008201c2c0a400030310502d0300c060440001c035079490030107070302a1940d40350075001f2074024145e2114030880f90040b4a007420014100404840c910303500c0c96402da00041241400360681040150b60308202c0f04940c071020618443c0f192114145a41078000921295000d88254542900304100d5140070050700d004900800b000642d012144001c164544240a0300480c240e04801c0041740380c1d50080490360240030000329078800d00c60a07150903000c0b40b2544400240010548004000d1494580c004080e071003030701034503540055560325800115890b081100c202594440041200c6402e1660589911092102180c0c05920b6580c5010303490304018080a070404c1480383d4002c1c0c042d070080e0031049483e05c491500e2580c80150341703010401004241c808484905800b58014801d2034140500568900c5070310286181d915075503220402800800c0503a07400000d210030080d0400170901101c0d000304110b10025030f4900e000c442c0241858600e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 834553624 1250 834552374 834552391
    0xf030901090c1d0a0c020a0203030304060e010c0c02090a0b010e190302030c0a180b030319020109050f0304080c120c03030a08181902090901091b0503011508030304030c0821010e 78
    0x4003c80076500306080040c64000f010315000107080d003020303141207040c5800c908001c3d4251000009200411095a0090402e450458000c104481091400f00da01307514418001c2c1d80b020038800407a0082015500040080a05052010301407074198045980d402c030a03011001c4e80e0786020010410b43c1018886417014060494440c6506070034040b5402460040000000c00d81e0b0340c0b00e10050307450301d040086880226910710046112001290000e001e0610010103c42c40d001e80c1548508040f00001030b00c0946070b5050103080d001140b642440203c074421043c12560340b1a0f403607800c0741303901e0510050076841010398a021441c500f542001440c1c120042c0301d290a13521000a100c140c1701094a200c160a81c100d80849854540c08819801b5064280001d0310040d20a08024088042c44912004803503080c4d00034840d1500c402c50400840b500780c400c18806800800000c1d000a04c1446c1d0001450700c200c010030304002c5c003400402c69610014009188924001005000b11036143c83c80e1580300c41c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 834554874 1250 834553624 834553649
    0x3411030102131a0708070b04060c08060306061002070b12180d021002030402121c0f081501051315050a200c041e02070614060a0f15050f030901090c 65
    0x51545094641c0d200d0303c41c580e070601a4121028150410504582c240c41c2c000402ca600c45d0294100114180ca06072400c8815600e80309901c1001801a00c100c0e106103001030181c9069510b000c2400841d1040750341c00000c501942030007141d040d1911010700307800100f506406000b442c2407a0304140d102c59455454086034414500354850a0307000442c81c1000c04030701c8015880303444520100b82d0741442400015210f014a10000c0b010000d080c03079a82e20140c19550302000c0d109800402d41d8402400d449404203506e034441100b6041d4060401060a031050305024500b07940e0715054446600d51121a606c0000d400084c6031100c140c1c45101090308001c0c21008015180c4202055a520040d40035030710b000f6070f12110b0320070862003494420b00d6a68120030043d5940c9100b403810301c0080c207001c034540a480c0e02e024042049401c018003020241c91181c0c002c4100300b8101000081e410f0441480c01040020400901e050b07082e041d0085c5000d2007800002040038801c510303011980c40d10982180804040d0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 834556124 1250 834554874 834554887
    0x121e0b0105270f1c110f0609060304050a0b0f06150c0c0909120703090e01090b0307120804050a0308030610052508070507030803091209153411030102 66
    0x14841c010404000030386420590040d82d038404035a1940c0d0041e1020f511002d1489820340189018158889541c03081050384039401c0f980d0200180c0d21303141c1444541000c820306c015007090a00100454005008408a411081d215512000c50040440700e4942810750482030004900700315070f00e03601c42414450000d08025408581c1175039603e680b85854410704401010414a001c140304154074101c404110760f6075800e0500300071341000040e100301b00c2c10003191000010080d61034030a9100941000f0701074030344989041c8481603d2103443d8400c0c2c8048004000c0040c2659580255000540c810210551207107000000c02004e8020301c05140181700b410081c0046001410050742c415a03004115003c8018050900c1c50542c01203c4000b0103074401c22001006202c1041c001d07611a40300107040b0b03103960340c1000703420a050081920b00d03a0030000c0da50030039402e0600704015240e8251407500340500f50001186000c032104449000c0d0628100c0708445c2800d1140c40e01d4440080780c004d50080d4503298 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 834557374 1250 834556124 834556147
    0x4150501080105190b0a05040c050c0c271e040c03060f05091c03090510091502090307030305091309060b0103150e430e0904030915121e0b0105 63
    0x79807240064804c1d60710540d907440e075a10180244054400a04104544a100b41001e0425400950a028a40300d03c00300c403101860300721503000752003042200300114021285050407000c0d40141c110b412404010402c584281e40e1082420302c514001d04020040c0362842c10903c0c00c0f503c0310080000c2540c1014200304400b6070001d100c0601000c0c1c030405000540d00844200c008101c40b0304000c10300e000f41c40e180d0500c2c1101c0c1c0c000000d04ae01500020381c902400310503c0e000c0744182d00386180c05030440d40b0308201090040c2c0c081d0100d03c0028000c9614888400b58800c1210b100c1a011035550f079803140c0000c4a07581c144140695001c2100240100500b04115000b40d18002080c1045940b40e0001c880e21514407103040b540446400071100101da01d6880061920410f41c030b80d2000004c1c02800951440c3c601661042c0c0980d4041c0c41d04031246081c20441e40030740000c0d03a03844041c0003140d0319510004401d4400c00d40c0e0b65001d0381d00219803800c0805440161000440e07020704000f010710030036a6a8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 834558624 1250 834557374 834557401
    0x212041101020109050106080d021c0918060801180303060b0f0f210702060618010e06150c1209040b01090b18030a0206030108030d05060907020307030c0809060304150501080105 78
    0x36086006000034284620040340548068500204203500b40400020380d12000a008030710521950240c0d4054549045099a40070b03d6424000004d0b2240c5070401000001c1513814545890048011030003649542881e404d4074041100d000c8040c18980510041c15070500c100300c05010300c02101d625000c40802c5400a40c081d500260030b2800700041d026852442c240307152030b1101c02a03003030351000e071601d03160180d22004101c60301400b07011100300c55140840750896036816185409441025a1545420311110803140b802c00703030181f00200002800300ca010880181449000c454940d41c0b03250744018402654000500c0d141031209403001844020080001e407820740d13010b801d14495002c1180d0009190550211019400100020000c90a02c10220003170904e003d9a603014422522000184540b4180444480006070414004500040e01c14100030f40030754011060642030040000000e109580305903801c80d20f0b580910280700341c41d00b003806050300500c1c2040c001c0005240800488406 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 834559874 1250 834558624 834558631
    0x25231b0402042706081c03050a0917090d20010e0904030806130204050904080a180e0106030c050d05070309050610030308010b090414071101110f07060507050705010218090106030212 80
    0x19400c40503200f035458125803104000b0884501142c030300500780580d04030402004108000042e08020009010702c10b50b0058800040d4800403030050700300380d0380d41c17000b092f04840310050380039039140c2000e00841d00c0c40c0000850700d0020b0515605503003502c0005000080c203641c05500609004040001003600a02d090341c0c0b02c0010b270381410420700010310341d2000f44565001907074042c0b8484c003407006100d001c00183c8a10520354035005030741d01c05040180c0100256109608000e000580144111031081e0040074011113181840e81c00c201404603801c0036034004039800c0300001eaa59a62038117028042007200e400c140003141d0411542e0661310300074513a041c14055100540c2000450b907089413039660081600d00701003a50801301d401c2c8803000500c1d8400d400c04500e03141d820400414484410071085890342e115503141d15190038402d648110142c90010000c8080c41002d001100c041642800144001c1560380c05000f550300000c0204096220180c02c42001c140c03040c04444802d1300c2c800004c0c0d40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 834561124 1250 834559874 834559919
    0x17040506060907020703080d090218090c130207060e0f01050f1b0a1e030603021e0303072006030c0301090c090305030d0f060b1602040b0625231b040204 67
    0x110b9070742d9040c1c2a4a810b00c0b0b1740c00100056000240300c1420714030b903804080400e20031683d49030795065a8660202c441e1090310941d2213a000311044044034a8111001258008103803400360910310180c480344204e801c1d13190b019003103030060311a1031a070580070f101c0c1c08d0b4414031444401c5d000303041403e880c003102c2c079806111810030400041c000700300380d0048462540710310b02d603010403400020000e0000c0180c8928030049003c1c0b129070143c00d40050b00014101005000500210b0400c0b0894032072100c208035a01c0313034114545000c21105244d44410300210701c034500001c60b441da02c2d450640050201c8040500c0c50040003080c841c1440002c802108442d035080c41035001042c45128a0242401042c0562000e0115100043e000a6440c012910340700f1081c0200d40c00c0211380c01d168244030581c410100d0f00301101d80700c0701148442c5041c4240e229081c0c0d024007424101d0418800740320025040001c1400c01a6000259110103000d21420302c1d44000300564096051031300d4400e0561080100c103c071b568 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 834562374 1250 834561124 834561139
    0x20c2b05030601050d0e0c010201061415030a09230c0d0812150405090a050c03030403023115030209070c02150a020109050a08090a060c0c0302102006071704050606 72
    0x95080c1c2c890016110000c0c140311081046e18818550f643d5644032494205000d5402c0010010300030900e00c1a0034014200a008440d402e440c1c2100303244c00340d0000704100c00d80d0342d5840202c4040307244181e0050400000d800e40d410a20800e4100380e24103410b44e8a024030070f18000d0300100019810200b61580099a282080c03c1519030b03a19004200d5906161950031501e40b008004010f0b0340014807814860185054502c2010f00300b0500d41c5a120310700000c0d4115008400c800d10004141d001c08040211400c040c40d68641000d10a40c2600d203040b07000004030751844000e000f03502e442d8a80382d070814480c0c1465401c1c180c00703a02041c0086580404a01450804203d00069134000e40121151030f1b80201580c1104401d841c0c0882190011411240590010940030035510700803010f0b04001d6412440303074540186180d081110000d5070903094402c01005402741c081200210074500020005040601001d19203030314020a10b07659140d0000c0c00c0e100c2141407001046c404200d040d0403560949028 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 834563624 1250 834562374 834562381
    0x311040602070e0f071722050304180218190b12100602010e0d0f0e0d0f05190f11061209070602120708040e06190306020301081006150e130e01020c2b0503 68
    0x9039140391070f000407d1818500320064410488040001c10954008030b5807200d981200b00d6000049006400004c2c1e1200071426514500785089245808106441c01d100c803072031034031042c4843d125004403030300d001604160018080c48010702d0305d43c400684150f01c02000702211004030f0a5448408030948424440304041240750b05108030482410804080c2c59403550a0080c42c0c100404c0c1e0f2000c90a03240c0d80102080c42c204445607d8000300c810381c11201d900d030180096200c800c04c0448a0b41c0c081d42c841800c01c14201c26a8901c0311a51151204c1409800d00b18900f050190800c0a000043c2c40340700401c0081d54002920442500e0640d20702c540e82c0110750340c4100c0405d00c50140090303006003400006400008002c225001103068800c1c45050740d0f4804c401a08a4003078540034000c0d491110303070900700c5120051107440c00461008008209901341520000c1ca041240c80030004541a40d400003201e400c511001c00c00e010b050070b8845168a01003210b480950603580070b101d00341c020000d000010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 834564874 1250 834563624 834563641
    0x603040f14070b04080604050105010906060f03110904181a131401060503030714070b030105130c0e0a120507050f030309010f211a1f050a0311040602070e0f0717 71
    0x410301404105000e550b544e13841c2c00758255946012034085039150700b094000b14101d0503e0140c801202ca040c1c0314511041c060340c0d01900601340349004410f008905000010b4038bd0707910302030004900341c4819002010b00b1941030010f00d41040d484030501c44000c03c01440003500d298502e401540740c00203207048601c0c9891013481c0c00340c805688240e5041c4030200f0f070201440303190118600d030101d07243e00f1104030a42d10a26000240024401d06500460340200400c5c00a91a00700e05581321191a240c04190b02880000d40b40100c2134111001030211440080d0810008110030f031f001d003100f103901043c0c2c550181d0000340d491207007041c02410800c03401c569100460052400106c1160b080360341000c07000f03007116048010b2a61030342030b81003896000845140d9040066518404c0c40104503e040c0f40101e0010540c1e0350b074400078070b04040559030342c03208013413041e03450290000d00701d142c2c0507000052070b00c4542910404060704481a0040000501198603000040d85071000c140159101c555a5050079 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 834566124 1250 834564874 834564883
    0x20705010509040f1506050c071a0d05041a07020d090b090d02011b1e0b070e1f17010b03060406061e030c0306030210201b09280b0a050603040f14 64
    0x28401c5d100e01031940114000303411402814212a800044884542d0b03220031040c90200550180440198100801c0008000e5904480e0340240a003100781d6660404400b09130141100f100d0f0500143c20442d041c802d0b613a40807501030000e12403528140e0030a841c05001a850b940b012100030b06001b2645042c5000441454407a481250080004101c040200d0054550000c2c10345080b80c02e114108000b0340c221380a5411821000c1c400b0b8180361501420525404940340d10b400c48030103100d0a01e00c20901040d40c4448540a01091400340d516810200140001d881c8590002030500c069004068040200c031030689e08140d401d0b20b80802c0c070540d26041903000709560780004c2e41220141d071415043c542c114200441441150751100c1d00740c02005034243d11014240c00c0c1035071002d40b5000b80090341c6800054150085104110038010f025103c801c0f616040403001000c2e200340c0c6400c618801441c02111542c002c24003a56001e02d1458035644811031003150550040000b0250040100301c2e200c20030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 834567374 1250 834566124 834566141
    0x3140d14070c12051c050702030c0109030908010e0a020904081e0c0c090a1806052d0103171336020d180321150e16020705010509040f 59
    0x90003024141030880e401440024016003d90f600124905150354503840398044812481c417801c0050107100780c4900400c09000054045811880184002c40d0360380400c0c418446118880e8681010581ca4500e07080c0c25955100c28046807600f06108040158883c0195207030302690281213240c0d11074204490036400781d0950f181c00c40c4035a0104841380002000180c420703481004550300c41307199030f8000242c800c2c0c80b41000f0752031780001070b2660500007805580104d604002e031100c00340c0050401c01c4149141040d0004040c480c1600c0070010001e02c410002c0303d008804454010074a40002e40001103050401407040051254140b03448010381c3c0100e0860f51450488911002c0c0c1c801d8a6203c0136000c3d40091100142940c0340140043d200407400885843c401d505480c0c1e0315120f00016089400c0003100805040e1882e02e0b103882d00f0a031010480e01c440641983c1610010390300f09080c0841b1000f075111003820555121300c6043c040c580e040b10035920603035011100807800c94400b68540b0301400ca105c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 834568624 1250 834567374 834567401
    0x306060a0b1b012418060305100b01120219090b0307020303010302010804022106060f0f0d0201052a0703030f0509090c030901240617041509020f270105030a03140d 72
    0x144941c82c03e0201d440901d0100c5d210304150442603104500074104451880c48010b04560014104103001a0181c00c5035481c42d030141400d240c1c0d42811071480050380e2141010407190b00c181219070710055002401078000c0c11048454606500d0111000ba40d00c0c441808040d041c0180703034001604540d180f904030f1401203481c1840c904038049401c82c0c00d590300c009171f501c070b8070400d0b03421958031241c00c00000c203040711900180001d031092008d80040d40c2c144d00800300040041840c1c0c1c41d0000180307500c0709134426408084020003415156090080110054030707881420404100449002940c4440b4025002009008119901e84500a80c2e0340149200549031070000d0b0302d408801816005c10710900d0031541c660325460001079010308040c402490846008140880c41c0d400140984116404100000c0c4080c0940300c10010120001e0980210f0101e6402c005101ca0305041805078200034260051809030028607000c1c40716540500b030010a201049144240480d5040550409401c0000c651450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 834569874 1250 834568624 834568661
    0x306011a0d02131e062715050c03072a08030912010b13050f0a050c1b0a020402160c0504060501020a080702040b040501080708070b0a0806011209050313050306060a0b1b01 75
    0x80c04d9908070000d568411071000c2440004c0114030803103e20004150440d200c038a90f40b0860500000c5508040900704020811000b801004c20b1264104000d00820f0300901c481e1070061900d1450045100c600d4260f841440e40c410002c101007070380081505c0d0400c0c02103803e011650305406220303005002c0d4051165016000d00c4040c1c40c440c4d95580f04501800280c47c407050b9070340d1340018000540b003007502c0c402c1c0f0707480d4100f01142a8407029641c41c440c0c5141c0e076083c0c1e1070490700f035000103044c0d0704240013900c03071003112a1920341000800e442000c020300c42581d040c07045a1a12001035180d000320791010f0821440058038004650f51a405000750700c1c0700500400055071510311550741e8001a009081c458451404041802a4018140d5044d04925501c40b41c5e50780d108001120b40070075200700c4a03030040d206c5400b500091000d101804080d00d4940558200901e028109850210098107a034003d2082c130f00c09006202d4103100301c4101c41e82c4181c100b8815100040444d0043c40700b10716801c6580f00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 834571124 1250 834569874 834569909
    0x20603010906061106070e190801020a030e19150c03021608030405103c111c0e030a0e0303040e07020c1315030311010b120106050306011a0d0213 64
    0x98551284090f10b059036a80740040e081035000c0c0380d60340400e035011804100f040700720444624204051002914505062198140c0e5500c00542039030004005100403e0711100d6040348400304104849008001d08040d803001c10300d6880307645d40c00c02c01780102503620781c03160000140b05000c0e0701110042038080200044507a40707400c1001281c0c005590481e01800365004444013610640154001a40441d025906c51200c001c11203500360161030400d0f0004201b1181100000f0552245601c0c6d015004011503440c0100215001c04446050704800300d6440d0180e001102c110010036a80d845a0600340641e0b05040ca00c002803450066030300040750000180d040001880d4042500d9200c1c80040c3d5090120260f250800c2c4d094843c9243c4882c114586c440042000c00c0c4140700c50f1806200d0100000b81c214400008941e611800943c1e81e2042d179101e240c100500c2c00c04104841c010300408421014040207041001518030030b04001500e400c0d00810b004900919032481100140391040140c00b4000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 834572374 1250 834571124 834571139
    0xe010204051c0605010506190516080711010e030304060801051c02090a060306060905040519080d09050309090a0b0312070203070b0a110c010905100305040507050a0f030b06060f0f0a0c02060301 85
    0x3580c0102c1120942d050400000350381c104182038800b1a0200720b8080c55030103041750111829041101568100c0345031a0192000c0740706030380104980c9005104030440003610800150a03000c0a400c00c500a03841000200045580301c01501c1c19a182250014605d181c00c4005403940318000401a51042da900c0c144805424180e21500840744116024000c2c2d9545410700743c12540100c1d000340260304250090140541107000501010303102c2c101e07a50400701e00d2461042219500341049402d940005880c88143c50201e80d030950142d83c404080c082d84424002003501c40c40e0043d42d00c8000c080105a0782c04640d01030052902500003242955150340c800c46000f4601d00300c0c0d0074483c0c2c89010b51a0407440030b5205080c00d409a404c09009925000d080c01811002454020000c0d500d0f40144a0045010b42e60000e40c072009104034015400b4643c21404c2c400007081002d0b00142c80313201708011101c142c2041078103a8696181c0c000100307499440c1c100041c3c0d40e0740c5071a440291300c50400400401c1d001c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 834573624 1250 834572374 834572419
    0x21c12050c0702150d0e1f230a023403202a0901060516020402040b0a020d02071d0106050304140a23070f03080a0903050a0b070e19090e01020405 64
    0x15001032105020200b1186080c036101c0f100f00a1030201f002d183c0700425102e2880d50002d40035011109180000800e01d48035520440a06440300c0400c0740e000030795442201650303c2040d6074007580620015001d60903a2407480080c10021004040c481d6800c1682000c440c03e860003101c508074001a03a0b0143c2d41540069051044000202498400768060740b0301802e040b051075050764506e1b25003501d420048800300c24043e480b0350040340c0c056020400402c00c582c1010141c807412185400400d2002e140c1030001e820820240c004e248480410781c41d14010781001aa81411540181010350f980d444906107680610141d01d04110f8a01c1190400c804200c10740c100035101d07044510640c1d40e005040c5402a48809440c8120b0a0750031a01d00d0030300c041080c1400401e0b810060b0705161200030790380c1e61480c0c08c0000c2d00d5015a0014070504c204511300f90404845a10020211740b4030035080104581c80403182110f00804030303081e0752441000c140c0341e8254100ca001d01002480307032211190716201000c10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 834574874 1250 834573624 834573637
    0xd090219080705210601060e04060b0f030703060e0405030d020901050d05100801230a0b030a050a141203040218150d0605011706010b0409090f020904050d021c12050c070215 76
    0xe0340800720344c0212501c03e182c0050326000d058082c01259107440000c84522400005440c0d203e41d80e060002203034003420000701100070105001d030b512854800005400c83d01c055201001d100581d500b00030002c2c0c80070040f500720740c80c00600140c984203148012103a9000700c0615030750142c41c00c400e01480c068001405012039001d4002408603502c400038810500b42d844d1184011021004042070703129805410004210310080c044030b820030980d13110145001c800390300545445203500824100c407041441a02c4c964481c0000d024514102640070643c00c9101d40c000b00c0b0551190808541c144071221840d84042078000d0035510107040c1814400000c210a00c10068140358a1001c011707080c02c041422412503c2c00ba02c40390070a442c040170107001e400000070803110022045090300060f60341c611441d0086004600501203d075545d80080d181c49034503a120310441070a00e0040100a074040805010f90148010115164440d0261781045014061001f0350003605100348440300488a0098602d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 834576124 1250 834574874 834574879
    0x40909050102030a32091005070503040302010c09060c02090619080c0a151407030908010f020c0c09040b0a0b0f0405070507120507081e0d06090218090c0d090219080705 74
    0x8143c5a980d01080e0111803103451742503007502c0c10b144c04038500d421300341d03210b52000b0958844660600b48801180c2c0e0456101010038808001d010074550b09100381c510080b0305003000c1e0140c5d820418050594a0f42030b0009102d106420000303852601c07005114030034030000001c1c6040c01c60301c414807283c80b40030b02d1200074014401c5960002d1520130031540b542504015844444031039003001d10800059000c601305405202d410a400105c40c2ca092240038031000c41c21f6401038851500103525402d24000c0c0400a1040c0d14070b034148008141021403107600f008400000182a501400c04036a80c84802d01103035a01c546010b04200400390482c3c01450594450b02d10f030001071140000644e03d0740103194000d02010018007a484004038548000c9044802000100d410517503c480c0842c1070303c6c2c0d03a800511540340c010079055074203c100401c8410a1400711340c03108071460b06050541c3c031ba0007540310b8030364450b0b20380040d41d0a548034810b0040e0000038a2500300901500c500586039030354071a2207100d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 834577374 1250 834576124 834576131
    0x80717040f151d15070e1809070608150102250306060b18030604050a0308060d020907210b010e060a09121101021b0108070e0112020a020f0d050a23040909050102030a 73
    0x815802011843c00b40c82c07813080100403030613101d80d04d00315542001d000c0d40030b40000000540a420501d0791413814442e200590080100304e060001c000c240c010040c00c012045500c800c140001c0307a030080f0ba249054175007602403103c4161030700500300c1c1074101036102405142c0340ca0300124210600314011f10007000c0080c502041c003d07140050682d2618102c0d00503000340c01c00750341030001074402c00107035401c444014011240030026030009080302da4103071407280c049840d41000c060b8451078003075849548810310314104071481c4060006400c2c000300600d800e1054200255030320310b040c05084020045c140b08410200070030001d00d8482003034145408103d01522849036505c1000050307512464a0803410303556889036482d03490f0195103816500c94124140940c04c1c5a00100003550700c003502104a10750f009000084550043c542040402034280d010003800b0452082c42c11b402200020319800d250000e01d81401e684801800140140d820001c4000e003401c81d03610074020150041c0d4000c825048081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 834578624 1250 834577374 834577421
    0x1031e06080d0801060804030509061b01050604051b0d020d020c0111070309050a0f0e191107170a020d120e030403110112090c05010c05030c0703050703030906080717040f15 76
    0xc1c3d401d0725091244000283c4d203180043e00080c440c1c8041c01c940d42028100e81c4c10403c000f442c5115102c0c130b203074400c01241e43da04100411803038107000351504108a40e810000170f1030101e03a00c0d02c00d0320130180b081000a0300090b0010000101d54119024030200354001c00c950b42c1c42e4115080d0581c031014003600052200f040225651500000341022500d81b010702da891185408507083c12000014140d124940401009030307005581401000414005034001e940d4070300d8149451030b0a1110301c4059000c03140244070400c03000c4e4001482c03480c00700a40c20076400a811003c43e080140549513030407191030001040010070800001b84000c040c4100740c8412420390030020304001100c2980c0d4011700700c00e14850040055501808141c180d00d4043d5040e24502651540d00a18016076070b40100c07003d0380440d404005041e4414502c101a00d0346240805441c14041c3c001802d0700381c06400e200114062101003000c00103524050b1070302c250701c1714211409031b00a949442c001c2200a403402208400203035513 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 834579874 1250 834578624 834578627
    0x6010b09060702040c050d1a040606020c03030f07142a0405040f030806030a0b0c0d0e0f060115170708010810060501120c050408060a06140f030a0b0601031e06080d 72
    0x2515030214014001c2070030080590200005040e424501409009040291000760021801055000b80030140d11000d4840a8424001182c4141d80814115080800780900c02d039008001c6070b0312117001c0c45071251104613900b005094200c81e20500d203034a21411004100c81949074951445000307030040b070303886c520f141c41080c003041d40e5086030010141d8500400c4140000c0c01070481c039800c0580503013180d4050304a50340f0140d5188042d110031289501c00308003018030529a014038000301c21004003414014004042c071a88d1284c060103511903050b80046261003940c410110f070241d101200701100051300349201301074031f444028080c6524038003401d81c10548040e464001c950840d00183d48140071510200c403803c00500c045c01e00c89041000c200310015100604201d5a8007a01015400042d0726140921032241486108001c602541c25111441110f40d004140803241941114404c1c0c01e0b5914500124000d00008a00444984030358488011071010303a807010068500030422100c69071031707000c0c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 834581124 1250 834579874 834579877
    0x1b0a030e041119052a0f12120a0f020a050909160c0602030a06031a160c0803180a060c111504050601060f021609020a200d0507051005090f06010b 64
    0x1000709040d0001c0090440c1400c001d42c0c0040000c00700d161007400c11504445c2034070f00c541440d80d43d484484100f44418840344050001c00e20f00303503540d0010440c810010b440110207004412201410b1501140025042105500903141520078400110340c0c40c1c00346a000703080342e04209001e85c0600c103083c0c002115076046401c070404a100b00c2d121040d90140c0741c0c0e500030203584010300500c410380e228200000040d4007042603801074131545210908915000004120758010403e1030000c00448034810390120301d0401c1281d402c0340721454403120b4180504c610b640b92100c0c181c2c00501c130510305244001d92950012803041c5040a00050302c44944154011103140c540a039070180450304100c00400070340380201c0b400b42c070352105801602d1094100400c000c6c0c0055441d0700c0341e181749400013078425281b0340c01203503c1c0c5040341c22250040c0520107400070079500d41180312403100f0301c040054035506110080280c0d40c002800518180914030300820403d40714109140e1200030381c031521002154403106d000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 834582374 1250 834581124 834581141
    0x110a05060913090c06030207050f010c0507030c021801090c14030c181201021309050606130e0612070810050907081f14100812090f12031b0a030e04 65
    0x10241410301401004002149210001c0d50b450b007507440e06540001444d94844034010449a140140c541c0e0250800d141015280b04410742d03c0c0c4d2402030140203080d002815103002a0b01807900942000d130b03d20129075103401d0914011040303055480001071140c420f8120408694040d074075885001e490310a46e100602040e41d82c46110b51040c4490390403098002d030300c44100c0d200107110840c60343d64030000c03508a80c00f0180e02036130704003602001d005040103401915008801520401e00e8085c00c03000c103c00180140c0100101c20301d0f09004568165200c5080820101c00304007079401403503882c8082079991800d01c00100040741400d0015508140c0451305c4d204440d06140a0a54a012115440007050000c0c4403c400130342c4c0c409100c0c030340c40140400d8a00c01c59203402c01c00380050504240300c0c504200c540c103c201484040004401c5034441e01550b280080c0c3c16a4141c101c0342d1061744081c114050200c103200c0b0044101d4020103119000580329445174000c5d103c003520701d5081400e10013a07800c1034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 834583624 1250 834582374 834582379
    0x150a0c080313080d05090105010b160b07050f040e1b0403020310090515010e04031206152f0718050c0414040608061314010501080d0c05070e0f0103110a05 68
    0x98056404218160025a4085050804085104456511100607401c1088545401c0e9034407410000380e02c000b4402d40c0c1c007510103256130504100c02010a5400d40d0b95400c4020b0a407401403010680450250f0141c40401440403c0c0e1034541d501d81c845089250b004690078455409510001100da0491104403001c1d0307a006005440e1644103c0c482a0140c90050070849262190181c3e902e400782043e8140d60280104182e070321085e042c01e0900901c43e0196548440880349001c0080100e10b040b004c4e14a110070040c14001c0305140c0000484000d00f0b103170069401350000c01101005151760209001003130b50340b46802c90401e05100001c9908440c4100c4146032152030802003030100c010070f0303005030f1103564004002043c02c1d5150798945040c10b4041c2c6403082804040c803208010494810320022a68802000810481d850242000d0303075100600c200d40180700b0f42c07144100a209003441b1074006000c1d98243c40e022410645515803101c1001d1209542d2043c002a410100c2e1901d00a484201d4100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 834584874 1250 834583624 834583637
    0xb0a170c1f08040807020d06050402040c0216091a10020c100903080703080c090a08030a0e180f060a0902040e18010516031503050f01050603012a03050403052205150a 73
    0x8401d8161400c0d84054001d136403d150a000040040c1c0d9403c8901c04083d00c50000030170181002e105000646008446400a54125212505102c4554100c110480314405008958640c0c1c0310b0310041100700d072002e00340e046100b04291103800c0e600003900080c1d5040580304110303c2c3c8080d0320219801d0011380402801c0300410011840841d20914090340c0202c0a01d0182389451101c00005442051590100701950004580e18000c190042c04815003060291080b0310001454646103103a20300051200300c204007041c020500c55110520b4000c09400441c00440d41c450300e40050072000721003101c0c1051058403010b203240e0164018044c0d140245204400c155410b50380f035506401524180000e14814040c011000011860800409800400c180d00009181c00c00c81d0030305080d02c4014038181c02980c03400061002c3c0882c3c0e642d084d1a021060314001031141c445141c112018440c1044010008640208035540348502222800c210b8004454540f200c0184101e00503981c001d00100d00040b681 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 834586124 1250 834584874 834584929
    0x30f0f090302070621050a0209032a010c05060415020c0d031e0227041503060504110f0603070302030c070c0b0a021b030a141c09080114060d0303020a030b0a170c 71
    0x2946d4104c25000380c1200000b50509982c180403a1406401a4a81c0f2000340c11000d80c2e00801c08514620240b0071081ca00401000519225190350f04801741008144054403030740482c0a00d5030385e0589491100c110141c4da00f044001e60300030090b214408403050305001c01b00d00290b8241c201e01c00c8550440e200400600f0b0204500b2401142c0c100180003a40c1041d180c420301800c1c5c080c00a0313500041d6206100000311410035040c52007038250140c101501625030710f000d040c43c07a82c804040e25448030300780c54013590300e03170329103070102d1060050160062140143c0e110228482001d2009400414001d6085a0210f200300c1c009a64221a41140f070b81c0580201500c80d01142a00316a643c41310f02c40b104588801c0314070b1210b154500601c4040000055615906000da100c080c001c003402c1400030f09842002d07080183c0041c0402034650701c010305055002464020860103a007001120f02801441c0d0308000e956070007022003580341240c81c1c00c400e0141c030414a00720700d4100f110300700140122004910000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 834587374 1250 834586124 834586187
    0x10b0a090e0601090302090a0609060b070c121401050a09110904020a18020f0a08091207020102070b03251119120503070908012d02090f10030f0f0903020706 69
    0x741c0c040d184504105910b000400940c0316420010b0198540410014a42d890005a402121110341050f003030b00c00c007000f40c01c01044810100c801507520508000650721a1460b180550320f4507184003032850750a2000b00410807807940d00034182c0328020000d900702d0069040030000f005034200d600940c42200c3c46c0003480041015464000f0740705501c200141342400180c502840c940010806200042c50202000290f15081c4003118a80300042482800e01a091380040d459070390318021900b0b00800400000c0c042c1c50001c0e400509050a10358010100b907283e18020f01d6030613407104c0002d6038403a41c1110804008081403641d101c0c2e8001501c040003040c01802103032942d1018000c02d01f0402d8800c0c000c03d01e0b44080c41400da01494008100c40852004140703502800c11621401d01c0040c4180301c00c6010303464014200c6039020703040321601c00300030080805600034520862045036141c50301c14a86402a843d0f44102e200c0c50083d02103403e00e03070350349101300c038042e1070021a04641c20402c0b01d05140398 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 834588624 1250 834587374 834587399
    0x91c0b011a03101511070312020c0d0c06030504020a03080a021608030408060f1e070809011b020c22090305030f01050604031208061f020607080106020c0a0506030405030d0221010b0a09 81
    0x4001c140340512403c030752410403a1408200340c009550441008da00b420302180c04011301f00388000c0c1640c24142d44002500d41e5052481c585c4204820b243d294800075085595550601014582c001341d030755140d9140f22002581d070390910150415142d14201c022032600e90020998007140d0b64a4020042507035603846802d500c1d440034004d508421507003025007840000700a03400f4400d09842d40c501e103075441d0401c800d9003920144409820395000c41c0341e0b40c600d001c1d800b04900700343c51000d40e81040707140c02c03100b50a8200315801c2c00000900c0d10b4018071000f05a8410000c50286001040041c65079885404002c000c1c8524400101081c05c081d85c001e00503030141110701e510050040903c002e09419660b00207030b24071811141c200580041040000094000e05520b014100520042c803d080e1200081600d81d81c903409007900c07402d030110010f0100700b002c0003150884000034000355110740c0410903081020b1605591200d5003a454000030030303c042000256003a01c411596100d10312484c00c0388920b0b55 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 834589874 1250 834588624 834588659
    0x11103040810020f1e0a170609040210140a0c060e0606030a1e0203100c080a0e030d020d0b1c0b070f051c2a0e0a0b070305091c0b011a0310 61
    0x1307842e8180000c030b408403800010144080e085c030b071301141e0b5814000401002c0000e84c0222008005861050088e03685600b6202a4800e5041e0345482c2440b5003500256204004c4040c0c191048900203103079504a9800742e0480705180c0304540c2480076103036421006454501c100c1c1c03590b405a200c3c02200003c00c40008030403140700380d40f170f071448c0c903000154011a00341401c1c8050001c0700c03900c0319251b00e103103a801882d280e4064801d1504000740401c103400c00343c4070302c2042d1161034081e402003004012140541d01240d0406401000104068400502d0300403503020780b2015074601da00f61f00000d20b41c2d03000f114a000c04680c50b42d00c0520f800c0c404501c000d600c1500980e880021640c0b009036074200e0159131112901400080c50768101100c07100002401d03074400e118a2405044908402c0003030701c0b8000251080c1703e50504100703450710140d50100d0341d2038038034201200a8480440014040c4a2003141d10707810380b03101041c2c1ea024050310b00b80d100e6151000742d0300d01000c00c8450703d00300404450184140c0b90b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 834591124 1250 834589874 834589897
    0xe070501210b01050d0c1d04050601120b0a0e0108060a0e06070804030f0921060f0c050f031b031008010f020f09100e2101050a1407110307020402030a050601110304081002 75
    0x45c1421903000d101203d82001c901404102d81448070000c0b1a90810004c43c1c1c04c500703d40a00281c5003940c0002c0070204a54100c03070046880d916040c0c81c5c1d507075140d003a10142c180741110044669440c885580d4403101594290381c2c0d07500d0b01405c81c4100d41c011580310320982458a4004090702d03643da00b103c9513458100b0180c10440c1169010443c4142035501055909049421400005450a0440407903402c0035800300c0c0c440c64180035501d03594000b0180c42000301102c88040d12583c0c1c0968000b010840112011105200042004a4881240030580c00e032000b0340c000308030703000003800104200d200e000c900040e01403051080500d285490000c01c49629047e180c44014030b074140011800c40300080541071002c1c1c1c40d400d6040404a024842d0f5035000180348001c2c03200002c0000d40b5100d6a0020b0140c1041051f0081030500c038440802c121600d5aa01402c00c555034a448000c24000f040e040e40e0150000301c541c200c1f28903040c000010740c0c0076a0345250203001c1441c01440c00300004c1d40901040034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 834592374 1250 834591124 834591127
    0xa02070e091f050916150c050307050304170c0f011407170c01021c14270a0f0201080f04021e22020307080a090b01050f01030219030e070501210b0105 66
    0x1800620404803107150002c071014049424104000320700d00f4a206807084124074400410204203039854224011002c211b0b0382004200c200040c1041d0341140710700e150241507072100050004090802d040102e020006880584171030342e1440d801c118007040317400c1259001480000c400410340c0d003070400600c0c1551080c0380d42e00030254402904603068002112480d1540d60205d00340c04c0402140c510710008028403039003000310340d101c103070420680a070103015007002c03128410103035410b507410310303800805010031000303c0300009010700e050818003c40b250704070b001aa04502040051042d002128059a402800080360300844410030b10410612500c45030b20007500714403070103030700314090001d11154000080540d0f0780c94401005008407001428100000d480c4c0344245000c51482040300c0c5c15180200c07164246c41c15040012006030090030700e21203080101007082a4429016070080d01440802d1054802142d6603000541c1c2c0140c1e1a41c3e0315070b04040d2502c00584142007580860840c0d5170506000707 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 834593624 1250 834592374 834592393
    0x6090e01060215060f090108100614030a082b05151c030305060423150909030f2115040501090e0613030507080d0b0a120510050a11120105040509030a02070e09 70
    0x40e209003088e4040e002e16041140e0b42d407035204090140c100604400400c0310540b400c0840030a0f65030b400c25002426101c004107080082d111410141c503080440341c540c45160340c900701e40c0b100c020101a03580c0700004c1c400c185842d249040c00d03101904070203007034032024072030000c1920190042e0000500702540316940700411a03409007640000f1000d03080000c20030714107140c440b8002102c06407041c0424414640c000030095188400021101e03607408500d100c3e40c0310807480080d003138a6107421019104500400c0204401c5400f11802603504000407201400542d81c0c610705001110440c40c000d0300382d5000303500000e41101030380b000c01241922a1410768900341d299207a0700352640010031022074040d00c1d0381e03000c00145003c46640002e4800d0322044500004141e403100d60310b144100a07488155143d400042001c0c0040d400540e5043c114080c0503039803074a01b071400c02407190900815203c5d5251101103140d040d000011b54002d20015001001d402d0b003820f95041c2f42c1e8030001e142e1300c2c080c80303120b030750 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 834594874 1250 834593624 834593629
    0x110921011404150b100c1e050a0b010b040f0506031009020c030a080709061e03060f06020307062405130b060d05150103090b0a231006090e01060215060f 67
    0x3081c40d808203031808001c00d410070b03107044a00c0c00038251200032010300f442c1c61000300703a9031600543c024012501b0f020450748664074000f03029840007240a000708110003c040180f01000c078a10a10070b01c0390484101340e0f031721000c01d0f41035805640140400f00c001c0352024070550525500842c5c00010034a0b2410312550b4499811080c0c0e03026208112007500007240951103140c202e880d00d60002605e003058055141048401042290385031030301c0440701034001d4101da010b802031f84000c0280818400300040180c4903880a5074039400800110b44152400e21175402180c0f05400b00301c154007202c269405420301d003804000c40c0f91484081894071a40e1458580301c2030343c0b031000920081c0499140880c217440c1a8036818001181c413011141072600300724216001905a200319a402880c02100040308403c84815285070049011070741603031803028040c48840c05402d851030f4112074160740c5841c81e040d182d09036851103440030300c1200301580c0085540300c0301d464008030280d403200c0080c2400700ea10090200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 834596124 1250 834594874 834594881
    0xc03060420030703090c0f123005040f0b0c070b0a021005040b041406070917070306060915210f0f0f0b040203060c0909220c080c0a0911092101 63
    0x5450012940d01c0150804105821021b50300408081403a124407501e02800340751006417803d00180581d059003034240e0143d90301c80a004008522180000c05550f010002920662280c01041102154203200003400a98081102c240d00d070b0321005000c001c0d1800c900308125400c00b818000a40c010341400b02c0c40c4014600c07900748218002ca01c0310a8605103820690400a0303882400e201c180c0107102001450754008191030103c1d10f1a100801d4143c2c1c101da0b003203042038225040141070b1410800005031804043c1c00c506806030494040c00c2103540c0d62000b860100b50005031002c0c2d0183d541030301c0c1000c19861840183c10500402114070100c8141d80c80c400c503c407a800e4122009404a402d00095040c2007122a83c0803650800781c0c3d18000b0300c0300c0003420300307140202544140c0a1141c602d070803040700c043c26850680c0d441401c031610540c0741c843c1d0b00d0b2290303900404035024050031180090a8030440c0030716001e415520640c503181c5400002131200c0001001c51880c01c6014200718000d02002c01d10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 834597374 1250 834596124 834596131
    0x2190503090a050406050d0b10050310020301140a05010f0f0c060f020c0106050406080c150708160b0703200c0c06040f0611160b0a1704140609060c0306042003 70
    0x2009180e803442064100710300500a500320f41d000e83e16165060100e52621002e41694035000215550340d0341c0d0391010300a0841c6550069074240c092000480015940354001c0c40c181e035a85400782490b81d03045130501240d0710030b906c5a1400a059188130020383c5015545a40c81c80d0050b151600030403800740c640905403074000c40341900310343e80041c80078000ca0080c403404002d800125010b02c4032520300f2030a10758510003905800c3c4119612902814081c0e901e0341103507111544071840c0b03510f4040400740724040170b03c020300c141d17058000e54002441262191160442d600d01c0004a42d0804030300c01c001c80000c1e000208840064820807840c41e40d948e0344c0401610003004011a0000b40d542003d0000784214000c4488801c0d56001103083c2141d6a5040107580598551a03245901c1d24200d0f803013144c81c2c6502500c03600f2801010710610043c0003018200c0d410004542d4121416a11690f0031159200300484901c3e55103501400807414510307280d0026440c180008601d040c02406004047c2d40b55402527 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 834598624 1250 834597374 834597383
    0xd06120c0303080a06080d0e0a0e04080403051b210f100203062704030e2229180613051f0501051305150f03070309021201060303050d0c0219 62
    0x2090304000300340d070180815500c5481e11030b060110310319003180140d8a07400d1604000500611140e044040d840740c1b50044014003156180520604240c101180a94018041a1100d000c0c03a03650340d00344046c0029140600d6405445c41740300c00c1750100c20404510240d4101c0310701b8051440000c030100c0c010004982c42d18181980181c0d079060076070810042d0b405040c0b54002850001888010305901031618980c040c0e01402e1030302003221850000f94468010504106140c00c4955000c0d82d04145d1b0b070700019210644da03c0b1983c0041ca03d01c000f800864030400b03015031105d540c4610100341003040d00080d4001d138002c0c00c1880210407000c3c502041d5901200c0e40d80c48060385903050100406c031000c030303040100000e08044d49005422440d84400112a026250041850120043c18505c8480032202040c001500c001c5d00d0b0308001000a01801d40040182c0c07054085203007600c0e00b000103218010449a064603404d207040301d1078003407401900241d0b06507029070007046240e000200d000110303d0021b5104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 834599874 1250 834598624 834598643
    0x61d0d030c0e01140304080a032a02190807061a0a06110705090405300316030609060501052217060702120316051b0d0e03010b0d0f080d0612 62
    0x1041000b0601229000c41d64100462091843c0c01c0300050021240c01c1600b00c1d0391650f48000b50003042d00904406100ba0a003000741c3e05100c2407016250142c1014500c2a90941c3d903590803202c445000314850800180220b03804002c404001052540248a804542c01103404d54880c0030000aa841c40503520060224416204062201c01e044c40040302408003200c0105060405440d400e50781c03024820950032554500c2c00086801900c11a04540e5541c51681146c6e641381c20030000700350b03000c00450384004c80d0901e040407031510407500440c015580306a44031400d00380c920300150007500c95613099484000a2100200e41086008882401c8601240c01001c040c10308500c028a8500d00c60401c01e1101c81c18814081f034404829804150142c03940740035502c5000d070001080c0040c188003c0d030301e806d00c22040ca4040058002c4920200174904400030040380401c50148144c0d900b88840044c03458400c5a00350000940450140001440c52880000d5a40d2115050b003403401d65510113480c6401c6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 834601124 1250 834599874 834599891
    0x1080109020f03060f130c0308130501120c230405030a050a0b0f090a15021b06090d0908070519080a0f1217060603091218040b150304061d0d03 63
    0x510b0b050741e496044040d001008249032641c040c0c49003480282c0001d203505000024541440200c1c06a540035503003121004d9923a80c865a410b1503420f40d54030805001c40c5005005c5c070001291486507030011300c03007602ca50b046841400d905541e034054440c2c2030f5028210901c00400d09031401c101202e001d030321802c010300070600039080c03000103848020100c04040d9000c008210082c500424900f200e40da214010070300c1582d022803030802a0280355841d600400401c0d40e854800c1a00281d40c2e0301900710001610106d480c008411540c1d500240540d00396580096070403c401e00f004600c6109200b0701d00d1140c4c1d401501d42007868240002c403e01654507200030554003042c045142e03d1400050514200103841141413080702800c07500c018803907441800007000181d41c128051200081ca00140c5120703d80e03a00a5409200004141040a600403442c2c000c0c010210304040b074880c9840e407500c504182c2550780720b5a440b406051a990000500c0c003180610584c1e05c0c1003044904080306464801140014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 834602374 1250 834601124 834601129
    0x311032a210405121305010e040209090a0c08010501020304062111120103020109170c0111031312061b1d03010b04050c120a18150b060304030206040501290f010909050108010902 78
    0xf031144c12800a40c404002991514601c41200b1003100c2003030030424050b0a290b40001c00038043c0d244615001440a0100100e03a020740c0d120b8036210300c0b00d4a9010342c80c1d803208012640e174040c9000e00008145046808070001d008091405a005040e400200320b103c040040d50003d5080190341050317400008005108560304a2000e4001e00200a0361301c0104100780102c0d0f40d69070302e0312400c40c180144114401c446135818001c071403c03654031401c0440081d944900711101d0103180300d002d80c0c0c250326021002076461400e01d00100d140c0705e55990030402081c0b000c840c00d00c00303100700c6030158159a40c0300c40115645a502075240704000b0003145c141c076110620305044c0350f100014110b00d117403807506545680e210410340508402c1030b003020380703d1000701d400444030000704888412184d2011003c81080b08159001401a03c11403041d0002c0c070076a80020394001004444006d8092007400c0c807807a501d0079082803807864859840502d014661541d07203007035240c12940203030042d11150751200d00d10003e60 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 834603624 1250 834602374 834602383
    0xb041d010503010c0804060b1f090810020307170901090510020408010e072102150414030f0a030c03050c012009011b0f0615080d0c030311032a210405 66
    0x14a0309400138044040000801400039000510050045540d011110400d03115841e1858070b0404403984400302c4a2040009440b00e07400b480b406e825071140b6004400e8090550003a24041e4140d5202c014411000301c0d01034000b02001040302900e0740d40c42c09000c0201c1d2040048030707050312a102005075601d0620340030509660350702d403400c04182d0001508120100b040685030744280300064003401d18484500c0020040014105000c000701404076011440410807010405000ca0807000c4540c50001c101e20300e42c030f601d000440078002c503050070f1007140800e000320000d01080130701c2000000d09540c0101d10f206501450038500d4590f21000c1a032070245d50b084500d00ba1840484050050492010b030b561403881000d58400520890312441d51582d4614104080c00161a0310420b07036118103114200100480002c100a40009041840f8614558001811070f8010121009074000c1008075140c0c00795400350940000304a0502007010769251341d44072420103840342d208000c004450409040544c5803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 834604874 1250 834603624 834603629
    0x90501020105100b03100f090f06080a033e101109030307020d050309090c1e0f0306240a11010b06090d03030509010605151207030b100c020a0b041d01 66
    0x541e07242c01c0c14000040e0f0302c0861031084801101d406590b994030603c0580c6c500600e6441319424440b2044041103c04042d0004c1101e5284000e082080b2555034111a035500c02604018001c02d4080e4244814002c0340c200c07510a0700381030400c0c0c8050007000004510030f400007038040c003426001840200c506240500810344d140e01c6014629082c0030390600040c0d02d0f0301c25958001d114121100d40349042100c1401a642500402080000d51b8542909440283e501c0b00c030b104421760035412021100c11002c00140c0341d905580b40b0b080d5003159245014000b509084266020041d040030080c006207200f108003e081513806031780c45038280302e08160100d0a4598020780640f00f080300b03220f244026200c0010700603055805140219168031109441401440b064018503040341c0e0140c0301d5041031460a0081102c1d000e25440060303d40d070b07074000880481c3c9014024541c041100703000303410701502c04d1a07985112400141074154455a4211101699015a00010400052900e0b20400214400b5110f00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 834606124 1250 834604874 834604877
    0xf1e0809011b09170709050906070f03050403090501080a33050a0b0703141204060915090c0b0a050f0c07030b010b1e0c010207150e07240e1302120403090501 69
    0x102c0ea90007250241402103140903a05002d00d4810903242c1d51041000300c040102444001007001e42410001952039000489000010910707104284a103544a481168030654160359005070480c1088011030344840e0160a08000d291244052401c01ca10000500d01003225441c00028a4460815900303140c45190b001c18802d03550440d08005d60000e107400c0310758540d45880d0684000085c00050089406082c81c4084464051010407081000952050b29410300503600f200d800c98092181c403055a80d1001c00030460f0511381c0382000001c6280c005401d003d440360805509149400103c0fa2031500600c61412082d031048900308203110680f0398403405840c01c0e03105e0b14602020b03941c003d0700e00044101080b81c10a0005401c1110358020b50546a1680e03100030568600d800b282c401c01301921040443c0d04d0079000d441c1c000640c43c880524148240c01c0700c0800050041c031501070540320204420040c40e0400103114400484188610052801c1181c110042e4007605290400410305201c5400550 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 834607374 1250 834606124 834606161
    0x609040c022103100909020d170405150310140d08030a1409030c06060f0109080a030306151805130b060f030103060507080f06120c0d0b062e0f1e080901 67
    0x507003040d21803404000c1e84e24450303020490b1b210600c00b1036204169004041c0049160a400c0b940101c0f03901c0051040b1841150301040351108603a8201e80b520003540c1d040c0140e80011402c00004038250209481c00310002c1c904030485029444805940c0c0c07089031001900c81e50360741c8035200ea802c00042541c100503500021420152504000382e903c0401502603071191012030b04950b6280e200c0c1c41100f001e01807070300685952140501d006005030000e801840008401c5291880c2c24500c50040d000d001107c10002d03510207072805051111040301c10488202d01c1c2d40f03a003602a425102d0100400d20f0000d5103810702e9503580b440c00c000d4115800a0b011400308110304003404548616240308681008044410300e0302800082101880c2c084018809900541281079050a000a02580c544070707100039185149940e50750307520515441a64038040d14200c15102c8050306c620312680044100c50b9003030501101e91202140c1240c1c600c210300c48180005200320040108840c0207006038000c40c0422444031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 834608624 1250 834607374 834607381
    0x1501060203040e1015030504030206160903230303010816060e0919060306050702070614030903030f07090504021201090c09030503030a0f1b021c17060f0609040c022103 74
    0x29207a00c035a10403200404045000305600001e905166002042aa80382500044c078101d0003801a10040310b042c1d0143c003030740e000a10250030700310b2032071848480c0b81d81c0c54080350308541e60107181c0341c60b50207217a03060100c80e030b910415001e007000158080c06110380101800d8000140c04d0b03000d40e40c0c2e40c00041c10001c01841d507280701c0c1c45501c4107640102601d92000001c10704003622000800185e80094000e0f4142401e01c4280381d0041510f8040d503203256652849008500c5c0d00c0c04083c40241c410490b1603004100042500c0020b000703440d0030007101d1400b24000b035039440016041ea080401d48001500d005001003008440501c10611490003600700700c04d00314990303190180c4134000106181e200e9038030780613445c111007074550080342e45403200b40030030220420f4040025503a80118000980c241d01c0c803868280094002d24040c0d160581000184405595031420301103024800841036820081c103201150155449009940103404123174020592088860031440d400c06c8050414100e0200420a1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 834609874 1250 834608624 834608627
    0x6121718010525061b09140d0f0c09050a0e010e070302090a020f0315030f0316021c20010f1106060f060f03040c03062a08060604080d0201020408150106 67
    0x10400380000c01d00344252142d000203100071040d1660b500103001d46078032070040030400004d41e0100b114801040070402c0045140302c2d0954600703200340548091040b102e115419030f86090014907400c1e9118802d42079000f469651184c0303040c1004e8125982d44e9889a00b0881c07840214030800c0e522140b9440240300d640345125005864541901019001e05010740004080400d0358044603440c02e10504107940d24074050401c6144402c207410f03031a10a0161000322502c0201c0042510b01c4a0b040184406190784550b003040b40c60f0b003000910030000d10349202100301050310381f00c030101445940203000c501c90342d03403200041c842c83ca10307808070007070240ba880c000750740303040009100340d0000003910000d03402046003002420718010040038900c400c00c00000c0208108094000c4004c591245506004080d410310401010300340c0b00482c901d0300310110403c154150b114840d030a400600c00340031246000d4441385464140b4083c1e8500b0000340c5c3d00041c08201c60380d000c01c400003c01c40300e02d69410319075060100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 834611124 1250 834609874 834609907
    0x1f180308031b0405030a0804170a08030c0a0e06030a0c020d08160e061317060a140c07030c0b011706090109110105130e0a0903030b030703021c15061217 67
    0x11100c0024075125195010b60115000c0300d010703140c000d00300c5102140300d01d006c10383d5130f2203801480207040c005041041403040c001403403403496030300600d00c1d41103641d10007040845400c44800881003080605500281c0c1e120200254001e03400c800d40460300c40300107078020b03140a42194117803040042c0d0408005414a100103d0310343c0104503d844104148180b000541c2030007010381c0035440d54240080001d94005403d000590f0751010b105483d21582c030720007803408a032a452841d21901d09403c0004c0e2401c0c01c0c00b002000764034407904213031540d10755545948034242c1c004d07080b00101002c4609600341e0040d0410070031707070310610100c024400d0520583e510f21002d400d141940e814807a0100d920b2100303003035200500d00903102e501d003982c0c0079241a00b850700250854060940210745401c0c01503605003404943d2205481e0090941008881100390140000040b881c05440003d00d00005800051040c002c0100500f24840c17180440303a40c5040c100b0031101101d04040b0a082c1c2000345c051603034001c42 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 834612374 1250 834611124 834611131
    0x40b0906032a09010806010f080a0c030f051e0c01110606180402130e0d0f0e18190e03030402030c01051215010504090e010c031d06130c051f18030803 66
    0x100140380c4901920490346000000b01925920200840000c5140a40040c2c8a412590402d5a01d44000d90301d070146500d4503035034400038205c3c03074140c0720600c040346a0440300c0d61140d208404039041e00402c0400203482c200309003000b40741034029030003081c01503130b00000c40c03407210424201610003810440c1c000b4104110314a1416801e0a208002500f59a5801030030305281c5030503001480a9000b803c0c81c6622601550201c1c070200b19a03880398030010b84101c9078100902e03009002c7c20151812001020211440106045c0b801d2019200f0545c4075140c50042caa40301340948001c40d02da0a00d48105801e140f8074030700007410440c1c24044200510748615125802c0200201110007115800c80100c82e14895a00100001400c00d404900543c1c01544000c1914043e83c1d002c0141440c0d1201c51402074200c0303076644d411603201c0c0300450802c2880e1075803c10500c3c4210030040d9000d40d03840209204049003441c2e00301000500361228600340d04000304018110030000300d4000a821640d4040e294040074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 834613624 1250 834612374 834612403
    0xc040b0a03150b04061b080714010212160f1817070503070b120109091514040b0708010b090f1c0302250b04031b031722050604061b080a0905040b090603 67
    0x80301e841b400c2c0300100c02124030715900f05100c224090913501c803683c081e40c07180002c440300c004004001081d62801c040003c448007240e0b0780d0110112500e06c021a5030506c15241c9800d4664003d0300002c03002c1030701c00d80a2170021000e014091300e40c50b0000701414030301164060800c2180420081030fa2042c81c4628606607a0a41e500040581e22800c0030004c407034403060380041451403c280c8070013904c801c0c155644a41d00c5411a0b14140d41c0701c0788225814502031103000c2c40d8410501040c0b9191034500c940c0d0311400005403140c9946007842901d0344812004100c10780160b0403210078483c800b05050f034509580c0d5222601c3d02407261410301280030a01caa8070024010009072042c0104113421140101c000b160001d00c4004c44e6580407860000942c0a0034100e18407034444002c0d0001000341c405050308956004080c1d03410b03c2c0c540342040da9060740f05a90050303c40f880000100004500700050b120302035581d551120300d58202020310003159007115a041c4501140003c00a26030f80005035280c2907a0741 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 834614874 1250 834613624 834613667
    0xc14071d010e063114040b1b03070f050702030a030f140c071505130f0503011a4902180f070e0a0801060b0307090f030804030b0c040b0a03150b0406 65
    0x50a04213148605130b4045004d0350800c280d18500050707514105000368055031500c090b5841d0f0140310014810031b072008819105003407000500060283c64462030010f21402d0461030305250343d001070708129138000100d0104203083c032020f00385540950464405003600004a2811000507107469883d8818480c000b44000481c00d44412188520181c4820310f040d428208100e035110302e00e80c04c1c0803183e40141d0b40690b02c2d10104031815400b0310002030403558042c3c40c0b42d041440401c001c07000960980c080400d84000108103030021400103201060a081e9440d10315a121014410005c0510401213200c1684a0701c80512000c100060388054003c0c016040500501400c44041a2401d445078060b0007594a03051000400c2103a0743e0045100343c615513103001032551900c012a8a000c01400054107920303003072109100050002400d075801c4013083d61601e05050b500d0101c441c00341c0c014941c1c003002070f40f1a2480c00001c601c000c0101c0203444606601410603041c00d100606103114044000710340f111 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 834616124 1250 834614874 834614929
    0xc0607093807050f0a150218040203070e0936030921010606231c02070c030f230f0d1202040506070309170601060c030c14071d010e06 59
    0x9080308642825a0103c1500d4444110002c81030329031960103020b981140c411112600740712a0b034800c403002e0904005000c4412505102803200035000100703840148507080547e01c60503514040c20b24850080507068042440ca8400810070324510f558411410752408511219025008025512607017002d0760303404260800b221036042020b80d03040c0891255440d0900c0403564684c800000f13400350319106100c040c442c5001e84000c1242c4141c4085400e10341031600180c10280c801c2c1c000b05445402141c40c0d008a035100e440303000c0c07815690a005c80d0250100441d100c017488544007211302e042d03001c9000e4111240680c0785c01d03403103000c0a10303140100810007140c0e910005140d8146d0f8007404000e01465118001494064600310700d5024007600c0d541d00301e40e54403990100043c0d00e8103944150743d03200a190a195802c0d240790354100d000312107042c1c1c0003454400e00c01d000c201800c01481e46125691282c44142c4200c8e00b464010382000b844403001030b04001ca103443d0800034074090f60200d000700031901c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 834617374 1250 834616124 834616229
    0x4090b09192408010c0305060d240902130605040b0a06080c0705011b0e0112020a1b050309040c02060a14133924170702120c060709 58
    0x6420084040403001c5040c00310f125041507010208410f502d4908000c2510303410208011180c2e11400288450031586040c1e8042d504907046030803403280c1e89004a40b6408581c002070082000d8011200d002e941c500d807c01007490315025505860206a6044a140c0d00b00030b40280341d140002c10251f00741030001020000c02c80c0941c48884050007284000d600d0041c120740040039440200545800661004640c0d9005041407007207481085a0381c0346d400341e084040c84030140c40e80254070295903e02081c054400c1d151520f010310301901e511035015001c181b4040280314200c4000d5480381400c81040010807c040759601001c0016982044401a110130104001140846040c03030301c0d22901a1010100a0040400b208a090300e80242d6009251800300c200d40b040c0e1945c200c030410000e40600612103484102d968a590021140d2056400b44008080c514207a940040d0315901c2c5540170804000d40c41c1c1c1e001180001904444002c0c044034955494141d10f50b025174803414081000d00e0b214150b000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 834618624 1250 834617374 834617411
    0xc08040f110d0209011d01150905040b1210150f031e02040209030f0a0b010902120604090203010e010c1808071a0c011407170906090a0321090804090b0919 68
    0x2e56000b0800079042da10b4107518a844a249600c16141002078000840c00c038109100d40c40502c0406d0f5668042e00703140104000c0034007040c1401d1600104040d50f2030101e41018001502c041e00c40501c0401c4500c00301e149540ba2900c150711654110008045c00c0c400250303001d000031a501c1010034088011216400010028440e00744280e62602c11140906c2e40300c0030121b00603529a004202c210480d03a80c2c0c200c450300786c0c401c14220010501d191400241c2e0340c902a03010008050028000240c814041e000050031503105210b04008119152803040c0701c4010344829102400ea99801351000c1450150046c0814000d000c54012910b008100148481c000354840c0c10f025004580740c03a50340c2005107001d0300b6070f00300960300e030150755200000500160002501e14090081c88000b00000c2c15940c07400c03502c40d004103044040a141c0340502c0e98110810f40101400b160180b404140d0b140e1408070118225091203a0b03040c001d01181342007100071044c0301c00300d0300c00821509010600c040301c0300200004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 834619874 1250 834618624 834618649
    0xf021e04120204230f04051501030201210e0609030d0f0b0a0521030d0e06090610171009060b01080717010e0c090904110103110408030f0a110f06040201030c08040f11 73
    0x1d24800e04100400045c510b00714500413409101030740c074480540c1c0c6510760403c1003400084c0c0400d50361206211540e80015014202500f5850700085d904484c100d0f29040c4801a10744e104558804601d40344403031224480d200510102d00001c205410301400851144070261266a10a442c4075002e88043d5088070a91a081121002039a5940b2075061508004204002504201d486050000381040c0000100c3c81d01035800c501c01b20700501d20703000d02c1c110b0340300382d1280540660240b4503000028008038024103521320302c64440410007403032171070006000c0c2c44000c7c041000c01103003418842d103070595644041c0c107484052005140365501e1048030010352145045581e000090b9a042000b444503605105c0281e800c01d80c0c081c4000d507800d20304800a80038600440a5580042292612290042c0000c3c40b070841d007030402c00d1029a40606581c18414040709441494211000b000115a414443c0c81030f8104079042c070b805d150400340c1302e10b0508004440001c000102440407001c0a5582c406060359 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 834621124 1250 834619874 834619931
    0x503060d080406090306050a05150609060909010806070212040f0b090111030a0c14011e020a180f030515010612090201051308071a0702030312190f021e04120204 71
    0x141e4540e00d0340021320004280c441500c00700d01d8038000c1101810b99005103805020b5010810b90104980400c09c549680005907060717001400f008426415151002000d000340b5688025181e20f203802800681408030025007004641c070100000d0060965040184094480d642003007a00c8031644001683e0800c4110100c54491002084039600075500c50030000540d441010a500b94000c0b13804d590342070712059038a510407202d07004441c03010100c3c50380c05000c0080c06480d080048181120070264094001e4224aa038905815014003e10030200720030b00d03032107503c14012181e0303600d005c6008242ca42c95440140c0c0700c2d0340b2400014156881602a01e0848200b100d0741d5221507a80e40341c140d075603c0907116071410107210303800d00b00c4102c0f0b1b0303c42076660140d009405540360512035107140c007034440010820001c88803019081d01c030304615445940c14411000c4001a520440f07500380300c090207450b40c40380d403028008102c1401880c1c810145200100e60664011402c20091400d074140a440b0045040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 834622374 1250 834621124 834621127
    0x1906090b07030c060612020f040605030c0105071a130c12080d020a090503031908060a03020d0f0c0b0a03091a092d0307032f07030308040303020705150105130e0d0503060d08 76
    0x586c061000c1c2071200302e40c803c440c00980c42e400c0405000a80d01d65220300ca80c036030461540508154050320003007240300c3c41040d80c0c1101c0c4c003000a02c250744200503202301464141c200079400400c051010820040c02404800d680b00703000741e03640e0507081e00c81c8143c0d0010854000c20b0500c0d089010700d0404000e09030050580b5140c00782d074412260400c3c5a0011000007820003808100c40d800c0018070391090301e40140c00780300311241644401a030703192175000844029040b0301c400141c989008010341185103071a40e01040c440f003142081c207448a00c1e00354511181a118050004400d0001040d068102c40c0800d424503130f1a25050303940d01c000d40242404080d01000619504041d80200402c40101d0f80c0005640710100e00c01d061050411101c00200b041d901204003440400d008d240004e9201d40b0a1070b0140c83d1a500e6500d0b54180014589400d1810b00d000380142704524000341c2940d01140d00742e004100920924480da5900d4111a910b40c05000f0300002044164994040e84210207400c082c205 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 834623624 1250 834622374 834622379
    0xc150d0606180b04050a0b0c070909031808190b0726011e03200f04090c0611150612070b07080306090109020c0c150d06090b1906090b07030c0606 64
    0xa80406075022040a042e0161030011a00d81064019141500c10141c41d411b2541d041c00d15041080d4414041c0c2c0ba2a441600c0000407600c0e554061000024802c0c0d903690022038110070586a064030641140f54150044000d07442c54130100c9881404d901d400840140701c507124400140c40e01030aa4200c40102070001803031302841c0c20781280c0755040b030b50070006040c45800781c80d9411000c002035000c010b011400500f0019010801804012005c18005110406285005000a04941c1c1d6090308030f480100300081049080c1c1c12126112450b0690405040703090303020700a50040c403d004240034415100e48800350308030b107400c1059001821100320920364510b10307800c0201c0660800c982c0944901424000890a0002402580c0425107140c005000c0c625915041041030048072040030300820041c003154100c51454069540102003880000404822480c14000f00c0e2121070200b0748484400c840800c00294021103001c11107001c4241c86803181007170700e0700300e903c0d01205501a1801d803c1842c00b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 834624874 1250 834623624 834623627
    0x110f040e04020a0603090503030103080a0e0405010909050c010918050a0b04051801150e0114030f030f0408010b311b030642020a0f0501020715020403050c150d0606 72
    0xc6000302e00884414a185566500807400d507012580f00902c15003081c80100002051880500307134032421418040d1210748a800458101c4209900003580e8584814454085c4032003482555482c56080c42c00f400554100050401745914106022003000d5440c00010701010041c1e01010298500510501c180d0601001d00040b1007804254014a0b51a250881c20010000a500811076010000d0744001d6031801d103100114854030719440741c0501644200e400352603814070060500380b050321442e030380b00c5040609880c2100c2c1e204074024058244803a0a2804038140305503020b60b40b118043e4480c015021171607640c09401d11000034004040d10f409440300c2190190011011b840c02443c4030199440345890304440071070740d901c55070209090941c050000d40e4155030700c0354134035001e401211400c2c00039588841680001840956059501051a80c10840d405400091284400005504103170840d207520b0f03203882040b40068420506194251a0020305001340d88851505660420032656a41c20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 834626124 1250 834624874 834624899
    0xc1c020d0f17070209160e0a030308070f02030c030d052707030b0702060f01140d140610050303070803010e04141c1404030c0308070201050c03030c07030207050a0602060a110f04 78
    0x18101c8808488240381c0003070b8148082a0303486250004c11040c000d0f181c0204101c00010301e02c410904010a00500c0206038841d101c00030700451080e170b5107040518204c4401080d19031655003c4086402c20064095030080010030343c0c41050007203400240c640c9416034441c8940c16000a90408003080c180c1c009040000441c42000301e901072400140c03030365a800c00c202e0310303503000700d41c0754100280f2800144403204202c8000c071b0b01c110000d4091401d0600c9500d0f04400c10461901140259206008010070401210310400003404141c0c0110300341643d075a01c400e11030005000300480c6600300780009080c0400d201720404107a503c50283d810b11b5014003601440d400c4042500c0c0046411400380c440304511920454040300e4108034581081c90869403542031a50041c84181d04014042c40203028114081c40250b0107120480c241665501151070040e080056a501040c4560149c1008000564001c02e80660113507500000280014804810550324010450120401040032a0103d48582c05e40c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 834627374 1250 834626124 834626153
    0x7211a130f0506010906120504170d021b031e090d06060b03090c1f120f06080a210e040915050c0409060e040c170106080a0f060c030b01020c1c020d 65
    0x14070030711035507031903000558400c03410b03110b204001282c803010807000c0802640312a030081d109030301080b0356600e444d401e50080e81102c1040b2103441d038001890340c40320790051285400900510081e500b00841005c80c582d86228080e000c1d480c444001440c2003e42d522548190030b0903600900070441503489400380e00311500100c0c0e080402d84240300c101c80c100d260950039405040480045207403801c005401c01c682c1514034013001d002c801d0b00e520003000021100d004070406019100001d102c5041d103800c042c6015a0a0712003034543c030012840e8000029031000c2001d05000c0c0075030740800c046525141895880c401d9416640c09180341c4824030180003200c10050080700d80c420006d002c81c40d00d48a983e41c0030710054a00500188403448204506442c0b04a0280e511011200001c1c90307682e40d040b50b0b41010b462140440d0101250210341c806c0000c2403180341210201441c042154071b07410382c0040d40d00c000408000f4481c04400004e2040e18050001c1025115405405c2d04034046151400c05007618100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 834628624 1250 834627374 834627401
    0x603190b01020616030209040207150506012015150d03030501080d2606060c0604030e01032403020f04110f0406020c100504061809020c100507211a13 66
    0x40502000703610000d2882d000c4c14850300c050750b80d00e16200c4190300940c40440e002d60065000c1c0800e00104110142c0c132044201e60b010042128900000010074583d42650381864814620002c02020f42000030526200d00e8580550318150700c504d18030102c3e0107a80b01c05580d00041074011002015859000349040350100c004a17070844c04070032800e580d03030203041c02a614042180e2600220103400e594049421074409040705141c00310306800da605114089a0070750214a50315031085003568188034a5100f102605a10120b80e00210141c40b4032242074840030b84180c1103490308030030716605d650044584c2c203c010401c0d5a2034003008200300c1590071910400c4054011141405102c0c1040e0111070403103e0307503980d1903103080d08141e0191000304c11169004040200030801055603031140c0700405507892440014020403242c4142102500c800404c031604100d400180c00007803034241e4040024400200001180114202c0c480c08210040040314036070100d414020b5620b80b01f501d900c524a641c548 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 834629874 1250 834628624 834628631
    0xd14030c1b0a110a0501051c1521031205090d0804060b19140102030703080a050a06050d24020c07090905150112050106090b0904030f0905090a0e0c090f04030f02070302060319 77
    0x45c3e20043d1130900175940101038411224080001080e143e5002c0c5150703009a020190540c2c0d280c01c1d510200d00c0071803811603021b441d61801d010506820800c407100460454105201e1403a20303c590715100c10b0164002c50921000070007117001c10040c4d070420661404042c000c0c130385850071540340307004400d002d108544400c460b001030f010b510b500c040111690740d81c00d40ca410744a5190750322030324001d01000303103aa55079a6440c00701158032b95441e152041528000c00341c000c804481c502541c20000c1400307800c40b1706031f44100301c81c2d41240d00104041e0111048910001244603060518600708010190401002c4100c100086120007141d0505109140207400801c03506441e5403c030001c0f6010341d07400075444440000007500003441107022a40091052908031106a03840d004512200000c0d00c40e02c0c100790721139900d91010403040004003408103046030902c080e400c00380ca92060024001c0c1c4060204964000403000300750081007030304003d550284c11308d036403860280c0c84074049440f00b040000c051800c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 834631124 1250 834629874 834629879
    0x1409150d0221090304060c080c0a140f010605030601060507020f040204090207120e03060c090103091a0105191d0402030a200f010c02090106050c100501080f0d14030c1b0a110a 77
    0x95010320610a05003000114030f00b1b420140c0680e01c11000d1402195280b40801c203c4141c18018003026107007a10482e00704082009050000741090044511400c460303240c032a0800483c1d5000038642d0448109080865a50480e070000c02d8a11420740440380c4c00a00010340014038416550080c01c13031a0143d050600c000703001c004101c40e144100f050060b4568010f80104d1201c440b24001008492414140014016180c1c2c5e2142c070301030410030940c0010b1640030700400181c04c00e0074116000d0010206042031060800000004030320811200c0180a4007460014046440810100e6400c54205403100d40081e816026030844013100503010340100114205c00046500892660801c00c5e0b00a01002c1e0700c0c0e0a145d4221595001680b1140307281c414042c4a200451885c8039040c0a007050fa4013920380c0c14407500302c0501d0202c192040b0000c1207150602c60030a1315034401030b01d40001d945c6d1036082c1c0d901c5850440300084002203501d4103242c01042c40ca40c041041d440c03e0f40707107046001c1e60203e0040d50b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 834632374 1250 834631124 834631177
    0x20f060301030c2304090c030b0603070e0117010b030f07051f050703030e01180c08071502030a030b04020f032706130605090109080c0601180902011409150d02 70
    0x3071000800c0f10784100001e01c075070b000903030505580e520412840c2515840319400141901c1203494255240010000140240300b81b2400050380000d040c1d0051524034074195a40522590521032142103e100c24200704001c403003074001d40b1010f00010308550808120401c0e0588031704141c4105480f882001d01040410508000d48004881c95900c40038100010340d02e054018100b0b0b0310a80d8025583e030a0030048001c0c10401d814841402200460081c0e81040c0c5044d1401225130031290112130725096170b80783c05030700008540034542ca515001c20246c940c000464003038090100c0184031030202104000d9019420344045010980c40c0340d002010840400710107441c0c6d1020394100c20302e43d0020300e074880865030702d0b00826001002d410000445000648401485810000c0d000510342c0019004000107210004501400c1400140c10482c0e000e26a0011b800c3c12104050315960040c040341000055483c22048504070101003041a9910080d01c000c1d0001c0d88003440440c0086810302c4545c8104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 834633624 1250 834632374 834632377
    0xc0409181208070c061109010305060d05210c06070f0f031505120312092a010806151612030609020711060705071502061005010219110a08011404020f06 67
    0x5030840414441074030940d0003151601c030002d02d504180404d40007100b00152a5100f0850450004801c05840c0c0c450b0000040580740041e0aa2b8442c01e44803a10380003254000c203603095268035601442000b0001043c641810b8000d40c05a003546000d05810480074a070406001401040349903503582243d0b040000540c111202c4480307003020903c0c01ea10a0201c0e0030030000c0640c03040001400c99041200c099904801c003c01140c007101140c000080500760038151030311000c08040c00c8548220741940d44400246040c2000702100c1c49002e808901050404150003114254074608c241a4512513590030300080500301800010000713840c198000401100610035a81e046a00011180c0c800c0d141c10200303c01d60300600c0050b10a8000e42d000010ba4050000c0b46044e400d8840c0c011348440d150011010012940c1030b408035042d90018661220707071000d030340501303205264842e00d041042c11036000420908049600012a00d628008040400f1100246424403440c42190020980743d840380034440903 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 834634874 1250 834633624 834633671
    0x402120318010311041a250b0c0f090301180b0a0b240906030f0402090c0910030e07262107260304060209150f040306091a0c0409 57
    0xd6590308444441d590302ca41c02080d52a4030020b500c1d401c040e00c9240d1082c641d184803d60901c03100c0b000078101048044031100203415801502c4068259a443e1114007001000030f201e0403043c600091200c0b1007040e00002d42d030340240080c00070801c0b000200c5c2407454041e4251000e4400d10640e01c00281c5001c0e05000d4100d071001d02416122010b0400d05441c0c03812040d0a100d049815814040e0744d0064884402642c810040891044603c3c2814014803100c85806082050340342c104104115150700c91a102c90104081850002244808004010305003038007074000d40c2440102003103000e92081c03d20961090480120300b0b5401020b002d50400782c110030004c200309421081400320342c021400401d25100502c03d03032103448c0f000c4650400c00f00701c1750703208480840d0110350102e01c2141d142004500c80141558007281c0501c0c0c404e2184803000140214880100421740391920981084200b203c1b0324441030120880c0409401c0c61403480c01c65801501584241d03a141000180c0e4200a00c0d466088 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 834636124 1250 834634874 834634897
    0x30e0d02071a0712021006080616080a0e010e0307030e09070206011203091e0e060306270a0204020f0306010f08010f030b151305100b030610110a0b0f04021203 70
    0x4031649420340700560900e5100010000034420702c060008104070001d5851303601001d90140107400f4400001e40111040c51304001c0700f940c408810414201d143c03c80c0040d41c11200d04250201e555803210100c054550303404c0c2c140300d650800f95403284120300000a00f091900c41c0e151004012800f9003030142c109022079508006a00c2a030040000d001e0031580003080f24003a107085c1c1000c030303151200c02d0f0040e1151308420b2051445403c0800c91410403800bd6a08120101e015000a060003000401c01802d08080c3ca06212042c07441440c080000301301e000341c61a800b4106646920030240c0307501d4a078004481c1180400c0b81030300b058658038810110389040c0d03a5042c99201d012030444d140c6000c8403d0051503129092800e10300c92040e60b5807440311244540315420081964039101034030301d071111505d40c00320b00141804d00512030f8985d11051600424001c601d00142c02c000c246050078508400c80704041e0941c04900c050140c020200e10101d4400c0e4020b071446404039404482050b541d01c614886206c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 834637374 1250 834636124 834636133
    0x3210402060d0507261602061b1b011e0606080405100b010912050f010c141210051c0501060510021b0112060815061005030106050f0712020d030e0d02 66
    0x6070200c9158010f80d0003a140389001c420110403c42d18440b001a441800000601d4103400c120590f0060024204076601c507201800a0b820842c81c0e648030800e814032020b821a00c0481c0c4c02d650406d4031114101000e4124009000542d48a00c01000701d0303c0c51103000850504111020612900428507a40990360020007007410b101c0042025004121541d100780c10001074460003e00c000c1140ca0301190300303001d04050040031884001c0311382102c0c500c07000142030050140d0f1401060a00b2020b40d4081c180c401c40040440d03850840000000c2800d400860f803200d001100b41ca01d4030a40401c0102c0644294000c012454840080103000070b10a800500140c1c80620413140d1142d00101040e9214811306203d1048030546000c2015101c0a4010104942c0240e011200b0003441000b4681c1080c0d040d80ca602440c20300321401491480b0500400c0c0510030b0011303180c0d07802c06d01031003101c0d685500080c40c1070ac3c138160024025102c0d0707000d981d43c0c0006410160111a0244040b0765030088029540050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 834638624 1250 834637374 834637387
    0x2a02100c0c0e0a02070b041101171b0309010204050a080d03060815060402162001080c0a0c14160f03030e010e090a0b0d05030d090302060702060103120815030109050321040206 77
    0x680031040d00400c040034480d0284004400940d000c500c060080d2320603d60009481d070000001040d161010002d0341d1408030340c3d001d1087c42d0030040700c000305046000356800c1c0d0b00d585101002303001e4419503002d02c0c0c00200244002a07250008103000700cc0b1a119070b07060110715a175100803030f62030781c0c900140c140283c108000b01c0c286240c9540200158614802030750990710b147d88860032811109410302c45140d800c0e07040304113a50384c0048142d6102c686801107070305100d41010020040c8680d598003d0900001d51410300606c40100900500c07001f14500c9c042240740c40d1004060481c03080d1100b1000b2451000501c5510343c010204c900d80102c0c0540703200815507a00d00c0c0c80d4041c101c00c01c1c145c1d400504079400300010800510003895103810002000c9049500c070f1500034644000201664215008030005000080c1140030840c0c0074003540c684410941c5030200000032a01c80085519810740c64480f2010400502002510f15001880007445856041580b10441d03a4001c9800131b44c07220082042 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 834639874 1250 834638624 834638639
    0x30c07140409050624010503041e0201020f1906050603010513060b04020702120106050a060f0c062339040b0a0c020d0606081b100f2a02100c0c 63
    0x60240044005102141600d903c0c0c0300d00c1d0920005680c0900c40340c030896000701c1c2e2100e211300344520280080c6041450340c41d09403a503910609905441403a0940d5103240d54080d60700c2006034180d01041c41058030141e124900d05504814481501100c03403c4c101000207190b80380600c02d0502c52180740c0702506645005540f441d004203005c0e41c0d4568015070034400030001d610f0700e1022041e50300000000050300c0c2d080004120100781964080d02c10000f54900040c02c250340700744030120481e40304201092a190351106800c00d541c946580c1c105082c0c0c5c0d8410021081c400320f01841c1c04112034841501c44200e0043d855031040100f50600f40c030f4100411081064240b040028140c0d401d5900d0561443d04050380050300d00c0c501c5000540d00346485410074010104140800700c282444034415071680d06050b8082001400011240c1040c81307640b1138038100c6540100f12005000c0c0003103100c00380f401003111200300120f028040c160301a40b4106000c0b004030f801180b0300c00040da0071942001620785032650 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 834641124 1250 834639874 834639899
    0x50f012c0903040f062a021503040507030b0c030a05010608010b07260c0f061f05130b030609010c021203100e0c130f21110f0414100314030c07 63
    0x1081c5180b008010004403141c80100c014003811003995840c40d00090100c0b0443c2d03164001d800f400040b40350700030381801a03581d1414680031b041c0e00c00f030194a035915400c061f400c00300150300284c00c100100003013100c0060301000031407144092040802c02d0380d072155012039910009000782c0d5444242040410089200390380100c200158051800c50440e0686540130001e8120703241c0e10500b40e10181c40c201510f02d0074026144d010b4401154007400e10038002c0c0818100c1103034030915000c0c4070500801c1a1605003504070190090020341150f45904141034924000d2100a820a005008031100080b402003000c04503400703116510240451780341044c150104c6404050300650340c40204000d0301c803055010000c2d6030000d000c401c1c0303000000c501d441c600d9094070b031824040b040c0d00040c0300c08540000d05031481c1d05c0c80140f410b8500c030b20442c0201340800c5c024469403484510301e507942000c100300b1402d0903860b54280c0c1c0c401d62461100e981a10b0116a4a018400c1c0c84030550b0441541400800c0c0e4094 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 834642374 1250 834641124 834641131
    0x1031209181d070f060206070f090b0304082b0b0d08070b060112060303030b130c0c0b1f14010e0108040f020d02041d0109110d0b0406020c16060201050f012c 69
    0x1c40a801c5071540d050214949003d40d4888142c00c140d5120070000300d0780510045a0081e070340c6c208040e000c1241d031001085444180900d000140002c4007107824010748c002a1003c03543c4508608225021001d10103448040044c0b907548841d05000403450b0f1810a051842000d80c0d014603402d040641a0341e80d54070840b0020002c90401c101c0d54510640c80b402405108000c60181c0c030300240b129480307014001d2103644107181d12201c03400c143c1402030207944841070040c490340114071580581c84030006a0340c0c92400300b4200ca4501c080b404080b443c54503400303640401c400309172144034203104c03503500540d07154100729005003140710321041d01c03009420941c90190369140300400004011070780e14078040041d000003003404110b0395030b0b010400402c00031180590250400320b03400d9620034039641d10f4107100c0300001e00c01403072a500803844800d0031108003e68208050b102c0700a820550321204000c2c000e00c0d003120801c400581c0c0c9000001c42e986240901d610300007096081074408004049580303101c0c076016 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 834643624 1250 834642374 834642401
    0x150804060c0c050a0b1b0301060203071202010e150a0f05130b0c0904021b0d090810090c0905011d1b0f07051518100e0303012702120103120918 63
    0x81e00c190b00090040c4451540188240048109400d218204035114030002c420541e51400c20001886840e8001003a2803016521030f1500051402c0c950040f03002d45190140071450307114045ca502409074803021454481d0909210030080191001c0484065441c10780710b03062107010043d01c00010403034801450781d20082c552815494501d448002c24201d82c4441a112102a4645981814040140004d1404840619256070071a050070b10154903210b072030071680f0b80035039540745036010005a03050840040a000b80304220765a5100c402d500783c0d42d50003000d0401151301c040050400346991099501c0404210b11480c24000f2200500030540d0041809a42c68460b01c5c007001e190814224105210305400c00030303401e802340a10b0119107800301d82030a01e2000707400c000f0050b084c2640041541c1c1140c1091040340141c0e190b440c05403041085800703814016a0001481c01c405d149207800e094100c070300ca00c070603078445072011004544515650103032100c0101c80d1141480d4040b2207030040d01404005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 834644874 1250 834643624 834643637
    0x80a05040e0c0405100f081303020f0303040803090709181106070203070602010e10020712051c020c0129090c09040e01090506100501140909040c050904030e0a150804060c 75
    0x300c240395007501000319204414807900140900190610f04140c0008000a0406005400031500c5c040c000d0b0900800d00d280040c0c0041d100720606100b08811444415400190f03075403400c0c28100402c4591003210803022a20075410005402d60700d510515110403451a20200141890390342c41c041c41d2810f20305c046d031211040c892100503039414058a030007040e0715000012015801e0701c20904009100342c1e002c0420b441400300002042c0c0c040070141700180c0a1500550328291000340c0c3c285007502d40309440703074244041040e54009205604c00a1190406403110b4010148420f00c0e5403c1c0e40e040001d503801ca4440f0700030031003d02101c80034111050f8010320106416002c0c2888074211f03112040b0540b0b40382e10800a114501004881c013101501081c82c12800c50704600240c031441d8803413030042c54090342059001406200800f91440b0252000030080f80c0329051605005050071848500a0310400b01c00340002485010452412019000f9850f00d61544d52280c031840d00038900c4151603800c1c03110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 834646124 1250 834644874 834644879
    0x30e0307053a080415060f150315080601081207031205060f030316060e010c0c0f0f1a061003063c032303070b0a0b0d0b01330c080a0504 60
    0x42005000b5020340469540403802c0c034080c204408030b503044210100b04546003070b1061007140300380d00040c02611000042c0764a03404504404500900c4541e03452140c11080c00d0020172030b100c0109410f4121150201100c1024012a18400e014403034000f0090210b0420920401d481d0040d801c0b80d680b05000621150300000b01c0804a415070b8807282e543c03c44031506403010300030480d403445a2509445044002c111101d1342010140c109180040040c00850204520744100240128145a071030f030b2254004d48250b5580302d4160345d0342c4041ea170052150411003003040d50180721303110308801c454442d800a210b441041c0f160301f20794050001c4841502d00014400e1541a01032a9440015481a4403d0582c20403064a1360702c6000106050940c540040080c140440c00c05200c1e44e0f0050400440000d82a0010f0002442c40030f02e114007c03c5034940400016480310303106075255154074602a400c80b03498268010a91041c282003003c4086840c401c080310201d1110009450880c01e41c0c2400752a00d41c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 834647374 1250 834646124 834646213
    0xa0501020c0d080907080d180f0902121503120f0417030417030901080106030e010f0e060603010e2b2d17100e1e1303030e030705 57
    0x34040415041c1a40c0110110026030b544001800e40c030024410107090b0980c101070340075403071701003140c603441c1000794500e041c00b0517010300c114003c0100450401e41d00481c0e030300c2e40300c1c2d00a90880c00c142c041c6804900d000031010418100c1d08880001c006010701140c00310f454101c0e0198024420400f4084814800454599024800d9510000c4250700640d03e907481c00310101e030040d14801020202e90014401002140d0f00000081d040d15094100860040044140b280c010706c0c054403010140f50030030b41000d18113000030594501072941980240700008244c00d4250396441c0300c0729200300c01420650a80c03000134910521402c1c002d010729100808160718485049205070b1181180c0e804000002014191500712004101c0a4004105c100140c079002203481a01b243d43e204a00054400a000070700000401107a043c100400340300c18042400c01200e00a1207169644086000c00d01d0f14040c00031040001054840050b4010001c14000c0a1408211051410304202d03c02c24840e4040d000541e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 834648624 1250 834647374 834647377
    0x18030b040b0c18061c0e07030b0105151e072f0307030302060a0207020d020306041406280b0111030a0306050a08060933190c091202040504020d1b031a070e090403020a050102 76
    0x83e01d03984007c05881742142407031500b907903041e0b110300d101d1104142450160003448040d2854002240304180d084000d600d08188107101301500140180c20b01102c551000381e1840c0710610015045408482403071401052540d141800c2c00084d000d03034004000030700742400a40041080f07c5c404cc0c000303044140300764042454800159400c0752211100e03080f5541503207040000300c0d804502003010b40c0010788034481c044616000800c100300321940b6410040c00d2a40100c91200c401c0b01d054003141c1d5910b00c0c00800074001c000c14000d0070311903001d442000039000000101c460103101c01ca40038040790000c0081a40c52000858000310201d814036050340d1201d845c10b90031a1050711003a004802104542c08400b00700d80304121700304107000030424140030001c048000c2c8072a943e0f040d280010f1580b03e9000142ca12405950014510404040c13514406601c0044290440b84150340200400342d0340381641101100c01c507482c40001c1e81c0203450184a15007080700542060290054a40540890f20b440e42039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 834649874 1250 834648624 834648641
    0x1050912180d081204030f17010b030603010e03040b0405031203040c230402030a020706150f060c1e06020408070f0b090904020111010c020609160b0f0a18030b040b0c18061c 76
    0x444800e400704170a00d42c1148a2891880d058500030b1071011a040721042d50301010700901c00c066402100281450300c0952003000d09414040440f512182c2d1140d0f000065401030007800c4c02401201c111040f11900c078020b0700c0c060b42d44400b504440904003d10003511a00b050401d25000391903000320165501c0e41d200440c040c0902032405a80d6555605040303007aa0380ca1440200030540b031800801c004d0819810440c1a1443c500e4906151007050402c2099540a103032100d80a40500c100d86040203d0b56004204641022044d591120b94660407451100c5003482950780b85030b41009000c00c00c0c50915019a801807050400715801e44030000460b08480d00c120003500507900010522507423040412104142485080c01c41d40c6090400d4130144440c042c0d0068482200404500f1402440c06003060001300d0410214942d5025900d003850041e0310b00a0b542650341c2c1c0c03c030702c000c0b810a0031500103d445000f04182d60b0403640c01c0031024405268460000c8180000300d16000301031031070407400b8042c103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 834651124 1250 834649874 834649897
    0x2105040e100f08030a02070911130b0403030201150e07051b01090b0f011401120f0905030d0f15140f010210020d0204090c020f1b060909040302030c01050912180d08 72
    0x15a00d05150070184031242d02d030080d49240e8000c0c007105031013560005841c01922901640410070300021342c0f03001d01500440030f040c400c03015001e4011404800b14800381048034040d600a03c080f002600303d00000e8005800755001181c2110006810540100010032500509c01040d00c0c1168031850903500b107403400c01c800c40303048a442040c0304201089164450141200301b01c01c02c40f10f1704000019040b10443c8000310328440e1107482103400b07504140d200c041855044416a0356a40004080800a041c11030311618250300d091401d0300902d0090104c0c0c3c060700c402c410066103403000101009815000c9c2e1113120b0441c45040000d51540001d4001341022a0401e0303000341c2c4031400c2999400c103a4180c018074a00b1580019400b4082c5080080e401600306d03a0304000180300e007000f0012405074803460b242c45405c00c0034002441b081690000042c58900c1d6054000c00444d12220541515600c82e4030381105a400c0c01e010540c00314400d50703800c0d024080c2c0100140d003851003603507404800340c000000c900d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 834652374 1250 834651124 834651151
    0x30809150a0506100e01051209070e010605031618090509070f060c02011d0f06071103190203190804090b040624090608010f0e0a15080c19032105040e 66
    0x2440c1c10b0284054413490050304042c1e24a40380a40002c01078000c0149401440041c280031a01001c401e100d0a0003910301003200d0b80640d0b03140c0101800c16031054440045205c000d101c1d100106105040110721040c020004100b0b0610300b4014001929020701080c0311405501c4000038174007082c21008000380450344419101d204980009491078040000700340d980d03070b168140841541e940007000710401104035202c0b903c3d0720690600405644d07519910682510070140f00c00760703209005522640e2140308030304880b09030050003030120741c00d102d00308000c00040045c0f01c00d00c05520b80b6084003003041400f0b400020f260b035950340c942e0030108030803018401351020034105d8000d140c3d04c5886800600f400c2d0610080a5240c20902c2c0a00031082c42541000000200400d100e1703112500103600071107031051049000b5448a40241d01c803000c003006030b441547c2182e140c4034840c0744e0800e05c80c200c82d041296042d4a2000e01243c0020160071300d0b0b41000c11008100c003050f5244072400f032500071b141112680 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 834653624 1250 834652374 834652381
    0x150f0d0b0414041203061e150c0b01030b0105040b011d100c08031801050c07080708070804050405090d0906020a0308040605060118060305070e0d1e02130e1f0603030c030809150a05 79
    0x203400c0b06c80302c2e0801e80381c0e8503c6680026100c0d42020280301194040040c00b1030301280344604540181d0700481c000c1030080c084c4000418031400d100c0708c030b05035401100d00700038440d0310400541d00781c2e141480000d03801000d588241d10301d1030100c14200c1c2003001c9040c101d80507001692081c80941c030031640d01e441c5014404401590442c00d11616500c2150402d1180c500340300768444d8039041c015000000d102180008000c810409034009403001413402500c1032141d400d100c0c0d20f654590747c42014048c0091000744000404910019400c50300c1ca406883d490700549031a01c0f804060480281014180a030240403000100308103c0e02d440242056640050742d8200240c00414600d043d2a807203215054540c00e980c0824142c9180e0038010242c0c185041d07555050b40f02107017007000525000d0a4191600c0103500707540c80c1c0840c10f4000d010081070280c10240b1031301115812904580006000200c9080741440004c1c003031040c081d0030802600440c2d402081e28100f00a076004100e54447e00146c4503000e2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 834654874 1250 834653624 834653627
    0x110c0a031a0108010608120d0b040507030e0c451e0c0301030201270f080a1514071407021c1e080a0e042009150f0d0b04140412 56
    0x4074050321840300244401c41c036140324a035031f40c00c0281004006040002e101811207209910281c01d0380780280c402d2086240401001c1d001f0700b030542c00f50ba210b02035241000300c546014600e84000700b0410103540301c50440e2021505842240c5254000100410001c0780402c00b1340408451142840410010f0300c203104c46044214408060300018085405100510060b80c009151405400c1c844a002190f080029400f02400305194041c60500b02e000e00d001c1900200407401e8108a801440030110b10140080e6400860704c1031039101d40002c002c2030203e4055032082a044489a0448081c14106412500060b15409038164248c440075900f985e03e0040100707413188000143c50342803400710308607415120b25816110b09a04842001b880ea0045100c0e99915404043e480c40424101303903d0744042c01c608803140d0320000d0303000d02c900034112000c0480e5690300121607940c01c00310700c2c085c101481c55040e10050b01da040134a5601079241c51322a00c40e2980300c0c0010307200380c0c0280820204070800540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 834656124 1250 834654874 834654923
    0x9030106090207140d02280210020609120f07020103090c0905100302040501090b010c02041104170303071e0507080901090308070302060a0f06080703020f0a0b030c03010911030601020d110c0a03 85
    0x125400d581c00c080c05d0302c0d0b0b155401080b81c14003402800084c0d40c4c03203003003e284588141c1f0030541c025405145015000f00040d40040d81503c86c0803560110b6041c3d5840c441c00003500c1c01840040d410340c107820451b410055100360070658000384210030340e1441725261410042941c10403510549900d030001e43c02c205614040c081c0d00c0c014030141c0f10030040702d4001c1c03000074052103203150083d00480d1120222040c6032070300000c583c010f0030031144101818411070a0341e91240e00c19921200058103c0d003200030746a400d410312045c460b203140c6405161503d29981c040030b030b4000394845410b0201c000c1000011800c01d000a0600901c01d034042c080500d4a006600d0444980c00003001c800e0303241510070700072040c0015092013566011598050050350490010f82441050f0700400d5988501000740070880d17042001460580e10011428400103003005180c80043c0000c40d80030740113038081c0000d032036018026400c007a512111003095030300c0c03204080081200d014640c1c1c001c840c0c0c2070040106240d104400c01c0d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 834657374 1250 834656124 834656153
    0xc0f04231911070809101e0909060b12011403160602060405060703051902070f060903080f0606030c04060804050c030105012c1005060f0d1805100605011409030309030106090207 78
    0x841c0c42c0d040c4900d54031010200c1c022038111034058042c0d003044100140c014104040c1e801181025102070743c11500f80140800001d1040f404036604020020664904060599007075203060100b20f11540e107090ba6240d155160014403940502507000740c140b56000c84104a809000140c00420240c10a440c040b458000300501c1001050714050612211240810b10848950071f000d0000d6100c5055003400c403071440d06500000c101c1032414600001701a0880422840344040003044040359031b56006102a910084541d8000c0c1c0500300401e01c030060149145a80081c0035000300d40d0701c40c841c01e002c20308440f002c1e000010780d5424a1041d1000a202c805424000410419000010305240000d490711002038028140b080c3e40c04111b200303508507103d00703070703044e102c0301540074032280031040d002c449000a024001d681601445420b25005400743c000d0300c080b03800607550303915031150040c040726032a0022500e1a5050004020700080c0381da00340078440c040d1482410060b0384010f146410714140b8443c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 834658624 1250 834657374 834657401
    0xb0307051c0e0c010c15020304060506090c030408031b0d0905010506040b03010204050901120807060c050306040524011206030501051f0608070801050409020402040e071806020c0f042319 82
    0x2c40c03003000070380450f204004040a080c00f15410050707150007040d100800035503c4031a803011040006115861300654081c0409a03100c11140d110740205009501c8110303030282c5190000c001090845025030f50b0342600022241038142020301c0c441042c030545001060039a016034441c010320005140501c601e04404104070b008501d031600e06804150030b0230b01485408a101282070340c0c002401003820849030401c2c0d00c00c0701041040c95421014000c3e400c19a080c80c015440c0c40e00242c24002c9082c6c00003543e0400d41e103100b10305051440119100c5214403152446507031140000400034200f400707280e0040c4400c0008000707041c089044d00303c0d01c46695014804114144091181081d0002506415502d00707407000f2a824105001080c00b81c0325550061018502d420708111025034405050110305121395086407401e40d80340c604a80e0b9030000c00149034400002c1380b41d5499482c2c01c1c0c0c08001400c0f440d030201e0100c68204d4085050010701200d0810441c0c881c0e000460309544d0134441c40c0d00c0120003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 834659874 1250 834658624 834658631
    0x70308101d01090209010915050415030212040b0429040b07090b160501020702060703030b040b0f0a090518010501030f0b1e0106031d01020d0f050a060303051903060b0307051c 77
    0x2120344481c0c0c1c45018030903190350340d5002580c160981d01c5500914040c041502c0b03094126401c4007070007001503001c2e10555510480c036104d07030305c10b1a20034021103041c00c0c20381a0140850702c542d140c000c40b450000d0b01c2101c0c0c00600304007065421a20a800031902c8540180c03804803807400c2e04140c609200e004150500700215900c00340801014041a2806048003220707021801c0c2c0345141142c024803035010040d50007840803448008042c4d040e0000c080c40d40c0300362414001090394505103d0034204000310b1030b50015103420103010b007203810b601a9a100310600007408241c1000c0101c18212103007130708160340c81c00310480c0b54800c2c40350828220f500503903800903026025401043d030840040b0306004801c10580c0301e0241c8019100d01440154420b800e034802103658132190b9066000514002c0f0514114034100000a07014a844c0c0c0314100459806403070f420b2400b462070a03840d070840081c02180c0103142e41c6410210340484100091440340c901c075203171250388501e0f2002146425802191203440c1030305 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 834661124 1250 834659874 834659909
    0x2101060503190f11060f1801020a050c010c020117070c02190e0f091c110c01031505060f0408061509090a0c0603152403050f0714030c07050307030810 66
    0x14454428090150018400180d4000c40d00e04849001c400d481d989510000108140e1103020046d0010842000404000c490b902c0300c42006a845140645000d007040d000112412500d502034020010680e20514129250201c801400a8100010b40d0940001460713605c0702c00460030022001e0380d074040c1032464004030034500100c1900000780245004c5ea4010328202040c01000100488007801001c02c403842111405040b0007801d124103484208028030610414041d2540a03101d51140300c4008220700c015281031900380541603105211035000c0d071400f00000940710301e0522400b40200c400c1030380c2102d200c03611000c02216090160000340250041e0140f4400140015171400486e0a10300f804100c501602c0b82d010b10040e0180d000300b0303e00c0141c0b11940294140c40383c000e410050643c034100300f07603182c62030098441d40040fa540c0d00840c3c090742c031001c0454420340246901895045126180203c02e035a21400c5030424102140803801e0101485103440d880e0040e51302811101c3e903161103200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 834662374 1250 834661124 834661153
    0x61505030412050a0e04020304050c0901171504020307030212061504061211190b040302120c03060a0e190305090a080303072a08040803120a0204030c051e2101060503 73
    0x150b459845006000001900e000041d019840d02050344100400c219100d142500300340e51150082c01245101d464994004a0074068118504610b80c1c807180042c0b813400306a990300050f114002c0c00c1039a02d80b18135480080180d485565041040300004090401d900300481e03240030058140c1c2c3c40c1841203040070024071000010513540750202c1d03040946010700300345000108290782904030514000180082c03001c205041c42e50700600491340309588103510074808101d0725440d859504801d581c150426808600500c0154018881500a00b0241e41c4000300c0410f4040020a603098100d011840114a0040c289000d030206801171107a50042d520350718042c1001480707850044008865145024640310f010f0141c0c40c01e042c0e40a5003c00c2d11a81c40303444e5540b4583d250401d40b054000f041c002e6000401c0b185190082d902100e5000c100d20b01001d040400b080400444449034228043c254000921240d440d06007000d4605402c02409920a50301c6107481e0079102aa0403585c02548212519400ca0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 834663624 1250 834662374 834662393
    0xd030b0612131a0c12090a020a150306091514010f0210111201060509031c020601230d030f12060e06060901021f0203070e031606030f0e100615050304 66
    0x1a4601c40030b01c94015a0389406040d08031103400f0240c02c8000340e000c00c40c2200119004008410f0840c10000c05655440450b9568007540e12000f904000b444000f04038144205256550b00d41d84c03400c0110740c154a46120300700f11036020070014180c0d20300c01170801c00419183d912103650340307003031078081c00244507400040e40d214038200440005030359030351503603145030904410340d0126503050032410700350b51351804018003070380241821034031070b020f207500c410140079a40607031886c00700c03098000c0d1240340c0c41e2000c40b4881080b03200000090301d48540301405540d480c0c800000b1024407a407100b55103105495001040301542d10b0149c1c030703490714041c0180704125402101c0c0398020700446004c5c1c0e9501140700102c3c00c00b01404e6440c128180c070726900404a509940203541710f61100e40e00d0b08519085902010b80d1403c2842c803502c0141b091190034030a0b2482a0003626841a00e52804203d0312040c520f590314003e1070940c0e200b0059503514092013802e000780c0e000b00700c41802c0d20300341d800e41c2000d86410313009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 834664874 1250 834663624 834663631
    0x7080d05160824010f0c170d0b2d0d061e05150604090e070b0318010f0b1806030705120a0b070f090b03071704060c0210110d090c12050d030b0612 64
    0x10701c0807008441682030b110740c0300c1c4004c2c03641c03206405034640500c0d10205000c0e00a223000310b102c80c0c10b01c0c8450b8050f0500500005440d80d00704003030080750100d001e0501d14034810010160b0000010003840d00415245c0c01680c3d880c2520102039110051a07030107041c2110303000b6020600710202e050314503206503644c80698003036524840001841000e04400c052502c941c0f13511000340044044102310307420314100c401c4a5040000b4009202110690441904030746903801c40a90100c1c40d110310300091080c40794440d80c441009402c450900351118002a48140007012194950380030741400f00810041c0c5000030303007003822402c194135140c0c3c07036a00240211120340545a240c0c02c02000140045119450700d0406c082c050080c0301145c1414200350020b00030070620390026104004541c0480007151050b203218000302078140d410101c071203800c480a405240703010389034040384a6010500d5808031134104100c0f031154000300b420200e4080040c1c00d0701c120b2000b140c45214240f003650384c00104545031507032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 834666124 1250 834664874 834664877
    0x150603010b0a060e12012d061203030509070812130812090904150516020613020924041401150c08031801090f030f090909050a060207080d0516082401 66
    0x5640c0d81610100fa40702d045003020b46040d600301401c5801d0180c1c88103c084401f00c9442c4100420f40f01e400955003951340910814252a04410b40c03500824031a503c8031350031000c03000584100310383e079000140c80e00030003021004911a0004a10780151340d07a254a02c0284014000f405007401c04201954031800b440f42c4587c004c081400000317003000000450300744000d4000e18100881d0070315041032003100d442c0c0741c4203402620a0001041c00b03000a0820504050740c020504002e40da00c54503801100c1104d603a0752060f80300000028072582e9210f000e11020b42100c01101b03242d946c034184040c220540b4400d00007043c01000d48100d80410707a640d00306c07940801d040925600054a0822f0390780107002c0d900b0003a05148280e901ca60416174090207000e00341c00310741c0d21100da080c1c442d403610084a181201c000c1c200d40c0074000140020761036030041d01000d40900b410701c1c14109900702c02010b40c1c808440b02130800b03202501c4015481e8101945a8016072a00468003a0800d65001044000c0c10100d40d0350 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 834667374 1250 834666124 834666137
    0x30706090c44160e010e22080d0b03011d1203010e070c03111006060e0303040b0d230a0606030f0209010206040b0408091504080f010b0108010b03060d06050108150603010b0a06 77
    0xc0711650b08021000010841481c1d90340869074401d08140c1c4818207004c1e45103880c1c07580c03002c40d501710f41c044585504452820b01d04210005243d40308240342d030024104502c856100d00010001d03540a204004508100c2d410038440fa09500000310304055503184003002400b0180f00521202072012042070380701c44c01d41090200821103040c1514200e0380c01c00c0d40e070b10a10403d000f00c41508160b07000b0108035802c035180c83c560300d0a0300c0e0400d51240541d020340d40c0c44c10300500800030514819089006016071040000150740040703042e40021200461b14401d80c5500c0b4141003060b6907051103402d4400704003403c11400c081d40040000c2d15200050b0000c0c0005034400d010401348100d94040340c02c50240101200000c9200078421042034010b4842c0662501440604007600c0d00f040c000c0b80407040050b5140f1005a0130310b82202026003016000f90307000b40c0c0100701c0c1c4c00099135611a9502038007240300208030260214071065a0004001c1034a070181c0d040c40e008810301d80300c414448041c0c4046080c0f41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 834668624 1250 834667374 834667499
    0xa02031803300403020a080318010207082a030601170c030705090604090c0b1b15100605030a0f020f040519050a090b010e060313150e100b0102030706090c 68
    0x10700b0700c0c0225080a503111055441c0050914070000003061424071081910100810200040e40c03103450500c500d0b14150030032010700d480c252500000c0d080c40c460034001164490004004680f070b00f030f000d0300a9100020003d00000041c1c804000581d00a82d0460040c9025400c01010a00c248405400c0030701880e1070301e07041c401300510080d603d005000007a0300c4949604800c9288070301542c096400050a001d203400c0009040110580203200b500190544080c0d1440e000c812245030b40f00800420308590760300000420118140020484485101e40b11910b0300c0c03c100804c00e525000d807240540f2260201e02c10400c6480d03281c0804200c13070107514001039007024900165480b4015004140d4009400820440c0c22000440d04400d038601601c90b044005003141e58050448032441a0103555a101505002c1c0c61401504220040032044c07040c0c03030800445588031003d584036228200c0c1c075002c0c950006d020084d20400c91841d401d90410700780c034171124a844a8200c41d1100711010780c0c02d18219118 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 834669874 1250 834668624 834668713
    0x405040b0607380408030c030915070507150b0a091a0d0b0f010b0c0613031707031a0102070f0e040609050d021c1707230a02031803 58
    0x681d02c1054000c039051000d0b036a410520220f07101c402c961840c0001e0107000f03050000b129031801521079644094480e1441d15001070000040e08010070320f010b01c1c421603402c0368190300510303500e40c000c84003610350b03e071a10740307500d0420f19400881414606251034065070300a10781c1c0303204a4108070380a502c400100c3c51000980403c070031840000a41c1c105000d08500c000b00480d0350000b44c4603850500c200381c40360340c8480c040300d1a41310307280300c00d10701c0e920900c0800c080180460500c2c05481c400e0508819851003000303196030920045482c0c2010960b03442c0c42d40700c1000c0b00801e840c500c0109102404100782030094003c503455850041d21480915000000c0030485158008640c140d0848100e85034a0003241e802990703011a10a4520f00c02c030700340c003600e95090240c594141e48043c45040040255115181194101d20300176a101d00004490546992130303a000c0010a00e120155024580d40c81111058200076564000a6400f962154144d918000541c9101900c0d43c2030400c1e1400a50003407000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 834671124 1250 834669874 834669877
    0x609090309060a051308010209060706020f0909150103140108070314030c1c02071e15120f060503070b0f0405010f020c03010f0209010e04090302120706090b0c0c100b060405040b06 79
    0x28042d41082000540802c0700f83c00001400045c402451081402e41e1641c114509074015503c65a0304800280081400a0402d4005e45102a5020207041c1410400c1c2c0005400c180241d9900100f0a800821706449507418024444603c0c0d8200c0080e005514000e003480d0703103007801e200c080d10300c10a804030b601108805100300d48281040404488803c4200303400c094901101e0303010100548240d0b8800140080d60040011851820030020440146804541d40240d01022851000c0144004411a5500c2030b1700c03a0b05c03c0c1c4a101c40340050101d041c1000e262404809030407010b4007036402c1c400d000500822034129002c0c0c40c42880d100890120002c2c007645002564600d80d0307815404c0241c03150080c0f05c6030f4013906800c6402d0b600c9458aa040c0030900044442c0c104000d0011307000741c40703828100340099004010340b500c5154009860741051700d03845403503813046e5100012400f002070220b00040c020080665440030820041140c18680e02c00601684220b00c1864011078580740d51150a0380e60300c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 834672374 1250 834671124 834671137
    0x10303021c030e15370207050c04141806040b0411060f030703020307140a020726151609080a11060409180311030c0a080706060f06030e06060d030806090903 69
    0x4c4034001c15401d80031401d5940d0850390b1442203c00220050001c2801380707a07001380450403070300c144166411144503201940c01020207803203500c01c070f03501c40140d92540c0c4694401040503c9078000a07007420b4500c0c40c000c0c0859809510382e507001d1014440410070300b2480d290029404800300ca40d085038100820740902441d1010704840c130010040280741c40d01070b0001d511403801641d44486c81e20406860b81400d015804540005900c080f1042c40046822044904048000301203545011485641b40349440f81c494145d101e021002000e00509895420191072103021030700304038005134140031150307a07104078a14010340046119070180041d5221a011503018044102040c00181c040c1e00e14060211b02c040d10440000b111880c0c4410645808000d071030200c00c0707890261101d8030b87d07034403520000d401c100c0055510a0341d0304d00018540c080381c1c03045030007400e00341c03000b007403425040224605003180107200e1130003849881040b0000942c0020350a0340f009086036a07000d0b076110b002520b40303075004e0f24 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 834673624 1250 834672374 834672401
    0xd03050c0a0f0b07022e1b050c06070504030503071515061706090118020304080702060301031b17120f040503012c060c070f0f0b0702100e01062702070f0b090c0405010303021c03 78
    0x80d040507005548c03050084c004410140e0813518141c682072002c5070341e0b1045110150181c0c00070301614000501c07800e5601d002c0b000400001c11000e184400c1d81d25101030781ea0140000c941040031007201c6190880b02c032a03000200300e0765900c0070b40c5406504e166116608400409070b0398008005010850500141c9103110707005000680c40f076031680f40132200d030128039000702d402e6184050005502202d02c000c41d0b68200c20003020300444018400c011802c0d41140500030b10301d003000d00011a10f5182417242c00f8090311072480c1080b03249890308445144c0070001c8000c01403074101e041007201c0a42628100d90000c5d82c0010000781220316130400002c84502c403032000b03245012420a20080960009282c201d0000c00b00041010b9103c03060b0b0f5500b00d60302c81c401d4801100a85026282136900041c0f031070301c1c00c08411009441c040b2581c4d110f083e4011000c42c00c030f65481c444c00601c070f0002c504100418070760301d007514100415415500c0103540c1300c40415981d20400c4209500b54611846908841040c0a00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 834674874 1250 834673624 834673661
    0x180b09030f03190f0b01050406030b0102030405041a150c03091509040509060106020f060609070e010c06060b0301030311011a2b0614090703110d03050c0a0f0b07022e 73
    0x2c0690f111441107100b520604190800c0d1a9200c801c0192191881142050b107030f0314681480d10344190042e10407000e155056000070710000600d51500e0060403c7c551000340000c11445080c0d04001e2520110082d05002e540c0074000c4025910001040359a00300f030840c3d44845407501545448003a206104c04a50041d080c2400d01040e5100001c40c03905072651038090b525071800c3c0e003010325581c82003160b00c0c5610142060214035140d0141202405001c418940b60302207201d291a44011364100780d10840c0040c2d000001001131552005103980c000031031000074046c60055408000b408800520382c188503441d008101c00c0da004c07406a5526012180900303d01d07a18420341841c8000b01440c1420380040940303c0c0004140e0381c07020a002c81501d51103460f11003140950414041d250740003038000c40c00e00c0f20410001081100c02c00210003807034854198281c00300d259203040004480060250001e6501c0302082d9414a103184100742d0300c51040f4044501c1004d2065054400341c11030007504c62580c0c20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 834676124 1250 834674874 834674881
    0x11704150b061b070305010b0d020616050f061612050f0a0e0c030f06040b010f050604060f050d05090d03060905060f0d050337170601030504030c080f040810180b09030f03 75
    0x41c013048000489010b02c0082100c0c40011051140ca4010488000c0d40000b00b000307071352041281b181c03840101034000e004071162580300300c101038a0a0004da41c80c0417811300607020f1161030340d4003841c5042c000103c0e00041c84141821045403424990103482111682e84408400c02c69000c108160200c040e0700604849803a070724203400e180c0fa044195000d81d003400001e00081865018058071808450020b800700c0d00d09403402200311840042036110908106080040040700816030041c0c5000761050006442c00390590070003c1c0c112981c039400248000e0805080000a648228444054080c2552001444611031500341e0440c03242c1108400b00010755084400c030050204e10f4250044107100c451a40c081c85070209660503891811079403040c10b0007000044103035100c0e0300000e40051007410002400025540c94408039003150001c90031600300410200440c020401c0840664000401c0821500613000c0403c030040d0591240501003500400c049a03c100040003211582d040240039a40c80c0d0a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 834677374 1250 834676124 834676177
    0xc1b09060e09030f0403030c080910080f24060c070803041511070e040807050a0b0a1a1203041a0c030f0d0c0e0a030212010906020304060b011704150b06 67
    0x3065006074006400d600300000d20320000082120320764500800301c0c40c141480c44c0e50489001440180441d103140c000e0208800e0380c0c55951426940d015070383c07078a041914100c41d442d94820401031504080c4180c651980001410004400c0c0d4018410703140d460740e0f03c10b0200074600c3d0410340c1d409521140300006d0b000404e032201c0c820303c0c0c0700c07909655212044010b0003518581c0d070b43d2060040000010303001011034005403600740102946881a0140c03181c51009842e00b042c408030840e400c80c072070342d140d01c1c1d001404584828000c80c01103048070840c05046903204140d9588c0981e0158048003000704000040c40a420429a0680c1c8001d0741242c3e03680301c12020445040d00000c2903905c0b010b0401000207403003401000580039800c8080c20740901d851458003000900003158440c1e030a1956910b284102003011070008503c00e9018080105003015480001004561416008603848103140207000000c0c407034001016a260701c00c08089800c400d00e00000f41d55104000800b00220111241c3c2032503107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 834678624 1250 834677374 834677381
    0xb0924131e0b030616090e0703090813210b01030f0606030c0f0510051801200d0e0a06020309011409031204062606061204060f1d121303030c1b09 64
    0xb00c06030113950a507100c4c00c607100705254072510341c40f000c07031907100c02407000c0042400c0003580086586004130341203d4680300d65510358403040c0c894294100210f0103001005880703194106074122940000200355498480900c524018023004040c420803403034400a014254001a01031500014040300e41580c4820005041c503180c4281805080d4030885510050f0040040c3da1f0200101017405a0a07a040c3e401146e06601151680080c0e41d40d00f9610b03004034804104020303000f510b541707481942814040c204079102215038030040031035004000b03540559902c080c5000d192000d0352099612558103400180c20015070402c0c66404040110b000a2142c3e0300c00c1250901082e28142070011824a60000d40c20b800d0444115801400410902000844400402c2c0d0f00500075880000c0400b0f4241c28003066810812035402d552402c0e854002101c2130604c04a484280040036451800d408082d46504600c494807001c0c05010030420500144041c01e0b100410040d2500b042c9841e01d500d606081004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 834679874 1250 834678624 834678641
    0x60605030d080726010b0a09080d02010f0b0d020604060c0f0816021c031b05010e010204030516060810140402070501050c0d0b060702031507021009060b0924131e 71
    0x6608200080060407094100e0004e800c441144040c0e980c01c0c07000d02c01042d401501c0e51400c00024010000b036080c400d01248845000781d50001c102064040c0a4500703440804101a109000d202d8000e801699a01c0c06c4404849490919000381101c60130680d140002521019091040004404030800c00880b00110500e10843e0743c076101c11240001860b0030b40d610300c401008101d01c0808040c02c5100c210b045d0b0308140c420380002c104225561280c07402c2e60440d40c400c841c1a4414051000c03010071084014010b0a080c0c9029079161a0207010840c20f0380552151803840620700c4000300b069200c07078040f038000941160082c81141400000810103501103001c0c60700031450b05135040c003d446c100b4100c4008075002001003002038400f0864054441c005401d070001c0d84201c004804c9004158021351241d0f84c056400000e496214200340241c9543c001c0880f014812103040e1011404400c5403a0440504155800501c403040689050020005502c1110400d60302c0c0840781c9070643c0503042504c1d0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 834681124 1250 834679874 834679877
    0x70e040c0e09060f1f0b04151b081e070b060301050a090305030c090301061e0312141c230915040b04060902060403080d020d06061e0c060605030d0807 66
    0x103584000704074004a0941c1c0c00c031855001600440c51071880b41803003a0300b0000411004910307400340d6040c2e42c03030722410b07501451441d42c000c10b00f000740c9032003a00c204502ca091401c0c00c0300c0b40d0301c85814039901c500a101c4005c0c072400c00030880c6130a0400100e60450780401040750349948542c0b0303080000f101c1c0743c110358842c4298241000607038450210b001d5589410340c1034480d01c0c155140c450400446401c0ba6040c143c00d9981c5860001c0c944401e01c490f02d05805954440d450140c0c21810f010b004001800c01c0f1f4024002c2500100640c05202411540b100c40400500280c080010000780090031880000b140441c201c2c2c80c0c0071080030b909500c0140140d860408a0392449000d40b0b52a0700e0300b204540162000206100240114001ba00a50100da20042c912840d081e104d5440c40702c2e81c0c02a003220b024140d03000c01d0503000f2814500c20340c005041a410030104610180e12190f4050340d04035001c03c1000346840e004401c0003d582c0201020780f40040681da20740e844140001c0411a0031143c110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 834682374 1250 834681124 834681143
    0x20a050d03060503030a030f090503040b0c24010603050a060e070e0f031204120c0503060403050903211e0c0708010e07120b060d0203160306060501122a020f070e04 72
    0x4a00c0390191203180111078015020350300b8050862415401410040a814225030b00d6a034954002802400140003914085a5094698101c7e81816151607042800285520f040c4e91500e910b007080d100c0b40760304540c100e03d00402d140c0d0380c601c1e4005c01340844c0e5012080e052080000d00c0071050b00142400010314094810482102411080550b02c02c1c02c0f404000070340c41c003004207103e02880c121802d1710540c040c0103c40070540d529008640340400840e815400a0004101000030380740911141e403014640440154011030f6444204005119007941240b80f88800d4000c0140d40007200c00b518034400480d02992003440d50b170640305010b00110342c40380105002d071020100341e0b10040080b1402580e04140c03c2c800c40d40d01e080900c00b505044003400d0340d06102c0c1d114101d040c040c5058240e0080c62142c003000c50042d2a00002426520b1042c6002d03100c00d00b410110501a16148400a08004000c400c1c0c80c1880181310264201102e5624410441c06520310100d441c0c00700028041c0103500c0b407108003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 834683624 1250 834682374 834682393
    0x40b070e15220e220c0605190c02030c06090103060518070e0a0303020c090c040b03040c03030207050301022706120a05060109120203100b1909050f060103020307020d140712020a05 79
    0xc0825406a0181842c00307044400402c0028503613040c01c0b034820640300701562040941d502c42d0740c0e48141640c020000a81d00180640103429140c0e0001502500342c00c2001100e50680e000036200d000c40b80311a401802d0216040c00c050388641c102200405c3c000d45480380c940c0d2440b0f141600c02c101210554081035a4035100d26842c104500d00000316505a40036100500b0904108050301a01500240000000744404543c1c1c013aa2801035016500c07640c0d01c2411a4034615000e81003200c0c2c0d6001d14440c5e407050180400403c01e0b0f00c107901c00e6100ea02d0140410080d580b000515034025508101e100c0d034400f200304880c00d4543e82c0401e0080e002600c4220803035540b061581a89005070320001c0d050380108881d000201810b4029010403400103000700c02c5034505094200c071030032803680a07000300c1c0d840d48103100703222018250107074112a0071310b800d51541ca004040a9034030000321840000b0002c4c00500304007918051400c0c0c1d036040354042c8044003c00e9000f4002036440d03181140560307050003400d001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 834684874 1250 834683624 834683677
    0x30a02040f2c161d09010f060603090c090204062a0b07020f121611041d010f0f0b0906150c0a0605072606150d09240203010608040b070e15 61
    0x101c0048030346030754108816490b00b100c000c0400e4406014505c45e59201c0306032200103ca180250000b602189d603000603445100c0c01c200c001183d00e90701c00c00e645807041000b0302a0650010a0031150456509811480c20b4625100100004402c2002e03001c88415824890619808100120040c050000300e400c18620029010302c13500c95004400004100010660700041d05a0880303110741c0001000000c2d00e00c0c80321840041074132214800141d5940d20b030302040c2c050202e4819800b0500000d40f007000081c0050012491081c0050310107440703040451504050076894608486034002000306075070400d030031498020040d013402c0e1004804545101240d107100c0003a11071086000044508203070884d182d00f014401288944075600c0070b5208200000f840154003400b81c100303880d00c02d400640e80c80340a5401c20b0741101c917400141d01007500400042081c2d6500c42c1c3c0340394105070054078200e03079a02d0781482942d4001c00903820742d800004a03000e0b094560740c02030103410100000c0c200011b07188003102c0f4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 834686124 1250 834684874 834684913
    0xf031018020a120b040e100e010c14070206031009020706090213020a080a150803030108070603110f0702040506060702040c1d060403030c0b0c1c020307021902030a02040f2c 76
    0x1402000160982081c010380c0340d1071380001c0d070307400d502400000f4036580c4400254207010742070100a00040c8ca03001d90452512007442840d20320005450700c0204980c0818034091103126031100a4401c80020000c11030b0914064401c17002841c1c40c40c405c55079000e080ca03144000e000341c14800d0348a140d0180707100c01d03410700700d00855005030410783e200da01541d100000b2100410080c0200c10116400140200340b14400700002d6010b0311441008050301c070302e404802411344a6030b009400d04454180204252400c040c001e99022036812503011880d0360341c02c1d0102e09140034560b800795125003040100e2203c19000b5940001c1c0100d0305a0281c042044607040c0b0904c4e20461000170002158a451000030442c0d0204054008407a000703224504800c54140e03100e69000701d038448006560000074002980c0c3c042000d418200301c0c112082c400b680068001a403a1408071102a004a8683d03d070303a086900158881e1102c12451007400320782c0c01c400315031307007210309001c030700c10f900c1031141108082c5003010211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 834687374 1250 834686124 834686137
    0x130c0b130e13171c090c080307051011040303020601061b0618030806010908070306110d02040e01061107260106080f150a0506030a0312020c12030f10060801060c0201050f03101802 79
    0x240301d64040c6011380b06580c000e008424041c1c640c021207a00100d0030000602c0101081800b98000740ba040d4600f45400301103030110020084501c00420013003001980200c3c2c1c0f241142c1c03260802c40d030f43c02c5400c0b40e88410b40520b180010711701498100d8641c02e01c08100c044d140340c41c5c080e966998280d50fa507030054030716800b5130266042551040d202000090100d8220000c04405030100605041540310b02806070782160b00308940c445100b100500c01c265000d40c80c61303558420781c002041d80c2860806000003628040391408104003400e0856001940c09400c030070003d20150701280c10749d07001c2c4600103441d0511190b046403081304443c085078060016020b2240a0310700107016100200340b80c0e45c155451005030029032910b80e003d00044600740010300c92010340042c0b0264060b56454407001090307207045d0040c8000940c5004020038400c00754000e52807411f442243c14002c000940701e00050b41d840c041c0e0020b5510b1b00d1800801c00038401000d1100b8002c441d400c0328140269810715280c03409034054403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 834688624 1250 834687374 834687397
    0x60f030c020d2c040f051806040f120e030a0c0503160305070e1806010f03030e011d01180b220503030c06190e1504030206130c0b130e1317 61
    0x18400b51070741d5210300010040e41e80441c18810000b00144001c14185d80700d00301400a10f0b40d42d00200441c2e09840c0c20a4080800355802410051074a81e503000c8098084a030060a102107090291071183d01610214580c480b000b0112140008586070010f6418001d000701d034040e00550f81c00300c02c403840342c200e4802500d9002001c2d040d00c0d400c0c0b66409510230001824242003040001c10503042e0403060110074003902c0c0c0c0c4000c44802e1811824068042c41908165034100316a41e08298079103c50816204181402440d004130b5100249042c042d03241d4498002603114040002e29408001460412400d20781c4010192000d0b5a621300401d900d03405140300c1128203402c0400041d406c13227502400340207052001c041c0000d00c4040c050480d0310700382d000d0462002010030b05052009140d010800340f58003640b8050354804894990360b440310100300ba4400c0c440b205402181004004842680c401d0241009000c00c846500c6c200428440c5021010015a4840340200c00c120b050404201181c550304c004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 834689874 1250 834688624 834688637
    0xb03032d09042901092403150f0807060c05030319110c1b030601080304060c1b1d400b0403020a03080906130f020a0801050a150807060e09040c0f060f030c020d 70
    0x90305030920000321b0034448074201136540c41c0e10f050103241095603201400401030140702c4141030080c1d041c68a611a00301d80240b29001900380b0000d000002102c0d440003070000c14118444420410801921303884211803480080820002600400020b264008008041400c182862500240341d100d550a016042c1160001c110034407059000380403031001d042c07286401000000c400e041c000610b8140e50440c10310100e4180230044000300c0100c1c90358000781d500345d0004c400071510074015801070294482c10b051010221303112034140c1401c2c003d086c009400221500e41440c042c5070007074542c1003c20046000c5a01200403d84421000607810b119080042c101129080c1d140c07940107154850030302c101c1c1c6c044009140810380781c03000e004450007070707031500c0c00440c410705650182e0850b180c06400c81a080c0d403002c074003001340380e5205d02c81381c0085100752030070545500d4a00341440f651016170009100995900350016840c0d6112580082440701698100300040d050442244c545030311110f1180054030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 834691124 1250 834689874 834689909
    0x150e1003030f0c050105041a070906021c0e1002030a020609010c0e2e050306030f1f110409020316030606080708010b0a020106170706030b03032d0904290109 69
    0x6580340880107442400d003a4541d5142e6134031103095a6045504a82d41045014004184e562203003c0310340041d8942814108a0b091804c02983d9500c1840f240316112003200c48080028081d10040081180251030b5024824801101035540e03405555468010701c00c640000b08501030610600a40c0100c1d40d44455a40e1001800c01c000c0f901c884c11040e41900c01d21659506420003035440309080d880c0e5403a025141d01d84581098104203540b0b1195a01d5000404803c064140d52404021005a0040d0000b1102d1072240405614011500b02c583c509100105001240003011220a812102550144001c0d80c560b00d007114080c9060380e20b0808500c120380107000800c92200a494640024400040d00641d00c602c4c0c074040b0001703044010080c0d0003201d402c1c0202a80750140f603134070750006e80080d41b512a482108400070351002280c0c1000600605044403800c4004044030a580c8005005000c1a81211340c1c0c000c01c09031a4030140038448400c48018210b50041d20400110f800d82e070840744c3c4005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 834692374 1250 834691124 834691127
    0x8031e040c180f050a0912111504060b0a060203040e0c071e03030b0307261c05070203150f06030d0f0c0809030a080403030801080105090726011e150e100303 69
    0xb15169042d601e41c54482c5070344941828410544510000c44000ca07a040740c5d4200848480e60003518001000301c0882ea11049000010300c5280c55401c1e81c180f48026551802c00350000d1510a41d8154440503281000a506600001506c151002e4103030b041c0d003a80b0340c4011094944501c1e1402001008a0342ca007200c0c040035404403040060103800c4c0424041543c00c0002c3c00e050302c0e034024282c104815440105424481601c080507804101c0c0245904010b212010f03507003510003c04041004000a501c1c030440d1410710607503034034820100c2c0c03500040c02c005001c40d2071083c0c2240c21600034850411a4814141300b800d212001d48410b03124480a400541c079004000d80c0300380310703150b018864046d0b89000901c5810007000214066036810105504001b00d843c20341e0300c0685034082913403081a042c0f2100980040051031b00303103104a4010a01b009000180c0500289081d05405c615185040804251300360031540160f0b249035100c8100c5521011580d0f031607141030303a4560b9072404449040c00060f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 834693624 1250 834692374 834692399
    0x303070f1d04021308030c0307030e0405010501021c140a050d150308092416031205090304052e0e040b010305010e15031c0201140105030f0a03120f020708031e040c 72
    0x210b08012004403c00d449085c254a5540680090749035a03200064003014141d20600c1100c01c0b1804079414482545040c0000b582c0f0320800c03014078414000b0841c0000380710302411005200d01c0c4d10f0340c0110340b603109880e001307002c5800ca035032500700c09403d00c440e00f1010305043c86000e003501e620401550070000094244480d0408001ba806039080c81c0a0681702c682112030080c1003202508441f8100711906450000c1003032a1313944000c200d440c01e00041c403c65410206c1a102a50b809480c0703111990303000e100002c0801c5c4540c01032000000001081d00b541035201c001d40440420230f0390140000c031013402c0114110b4409204400760502c1c52008100650010300c260140b5510080480300c812041034443c0140b4410500c0400c0580c1d510b0342e010700e184c0020207206004001c02c0b0060140160004101c58541100017402002c00000040540324407009500c649461a54013204644680d036a01d80010140e006941200d140301112085008c0081c0490806d0701c100e070b202911000f061b01d80403014419 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 834694874 1250 834693624 834693637
    0xe030d140c0f0a050a03110f0a03030f0216111e01020a11040209130f0f3b03071506080c01090e0402130504060507090506032e09020304050303070f1d0402 68
    0x50040c0d0b034104000301c2c41006843c8240380103201621169001d454060404400710700324100c40d4210703100100781142c0102d0300c4600039402d411301049007d46880504001d2040070300081c0084034082c440014002d10f4005000034081c1512034140e2491821581c006503081050300314016842448194001040d10a0080303070100003410240c10044100001015143c02d035212694565541c030450b84800c45900400b0034111001700104200c421109100026100841c4000f2031900e54070040b0402400320b041c220b00d00142142070f01c0d03c501c11407401f0700c050f0f04160071001c4603a04003a00817940481c04249000d17044816118440e540e131a1051050488500403c06d80e8000941c02c0b50792200d90142c002c40344101d218502c00115864410303030203003a55100360003150055600388100500c210741000d410000200c4681c1c80c420f03040c0b41c41c1d40076900a4041e001002417900210502c01040340001c0518002c00e6141c442c400040c1182000311601c0341040110004041007030903090042c141507006240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 834696124 1250 834694874 834694897
    0x101d0415120606091b2304060503150907030f061d190e0d050405040f110906090303071406091207051b1f08010602010f0b0a170a0609030e010e030d14 66
    0x8400340d449144104503031045400020740b01c000b905ca9141036900940d003860003012a83c00c00c030220000b2803400e8240c0218061442440000000b00710002117450018542d0000142003145070f240290008002d080f44081c3e40d541942002c1010a048070b40b5009004401824056156542e407114031040c01040b0340030341039803071a43c0ca0414526412045c002e00c4142d039050f8403059525881c200a201c100c90484c91400c4102d858000e044182508072001c0f00e20003c0226034440d00d850744400013030700318410041300030402e03488000307012450740e000b20340580705000c07480c190341e54550302c1c0e1104041480f031240024841d8126616454210701904005080040302404525951450100d0b4000c0901103c00c50000311310000010001c03a5424043c100481d04082400e0051020140c04902460140e0140010210301e10700007500310710b0104169041240c106d101402149104d040151807000c5603891a400503105542079642420000b9800c8004038095a80b0f00001140380890ba64139084000c6003034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 834697374 1250 834696124 834696131
    0x61404050712060803030601080702030309060a0c020102120406150501020307050c01030f09151410060516031b060c2a030e03120f0c01060602070810150302101d04151206 75
    0x1d420603040c4600380141c04c0200c02142d4174107000f4005001400001c0026007158010010000154004101c0c0c6801468494002c1028280c2d41000d0380680500507104080d500000100010300030076400542140029a42c180792041e00e94004a80324419000c01a00d01e03800204101201e5200c0d40c407030005017100d17030170002d5813901da81c1d06c1c4000e003003580644420766501c56046460780301032100b5068211b82109903955940d46000000b40142c0208007110300300ca050011100e0074180603030b040030340c21407d002c0300d8843d442c128a400b2000300091180c1100103140340e1400220070702c01080c0040241c64140c01401c07009003c0d5811039420594401c56a01800f5a40f144400f882609014206c90103402a080d510344009200d640c0c215111a4810411940f00c08400c101d40c0c0320200e90001d800e9110900800d102d50810340110242c0e0071940025080303814400c10071141030380407046180030071401201100351180704041006031261035043e00880341e103141e01001050a21602400b00a102d8080070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 834698624 1250 834697374 834697397
    0x4150510141b030a08060f13051e090f0f0109030c120e03010f02071e12050c0c22051b090d02030a060c0201091b081002030a0e070f090e010614040507 66
    0x2112815000000340030960004c62007105003070b000144a13500072001da4820a2035a90800094162104e42d20b002190079501c0001c03502041c0310b080600b01c00e98440741c1c295007904140c442d103a6a500c0101d801802c0d402030306030007017541406005100800360540e4810003100d0040d10f032605034040c2c05802d501484207c0380303440182e8600f0f0054184c07508010200684442c124181800c0e20384a500074100d0700070a0105c0d40c00002c2110280b0b440c541507500c2d00a49881103035024500d040c80700c40c0349a0707201840c0300c2c0700100540c140ca40222030001d440801d2260b0b0700d850200302100d94010100e12890711050007803c4090800031041421a40020120341000d20503845400444062034244c20060351102c900001f4018515031400c0c0c40d0320101c103840c941c2481d01c042d05840307009c1141c142900c19000070218440d80440d23007002072003407001c00070707030f20441d5a41d1040110b64141d4071603030f02600c0c103148220217814010700c03403075040314240020394400b51210400c10000301801020a4148507049194 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 834699874 1250 834698624 834698647
    0x318030316030306090b01021f18080f040f050906030c01050a02030f0f070309171009020111011d0111120412090f030c030201020105220b0709230415051014 69
    0x986034014040c1e2800526141800d05c3d0b00c4c15074030200c01c2c2c0c5d0306640c03110001000c416140010801840414a000a0110000584410030b11008000030742064004101c01c00f40f006110018000c84104881102d000c41d07660741404200c0008032078031541500f2800502c1d1803035004400030720054070180706503483c101191400202d00c1c1c00c0414808442040480c19104040c0c2040720040500448824031991105e50481541d951001b40c54031900181c642020000710b90082903042400b003c02d000a10030440b880b0700828072140620803500d002c2d820140c2042060752050110703850103100e410060506e03035aa49521142c0408442684100041c42034002244c1c041c2d030b91844081c5205240202140345940002429070b4405000030116806003880284200c8825400541150340803682d071106640c0c41505940d5020503520010303c10501d0350480450480c01480040c103c441120100105010350807203c0d82d00d04a40030b801d41022030f9519a602c000e0242200d5044d640c4c2c0b80c010189008100c545 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 834701124 1250 834699874 834699907
    0xd0c0924140a090f0e0f0c0d0207061a09160c0314070206040e0118020301121101030f020a020a051903172215050f040b0c0903010e0d090807150203180303 68
    0x440c00040c03d039150074001c800e502c01c505001082c0e1000d0107109400d0942c0c4203a010000506a4031a0800003c1e101080c03039060f80584200c036420000821200d140e07025003e03088641d07400d9040c0305450f10340c0003030005042072500031a400c0c03080c1d48021441d145603400303940b01c2070441c0711039072001000d001900c0180d883c4001000134002e040680f541c44d51414144483c00215484450b80c06401403005011844c0254106c1c0451074100d41c5002c4202c070600010f07001030208406100c1d000380000b80c0d07000003c1d00040c2e020a034510074802c0f20880034510800d582c05110a20700240045c140d96101d2900c2407190f49010380007802c55080d03040d41c3c48448206401c200c00480308540302c0c10401c88400d07404140b8824950300a0720202400000d140176620810003070402800a11040d10100d20b800031620f0075801100c44d411b44100b00d0340345c900c0c50140075001c030301c139031141c0d00307413445800c0d00410f00314020440014000c0c0140c00031420a00d9030514039549a42205003690144001d000c0403a60b00e00000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 834702374 1250 834701124 834701137
    0xc0d0207020f190602150613050c0d09060b010207050102030702090f06011b0b220c05040f0209040e03030103050c010513061b050133030201080609090c03120d0c092414 74
    0x300083c400e9440c0180203800d01a55106515520304c45004000c4183c540c04084003e440c11400002002da6440c0104200c4d801505a1491000d1a00c200041040b00991003548980401d8007110409d030384d580e004a03502d10842a009412402400111710f900309041810340d04044141400c01804141c54001c1700400000c50301034071003854007000e21820454200078596548a421008031140c1d00d26140c01021012910519000d107a8645e0100d100d1501035058882e400c000910520400c1081100d03188d070394000f80801d46e054060342198551030340c021011510041e0f484c042600a07145420425903140701e00b0200148051142509040000d00030700c6607000c500c90498103020042c0074847c2680a41602d446076130080d6425503010310241c0c0c1c01c00d80841c1e105000b00d9085015543d200e080500b48502c400c0d9090300b520a5007148105210004080e10271181368000410280d10310440403544a0300c5803103003030307803526040c0c007011000900c1c0340040d04119064105441e0300d6000c000810319661150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 834703624 1250 834702374 834702409
    0x120807030c0510150b0f2a071202030c0d020a120203010902130e06090313050f03011b0503040318050901030b06010e0901060903050115050a1e090c11010b03060c0d0207020f 76
    0xc00d0036130195541c007080800601103a880441c102118610b4004180c4900686c107200f01c000b0011207000018510031000020905c142a1615940c1c0c50b924440304072240413089100307021348c02c03051440d4140145255001a0024401c21050340307010711078031034100d10381c1041c0d8055480d00c03510b20148e150f1010103c40460040300000b1f4a0418040b0030b810161b0242100425400c00c0242c0f4680c05807903500e580656208407901d1412007801400a401042d4a1701038010b11001070303a6140b02c1d140c0140203984500d001c0c1c1c442c509290b03203a4084c44130340905801855030003030301c81006001117010b4040440d4002818141076264803555400030b1113888090703120300009804000d050042100c00c0c0503102550101c17544400741c80e400c04000400d1624140a00409281420342a81c100314591001ca0000c244a660400000e005418020030050701d1030394114856092008d9401c00d41000600d09206803056040d090900e4202d464031000b9520004050b0303402480c1d58045221540e0300b200401040400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 834704874 1250 834703624 834703631
    0x20112061d04060b01030b031b01050d050a020a09060203070321090218011d09150705040f0e07030b031b1908010f0c080f1e0403031d0106030516120807030c0510 71
    0x98a04401070714107004e0400e04050a040400106460020f42d02c031800010002401c074840c0343d140121b80c1c0b40a68008881424181424025031400583c01007540d41840e90703408001903203c00c400e036500c0c810440f008000801862521000540d055410844400c140702d02061443c0b094000800000c1c0c00e0a1080b40e0340c103a04010002c03080741c03805035002100308200740c00c02d41c039064040c99150240c1d0900c01a450b040000002c10003481401150040d18000f4201c034980c40c1c44050030b0036081001c0b901540428548910a141450005070850381961051400301c0e170f0088901c188210303005005485090209076200c04aa4910207001d60130010428140c00a40452240c100600c02440030300381844004650040c058a281001c1080b944a003001d580e00825440fa840e0031401003443e04600e2208c2c0c0c0310322120008026043d00010110380c061002c0303038050207442588030801c80d5184100354041500142c0c1100081c809809041e00c24000e0400c1c401020840c0c8032039080c0354440302841d050565 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 834706124 1250 834704874 834704881
    0x703170913140a051003082a07080c0f0103021c0b0a0512150105040c09090b0a031e0b010f06090314010e06070528052203081c050f04050a020112061d 66
    0x607910802d070f4002060417006861300e25548540d105442803c1c2107030711501d205c81161048048206090990f0071920301143d40b100e65981c107050f00e03804070328611842003103e854403655640c4a0300030346084c003103040010705032200c145242d04d00503d1400d560507001880410009071071340d200f500a0001392400d202901d60318489004505907910705030002c030301c1649000c0040010590104c111401d503080c03c9400907002d54001c0c000340c1800c0195000a000340c081d00317181d0a480d01c00041000d030032807103034032a038070302c2d0341c03684042c5a20413818058800025615101040402c4424268040b0615641c0000034509401c0450300e0030103208403180340100f90006101000f28019810403c902940c001404070b41d02c20b1118010103621500410080d035007064180c2c58105112800c131271001359402254a13540c5c201d20000c1d024260340149a80b8012454070b4001120303103115840e001c1c400c5038000068a0125a60307070043d5094500c0c400307035004159030b03044041443c0d000d00e006043c4002118007116410701c1d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 834707374 1250 834706124 834706141
    0x13051e070207091d0a080a050712030c020c09010608160513060f020714030a0308090c1806010e0405090a170f03090313061704060c2a0b09070317091314 67
    0x4078884031001580e1341d2400b14140e280c0e800b14024810701d41c02500c04d80d0312405000100d82c01d00580d030018241c0008030203940c0d042e940560000b0040419038082d9090401090b04010804a09100784404101c0402c0003402c65041d00304101054041d6003841800c02c80c035844d00740f040710407503042040030500d46240295201d404101c0d0740001c00c00310b0311803404240440c000c280c507a090050f0050501a884000ca000300e00c046c042d0004a000c058000880b44c0c115a0f4101ea41c20025905603000c00d02e0f0701080030490034940956480f4441d090300801c850510755031000310140310390105228218040c00704141d00700200000718002e82164008549482407072200d0002d0204642c40745090204481800303d5200101d480c0b40c1c0c1c440c0d00500700240d0603100c2e203400c0c0c0c0d221081d40f09170b10031070b402d003114440044034965403280d800d405103103e07486030764440803055502c4099000251034090841451642c0010a600400008030301509100704107a401d0160015228114040350a04010320100001071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 834708624 1250 834707374 834707381
    0x203152e17070602120a090902120402040e0a0203120901052205040f05060913080f0a0504030c1a120403140301181416050d0b060f03100b0913051e07020709 69
    0x80884400741400d1450402d01951720510f604180c0803030600465990b500c5806015a00000d003001c040c155602c1c400d01c8800c5c1d40300641118100d20443c601401c4601110740050100899a0f000d0000c100352341c0e070300301c422403250400200340703040107400c0010700c9a990382e00300d914941c1101c602a429040c3c1c101002c00081d03802c1c003041100e4080c5010200400d503512411099005a19070040540e11500c40c1040b005d24031405d81903650000001603e1803032164440000c1c4200c0c2c0c06140c50040340e5444030744c1022208205c0741c10500c0c1580500402da0048014400207812034803e09040700a08803002c54400260002da11013860045208020321840c550b81c01070031201d059040324000c16150054525481c0104544980c0400c0310200b070b0220302030243d13800b000b200b01c4020942da450340903408500c046648200c0718241400a010000501c11002c641500c8207204000c0c8051070000d80c404c51400108801021f01c2044660762400758004840c4903a05400b61519901414040d800c000088096 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 834709874 1250 834708624 834708659
    0x1103010908281d030109080c03042606010605030c27040e0106080d140f0403080405011b0c210f030201050916080a06020a0903080406080a05060d0203152e 68
    0x9108924140b18601a400840307840c0300050114a0184000c111004c42d0061280c0c180060080c3c1c00010b10303190100e000400f43c400c41d01c6100007800641c1281c968006c2c10f42c007411304900386500074001884440e0061002e15440754182c50303000e00b0403084041081c801c0040680312004c25800e8114000d440c01d0030300503401a6603001d8000d0203080e00c1c283c0d40c142e840d04007191b080200043d503042d03103503969a28011511011000c03030015840300d490b400c0401c55680948241e901140040c5030010300300300c42d140140f60301500013240c002064034001d55101058a201d001810040c3c9814003400041d03031008040200328082d6000150718a030100485142a50410018500d019003a008200c842400030b01240c82075070010700503846004e1004190b80c9008a0341000780f202c0c00109001c07071019403102e80d00d44035408500050180f62110001d01200e00812030002c1d425070414605e0402c80c030310071201c2d103401044000600d00031541d400040c20350380d0300d426100c070030030b4101c804d0402600e00305080b078010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 834711124 1250 834709874 834709927
    0x70512030a0605030a0201080615040504052511030301140f03010903030b0a0f0e130c05030601030506190920060405060403060506030d0318030807020c040e031918060503041103010908 81
    0x11171103000d40019210350401840c0c2881210160f040f600c221040c034042e00c004060180003440b560920282000461000000c21400aa90741002c40d807841d21460303801c0d268415000c095131139039081003101c4078480703a0354031102e070020301c809803075042900c00b44209280ba502945d400954034464404000b02c880c640d600400140000c00018407051414480064100000c05098482102d5a00c0c190b25a541940d11132a41030103680e000205002003c544188100c8140c0003026101405c03544a000701c402c0d4000107880700c000c03010620342603007640d030741201d030032000820503803c041e5a54005400d95205800c121045a200d4003400480e0400300824007990301a42001c1c0200304450306860000d0240b21000b5003040880f00203c0c2c07120f40203006090007410301620070b003d6456407000c0c0560341c1d030051a0210310415a030074a1184a031041d40010b02444c1c09071600311a241c50480211016040074006803428409191007500c03aa509108504403144524802900c5511407140924081d11403410b050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 834712230 1106 834711124 834711133
    0x105070f02060a0903050307120f0e0307030e0306070816050d0203040c051809060109020d060816050319020904060c022401150302070c0504020f070512030a060503 72
    0x14034280440e02140e01ea42c0310602810121a95040041d0001c0d01c01d0000c150058407910320210040481c800102c0d4614030b564460f0200d6086102c202c084d5803002907120105508200c8800c407043c022005061180b9003080007a00c0c01100038503000c250103c004040c0c0489004500b900d098080703001c001c5480b454a031030702d00c150061602819108005036955001c1c202d400c141d032648540c0050000e044140d281c4a1500c01079000301e85003580b050384030803010508a000300400d401cad90102ca880c14440a25203418181400d2031803440300000d41c03060b040400503032a0030058541060744040300058180008908030308114012003009100da5482c225510220a1100600d0603034244c40c2031880c2c0380da0a01000da08a22032010014001c0000700d00400203460154050201241912043c62614540d41c5c6c901d400c104200d0440b141101001c414480c005081c4e00c03491024050680007032 = true := by decide +kernel

theorem cover : BRFrame.Cov 834532374 834712230 := by
  have h0 := BRFrame.cov_init 834532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 834532374 ≤ n) (h2 : n < 834712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
