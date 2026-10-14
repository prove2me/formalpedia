-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1474
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:09:42.040502+00:00
-- url     : https://prove2.me/submissions/3e05d0e8-8523-47ac-a063-9ff4a1d959f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 264928057 ≤ n < 265107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 264929307 1250 264928057 264928067
    0xe03010b060414100503090c0d0f12080106230301050105030c0c160e06010807020a1704030b09010203161107120c0b0c0f010501270c0509100905010e06090913020102010e010903 78
    0x300340c0e07040ba81005802001001507030b0b00c6c88211807404a5412010354004503180840c07030f50715414019050020f02d01c405654000d84040f403e242c520205001500400c0741030390000c08800c0004841c8145442c0b1940c04aa40361140018050f00381480f9000c0000742c454400002512032800e0480c040b00c05401d54000300d145084401d000c1c020f450011540018141d5005442440c01415a94010400101c0686403011010402000203041c054100000404104840c0c581c03805661034800040c2e40c2d0a11011450282203400060018008000e00e8100d01e518046614021244104c46803120f00a552400d05055442504180c2c8070745d00c046015140000002408610704407a40001c000381c0e600c130701100452900c44058264040c801080101c01d50301580c05c80b60140005090541c144851038000650820001003034800098500703104026540c0d000715000a40d16040d6091868810b44901280002c0c0d0014007480c0d080004030000401c5910035031000c104805014001c2021032150b20700241 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 264930557 1250 264929307 264929339
    0x640030c030209011d06221a1201090308010e0907122f030c060913091a1b07021207050a1202031e0a1e020a0312110a030509010e03010b0604 62
    0x1c040c40303c1c180041200d00ca0341c0342c91220440c424030b01740e44554400040042c41b005251980d000d0700c0390703468486004000350046a4404c00e4060940742c0030700841c2c00f030007840c00e00030307112a03c01d0b0f05110780140803d40010030301d41036a64070b41c030a4985903911030515141c254190f1004130f844a40710b4850b000d01040203024031003018900c90b4071901d85692603806816000248041b64150030031000c1664604d00800104000880680b285002c096130382422001c4039903948003900c0c0e034440105241c42c0c0340c01e41c07800035a002081481c2c1aa015070190740d400014001d401e802401b4403918030808402c203004200c150018400107020308031094840c0c16039020382c0c007880d5040f0b029210b960005410a86840140c400b50b41a00c4002d007510190341e01c4022410182650f0a0304403016800c9401c003503101ca59408020350301601c07400c4450300c50514001c3c8440303010f1110810541040300c0b01c02c0001d907c0001c80f0198002460645001d58807400020b00402001c03030600e42c001400113000400081c00712142c0b03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 264931807 1250 264930557 264930559
    0x14070b0403050a180803030a0209010e03010e01090b0a0e070303120e0d0e01021005041e080c01060b0a0912020a060f0909020706090b070f080a020a050d02031003020f0640030c0302 79
    0x150000340a1216581403019001e000701750b8100b48005121542170b43d002d070a594105140c20251030380220042801c680c40100c007402140d440b40c00074000d004001c03120356044400d81500f0001126280030541d15419a40001801c008642e03200c04070f01c01d0650862955440400240c2e441514134080181c090108022800c1c0540101c0d444252a0066841031074821a0000400e06101c4403010041da01811404801c6030342d1a414420025980024403501c0058014601055035032a182c0c003000d00044c00603482880706005074040030005880d0100310030202c076558105000d4811011105a030803000300c2d04100000c52011848206000d8250064480d00d4043c0c800c501640c2c0340c001c070441d000465100420080344044000ca901031007141d001b801003a003640381103030802c07440d100c0d001c00340d03070082d14240e00040500c002030084d4640203001d0a0340140848480d450300f62251a040c43c2246088c0584801c4180ca00c03000d05441503000c1c180c52605400079642c030195440e0300d8030301113101e0180002d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 264933057 1250 264931807 264931817
    0x1e0703150807030812180303010909021c02030c101e090f0801110a050c0703020d260a0c03110c0d0c060e030703080702042f120609060607020114070b0403050a 70
    0x91200d4003040307480c1500d400c0001941741400c007503140f44a18070080e2460f00160801c0081400302c12003480914040d041c081004034801c04a80104000c0341000c0f041c81c2401d050015000380165400220511100010790300b0f10014528100c0c15109221000b040e00d000c50004030304e040400340d100b9061410f0f154100c400c503c4003925159454200c6040c4409000074003001c11050000ca40904094440d0a60300c8046a101c140c4030760100e24102c0c40003c0c02c4a400400480340d0ba40d1104024001411061690b0300e10b06109100e82c0040c03600d40d240d44040c0074001d03902c610b06082e00081c2b0102001f207202900a0015490314604001c1d5403102d840759000042030301c03000c0d403440e240c00315200c000c80f504400120305100e690307000c1000030700d444044081d10324a07501860404480024054141c50182001c44d502c035001100c0d404500c02d00200344500c11034a020410200340e4410040e50401602803901441c0b40d220b000760300070fa6200f503d030040e2204c180c0300c0400017007550002c000d1409800965071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 264934307 1250 264933057 264933059
    0xc080304061701030b011707081c2c04020c07050306010303080708150d0201050d020d0e0c030c190e10090f0903090e04030903060c030207080708070c050114030601081e070315 77
    0x690042c1c00c1080c04018264822440100684406030004d01c9080e44c1150030343d44a5039503103c0b014600740d00508003c40c580c2c1480b00751180d00d9000070441c450041c0d00c4901c1c5a4a2010901d0380c4c0e90004045410f6109a5010407544224003003008000301508014044421558403810041d203c442c0446110000407134100009010680d040300c07100103c0c002811408481c015580156023a401c64190155001e500340140c0d0300c80c85007400358a400c27640715006003495440325024182090030000844d40a90403e8040600320003801a50b4000c60b50540b900f0207840e01c0741d040031aa140f0301e0360b011004082c06c01502c4000450581d000c0c0d20851b21a45490040c21382d1030445e556903860444c0d019002c254045400c0011803950340101c54144003e19005103811f580e0340d160909a000103405544400011420700100710100403268090002403c1259070800010940c10081c0b000404090400100304040741155035072078580301c152080070071549068641140000c0051500d207494410045070100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 264935557 1250 264934307 264934337
    0xf02010e0f101107051504021201050f0f0c040f0512030408240115020616021920011119050a06050c0d05060f01020a111302030f0106110d1d010c0c08030406 69
    0x1007240e0b2455881000386c40c085041c81c280340503102e030081c810b0ba080100ca040d03103101c0d41001e00c00e0620030002c0f46104882800c128030f08504c90711009185410700d4100304000e102e12512110409d04441c0122490213908002c84901425402030380e010700403a104420b5012108100010400c269041450808560b80c1c1d0b200c034000000c5031100006005a008000821410013a4614081900c6007500444a41e10180c24000c0340504100d002a60306410f02081c0c075919118080d07102d00c4d4690240313480c51507007149041c8251180714281c40404c02c1d6401c0d103645001c00a0501000318413a030000410005407814810100d60b943c80b900e40d50f0b0403e03141400044a42c6050007110744400010b90081c50002c0c8103030b5401d4041e95000950b00c0d031195040304074038440800c0d1b0006521406c03104040c628103500d0030002410b207035101c0d803240909400c00700c07050303040c240d20011341d03460301d0440b401d14250025080010781d02020b40500c06086a112070300d001c181d140c40000100201d518940d140416090208 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 264936807 1250 264935557 264935591
    0x10f050c0306010c02030c0a090e1c020d1211040308070b0601020d050d0b060708031302030f060f0c0307030b1f0e0108010305060601030506060c0709051005060a08070f02010e0f10 79
    0xe481205400e801c0c004120070f544079000c02c410051002c0c04844000383c0d5200000c040140541c0304058044d102c9160000380417007440966194080755160006190b60184069103074800b0074040c20400050103100c42d071401c0190480c000300d00f61455940d588584030f040136060340d4040801030f6038684c4c041021914a502c00504d0340c0c10751009aa80600b07020f0003910900181800b5819030758008014030a010201e04072200542c007900200b14207543e203e40700d105244c02c3c85041a10a036054100e03204101c148031a03000c2055214400140055803587c400e0020380080004440d6180c004013081c0035240003071780c2d101c011804c1103055140e0348044550f41004540040c3c003400010b096811103000f1440c00e50180e0000e03900300c54000c00c0039081480c00341d0705a03d400740940c403400d1015121424001803207100342d030550150a06076001c9141145440307029110382c9005c1c00d8a420000c80301c2e40002224400e6000a03100c1c1c807200e041da001100c00c20486652505100000c074504d500d8130003207425100500e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 264938057 1250 264936807 264936811
    0x315010e070f18090b12011d01060b07081204030c1b030308060409080d0905070515041a210415020a09090624030513080a050c1005010f0b0f0706020307020708010f05 73
    0x559643c010007810800c1680103800c0b000c00c1c040d00500a041c1c2c04080a4080c091400034060f065108400e0010200c00c850a40d14503a00c2154402d034208101c0c8082003005003150604d03442c49140c00803e407600d2030101c419094000010780b2410380b0340b80c1d98000d810300b00005000c480c0a55140c3c1c000b5140d503000c10007180c43c400c0b40108024010421020074180075042842c3c5c10713000f1020340f100c040d5900e000c1001030005105120802c600004d0500000700002d0045400160b0701e440039082601c14084404002e10558244001040c0c2c000058200090b17064403d0000d0704005d000d54841683e040054114200e03030107211800350800c100858012490b07081c5007075010490b48280c0d001c81d02518260000d01c07019049090401d0f18008450200b2034800080c8204070a80e605c0c560398240341c0d0026030900305c0100e0041c1050f410800100210509284a00d0a903000740c0056aa0ba040c4920f4084481c450071310000e003110b00120401c4403064021622004a46100009005d0111280040030482c0c03c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 264939307 1250 264938057 264938087
    0x3080d0e0c01022a150a110c09060f0a030215070204060503060603030403240c050702012714030f070f0e0703050709060e130516110a11040504020315010e070f 70
    0x701c0f078030703040c21441343e03442102c0c04030060315421074442400824401d500c14481c112181400048400189510451005003203800d00041e0503100d42c0300000402405016204034810840030303a000d4403c3d80d54250300c000840d401010300d1800b00c2c6802e030013880d503080118240c0c070440c0f50140000e024100810010311904005001e0341c609400c5545411448403482000c6951103102207001203040643c2c4590250740010740c658a031038200a00c0014200d08003c40c0036064030304480707c00102c001c08003180b4010703034040706c4080d540020404003003854100907001e4450799104013140020301c404080d030350900361000060186a10b944400d400da003903031015181310002490300b80c802c01180d0720810041c4090070008014501c071207003030b07950542900d01c150703040e2044150005900c00e0b42d40c0c202c0982c14050880320050030b000806500c03100018900b405c90300e8000c94403440090115035041c860341d0107010260b02c24010315611002c846041c1d4808a40b80320118400003210094903000c1c58001121401c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 264940557 1250 264939307 264939313
    0x1401090b2103030c03100e0c0d06090c09060e010203070b0a0e0d1407030f1101050f0a150302060711010302090604120314041412071a030402130603020d0f080403080403080d0e0c0102 80
    0x140d402d80000365900040500760b1b4402e200c0c0e00884d0748031040c01040d0168502540c2e06459076242d030659130848805910940780c0900d440722800c600344d0000c001034102c03001810300c0d5090401c2d2400507030451140d03d600400318051502000311480e01c5510122600703c18200712940100d1004040e5141010481c04c912114800e00c030040000f84210b8900d8a107034500d1608921003080442407070309681c002da85820400ca2840c081150640c0c0314452086500d448410300580d45195802194082c03241ca40302510035030340e55030301405a9000e6011151001c8010780300e03568880d80c460703029083c945828130441c001840480f101984003020020f071810b40e03c02d5124070038050b03050b00405c80321560302140d208030340c00740396000215501d00524111200031a44450355407454103104210340750303034550602000180b41040c02d20150700d07500140700186500c2000100000700908061115004641c001803005000140c0441003056002c0509441102000144045a401c81da0a80c4440d0400d000c940140c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 264941807 1250 264940557 264940561
    0xc090d0813050d0602090108091f0b0319030207090b061c05040302010908130e0a1103060d0f0203070f091802030309010315030209011707080c0904080a031401090b210303 75
    0x18850001018203511007550603000c03907921004520300392078010041e64401d070b001c030311008103581044d0384613032020020020307241c1d214180421521590b5108032068015a0303039504c41200d40ca0400840c01490100c00300c01c030300340d861490f009641340210b00a02e1001e600b004c505502600f0302d541070b1421101d95140008003c4601d6403040003d00000f8420390456494403c03000208940304018a01d69040044050610341816544e803030010740039085080d198544a414034000c41607809484d00b00798111040c1e41c0e600c0711070500d0015150300a9000c1d43c580070310200002c1036012800d280086070681e003414050b54051a13002e0300e0785504203030040e4240c1c10802450300558440e03805990f61341004195805d185850703801056896009820094566640340c82e0724441034010400c110040106900811106003050701103007000a01400051680b000071400d80d0503180a80c01c65240c903500750704462519a03540d003e000207003212541003801956441094440d40041c098000c07400600b0400862840e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 264943057 1250 264941807 264941813
    0x20d0b16050c1b030a0f0804050a060531031505010e13150c032003010608130c0b030a0e10060f090204080a08090406050607050105042102061602010204080a03050d050c090d 76
    0x20003e85010541c180910340e0401c0014071740001d200f4445000d90305442e21103042006001007817500e03800000501506102152204a41007500d0700244040003e0b40c0000005901c00c50710007026800041c649940c5000e20601d161040d03010a040703950714030695516403240030004000220080c8040c0a0050b0500c41c510a0a040e81044215599030718001403603550041103681d040d90880039000d807944000004108442d8811922034114150f0503020f40703000360f1540c03034818080c05849500300714600840001c980032260b070f100715460040c280c260744410002c071580c0350081174507004000100d00c540f800855900d00c20302c00c2d00c05540c40100100600509502c80d641c0980040030b003ea441b64a0300800b0a50340c680c400908040b520440000c03c040c1080d15005401c07800e000c3e0680d040307000c80051500250781c00a803c0b90170010103a4811021a60f503c812400381c0f045410903001c0d8843c03520000c0c00c06174004020b0a008100400030085911340ca48418270922032074940301c0d030100d4200c4c544404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 264944307 1250 264943057 264943093
    0x906020a030e120706030501030210090e0a091707060e150907120f050703030906031b08010308070201120e0c13020306030a021003020705070e0402031005270703020d0b16050c 77
    0x140d442c0205078030014032050100d107142c80391540041c000242c891004208505090140082c40320690401d00200341c2480d0410001c218010081c5031003c1c0c44100074010310100c82c048001200c2024036460381c4140c0d0b414100050499001c1070046c1e4032400d944064004800407560703005003200d0029080765454800502181c5000000130389007403166000c1d480c0095803c101d000d001311700c80d8850b202c6091070140c02508031542403514200d80c40c0e007198880d170126800703062241507940c84042182c9803011030004071542c3d4407204410109900d04602c001d201c41c00003400c4508a42c007107910458600f5047c80440c1a408196016a0540c0c409c2110317000620b4002071803500806180740040c104405074032410b140465aa00850700e0b07911610501003541010b08c609925485500c100384594101200c030480030302d2080c114282c2e0442121200750a01e101800b4034001140c0040c1640070300d903210304088240c9102540d848a003042c042075580112401003050714001c00e0760002a00815a401008541c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 264945557 1250 264944307 264944327
    0xd09060e0f09041a0a09020109030308071701081c0c020a05121f05241e030106090e0102030901050612030d05070e041d060c2d0412050105040506070906020a03 70
    0x2511007141c400750240750710740c070049510850064040d80b030a244988240203418a014240c0b103030b8203051080030000350b600710b0716010440c1e07494030f0504241d40c3da9400840343c0350502d104201003a101c007400003c1002d00001c0c0b41a0300c0300d04c8215240300f034480800580706070702000b00003074124111000400140c0340c0f11740e15000c41c1000d181515803003480c2c141d01c00060b9509070208034402d55110141b08a01c0440821000344aa00c02c0d201d07819208148001100110240a003450307541e02070141444544080d00030300000c22210500307014543c01950001d01035001220080c0701c540c03800300000e6080c5030610050140543e55006546440705506840d4003401d401408901031020b41081c20486450720300c2074808100e1229002503801651420305030400c1001380c404585007405114000c008001c01d25070840160000a016403002000c41405506005660140020110214000342849011f4021134411032281c030a80b240c1d079654600544481031365020300e070010b81c800c0c1034000c006402240c0d401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 264946807 1250 264945557 264945559
    0x40e0c031b040806091212130c05040e060f0604020f030403030b0d0b09030d060603020405101b0501092001031a0108060d0c0b0c010605060405150d020906160201020f0d09060e 77
    0xd1050705078400140d9142d800341d031140300d095200e9410030490720000e1050092111042d02058902484400c039014511000780c0302564003000d03181110308108180744c040c0c2c010f00c006041030001c5500b1001c01a2105401c4500d07590f4881c0c80c00c001003092410f8401c413074892103a10001811901c070790310104c0090809820550300a000d5511070000b08401e1200d03c1e1242c1111001140c0e00c0d20664100810b88445074801018180103010601c000d9987d1a02c50400307040c603251003c81c2160305e40701c0c40712200000310041d1a17946040908014421740070aa0080c60038100940c0c002100a4401102215004c280400e07403406034600c0120340d503200c0c4416a80040009103035150703444454503241c1f2500c019a00c070300304840d80020400b40b000d10a00440006100840340c150429203040046004000040d0216900c0c500014100703003410344560584409042c00303840180c48089000d00d0364408070340c103a4264054852121070069540e40001d00b915000500e80c2c075003040c2440d115040d6103080b5103805071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 264948057 1250 264946807 264946831
    0xe1f0503100b0409051807080c10090911031006020c060703050c0c1305091509100e070e010b1b010b210a05030706150e25030204090c0908010c0302040e0c03 69
    0x14074800707000d0140c4044d01051500143c1410f00490003a405805402c0701c0c0301980124200308171195011a0ba0447c0d0305080e90f40c1059001030200031a00542250060020f4500d4400750b140b28189980155100b40b019003180e15955444003020780e5150109643c03140e03c22001c104210000303100d003000d042010f0440040380c1181d010800060000c02a11100012840d91007080102c0c61008201c002003110b024240d10071f03142005130015850380a6220582c95013516031070307108680310007048103030020f00c134520366200c0b556140c03400c185140e40030080d08038a0540c1c01c00003500700700043c86014400e4100030a411340c02447c4041c1010b11440010412405010b03464003e804100d0a000501286204079030000c3c0e8899000345107030b0568500e4229120b0500d84008228210314400c40c071243c50760501191500c4c0a203a14401c5020f0312441d0005842c2c1403c0c4a0030402d69504a1b2082e4180d4400300000c1c0229814140b0071000c83c080c80c8682541020300002048403444480c00450b0010b4000d005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 264949307 1250 264948057 264948059
    0xf0c02030d0c030311090d1b03020a0b0901090e010b1b070503070909020a0e0105090712200a1103030709050603040501020f0408030309060708070903060507110f0106060e1f050310 79
    0xe420690360004034804148400341070410950f05105d403d544c80d00c80311382c507414004400045640000c82107001000021002e012120100041e19910300031a4010b01041c80f49446120501050300081100380c041024454046801b048244180c1e050b240480205400e104081064805000c00095222824012124085115102403240801500301c888000c251281188103000d2101040d51002c0000a40000140000d5a801018681181062400d00050801402171700e00400c00e000c541d005401d0b001100c0c030f1410001e00c2c0900500b1010303071610f070145101210042e861344022112600000c0c04a00e0031701107498188059030304140200300050401c101070b404442c00d684075400a1603145d10100c200404904c04100b400c0d13000d07489140501c040e0030150b20240040301d803400004d040790788800006545074841ca43c41c40940101c0307006c031528120f071100c09600801180c02904001703004200540f9240c02c0500080740711b07100183d4125001404440d084941e5000038044540c2204c038500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 264950557 1250 264949307 264949309
    0x71103030423043c0213081005040203070b03040c0b030f190902010e060f0d0501080309090702010603080306060913050708070e010507210504090c051201050904050c0402090301090203010203090d0f051201060f0c02 94
    0x170282c00b1512102c1c13a01d00c00c884c1040c0310189400c00c0280a41249030928040200588020030b0203011907010703242e60b540325282c0b440c0440f420030858000a100c0b400100070030620718038015065008200c082e56511803c40071081d00001e4808100d0302a0100b011001c005800d41440802041d0a072031440142d410b000d2580d24680a44200ba80030708110b510114085075145840d12415030010403d0000300685851950b4400e15404002c000c10300c62a0302090008482d21010445000c40448850801440c980b025001c1c101003000c1e110f42d00040c4401480b04c5c02540035404a80c486a003040001c03082c001612840100d45003010322039403c00c9000d0100107151150f501400b0501d01d280e88406032140418442c668040c141680014401e040600502002c01c00210707180e040050240c802607a03442203d000319001d004942c0000b905503200004000790401d01144007120000300d583e48a020240500381150030740103100c0b115080028200040000502031074010f0640340c02c1d410309152034080346d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 264951807 1250 264950557 264950561
    0x203100b070f0201050f091e031203090d181517010b09010e1314091b010305060d020d020f1503090d030c1d130507050c01061e0308071103030423043c 66
    0x1c1054041a00308c0320120b046480c0501c21100c410200603521825403130070a41c06956402040102d0003030200e090010514000b001c4490000742541d0050100041c2081a00038041041d0451008030840b4000010070841d021100301c1e4001d4005a41d8541e404c0c000d0400c020f2881d0320b10740704640c4e0aa444600f000c41c3c07001141c0c0c040c0705800200c05002c94000f0002c580a40c0314001c1030050416103803004200c8565102000c440c035040d015503645696204500c04a5902d040d40c1c0021a404203105060b070340340c150328a0066109a40c00800c0d51580d0801322819400c3e034101c403480c030010620601d408110050840c0903000580300050842c845018501307000002c0743c0c010380d41c807400030742c001402c03200d1103409001d814014514000b0b604511502e80d6071b80d1a5550003400024a98500002e03043d003402800c2d21012200c480050035a84d4440d9222a441d410040040030168500d0b200340c003560092929105903180d07461294625113210115030020000e03003680f030300e0071800e5284442011590000e94 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 264953057 1250 264951807 264951829
    0x906032805060c0703020c04050112030c11031009050c04090b0f25080a0b01020706021f0e030c03070516150509011106010e07020c040225080f0a02010203100b070f0201050f09 77
    0xc0c3d0b0115030316035039424001d040943d0420098022414080100f056048800041d1719281c5c1500c0d00006a91140c030780222046151501c1f81d0703261190900c00094001e1540c41424242d22943c2240d0344503084038140015a40841806084280d004002800d95600140c030280e02c5601100e020444102e107070802407011a07a10b22540004942c80100407002c0d01a11450103903d0b400d0008180c560310740003000b560b03081d001a000351500e08101c1d0084511540350000784181c1c8442c030a40341c8032070417110290358a81100009892900c140804135110101388030403d8150b850001008ea1a0801c42c402511554095040c1c94100405940d43c454111002d02c44c041c040d00d0200781080980c20810b074002d28150118209034480d0344100454400325942d0b103501288000400e41c88410b082540c2000f0981e0301681031060121100000c0c2c000b0030341d90650066104174001c17500f24070310b951904100f601500810500030400225039120602660090000e000c203c009003070712030328000c02c0f140420810b1240c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 264954307 1250 264953057 264953071
    0x10c032007020a0b03360c10030b0a080a0c061e051c0912031a0f0906030a0b1e0106110c0f12010c05040e060105161e060216020f090603280506 63
    0x101007481851855140c1046181103800c180c40c840c00386d141d00b076290b003003910400d40b1172245812418210b9000741c201e000c80010040042301110707036413a8805d40301d0468141c100c0718031404840103c0c05a001d4444c005080468030f80103400e2036038860054409a001078031140c06452440504200d4090300c0c000e950301c80e4810031046a03a01c800032405815210030105403005d4140700000c00c3c1071900c403038040245080040329200300350b854a00100b03080070070104002d01080c03104810003098054070300f0601d000013940c00c2d42d92600d80e40c0e1803003203d00c102d100401c0381950f081866240b02600d442d8040d50b480e540028050f180803c5c4242c00c86084800115050000c500085000c001345a00302d007079650320907006e00b46946080088d01140c2c65403943c106004051340000074061003d103107105541d0503515401902103540710540052011062001e02e812031282c0f4640c00790305401d040a604460056402800038000103010003405138904030b55461804298901c2031080000c24420400a4003a101e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 264955557 1250 264954307 264954331
    0x7051203070201080a05011206020f16030818030a09170c0a080706080a090f1e06050106030509100e1c020a05011103010f0e04080a0c061404050f010c032007020a0b03 73
    0x1018400036000010050204245d0791403d00104100307007040c1002c1000710742c050b000690315800c01c482c3ca041405071841070004001003408043c109900030742c0042c0241a101401d82910204218050382c1c4c1c440c00d0240e0000a02040007080f22a8000301283d005103000004c1e00d000e2411400820350b02c81080d44081c2c1c02c0ea0101c0303010030030143c2050340d070381d000142d0540c03d00c40205962140c2e03032590080d41c001000c581900e00c0c0d02005001002d03007507407050b50200b024810340d40c1d11000100645001d841c0044070340610044211101c840d4411501040006400741c1442035524468070001c603a1020b45c0c4c0150302404a43c4c0000880a100308030860003144101e9480c1d50410340c8420a1074110b401050083e01d4502c10b0001084020054884580542ca0a5040718550349061006044a0608411195052401c0c0001c00c038000c900320a8100c04040208142e80030544114180c40d410002034544e14020701c10300300110b10440c010800030380042c004102d0150f4842542c0ca10f40d01c00c54081142d10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 264956807 1250 264955557 264955567
    0xb1c02180f15030c030312071205090102070605010504180b2d1005010c030e041805010510060206070513050609010201020c0f032104150f0b0303070303150e10030602070507051203 79
    0x8142c507800c0a01c1c0c81d09600410032040c440012a580e8843c0b01c80300020300030b0760400034040f24814100854102d00c1a4030a011500344402010702035005001c007158410f00b08070000c03031f043c1424450703208121059402c11004801d9a2070321180c0c00c1c009426151480d00900f41c2d50340741c1800c031110003414110b0304240301c602d01e4041503410a01c0e05035080a0704026030004000040395004c02d10040c0003c1c219800074031540003c00000030140c1c0110010019400e07c0200021915213051843c201d44d404e40944d061030303441d02d01c1203480f0320810502201144080c0c00600c501d041002c007030003103c8010b000040c03406030220445883d0880010340510103502c0024190004e036180c86609075502d02200b4405518181036079010284450a1001702c07204e0750390b03030560b800c0c11090341128090325005010313641c3e186028280100030303000010342c03000c03908416640050f50301e0403016200e102e941030015040e959829561580040e500515055a55101c2c802011600790360300d400c9082001d034100015a0b0399 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 264958057 1250 264956807 264956821
    0x50705030d02070b04150905040e01020c06070305060d06050402192405040b0313061518141501140d2a030b010219050109082b0b1c02180f 61
    0x8614241e8820031900441d034200100b4120500b500c060303038901c1c0f41c00d03031800781c00100071240784446a0003d54800d051800030100540198020528070400c0b0342035032210b82c0c03401c0058050b11000eaa607035402824809820010070190b502141d0094401402d0340c1010101d8022120301d4080c0c0d03080303050f00200c181600d0b0307001d25121f80074418000250030b0490800b440d140ea05015030000902030106900c8040b000020000240e00681a0f660458601c007007042d106c0a410b0720541c00401140c07660352030704807c0d00100c0030717245d84148511651f420345501000c01c82e00440700040c0d40f08103500b94030b01c1030113140c1c91410240503055294807400b4410341031b5500c0c031400340e00c50b0282800303481c14180303419001c4509036404600610400d05402e11110036240758a00b260041420f220080c0402102052071076001000301c00000310007a90184200480b4014100e030700c1240d071600c0c02c44d40c1c820201696030070003000b50a02c5012480c001040045140d11401400120102c2140c07064544500c55041110fa = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 264959307 1250 264958057 264958063
    0x606080312091f09031b05060105010306080a0b1605070c030609060b040c080708090a08030a0501091d0c040f021c0b01021908040b13051c0203060a1404020f01091205070503 76
    0x8440c420000902501d038460081005503a0f801c004004096110f402450501d030260a0000011426400c0c400801c0344605003941c80d000d00380140741c0003e043c481d00140300c240008050ba01c4941000300221141ca4031101145140c41d0310204105208050140401041010a03200c00a50180c100801c0b43c13a0300b403624030105e403040d0881610507850a0100c0503070310f60045406922246506040e641c5464030b07039045251074521503000300000b0000040016404050300704904132103040b6010f0195400da00f03041d20714070031150360860f1a80c1c00740f0316405440c90980c11800c0d190420781d030700500c1d0611070664406003924282c10101026200c0c3c4200300c0b2075030704211030044025160300c107020a601d40d65600c0d200c0e201d00d20416462440104c0c0306129415000d4070540149002400c05512099118070490300c0340a145040c0e01c80c0c0111000076016540d1400359050000c80411260025a125404c0040080c0070703007034a504001104201083e11a1401140700303186004600800102d46002e0425107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 264960557 1250 264959307 264959311
    0x2130203040302060a0504050c0d11030a0302012007051c1202070f0209090601060c140c030f070807141c0309030209012d47030405010b09040c060c0204090606080312 73
    0x4441c40c5401d041201042c004249c03595007076401c2381d1580075250a8140014070702c005802140d07050060400110401d13805500c00d4240300604100c0c2d070051a082d1204007401d0055540c040c2c41c58006181c0103040ca541404e03030341c07080c4509041c01d0844807010300d2142c0880e08100012074100400c407840fa001d524007160095803000e0ba0030b00404442d07040c207400070a03071940c07840020426040540c454202000902c52012020300c09002c881d0085003c070f684070341c0c40e42d10b13214500c0e640c040c6020220b45041c9241e900104800301822283c1d4001000f4058400c00000389420350401072070100110040e13981d503400328000c0500f202c050614005021248204961082a44440000c0c5040800104144d0951440c0030341c030b00030004284880b03210945282c0c20034482e846c8144108464101c5108900328051800b4500502c020018042c10a0511285100035034010b461009008002c001452041007040380d03680c809040030410040e566659400d4800d20f1700200c50fa5040801e015400081c12440c0136 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 264961807 1250 264960557 264960571
    0xc0d030504080a14010b1e010c020a3b0402030601050105030604090b16090605041206180507260a0215031503031810020615042c07030b072d0306030213020304030206 73
    0x34142e40e0387e211500030925110030b02d060021805100c0d09550b43d184446004160340d58544a4643c80d5120341810314950301d0310100103210500112801000041a091040381e000d002041079074280740040d40d81d40c20040c01982d000351194215000103003444070380c074001e1038038003078111654a80c004007510101d0340c0d42010742003100a1100b0421040c00106250b0350607041040020307450410b58035180c511301c0361800504203200e0101c0000300703050711210483c406000c5a01000354011008051901d07038000d40e0b40a58001d28144c0c40340054110314000f10381010f9a400500000d0800030040313410b41c0c02101e8100c1501c0701d007000700e00d26070500c2c0e00c0e0b800b0001d9203880500032500e00740c05121040270010100a00540c0c2c1c030044d040800032403001c6c0710003808014000103040741426812940d00c2107540801c91ba594807010101d094a80100030020b461214035828030880340400308201384c0340c0c2d41c803500070301010388600000000d41c41c2c1d00c02c40107444440700405039480c585400c0192500c10007070100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 264963057 1250 264961807 264961819
    0x70b06030f0d020c0409020117100303080f060d11210f0708010c0f03240909060c02010b28050a0609080d090501090e0a09140d0e0d050c0d030504080a14010b 69
    0x1032141c1035000ca00c4c1182d020044400051311002400100d980842152500040d41c00314001d0105e415041d1f071102045a1282c0c0e80e6203071070380d03491060070106075040c0c40d030b80c2d0010307072891141001a8200508400105000c0e16041c54034051242c0b5242c4a42099124100b80c0c000b260501c041c0007044c058500540b000c07500130702001a1101d4003c200390042100c0800301565894030307960500c2070040900340f981d010754450044c140c88244c0d00000740411001111703154900a40103104c0ca0060140c4c00380c1600023404140d401000c00518041c600510700b142c4d0380005220008246a0b40b44040c41010340000c0c0d03100c1c455a410700501c05d243c00c0019000c0f600384080082d080100342c1c1e0104100041d04d10f440c2c80c4084584075080d0000181403d50001040c503c007c55020002050016601e041521640e841d495006103110902987c918840d9000c0d0080d000f40c5000c0b8002d05154040002d00c6110740303440303440c2ca55900d58140c01c00303100d46821034800d440700b040300c401c402d800d00441a0381302c002c841c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 264964307 1250 264963057 264963073
    0x2030303150415030f03051c05010608090c0909030d0f06050301020705060405070e062103093114150a1e060314061809030c120c0120070b1b070b06030f 67
    0x1e90b843c0c00d501000003420007800003400c02235031652220000c48266601020b02103940c42d00000340c42c11200312100c807002d00c0b5110314034400303290006a042c00f0304600c1001e10300d4049034000c8440585030340f42c0100c20309500e4000006803074401340300801c52a800784014108038101464400c1c04c204240e8405480300d68482c050115036507800a0000202c051b043c801c40b00d003c0c010040e142540541c1002d0f56121080000310000c452001303050f0315580780c6800031580d92038016a80c1400f107420400c44644002c09681c001590700100305200c824681000b0300b01c81c0d100e81d0f56a0080740c0405c0d05c126480d000074104500300011074060240e103201050303020161440e8a0207a0225090360714503d800d03688a4800008120504414000c5400c9010481d00360750100300d0880c1040c40c10350001c00380c0501c0c3e61900742c241406170020042c880c10b42c017900c04035620384442030320707085a42400646003040881240e8440c1c110140210000d2260510402c4c0c000d50900e480400c03d070410004841d84882030f040041d07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 264965557 1250 264964307 264964313
    0x9010e010b0a120b0409050a02030d0311030a0f15090605130c020a020d031b06020c06010509040f0605060103022a0c040b030d03180b090304081606080c0d090203030315041503 77
    0xc16a096060340f85072038100e406030307200914040c0800140c010381182c07820780284144000400c0700323030743c0f280203600f02c411200b24003000714111000e441c00c1e0200000140b021480d080303a150460310089158141c0810103200c10b40419100e20051b900051403d03586140400a0782425840c0c10030303076004203034100481d100ba0071019484a040e058020300c9180c07000c0d80c107003c043c000c44850340301e1002800301e1132400205107031200003544809250780b001c1c0300c0e00c000041e052405584d960302c981d40c4021520b2204e106070750f490018201c043c0c18241415002e014251a1901c030041244402540300204200c0c0c4d40b40f07000302801c00c007081b1400350089082186209c0d9948002030000500354a1703280c001611084c58503105000300c5617000c000c0401507510240005a07070b0000140044c1c1d0143c20655068030501c0b0b011540e902054842c80c404241a0800520701c4801c00d4050100725031030440208480c0c0d42940000d042d9441154904841e400c0030340b01c64060f05082c41200010b403420b6407036006442c1103403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 264966807 1250 264965557 264965579
    0x14060103020a0e10180209030610031e11030a060606231804021e03040201080903040e073c1d1302030915091e010c09060f0215010806040209010e01 65
    0x40030748883d0501010125181004021101d8000e0000d55400210410711051010295004100e0365101348112004511230999004c40601160383c407807011003ea80820908060882581000380c4022034841d081d94500d803018464207610b94400e1034000303001c509141016041c3c1015560440042202c5000600d03209060421102103075042055540c0300c0c03d05c031000034082e104264074001c40e0a405254405442c0d0501d01850082c0d00c00d88801020f99500110075599000c5e0313104079803a020f4080041010240114450b0700003104c001c4410300315144001d5003012007901c61030307086030354042d103090301005543c880d1484900802108040e84410b9442000910f80d0501c01d8030725506a03130000100d410110100045400c410720307841d080c5d1035881d100c0c0760141c40d400c001400d0b9561685108203400c0214041c840c86034904406c1e01c1e600b1400f424403808a80d1a8805021f00701513100d00200149210070300019030b070003042c5841c01480304d49424818030545450603440900c51249000c01070104800807 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 264968057 1250 264966807 264966809
    0x909011b03020c0304030503070c24021207290412090f0e060f0d080a12020909041103101a0f030102120408030c04170d02060702030a0e0108061302040b040314060103020a 75
    0x1070724015031500b0704402554210300ca1039000030305c0c61000055040c20032013459201401c50313902d5604a06c094803029140a1030b580301c0036030341e0010780086915548405000e0040c0c03259078004c2e18201b02000b0603035095810313200214444003400f07120b5010041004070100a07401c50280600e00710412501d002144410349600d03000d680800c280c1d1000040413901c85400325036148900401d0403079035200c9030508841e0b90703100786d900b01c0014001d80403450b0701c0c491034002c691004001606c512116078481e15081a50003100c3c011941c180100309000c006e003005402511500c046404401006144010400800c2514411818080e074012721068007503082c81c040302c0b0b5205030800a0180d0303c0d601c020003c8401d108907000300c403c1c001201d200120310880000c10000e00d40a079002c0b5401e41d05e039094181c0c0c1d40c0c09084184c1d0000741241320344010651050300c0c600e8011601502f2503992480360340b481000c1c0d0300103802014005802040400500402581070800b0b4110700e000781c1400d504640100b0440559 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 264969307 1250 264968057 264968111
    0x8120615070b0c0c060c04030308060301180b0405010e030a020c0915061c02190806010f0c231c021f0905060c031302030a0303052710050c0c0d0806090901 68
    0x20400008441408070f0f422115100074031001c0e038000d4500981d02d4103c0b030300940030550000795500c0000b0164281445210540c3c1108065030742085600d039546080420003d1007120555200c05a4050340502000600340c001080e802400070b1040d903074280140e00324000c0c20184000c81001d96180340d5100d2000f20303100c860640507520200d090b0080000041c0c0715031914000d4a4a0780c9038200c240640c05921180164400d07030b1040205e00000000f100c0f191550034000c0e20b5910700941c0c400540d0250090314030141481d0742558a140d500c404a030340348a601100b0303800560480c03a01d105058481ca0340c8900d81e05d0b01940104000007441d260180d8446004200024540000010840140c84e045c0386d00491903004003181d004469a15000b8003400041d18001d15840c182c2011110302d039003031484000100301c20002060140c03011801a0007904010b041c000614104026036480c0304014820100b440c1150b803201e0b02e95003801024859031100040c01426980d00d001868201094101302400113251 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 264970557 1250 264969307 264969323
    0x2108030c0702030708070315180c1512020c01090c0b03090c01080c0702040516090506070b0f070306080d020a0b070c0b04110109091514060c06071b0b040812061507 72
    0x10b00c0800d2401002d178002c41c5241c4981c3c400001003012203146040c6c107801d0520140a1825501d0307000c03517800407042c00288100e0340c0b000b050211440c0e125140c0401c070031600d8510304000d86509620220f90006e004c0c1d0089035146c001200a0140d24414840288500c40d903146c9940382c8041d0071a10f80d0104588581085907002c00302c1c1440ea07100064034107554008004102c0c0b8100320070688400700e1081e052401080c01d0740000034891805070b042c1c50503035400011071071042d641c109542048603c018003403810300d90f6402c004603440c0c0c07040109c1c6114103042c0d0020003240b0100d051114903400000c14010412425404a10005200c400b10a81040e4043c01410f41010f1050041e9224203042e0032000307000e4501048600c10041074000d5408450318462440d07031803801c16003409107a115050700142640d001d030020400306481751244c20600c098008100a00c02c24641d80c03c2604502a5400c1d1240380c00401c5414400c1020200950070590840d050003140303150402200060040d40e6029207100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 264971807 1250 264970557 264970567
    0x80c0304051525020f030d05060409170a0810050a090c17091509030703171305010207060f0510051c03020c03010c050a020d08070207090b010203222108030c 69
    0x507040042c03007907030540b000c2c24078090703d098000e1041e28030201c000c0420030800345101d0a001d6001041c0d11401c01c1c12032024600d442d12000c1c04c01e02a00c030207402150020780d192191008500c0d03281c1000c900d2149041c40d1a0344206000d0003c2102e48044c00c11010001180e000300065510010041c08489003004042500c040444042c0c0702040d03810900d031040c5220400b044138050010401001000820010404544440c0c4d109a582d02410f600100400d900058141d18031105000b6140c0c071500010107076003807000d00e41d181070998029482c1156100c0d2a05000e6110341c550f030281c183e10004140c120007007103141000103901e6407807e1649a09082c04081110107051003880303608401103000c2c000340401080154010103d40c403180d041c1c0010301510580482d00d41c4074010440c01203209900519a05040502420043c240c0100c081d0544c441005588001c1d14615540e00c8204204c49105010610b8550505d2561b0000311000300d019000035100c00001d48844183c81c1c0003149071070482d4a40c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 264973057 1250 264971807 264971813
    0x61e0f0905041a0a0306020406110111030402040e07092406021c08070e06030906040204050c130311040f0c03050108070b070c170f0a060506040c0e0105091e040f0905010c0807080c0304 81
    0x84280703100c000c2d01300c04801c0c4c01006001d1280c0081044a10903540d002080391542c140900f280c900303554183c41c03a64100041800743c03405800814500005000750364505680b0340e03011080f2134241ca41080ca0440513650803400100300c2c00c4510007019640043c24140d14900709115a8041300d0b41c09100f40088200071590300d031b200d0302d8590710101015000541d030382449141c0550740e04046804900c114108000264000380110603145061429403c60082034110368500c41c00c2d9224058441d040390751108501078102039809030000d0b032441c07601c00003034a5040a0f01c290801c900d035040a02c800200704001c000184048501c1e4080351500c000386900d8000c42c2d402c041c10140d41c0d0607201e03c41d2052481e1482401030961045000d244221400c004d0612024000d84404440b100f03003e01181092000c210749041107409a2003500c001115160303620564000102111f011004c1c00f56800e941e10032880821609100d8503001d80d025091804191912141c000c001e114010300324659090044040307420 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 264974307 1250 264973057 264973091
    0x10f02250803070c0918050a030c03030b090117070605130b0d1803020d090f030c0b160c0609060206090c06030612030405100c1e051b030a020a061e0f090504 69
    0x360140c0c1d410740382d6844850801c040c1001150003001242c44c40e000340d00001125030070f01c1e140a258040081c20300080179407020386144200d034034154189a2a03650198583e541c0010481c017034904650b45184600501c0c0c00d641c9031100c543c0129042c06002c00919101c0100c0b4100e001c0dc54503003440c100c4d40c0f69003007400c00000d030230440c0c008001d15803201e41c803204054021420a1000043d5519030810b039580304112580e2040520000d08540d01490040c40008100070040c404d864001c003601007164074565911035407a545600810000340e8018081c0000e40d414000c040c1c0107111076005016101c1d550300012081e12014006078480c4500c4040703802002001c0c800d98008000081410040b041c442c9030140a4915000782141c01042d03c402481013210080020810190404010059200710b0398404c0203003c814415075034180304407802000140d8032103001c900500642e6450380d4a644103100c06148209850101030b003406041d12004a4150f409400002107070f8040f140030800b440e040c048454 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 264975557 1250 264974307 264974309
    0x5010b192705040c05150711090a020c0d0801090c052517040e06040e1b19050604090e0705030d1b080c0f1b031209040902060405030a03020706030b010f0225 69
    0x55454100b108003c1482500c80000c1c0c12100143e40740042840c104070740054512410400500c00c4002d42d40051090a0000026a00c4042083d0051601900208591074141c2801d004000144000e0040c010003000d03000d101203100c2141050ba0911408480c82c44441d5100200114002ca0f00c03120541807000310850b821124111420b03a035611602d802c5a0350134900c0445503d4040c0e03003801001caa41000004e409111a000c003c0c0b070642003101d05c3e0403c403491807a00508001394190035404074040c0d80703580c01031006206640001488401900000d82051610790001e80300f0340008403031042458005208078401c5e11081502508103505242600070b0b4080c880103555948540c066490003e08006030000c003948034581c40e0f0180000350b400309507440c3c014401c0c5060030b0078140445a224203240d004288454030040206013002d0702e48001ca803400d50040c4007030f001a4410f00d020845217805118110540c002840e100c80b10100600000c0d50b121000c1580340d0702000c80c141c0c044642e43c000b8001300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 264976807 1250 264975557 264975629
    0x304050309090a0522200f10090905010504110301060503100906120203060108010510050103110c010903080f0a1a1003090203120c06010b09030d1214011205010b19 72
    0x141030f403c04a11110081c03800b1039542011a002d11400c4501091300b44201d040c0b00d6010709441c81200081141d4220741c44074110903508141c01d007003a03c120355148c080c0c80e50205550f54803d007030340c0d2801114806884060744414000da1800d0003030081c0341038980032241500c0741401d001da9603444114404c9007640042c0d00a18801d440d109000c100040c0c0c01e403100c9100760089080781e000b641c80704411800c8840665120206c41200e1030204500e50080c0c1120a000c407207025241d090028180380d160940b44100070841c0000c69100c01c11005c50f19035800039400c0300003207408001039000c4090510218201542c414400d8054045182001d44a0340040901583c05400c1c0c4480201c001107034421904100013042c29401190300104030406040700361299120014014006d03690b01e000b0603910b40c00e041c01e109000c2607d43c1e500038401c60a00080e20b00a0070a0580c0c0090326820b0704000b82110718400035148250b010700c42c001000d40c9440c140a0548603a08118455043c4d180b181d168a0049220300c0c2c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 264978057 1250 264976807 264976819
    0x8010203011805062e0512070f0906050f0f03190911010207050405063a051c0503040b0a0b060d090c0501030e0712030315050d050d020c0d0807080304050309 69
    0x400d298082c1c0e40360003802000c0d08010300441d25900100314820460040424405000c0740c00020800000303100804101c419040c0645002e0310007484501c0b1300821651480410148070451143d684c0c0659040c0090800340341c1542082d5901124405511542d00c010360540f10202c00702e030000c40c00b05d1034005c2c0180400e004202495003072801c0e4410748010004907000d07009007040021142414060a0b00c01c0600410020aa01010003204034211820304030600328005480342c40648054180d506214a02a1000300b00d440181402d04046010041c40c40d010800c0c1401031200049542d40345035000f40350080c001c6561540400460154003e1003081000281004040d009004902c2800001d85100781d809000c00d110f440442c80ea12100c034481c13502811061800100424803980c41000c500303d000360f804040c83d60b114009101002900d00940c1c02c0c1c0c01c00c880f4500601e404100c002000170054030b070300d0030005841c1c0300e82b80a8001c0c903502401e218070000000e0f0400c24103008a400410000f4a4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 264979307 1250 264978057 264978059
    0xe07020309010e011707080a0f0902030c13021b030c070b040e13110d0b01030606080102030402010804080702180c03191b0e06040b0f030403030c0e09070f090923011e03030c08040801020301 83
    0x4003490825a231071049207141c515122456a0240100301800d50041c00802840c1d41078030600c01c000d00d003680c044800c6503003031241c400c1c3c05160f850710304000c42110300203603220070828110605210702d5910903c5450010001040102c48000c22554003940045d81d04039010203e090408420840e40c0c0001d510035558001c410411409000242c140c9000320410084d2a884d210114202d00c82070720080e0102d1402400500040c40810083c15154800307072404240f10181c01161f00c104c50141c5100c0300030440402082001141051010481a075001c42407054011009171200c40e4504280503108000c40a04070010b6521408200c0e4028003225403440d0fa0740d800080c51200d96001520101c00082c01d10122021507841241180203542006101c06103d0311208800d41d05864020307848030a01180c1c140000b0780620700d10503c02c68443c0710164000650340104104500d1005030000340e8540c0070480c41c000340b000c15510314425240d01d800e02c460b0440301410000b186001e41e0740440d05030343c00000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 264980557 1250 264979307 264979321
    0x60e010c020a150c03021905070e04110a06031b1806050c01020f0304050a050f010207020f040f140c0316081303030c050c01020d0603061a030c0907030b13050f010e07020309010e0117 80
    0x31301201118042c0c0c1c25140858074018a5141103000d118000d041944008810310260700d41a0103d038105101c2c0508502c0141035001088242d200e96001c1c00c04070b0f58032041c00003c041e1074084000c0c03140403450841100a000071618a00c4415805072008028011517059100e200940c1207540410b8480b003a981c1328517080c0341c07036603440340c603e0000c4841c0c0c00350481c1c0395600720050083d940903940c0209128800401a0280b01c0240203d90011440369201c2014101c90511012540d000d00c420b00c68881d900d10701402800054030b072a00044003005110310410200d10740384204160324690615010804000341da804031101e00508020704c20b81d500c00071300c00b070b90030400341d1082049074451401070115186241e9519192a84070000c10740503041600000120f11300385080903401503a0b420001040050100031540c413a00708501003080301c0d81c1c0d8050250800408001070b00400c0b103d22511181e282a42d0000e4482c0500b03540541446002c82074141c1c1d9a00070003c140700352071551405903452078042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 264981807 1250 264980557 264980567
    0x512090c01020f19020607080f13140105040b030a2301080709060504020a120c120603060b150f0a11070e0915061e090a0e0313060e0a060e010c020a15 66
    0x149954098450f542060006440200d1000c0d000c0f81809040004420a9000d00040e0303407141c40100c40400d010007910001d50840d402914400e00e2541c4110212410408203858842400140c181400028001005040d0f0315000f180d512140042c400704505440007101000002d20b203d04241d03403c20000041342101000a12400b101d802d244c00f4090305690708144802c038869a803018000413030b15030080360548401d41120404180034903091544001220b040811901c15400490780c094a984401300c143c505a01a146a9280c440c05a4139204103034038070701a40d1040c03050543c24000384040c9442c040d2014071404005265002c001201d84c82c01100d40c0b5184c03540312042204001300000032858904040003000200d46001d81801c820042000800c0007500c80140500c0c40d290301d030340302c60040120620203410290506026408242d00300350700500b2003040ca0300003a000e0007005000f00b161541c400004544007200307007081c40e03018100b400030070382c0404150000c0c070121040809501201d5405 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 264983057 1250 264981807 264981823
    0x20408030c0328080103020607050f0102030a02090f09012d08030304060b1c0506070525050304030201020601090e0a060906090b01081c05040b0f0a1106130b090102190e01051209 78
    0x3550120103105a8820001203e515003807040001d030704200500060405400070150140504102c0d9a000c02d410305032400e82e402152080c1090b0307000315045295051002c1c5840001c00300303c4e9403030b00560401104640388400c102002c27042011000d88601e0310400750f080500a00b0001d02581c0e41d80c502401c280c0c0103444203508071801800311608900d024099541d00340201540301000c5c0031b45469941e4220f6a640002d000400c00da459401c00c1012040c040d0022101c0c20320400203151904e1642c000a800d0040507030003003860350709100996844030b0000c02c525038007580c0a035000912a2042c2440d100810100b18000c0c00c00c00c01030004100381170001110401418401c0c800451000f80d40c000b00e0b003d01852040c40040c9205021140410280070040d0040a02c64079107040c03007196901c0420714020f0700b55046401a00d8929411081c00144004107038040c07440f00007075180140041c4585a211142d2101104212140b40c5406d0981c4c0b2840494101c003000c1e561800650420441c0d5039250785503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 264984307 1250 264983057 264983077
    0x60d0f0c0605041a0a0e010e190906031b08030708070809042a020c01020303040609050c060706150902040e151c0b06130b01020615060f03011215150b0d020408030c03 73
    0x444601044d516400048800d44442c555404c0d00b050003030340c0103680c0c0452005000750712902040d1024070803400c5842c2070006240801c8080707891841d505020030a07101c8643d26032101021000c0900c12424000201c4000da0b6103c8401e070381d18802e5003403d2a080c020360710070710f60003800c020300c0c601c500907194848171400803482c05404400b00c0c1c001040c1c0c1d586d1281424240036030028000540861380503405101a14020000d8404100c035900020b4001d40c0304100458105507910a080b241c4c6a940c2010000340140480031490103061a81030f00f54010010320030101d90700120707015202030b16420352101d40740c1607450340040510801e1425010040e421907486005080d050190013500c03080340a10000c000c01070f0050907044c0c4610f10312042e2121400304c0c0030342044c0304100c50303070780700452500850080881c444600200c040f9840c0150136031741051004041c03075007480c1d84c0c042044480b00c5110103c80800c000c031075a6a060000c180068020390303000080e03600010441e0844210044004c0c892010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 264985557 1250 264984307 264984329
    0x609230406260d0c0605040f0204020316090b030415180c0807030b0f06060304080c010e030d050103020330070201021c03150e07050a030c0513030503040801150e060d0f0c060504 78
    0x190071800c0c0e5512041420180004e83c2204840c010811030b600464119008400080314021550023003402d82e40161405a40310b10420708507000e0036846003203940030703128802c013091442c02e15807101415400b0080001c3c0f0400d81d140203990941d10001289c6041c141c0c09540459615a248509078541c5410320041d01d81d210350308005844481c2c24001d440c4601d10042246085883d251110384403500724140b03115040d0360715140c043c500c5908001074030300414004004111907056206250030440b80d1013502100e03000c2c0c10440c2882c1c1d9211903082030000700c250b0440f03490faa020b00040b8a40200c07204000c40c01c03400854036003005039041d04401140034038881c1ca8011a42d4590301d0540c8150100c80800008606100070f106191094000c000c84806c549030550402c065200c5085da807904075402180c46070b01c001000c105042c4280500d0b2161034824100001c8030345040141401080001c14440c840d203c0003c07400d04020400e85508a2240c000e038408083c0c1e5200d4901405a90283c02010f11034a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 264986807 1250 264985557 264985619
    0x30c0d08031909051002070f1b050414040b06010e010e0604030605070f052809090c08070f02070521030403050f070f050a0b0a2019120305010609230406 67
    0x80c1c0300d000e0f0070b85440c2d11030020556121403164100003900811002c071400480034007102d003c20b814490208100501031b410a60303841c5050100f00880e004c40c1c2560300d4004400080001003144d00d05030aa10260a0810140303400303c81004864503890844051b500c480049004010f0006c950300040c45111030b82c4400d0901155100160ba40b8060740751508910a04022120f2805104c86441c1d40705003414248034251549a04500f829070300b0030542d14000421907810404040d03807040d1151034071201400a452890708140c0840c05242d034001041810034040d0300c1c40d030401c00c1c0c20001c440045400105640801c00d00041c0151103102500c02d9091000003d01c01090500d0310a00440480b4000200580b501906050a8490303964444140959000103000341009450034000d90700824103042c8403215090843c900344812121100849080600d80030040c481285c2001c800415549001c20400f9030799845c511411207400c40300b1849411500300340700002c12946003410150144003124245a000f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 264988057 1250 264986807 264986851
    0xa020105040209070e0307210609030320043006090c1701140604050601020f01110d0f020f04030807151b02060a15050402090301020408070e090d020601031709030c0d0803 75
    0x1c081c040d032011b500d60000c01c02040991840003507420540c0b8107505035501e80c40e164582600320b401c10281580880d886113022452020840031104410705c1400c0901d00b481c1c06c164180b40c800340b450140128080200301d818101001040144040e01e0348080140903c002d1490404c00101e114400e01208940d502896080c1003018041e42c00b480307881700710f80c5059690304003c0002415014100b10306500030340c1d0054429290070700480d0700303084411034815680e1544036625401c403130b0540c8852a10705c0c41403110b03107440d003194400c8030204c0b134205021544800302810a00c9820410300300320003040b071070606c001c1d5644502108401041155400346c480550b100c00300c04c400d0b079605815915052024207000c1c000c501e000d034041d0200c060094001400c0a455204c50ba03c2d00040c1e4000740c01e007407060400c01601500810403008055901d20181c1070301d525642d542d4280c01c4030013039880390280d4045031801c19510108401048400000c020201c02801424071002e251f00617140781c01c44481d890701c16160 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 264989307 1250 264988057 264988067
    0x714030304030206070e0d06060803031008030705060609040804120f11060909040327260f0a11040207020607030e0108130b061318150f1a100e03030a02010504020907 73
    0x1140d9090f0300600983d50300c900049826000c0d040071141e00488a040300008240d151041d08041c2454000030b40d43d03410700d070440c00e0b8031a1071644481c041e50300030040d540020f280440d0094001030140d50910040d100d618201c2006d004d5504421280305a132040e60b814804603011000f03440780100034801c6508050f5080c8401841000f25440e040a50301c404203001130300ca030340e0a4080c0d001c032038101c103407503017084004030614840d9078421407503c1c5a88502c00c0220f56507188959000c02000005e04140990040d426101c1c060950060240040c13403d00340501c2c0c4480d0101c4850540c0281340d141c0e00d081ca0701c0c0160020702c40c0140c0600040310b080001d500340034100f007841201904000c40c01081d0f61030340f04211006c1142c42850702c10039103c0254110390305912440c80300e0240319620000301426200c41e240112a422420036840038107002008200b000000443c0302d840009480a55042140c1e110544d0140e070ba42d01c0d03940e09844005018a05c4c035a0660101c1d010324400c503002600340c2c6a60030100d40d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 264990557 1250 264989307 264989311
    0x30a1a010303080f040803190e0a05011a090f070509190306022101080c0607060b09090303042a23130207050f070302061b0c0d080c0f0109030f0318020a0b07140303 72
    0x18203017040010230b10044d5121400c81c00c2c0b10f01e0f4800488d000d0344545c2c04a0500400520440e0160b4442900071141d0b0030715030200003901010f940d244100c0c9440464102240405050007091000001d41200581c40b07482c0a00d10301d0341d001042140b01d070707681d1a10200940c01081c5d10017800c681c0701030711421503104042d0941200c40700030042210101100030000c6c81c2d801100121811a5222080304254803141c02452244085002440d2a0b140909082a441014003264200b1680d8000d594103612841c01000741030fa0107041c0785080101402c0744a200b05001e0a940311350110f040c02200c201c0c00710a0b001440c0c00b0f071003882a1420380d03401818241c0d031600d00e4007000317600410901c58128500740702c941c60800346860104030784204079142c000c2615546540d01c203880c0403200064051580200300709041c80b019403407008003d9841d668400800c085180d1600204258440180c40c600b42030000742c210019070010584400d4a5075182e1016403a8000441100e0404208003100c0a818021065038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 264991807 1250 264990557 264990563
    0x150903020a050127030303091b0501020d0e030a05060c03060102070506030103020f0d1e0803070915091e1e050301240e040812070903141f0b030a1a010303080f04 71
    0x1c0c406030404006403016044101c00704802c6101400c50a024401841c5a800540c000c0e2000104001281031041880b217040c4007507080f0b450042c40400c2166400940b0204039109480d0200c89190ba00c0b002900345a104071004e0258403c1e64140441c81040f40021805080e0036022508520f41e0765062002c0ca000074440a5800351600c04c01029601f4400c90340c401642c85801c00301403529a64a0411003980203142c2620300c3c1d4804405c2200d140d401940c4000501082054406024505e0800030a02d0351b1501030058044c64040f5000780c083e2080310124050301e089540c0d0a41c1c001c5a540748400700c0c14502c60a40b01e0f6082c41640c03040784400048044242149500945640d8200b81440c0d010b00c1c405042211096801c101c0c2602090015002901450483d0b880c1e9404500c2c0d030414401081c8141d0101410f908902c1c007104600010400c0100711140019010900000d0000000d05080d2202806000311054580c00881c2125443c2940e0523244240c41c2c070905611056184240d29004031001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 264993057 1250 264991807 264991819
    0xf060409080d0c05091203070b0c120a09021906050c01060e07021b01020309090403080405010501230d0c0305030304080d0c0509010903031b0c0f050102150f0417040302060301030c15090302 83
    0x4803100302c00d60402c40500d592410f000c1d28003d85c94000c40c28a034880003001030789070070100e40d20003004502d01c48a038012038260191410100038103401c0e101c50801a200c512501c2e030f108500c10442d00d481c0c40001c0001c10901300c150310700356561006040c40c0d204001035542035283c80d0340410403540c461007250160440340d00502d009d6802108001400c070400500c50305600c4184480300043e500d54404511451103980c8000550070185005404e58071f040e08090b0b411901884546071001e02c0301880c031101902181c0c0c0c40c3c10114207041c40354000225030400381080c0800802c110500c9070400007480300701082c4401700b002e44840f980844150103204a4107000990b611000c00101c5d101d500607080017084102300c250344668070b40e10701040303a10036404140b404865860812482d1780501101c003d9015603c0c035461a4030f8013202d20300703240d00020701c000c00c1e000140902c10006d0025000b50390155038080c01c05540c2e56100c3c2001849001d07980300e4440c00c9400081000c0c000340c0320750410320031a41c0c05850 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 264994307 1250 264993057 264993067
    0xb0d1505100e030f240a1104061e0903110d080708030a022701090905090309090a0c03060b1303020d0f080309011401050609130218210c0a180f0902090403080f06040908 74
    0x1181454011b001c14684540300c000c0300044040400061004121540326103514a180c00810800015a0498401409100321041022504d40c1400d40141032040358080b03010303a07051a00d01064081d07050003904c01e2102008100141c030340382d401440d034444003001102d020b50000322a07580040b1200342c1e46002030398210080250007050f802242c1c12450b0607083d2410800715034007141c4004812140c6140f85601d0b841c11500740c941510a40c40079203410210940303800910f45032507a03003e0b82480001e002e909481d051009000c2c2000090184980c0a14003075a0303810000500f501038010007019084020b40e01c00000b45600e001c004844105c07101500c0181d48140210380d42000390032107496142039032901c841c0c0018568400500c14404501054050a80210004010301d080c00c289401d4bc01518107450500ca40507802d00380507910b81c401c450109501d282c03404e80d03c01402e024200290402440000c2c0402c250300540e015105941d01c444000c07095031603000f004103585402e1000751425000b000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 264995557 1250 264994307 264994363
    0x603070c0f030c0f0b060405010911160512220e150d170706060f0e1b031009020d090b070f09030b0c070b07091703040b0d1505100e030f 60
    0xc034070709440e0080c2804607603035049480c2c0800d01010f210003155110000350030018245403500c02c041c0503140c4150100040c00c10918107241e14400e010040d0f01400c8141040b10410000f00200311506d019000078a407203135a6070064a1920701c08110f44003141e145100003140200c46c911005100e0100c0da601800700c3c880e00014001500c0100c042901c510040d100300c1c00341500128010202140300704400203580386881d842e00d1783c0880c80e4028070340303103550341040c0010702d000300422001d0b407495500c45990300d46a07460003945010302c2d075100e1a101030011640d400d0305911740e030065021074050102381d0000d9452640072a4610a6110031001080d014001880402c0d801018191b210318048072031032030198151682070080c10101d510070b00290814405101d0200c23668201c041e040712100c001c509140c01c0c415100d0241c040c072200d208100c0e5451a0309200700c15901e51080c01407202030719500003248012001802036240c0406c590282c400e880080090b0480003c550521380d441019040d12800242 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 264996807 1250 264995557 264995573
    0x90f09081b1e030a2a020105031e01030804030204240b0f0912011d07030f060e1c020f010c0e06030105060a0c120c0c060f0f08060303070b0906150603070c 68
    0x1c00c507040c080c4611220040c030700d882c0510032000000128019a04c5400882c401080b688011095901c218800c01e005100c8084601c0b1917124160b090a01d01d45030707510300180c1118403400d034000303920101c2c1c200000004c0c021210f000b40152030090ba01400210303060003648000c41020f984d92200c0d61110314081040d140020064002e00340c3c104c4d1200c1c07a00a200c00000c010b031200788001646a503541c40c04591025505401c903544030100f01c0604125465522095030318040e2440182c402911910100402c1c48117000c10003480d05801d8010a403882c120038003c0d580c41c6110480700c01503203843c80c05003410f401884120b115500091080f0b1541c2c4c04c01080c071005070008801501403103070380300548c000070385c8024205e0891210f5640e048030010700c6040a00d000c49496203c0820720403011542542141d1180c0003241403042c40c2003648164480c0c5011a15620480801510701a0404c0900440c040c0124885008100d19010f641040320f040007045180d100c141c801c040407500280e0b004000803560 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 264998057 1250 264996807 264996847
    0x15010c0809040f02040902030a1811010305060a0312021b03070b220b0d0203040b1305060a0b0604051302040e15010f0c0303090c0801020304021f0c08130816090f0908 73
    0x242010840d1000384003c0c0059030066008078818580100412041619610445072522a4121580290007450721108020891300348800c1c101500e94000907a65103030000a00021a800166600e20b52211000251119143c042c0c108115000014080a51400042c40d4064900014859141016103156050545040600180841212800000c00440c5080030306025800b0103400f40c1d40f880d0900e0034440c413000040503071449107145442a004200005005544900032400018040c0c1c401000100030b40200d600041e484500b8a551608a00c4c15030090000c803a01d2000d9610715032101541624105500c88400d400100305c070340c00441c114880d00d5a60712150003820000351000341502e48058041458206401580d0001b090004505040600c050320b0100b6480000c40d062603803000a0800d0000080600003840c08100314017002240e5004100a11400b03080341d01e0490082201340c060f0380c2a1060b840c04d280303407a10407082c03000c86016a0041c1a8042c0e4000d180c585007000c607171011445 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 264999307 1250 264998057 264998059
    0x506030d0302221503050f0c0d0b030c100302120c09030a03230a0f021509060a021c06080703141204170c031b0f03011806020f070c0e01060815010c0809 67
    0x9500c3d140140400030220500141c600c00051155550010304040e00b5200050000304001955008114403001c01506440c6e185035910b40104200c414000068a0700158100d420f03130000d804100c0301000d54265000700451a200c8000c0261070f0340b41c0710340310200d000d202d030f84540503084a1800c1001a00c1150f4851000e801c0b2b14400c0c41c9800602c1c100c04d41d68011035480310101d15000402d19000c0c1c1c0401810240c1080448100f01c94545101401d44070300018000c2d125260b004030304804480400040500d0020110000b00802c66a030740300d00703680f0102448140c035000c0242034035000c11100410303030800020000082c4d514051504070704c0554030725a280d29030361034050400c10240d01d5078180b000030300e05109043d01d491650a000100a4a1a41802000c0c400ea1400d00744001c1004680c2d01811041c0c0c000c9001600e6401c101c1003002e4a1242a0b802031010807820310101d8000354030b81c1401d050741e8423666407204035a1803008481046804400b4640842d102d040745500081001e001045002e034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 265000557 1250 264999307 264999337
    0x105010513050709030812010f090c020c100201180f2d0b07140706060509060307060c06020f0708030106030504051c02210418020c1002040f0e25030903030507030506030d0302 77
    0x9500e4903640c903960021007c280d1040684801001420303030058844001d044410010041d403031405a02a5036080d40d04481c1d0300400400b1801303800103000f9400003600c6090072510000c1d005c114a0451585150a031080303030064203420001d51040003031000d181007046c10181d0502950070a4440659410000300460700f000001c3c4281010308041303c028004541c410344010841d41c5c100301c20011035102c000c01c0076009078040c08041000a521084552016401c03490050303039582c40791410741d40b40c440c0a05c0030b40340744800400021001d601d54812807260b0f00842c1905d081040b00610fa95080144100b04001640074262040c5580b88441d520340c50066020009454203582d2883c440d0051841d034540003400c0da0109012540c0d07031040c04002608031001800318582402c0c400b0130b081c03605580c0100020000c0410004e2410150010b01802c90504484281104800c0031401005841c166400314006420312020942050107400b6460040100a000d403d02080c074480c11002508040c0a01d440d0007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 265001807 1250 265000557 265000559
    0x50403080430050102030a0c05210c0d0c0c0b0a02040b0414030a140106050a0f060512090102070618110901050102060c0d02071a0f01170303010506090f0a06030e0f0105010513050709 80
    0x140c210194080c000b48500005178880c51f240e4a54012604508022018414204007001c12810101e4017402c03d041c5810311540c1c9500c0310740900074240118603c0e00748413450a10358008140d00881c6e101c620a214541107696552102c0e425030a070301807846920807c000070b010070f000c0503144448032a45000d015084405441407a1501c4054003a051040c8020340d5484405120b541080344081014150304814600b0861810704000d280d0b00c520711540746c83d45003080c04103020410a40440d1081600f10000340000c19907540ba1b66013403240b071074003150340103045015030180303060482c4050704845058020b45000d64032040e48040960214920741c005c6607080111000084211102a60280203d0106849887d115200709020841a0004054500701a20711038086900204a0f4190381c02074403da92500820804a03c250100b00740c0c9642c000c2000201144080d410360100c10300d50600d108a400351004203c0343c60803128280603180d0452580308086d1710808a80d00b03d02d03003104161030100051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 265003057 1250 265001807 265001879
    0x50715050406021c06050a050f09040b070207030804090f0c03200a1202030c0901020c030604050a11010909021b010b120639090a0f050108061003020d15050a060504030804 75
    0x4a04c0c2c82e04549901e42e6200d1051089041190801e0b000c1c00080d80c140e032528a88030300290700741d08000c200508615050000502c03440c403d100141c025507008411035181c135100c240d08005050100308007414580381018000d150f42c4280203904458250b00c84560710440c44e0319040080381e0014141c1804d000544058201103045403000354440c20a80612585810324503000908108858402078404d80c0194140800f10f100400e80598641d071013102010740702003840c0140e4418450343d0003400c0311840400d12184c0c1c0b42c1c510103604038245900000b00a070007000c1080000518041d080151a50710000000f991900e45000c00c02c03c0e580d42c0030440365076480f40705c3c00a040c8070340030002d11418a40400c429045040c0380718040050207141100c03149507420400000e2081c400204643e108005003d4405091400303541142c01e092294801030000c09a4581c0c1c0c51166110f44c800d4a0107040d43d040c0020300c1c030748140300f03480c10f480d07008040c0c514161400c0094020569140c4803184803000f5101a0a81 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 265004307 1250 265003057 265003087
    0x6011e11100b130203130f0308040512040f18020712020a0b010f0e070c1505130309080105090303061003060503010f0915090822080610030c0605071505040602 70
    0x1414403540c0300300c0c0300010088240e042030701076211450954100680c01c1c880b41da840905485004040c4001070300e903035400306050380c210141c080c0505014180202e13142072651166030107100b14020300c100c0d0019100c1c480b003941c10344140d10441c904040e0300c0000b48050009081081010040c0f88400f60401e101a1508042e0001a81080c400350740040340034020058806442c500501e14039001a0410b4600110500075900c000e14100801143c06900c00400034a0b0203204d0245030030000803c860300d800e4242c881c00c90010007065000c646d12000000b049801400b4491013414030f8000b441c1180c5a10040c44040745285a181e014144c489602281a440910403002c1640d00c1c541c01040308a46802d022000310031003d201d6420701d00b42880310020a9040d021620102500c0c441400c142c100801e0543c89d05109800c8203d0074010b00080c0140400c0303000c8000207883c01100380e0002d070f568910341a00c0c0d40c4038011000b0605902401003240e5001c26a02a56001d4041e44000d89003800714041264 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 265005557 1250 265004307 265004357
    0x4150b0910092c0309120d050a0c080c0d0302093a2301050601030b0301090f1506081c0806090f060907120e01060e0a0c050f07020301140a0b15031e0601 67
    0x2519900114003120246811b41845c0d6103440c1c4c000280c42d9260441d480286144129905c1d0030074008072405650410100400319010710485030103a4107680c8120000401960101e1640c9108103003d00b400744134408483d080000078602a044114001c05501726007103440c18400080c0c800140c006001074503103500307203020742495100c0c100015443c030346003002501f200c1c0300301607107802030f85406414400030742c00e0300300b0144143d00314510a00000d09181064082c14080c1c104c1422130150390101038424400605102c4160060744071581181e640a003480740d500811140343c8400425140800c440b0f0604032440c541000c5145403203040005680d2001003a030b0901d54940c05c03170b82c1d5280d200700702c081308c000312454101002807003c0c041ca03059040c0c002d00600401024001c1101d0001e07503101156000d60050503a0040c40d9a0003c691410b1905000144510b140f01d6028003550b840c40d20540e0000002c40303105000051112402e01d000c0c28044c2040b00004200b2414084040d0001020442c1e00360450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 265006807 1250 265005557 265005641
    0xf040302152503020c25170102040e011508010b090303040f0303081b0f0414040207020a030b090d0507030f0309020a0803030c0d11071e081204150b091009 68
    0x1e42110b54a0b6445118512110358000405206014180f030320907001c10ba904900554505202080031700200184041031140c4c01500e034004c0c030707541804500d00113401800444416601c01d290070381c0d03100c480d0303240540000b1102c1c000886e0f460051054044800141003090000340440f8106a1103612120703c1004c0b603001035010407000740c100001050301080e404180300440350014140070200c00d00450501940c05004040d0340c5e280c0e141e2103d629aa03054564042d0004c08035000329a0381c0c2010365041b44c0584104450380121003822500c0c034040c100700d84100780c0c55515849403103070f8024124000c1402c1ca40c100e0780310205c00000a89644104040e5000b100c0019000780d442d004400708804031640d0300c1588043c0c0e942403001c0ba0204450038603071041500074035106e408601c140d242c5007425100710201081414171200c140004e000710049015064040030b201040251103000401456403c2203520104a001c040d0050100b42020303040f1b03400b0302c6003010440740d02c04c46201119400705050791400f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 265008057 1250 265006807 265006831
    0xa03031403130f21110d050a021f020705071e0b090607020a0303050a0306090e061602070e04150506090f04020f031216031b0c09020a050403080d0e0c0111060f04030215 74
    0x1144161038900020b0700d500242080212007003036064160301c2d18600d140c1ba45c280903010800c00038460080c0a1000c003038500710355082c0341785120b007201402034200000a69080c45021000314508004900c031194180078141060a907520705544010305a0285c407050760000d00038840700b0016250306a0480140d40b20b9100c941d142c0440c800300a040342c2c0d00341c1c452000d05007080c0c00907191030702c0482c4143d0440c40004910603541401c92040e4544900e55000607491203207207003004140082d100c1d001e030b0035880e00341c4240078071b4894a0421420007826030315001d40b03644c00d0740403c0044c40c110508404c0004045c0c242d03034204e1014518118150424100c034402d4500d41050781040650080140740070100c02c070741441c0201e206440704c0c0d0410616000703101c01c040c1d001440742640c0d4040e000782c41c0195813181c2020ba85802d000c0000e8040c01c41018014490710458400f05055800351825107401d0340914010400c5582c0c1542e450000d170400780080d4154016807418a10400c003039210b46200d40d43c48810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 265009307 1250 265008057 265008083
    0x140d02060309071a0a0507022814010306060809030a0f090f170c0d0b1518090f01150510051c15080c0d0305040e0702070807140a050a03031403130f 65
    0x215840d0995030780d1295004c0c0404002d12400650460300340c480080d016a50300b0f4810084d500c0542d543e41c80d40001190002003005d001480303142c12010080d03501c000303a03401e2098594a20b01904c0354039043d150004c8940043c407089182901c207110742450b292031480c0810000d9980e040d21071407a0b800d60000c2d01f0800c210f000301050010100905500c030f42d0107481c0484030a00c1034603014110345000d0704491500402560f9001680e0750b82d41c1402529a2401c030840c07242c103021f411240c0d14110807540c0c00595003000480c0d142c00310b42c0c3c03003071a0840707101501c0d290740390000810407201c6510200340305a40713a113400012101100300d48119a0804a03000a1036070003403d208096291211415140d8440e1140c0303292980025070000c1030320100c0310f1480005010351680c0000364140281c40e0441c01c0948100100040c0b1407422444610284006036800956a6142c50502100c401207000c0a00465040000000038001400065510008480307030904c15402d2542c40003240300c0e842400b503905140c0c402c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 265010557 1250 265009307 265009319
    0x10c1b0c0e07090906080c09042603070804050c150307030c0908010c020109051612110111150a0c14030f062e0305221410020c010c09050a0f140d0206030907 69
    0x1140e81d000e8043d0700010090710003032070001400c41a00a00050800c031845c44c0c0940d102079912b40b80113140702c02d61031164076443d101400500c06001107505940c540320744c443d40c080031300b0310324012402a6502c203100c80c40e42c1d80301f00c0242c0181c5079494501c1308020100f00001888182813044908005076a800401e00c0d2242e030a10b03c1c034021000c0c140581c03800520701e0402040c031078040101e010692000011000c000d2100040c4e4494001c5007038041c06014032889401e4224031407400a100c0c581000040000808107081140c00c1080c141d1a400c0300d003010404501d4031000d1103149a803090000f024210034061b4140b44a50004803800c80348614200c00e02100e2495806000b40c40d40310748403245e10305070f048141c035103130822500003240902030940340910700300054014800300d424106030490030341d654805003181c14000d14604280340c0000d103c05502140510f041d44102d4200c520604000d8412400d040000c0c007240300441c075042d8081510000000180c40351000713540704640e060054801285421 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 265011807 1250 265010557 265010561
    0x2409030313031a0c130501030c050f030a0f1b14070c080307050d020606090606220b07050601050a0e04020105040e1003061406011e0f0804060905031306030e010c1b0c0e070909 77
    0x180100514a40603c6080c3c5c052918181c0c0000321102441c0100f01800101c000f900d0a1085c0928039544507000804c00c141070b0035a801c0740006c2030440404020780f4a814041c0a442489821201d0020351801c800c2c030347d0314240350094010701b4007803249940c456580b0340f0b0441c07840d800900100c80c250003c1007210b1003180c061003000c0e80808180d407940e90900d040400211184140c540c0c0204502006594001d0070b50071184440241080086c0a6958106400c0881e82c80e00240324651240d103080601040342c281c4401e001e0f001e01da0607161113040074103000c1d084004140c010600305010700b03172150010120320640030781145020404920b02c0141401c0d000145503118a43c540c0c6203410040c001682c0d400d0f07000412524204480c5840819038440f490980058144204040c184e8030020a44201030120704518800f294640c0c1c03402c100c0c60010f1800d580c2603030441700d01a000f0642ca40502000b4240101882c2800c900c100c3c01e0b201400d44800c0213400c141740964024002500c5000e00b40856a128 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 265013057 1250 265011807 265011811
    0x30507080403090b0c1216050712020a0e040303091205040302090f010803030c0919030b07082d0901090615050f06040f1502070f061d2409030313031a 66
    0x1454003003241d00d0551006072150035544110384444030000340c1c25010300c01c1489038261140c2078400e83c0da50364620001c06c01070002c0301d480a0728103001d0140001200c0d150b08420200040d40907022a260a2a1804c0981d0506008205a0038940c0755405600001c3c8254808601d125030760b280c2d9070702d5908600510171002e40080100520340282001804202c20000070f40c2c1d40310582c034401a685076001404a07203400f200380e1080404194004022081180140f90a0301c0760401d0380d10981c1c240e03248071110305011b0017100038246240410300c5003800981800101c9a0100b024800403e484280703030354840072074450800003003c100021605010340e207081c14910404000031200389041c1030a2242c5000450098454945070040007001000810b000344072150042610301503540190756141c401400841c6844c119030000407a4001c411403504d070003907001c04402440001d1104070806020b10030003d600c03002c1c28582c9484180100c01c01d00d0b600e50035120245100e03016a030740c200050141c0080c26540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 265014307 1250 265013057 265013071
    0x10e0a090b0402040b040e100609050c0414010c0206070b0f06010201050912090f0a05131410120b0606161a0a09350f0a020f07080c0409020319050d0305 67
    0x240031256000c203a5600a86030496012100050045401c10000b0b0007481901e100c400c1ca80102045c994124080c1d52082040354210201030040307541b50950710015120368081e01c000d0748454120008254410410740d03000074405042c0134a403162036290500c03038aa0489070b0800000e89402000155642800388540040104009100d032072407481940300d180c040ca040b1035024210902c1e81802903900c1c207920000624019200600c02c0440300303170f0003000d04041d1246124000420300460310650020541c0310071101c1c5050f0903031340390034076940d09400100050051390748880d0034440002005420701c0700d043da00b84a010354000c00342c0c101c04034400b80303440280807849651400c82014085503074544005070952011400000c400028082c02250f044aa0660b000068021421403540c1c14400300802c05140750743c0884844000c0f01c882c040e580c10340d0303003d800103980103c43c040b1711a0400c1d0b0440304036944014207483c5020101481801100840d51003622640e004c2210b0714111509442144d81080c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 265015557 1250 265014307 265014311
    0x80a020d0f120515041d070b0a0504090506040608031b070e090613060f06170f01050106020c0409060603050102070f020a08030a05040b030408131404060b0301150f12050c03010e0a 79
    0xd141140030340880c15440703141c20226200c0f400034400d80c03290305400902c080000c0c000c108005030100d811000080424080d02d240c03103440004503001e00c400064a088841341d40d20540750504041e0b1030809404040c1c601034016485640c080358403082800a085014000c04030044220008203030180b40c82d106500c00f917001405481070080b46d100206c4d40550040032030900c1400004686800d030001d0000da40360010240c45c00001289098624182c0d44c070710442e05003182c00005403896040d0880e01c0c20b00c02c01d00540e02c02904002c15090980061650a018890014455075607444580c26a4000541142d084111030103460451400d404a580582a40f100a60410007021004ac0480c07103140150401020003000003000c0100d0101141c0c0310442903100c00f01c20366a01c844540800c183c40340d0461040341041c0010480d0780f584415203048480303481e40000d0391040751106485040c103280c1e8007410001030081d01202c24000c0e010342d60007a00d4842e030240d520f40c503009000461103c0503060300300440c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 265016807 1250 265015557 265015577
    0x92a0e0a14370e0915100501030b01120e060103030305091902040b180f0a11070f030503060a080a0c090e0a050a0803061807020c010e04020301030503070308310606081c0f0909050103080a020d 84
    0x80a0003246c281900c20a0800045081420005840307490010800c90b082030304140008104104c0031540138100c0344a40c40078001900c89030356407610390520b92440011156840f107110b0151030260403401c49264007030701b075115000e03418001c20301403041104c03443d02003500070080c050102c0451086001d00c1800100c154100300c0a5030700c1c4d403c840c18050001d000c000303000c03010400701d90301c04c4a41001000003804442c030804180c60a99003900315403165000300e80c60880482690b24000c102d985410f64040040d1101002d19030304c2100a400103045190403142c5500c2045500d00c1600740c3c10b0050301036030010050100c1080004004404840480d0f02860040c401000020000030594a209503d4141501c0350750300c81c040703100e1400710007e803000006440c4941084482c2c01e000d038001c44502a090600401c2e40380d0819079515a6200c0f01144120460201400050b11800c5207808107070580c03401103907160344d42c91980f080d20000e80040c0c804100c002200305400341c0422882c1803405860510a80d01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 265018057 1250 265016807 265016821
    0x30d0c05060f0601140d02040909060504030f05090f0d1505070815102c060a0c03090503060114010503040f0c180e0105010f092a0e0a14370e0915 64
    0x30f4070f07041784104a5040218002000800d5901690090421070004004032295820144007506c0182c0b802c0c1c000c600c00c00d11100640e44103404592403220007400490407121200b0a201d6001c10b81101580c07222040c011034030402c00f15004d40ca00072640c035940c600050030500c41049054100e40d24051092075140c006d084210740101409800302c404402d81c03101d0200001b0143c0b4000c0c0004c00f550780c0681c002451071b403c1500034030106d46041c000d6560043c000d440c1c100307169407000700f07018019070024a80343d404407640c8180011544144a507030681040105680c0d0f002c404c070b00b107030032982420505504041a411151041e55030b075004080c0244100c1d407405d80f4100e0030f003505000d5a00d0083e01c1e002001680b260008484054441c203640d0389801c000c3d2131320000c0030203000740e400c61300c01c0b081c3d01d80004064806050401640c0c030004c0410004a21494100c114550903107603841801030344280d1001048080c0c144180100000c0300300c4211490002e401505000c204030212510401c000c1c01d00240e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 265019307 1250 265018057 265018067
    0x11209020904020906030a051614030c0307050f0105070827060909010501050f04330512070c0f020d050a02120a03020c040c091a1908040b06091005030d0c05060f0601 73
    0x103070159900529038540c40081b0b0705140880c00e002e09988100400c42d81c50006400003d012074020350400c00f0313040001400c150f220400307001c417584d01d0ba00014090049180c01c001d00391480d08141400e610709007242d501c4004507004084540385506060714070000000c1c00034003d01c01c402e422501c2519007000e134000105583e1040c05200c1c10440045000e405c90b04046c8202c1d0060540c20806046500b1040340d5480001c15505003c90300171158540882c4080c092025120a00e452003401442562510004c543c1141071700403e07160680d03403240520160300c1d0b003040049440e0181c40500110303503c07801880004142554161200d0780b000913944d020950110324100004000c5a01040200003103408559854003508032944000c00101e0756041c0c102c04100614030030700c0c902103450074021515015228101c04403809000c403502500095800d01c4c26961213640400d440050350600c1c1e85a1011900d40001e0072030100100e908021a0010b2050070041c8640c42144001c1038401480c0c2900002c00b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 265020557 1250 265019307 265019311
    0xa141c0b040308282316050a0e04020c030d1506021002030a0906060e010812040b0415030f0f06030501050c0301120f0c081f14100501180b0c010b0112090209 69
    0x700700b06018010851000d00e20307034005094110b80d040c080c41c00b009004c48800401c424400702c0d00900c0c2c2c21030044548a48080e0b114410041046d0501d00c4d0200d604040d10f540c1e1001a035201000030614205ca61555640701800148034040e008503120000c0014490441d4140d8450044c1c0701580401004144d90000b401e82c14441d1522000d40c8a8131400180e034050310140b03000401c02402c0c0400482c42c607880402032070481d81001e0844a451356000580800c81c4500e00641d49800d900700020301c5500e4203c105036140081d185400580e10ba0240e41040031550741c0c0c0a00c4e04846d449040800600100340142504600c250f50340c0c5140d540741403041e070100768406c4002800e40c9009010a014417030440301610091420f602500c01c46039109000c0c214040d800c0840041c0c047c03a10030070358038400c0c203640c03400c0c801e5504079852101e66040000544486002031000c0b020300c1507151000c1211030502003e0010b00082c2e030000b0500c201c41c0c800141000200d0058800301c039107880c01d0a400741c0c0d42c00580c15 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 265021807 1250 265020557 265020563
    0xf02010b0306071803050a030804050d080f0f04030512010e061509090103030c080d05011203081302030c240d09020a06081003080d14070c0303051807030813050a141c0b04 75
    0x881c4d4102d103240341425102c65840075126000e490990414140c1100025200314810001d40300c0d002d4210005848114060391000c401101310703000900c0340705505412503001780c0241001418031890003c4444d580d802600109200400201400303e98100350301c000e016400c0c001c15036820103101c080480c0d2454014440542044428500c88040c0020041203500ca851502c0e42841190b85821114504e40501a0100c1c000342c004000500100003176811920580e42c0140640900358004d01002010106902c0e140b0303940201c1f41d001d00c500e0800342c0061440d002a030801049550a6004004240d1500e52040c0140301462080100d04640d444e48001130340d41c00083e1070340f6103007100c03050300c010000034116040701140c0805202215403c481c2c45011248642e80a11296907848201c02e40e10481107481c1c0c0d101c0d48880c00a1000480c400041e0030603a51554a542001740d0324400035644e0403690340820300343d0300700c122007007401d05003080c0c280d40c1030b058907082002c02170540d030382c0030507440d4028409 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 265023057 1250 265021807 265021817
    0x30207030e0d0c05061908060402070b0a0b0406120f0b0f09060718030204060e0a0f020405030c0d1403030c0309010509063702030a1517280501020d020301060f02010b030607 76
    0x101c040020300d4241a02a00e00904019180d5020140d1030340546e40d850f9003680440d003814001360961503d030084132200c6901c40031885564a403050404003924500310542d40c810b48421000c91094140f00e0200c0c0c034507005000303240d15080203082034403210034040c08100d080e0080c40104901d8540002d0416041809481c0c040c0b6605400b100580d03240c01c0ca900001d6002d4280a00016500701c0e001c1c0140c040c6599107000c12000d10310701c0c00c0000700d10940c070810703406410488844280e4900801c0c441032007809070868031100804281d0244c01c44d8000c0b914600b5000c404001c0c41016042403082681c07041481300100650308000c88045010300036000040300c0840e148003408240c076071841281b01008a160340c00d5407281044407491024003414210401104e80c00355000454000900e41c01c004601030401424008280030305040c4002c1c80481d907100c442c22640714032400503000340f0007814001e0f8114401030b01c950400380c0041c21502450300310411681406082c00d41c07a80c0210b0705a400105134144 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 265024307 1250 265023057 265023079
    0x3040f03030c17030106031a0118052701060309050f0606011b03020f010c030204090e06101a1b03070c1401080c0c010605060705010204031208010f0909210903050d030207030e 77
    0x3c40440d5550f686000240603c0120000801c0c5400d42c100e001c0100359900455070111444004440c8601440803000381401e14035010000c03828040038100c60300d545001e1180f108074440010140000080e40100002507491030309105020b81400380a03022031889002e00510b00344000001d09424540d04480340e800001c000b0401054020080b0b86000144c020090211810607040503000f504944140d4690b9400c10104400c1998080344680c421800000c03200c1115050503034524003038000c080d401e0305c410810025103170b0088007a502a0841101710000796902c079410300e88400b50030802d612521003110404c1424101da03070080800d0380d011600c0031559454101c0e07900160f0251046902c15a00504001741540038080d041d001070040d6806075004255111041c50103e038540401d1151130101150a175050240c9461a0810b041c4039009a0305200c0d4000c005a4144028281c0c07a0180c0100e0803c06e41002040b60503c6103903800300e140d050850030445180c030090000040102810311504000103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 265025557 1250 265024307 265024313
    0x1003150b0a05030604030206040510060b0f160c0315060608010602190321050f0705040f09020a050f031305010b0303090303070209040206073201061a03071e050901080903040f03030c 80
    0x1024402000b0042c00c42e00541002e040103502c40d0781c10b880070744041c064010101c1c1005002d0080108490311015458601042401c8061041c1c1040700b0302000603040041c40c2000c5044039003000f01441c0900c5007440204401001141120201d505c480306114000b0010402580c000c1488000310300d2216602000b01a9860100c1d035140001384a03000344050952040124079203684081d02c03450070100d904919480e42c00c81551140544c1c800d5414800031010709201000700c81d000303819444944c0c10701c1800c083c4a8084107000313400441d6207800603011045000c0a0004c00d0148000910094016500d00020480825244e1240500190080010401240840d184c0300c003203444068000100310b202c212405c070760350403800c070038060300c0c126a02041c80c000c40b0350410302ca02401c031660300c1969520507500b1651188140c0004000c0c40c14840d4000c415a0100b5820002c1100d0003019034502c3c5d5111802c1c8000b4100a80103403183c02c4541c02804103010340301c40000c81409032500f41c24956107a8246127 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 265026807 1250 265025557 265025569
    0xf081005030d050903010b0406150c170406031406040b0906120316050c0111061e061f02031e042907080403060c080a200c010e010515091003150b 64
    0x2500280d090710503030b07800001d035961250240540000490090280c1c01d880707c01c1206031806405142603107405800c149130310b64014254607403a40d104031071014807000140b000784c4803604540e2040303004c2616a0042c0e40510894820700c0d40c8094101d45c01c00c01055800302051001800800c11401003c1045042c60000420000d4400003400560070740400c07159883e0894460201034076189c0898088281100610400300c0d01511804905001d40311025601210341c405071409030241c1e8000f0140707201ca00e061800c01418941c00c0c3d488d500215074900031070900340c8060354081c0c500b038034415041c0024820b1b9480305c545408000c1d806203900848a00421000d801c500c14103000038030701d01c0006800010850701d45c108045816841d19070550726a502000c05064441c0f04031800d00920492114510000e00500a0600340e4440000021203650480000b82101c5050b200c40c11881e0030551a61014901442a540d208201e89540003065140d550340840c10a08002085201510b5130300c1c60120352610 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 265028057 1250 265026807 265026809
    0x906091a2206180b09190b04090813061103090109030605040302014116080702070b0c06010f0b040e0a050a020d060303122708130305010e06090c0108070f0810 70
    0x8100411102d9501c1070001400c202c08264150703003e0408070603a00340c0c5001d42505d445081c0000a07954002503800b035000060401e40c0c503996109554804141c00f00e180d01c0d0182c40300403503010044041c1d40c01e000000d0668207860140800f41e50040101516a9a1080c01a070840b944001e0105054a071440c043e80035004144805401a05040050003200c0d4000d4088615107800180c20055031208016070400120841d04803d50003803003009000301d5803091440707907485182481079400c0c49403240c03070044081c1e001d2108100c899100704014003011350704a00c000000d0042c0e0002c546440d10304103105c0c1a12000801d008003007540c0d840000c1410ba0242c0444070700280790007040140c10307180d140c041c2c4408000d56103100240e24240402000584290307500380442a4144c5c440220201a0b0300c48039280d025803142003a0310581400000010b109000d41c2d1030102454010302014903182c03000c0781c500220064600d041150301400d101405402041c0d900c0030411a01c3c05402c540e5a41c264100f141060b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 265029307 1250 265028057 265028119
    0x15050f0c0c03060903120604050f0105220c02070603060b090102060117010902060708120f01030b06040b0d02061306171b0a200601090b09101511010905070906091a 72
    0x10b84004c2204101002c0020415001c0c840d18000d200c0e1111014002211411190310303c0c1d000400c0b006000700d1420f42d6000418070640030210051910994044041e42d503030101100169011060a01c0240c0c1c040c0150780261064150172800c0070040c40000b03648990600c2802408140d894181214410a41080c01c0058020b44440d947d11f0b42840e1000f40c99110b114110300380c030318000204081c100c1040181e8101c0b41c111003040d01d07503212031040100030100000c01075403014124045c100140c58000c050980d80136805a20342d1010301d080c1024000d80e80d03c0d0300c1d00b00c0c280141c1d0104031f0303e0080300c9038000c2c544070120001e030b44400c0308120aa5005000170010320040235102003414250000141490603140340c00b0303040c0009a004000d00c80b00e0042680c0e031150200388003000340111900c41c2607160725800c02d0305d0208003854440381d006086039800401903520787c02c41c4206100618031030040000030940f451b410008007070851501c101d5442d0300c0c0c075054800d90507000c13403640412501005e0445c02d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 265030557 1250 265029307 265029313
    0xb040e0c060723032a0a050c010e0109091514060a0206010909022d0a080f071503091a04031b23010f0f0e0c0103110a050904092a15050f0c0c03 63
    0x240e01c4a144003645c8030f1906801c082c10403003801c00020303008205a44c03442c1e0300c200140b155104a07001900d000c0d081868240c10081080e000203000345042c0a451040e86031450007888003802c00ea440800d907001c1903500ca002d02d0302002030ba2407290b800503995044403550a40040c10b500c02d1310006400c0f04030600c1004044010441c0010038000003450740240101c2143c03a5210550745070410707510390807030b000c110b0303510380001104024000140b1600d04460780d103440d000807a102c05580d0340c0219040c0310300d8003130781c2d011108c204020940c01c04400905401e904000c031407403000301c1c1c0d240f40d04846807160100c00b042104800c0707458004250071005140c8000103041c40701b0001450307010004d04420310050390510404803504180c0d4001e12032003a000e64800301040c54841e009505a034039a07c00d2840da07400ca56681d40b11400b2441e080034804265035442d900920100480482c00b02c02035598001d40c89401200403d040030607001000c4a040824bd01c461940301d51200c5202414480340241041d0140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 265031807 1250 265030557 265030567
    0x4060506010215180601170a151b0207030c090203060d0807030c050f010b01120509030301170304030803071706090c1b210909090d08060d020f0a03060b040e0c06072303 74
    0x1131103070706003e4907002c041d40c1100c149aa8800e505804001d608a0850464101e0043c0d070001c20445100040440681d0340003283e210f01000c1504034080921150500517040500c6c28020450a4100031f0001e040303000003541141000000a401c101507810010301000c6d00003454010140100341e2405416005000c1c0c0760745c45100c0441c14082d05254500c1070000b440c81c1400720701c003001446801c0c01107942d0740007541503a00340442503207040c601e4560380900380300601c000070001c1c040500541c0710307107050364880440948489480c40d0440018001500c2800800100206240345600740e800041205c013410303403030b08441618182400c200010912001c0d00d001140c0000c006140300411491000b55181007440d950080391544841b15276212500140c26500815403038541540701904150006040b000d05414a0300011500200b640c0201c070590307140e00300c1710050f24082c8245061000c01c41c0c0604292131009000825522840000405560080c0381045621040301001051100308104407a591 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 265033057 1250 265031807 265031821
    0xb04090b01180c080915070c050a05100c030915050c0705030408060103021215190f05100602010c031a1908070803030a0b01030902032d010c03091703040b04060506010215 75
    0x1528880c0740c400302e401d051020000f503007032296001c580f050203580041c00c04405000c24580107920068290b404105d448c0c0d00c0c40021500c10b000d8140c0d0365125000038803607442d0394807424040c1e840d0711504e44141440d180450005c20082c9260070b46000700e01000107815621001801d0541c05a40400703090361101007008100c4010000f14035068074004c9480c0d141d071000204213203a035215400e000c100d00da105213010411002d0010b940e07a03d0422140004580007400c9103260040740d00458540301c51190140d0200109502880b940f081c90f4a545418000d00c0003040500014104a5914601440e10f000000c0d5690207100c0801c3c010740b1030401601c00040c0d0703c281c91035603074000780c40c10104c40d490006502500d600030300c10500c403180c0c0900901620300c101c0e9600c0703c2c41c24031900b00070300d0702c5c00c0c0080306105083d00303219003184600c3c240c030001040c0c0102e061200f136060313595454542c2c4540030010300020401005a2580c440d600a0f4085225078030040100c0c20700e80c62070b01c21300308000c8260030b01c83e00d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 265034307 1250 265033057 265033079
    0x20313030f02092d060f0d03020a030f030203011d13060504050624011202092407030801090606090510090e01121b03021c11060a091503020301180b04090b01 69
    0x3003074001c950307484580c0ca071a407664403251582da21210000c180018046039610007100d03134580c0000000d1010304100d4003a008100c1c001e2400c9001c40050304500001d908064003c4010a0410010f280c21400d642c102484410304d0080717400707580610004d88001a51316500e10030540d07030702c0b42d00031414019828a8a00310703955040582e000d02940b0480ca602c1c8180c0b20340505440c021003816074a02c180c00320210440002903001c0b541d0303250040512641c204000c8418591203809a014001855444030b0506004090f180d060304800509828043c0810080e81d000d0314040588204403451210400540c2c2c0079640328185502c28110460b00d8400080c1c004420892400d40f107009500200f42c05441060302009107005002c000d40c00ba180c095a084416049aa400340c0c03184075449d200c03003c4062600241c4142c108110034000a403a130074090042c0f44a00c14640c01d1404030342815421541007006404001120704034611210b81c1d94540c2c4442035540e5003000340c416401101d91041940c450724000c42e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 265035557 1250 265034307 265034333
    0xa1803050301090e1c09060f0e010f1d09040b060102190c0506030c07141e0f120f0702120f0106050108100501211503020415060c06050601050408030c10050c030103021f02031303 78
    0x20204008002c40032320240203098050300614169900300380e442800c201622070744c6840c41404035081006001c00d41d03580320420114042e03402401510000c0c0344c19400285045a0741c90070043d051180a820400142c4036807505003a24000c9450940f40e640700c0001c1515401344681c00340010240c0464000c201e8408510706140d03c540203103a0013540c24a803070a56403440305059883d1304d5800315100a0b09030503907030090300c0e000d45040c1074180341c41415000180c0307544000140c030f04a40c025210008030768009109140c014542820b1200d0036140c001446100c0030041e12582d4180882d0000c075060b00040400101d101e078145900400042040e81c050039828103a90000b240910300d055400e48008400c400400d007195107070703074600301c80b01003541d248406090040e2155040c060240008618198103101420002c1c1c41500100fa00340314250318030050f2074010345100c3c2c034081c040005001607101c00072040c5030005160515821205091800c03440c44c412908401c855507500d1101104000188034000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 265036807 1250 265035557 265035569
    0xc0a060e0c0103060b0313140d020303060901080a020616020a031e0c080102030112111504032006041404021806130303020c060414090703060905040b0a1803050301090e1c09 76
    0x341c1c000d0030100040d0211240c0d03018513003242c44280700041601d88101c42007100c061264048000707100c4100001880d00104405480150b08080104840e504207101940e0040030300b400140b4420803a500810014800d040c480c4000c2072122034000f0a54543c4541000110342c40b45001d43c00c034260031a540f410501200085a08141044d00011192814025241654800381c1400b41c00d00003959101e01094214030440d42002444000c00d0441d000c0310081e10045002c1c1a0040480d2401a102c1d201855000140c0e485078806000500c81c04c6107150051000b21415900160768403a81310741e1200c102080307581c055006000085104111507003001c104102e070f120313400302c60304405907008200d884c2c017503801070403420074801e030440032a4508403071416000002c5080000e041600c504a02058031000c603801e949216030f840030f004480110384203e4462403036030290b0294a40f4150340041c80d42c8010720a1500c40c0d0788a0b581d1544500302403005410407070102c800d4a20220031060050000d8200384144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 265038057 1250 265036807 265036813
    0xf0b0717040f140a05070b07030c0501020c010b13090809010c02030a0203010c2613030309140a05070608070201150b090a09050406140601110715030e0a0501061806080604060e030c0a060e 82
    0x684480715001404e0210140c0c400041d01e03119040c442d1650468102840550402559070381c503001243c000c0c4000c2040c903c3c007900106103e5410313001d0180681400b040d08032528581030b50301002c0b908482c244d450720300e02407a083c2c034250300a0000a140010540c1c01a500d5441c1200e00b142c81a0050503102e1004c400c411086400c000400906005110485c2e49400e0a4150b100c440f000074881c1d840804960b100d6048c45200040c8400d00c54a000c4049504540c250701844003403004a8002c0181a4046200d200a00074000c00d040003410000c4107205006203220041460170540d40c485d2108d00182c90740c404204110f2400d03050103006400b841d030f200790881c0c030f8050101c0d000d07502c10814003021024000c0200895441c01144045105da84c11100b001c0668803448544040e5040c00384100440c0941c0002c039007103041062003550810001103070580f440c540f040401050300d010401980c00381c0c0040300082e1003000c116019041d403040c0845042980101c1064804208081e807120001c0f004190032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 265039307 1250 265038057 265038083
    0x1509020a050402131403070e0c040e160c060903050408160906060519050705010603020a06030f140601021002090f1207060905030c0904110307080106060f0e0d0f0b0717040f 76
    0x2d2108070b00c074011214000c81c60034201032000c2a284000b001400c00c02030110341074980e40b10440c481d8031301d050b2860000341900103020001481c0c00310790260800380d01d000c4019000d1010502030030381a24a580100415156102101810300550545000341403903010b580140c1000d8124010401c21401500215880c014000c125184120240c800d80c450341c24003038202a000190036100c60704000e074100c07419900e07280b020005031680709610340103040c2600d002c11581c4801004100791041e2445460010406000b0030110342e0b070002e100c200d104090340303005030350300e80c160301140a401380c642c8200d40240b407000004607020000510107080b9000daa0360340300d020340c82e001010348030075407048000d6101858601080c0400c0a1041074100b00310000d0417918080c0d40e8030700c0503007541c0031584018080303a11100e058944d1030700f2290724042d100d011a5030300d509602d0350b038030b9020b00c40100070041c00c00001607001484150061016100c00401c240607210715140910b00074010a1200800b21109451100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 265040557 1250 265039307 265039309
    0x11e0903090905060306041e08040b07230c0d11030d05130803071a1509070807110a0b040605070504031502071208060a0e19061e050109080c040c0c1509020a05 70
    0x103c0c80d0302400300140030300416100c07611440d4004410600c14480c40e000345800c00009980d03e00200020103050f59090344594060a12488000700091201c82e00d02007500035815203040811080703680441201c00c19000c4005080800144c07081c0b100c41c42d010f10a1402c0f510072990880082c20811607200d403c410b031551101c5280e51079004100006001180c051034800444182c180c0581c1d01c051f00f4001d0405842d03140d1300040c00c04005031a02400f05500b0760034040c2c0d155218600515405100c00103014207000782c2d603480c1c444000200003421003540c03400440c400c58411030460700219040502f41c08005200c5030144000d41c481d071030444440066840071712446005485980c4546002001841407a01e01030b003900c519074008008200822203151420b20f0b4070a507204642c043c00780c0e8428400b09620101d0002403550b880d41025040c400729100400070a000011806241c0500343c9003c51030005400040d544691030640052001c08003113513010384020307140c1c003aa24207402210104bd1103030340d0750 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 265041807 1250 265040557 265040561
    0x20408150103140d09050d03050c0604031707050a08060f0d08040608011431020d1a030105070216062a030215070518011b1403031506090a05010809011e09030909 71
    0x8410440400e805c50740030445480c194100385809402070030094904600c61540608064003190103c010423041c0c0703183c10540118210b041e0f40091035080007860701451601c050401c110003010700303101d14160b66100140ba2109462940e119910403420368030f40740c40f014003412103d4240030700d2490080c04050a00c0501d041c185907154041d809280382448604044a900a074000c4100741e10b0464081025007034000c03070b0b48525000d5241c04082c021204110408140c00c0d6100a001340382154411010b145021034181080e100b111190304001c040036040e4996103525042503d406800340310000031010505402003a5618121007181c0054050380d1990401e070341c0c40c000c1103603600d14640f0801d4490304a50060040c080c9000384085150140450355444a08003102c04121087c0b075000030050100d41c01c0001d400e410070342c0086a0490a1240031408a26489060310401c1e0400892030040f1701640001e40c032a80c42090854140141e5000240100d405010725060031800a600060002441880c0b4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 265043057 1250 265041807 265041823
    0x60f09010c05030402060d2a0908010b09190605041d060f040c090b0105090303160c09050105030c06071e03020f0d1809050606130602010902090a1a100302040815010314 74
    0x940b16282941c44680038410b803508400c1c20222030607a07a000100300700150b0703200d04540d4810b0f24200106038a540d000200041015404031f1003a038100341410807943d81d043d036a281c0c001e031064102d0a20514110a10018117000d601c1290400d25101764900204400040e001d0300c0c4560070100e03851a15111028420b05100700e5005d0b0024200030b2082c001c0380b880da0810550b42d0814075009003448a601c0001c2e08550140c07848611914000310036100708448e4070324510062401c28001c1100390b144c0000b0a444084480c0c84a109010000d0b00d60b0030000e04045504030010713010b0f5402640542c030300d8040d42d50181c00b00307400301c640b00c0c80074004a000e1080d40c1d401d00000100519007801440c20a0b04005490301502080d4012400d000341540104443c10820040c10158000724525240c2e00600511800181020109609000d0491242803214036106144481a243c00c40c1e864039411044000303000325081005c0c103020324881c4d4501040c60000760340c16207011b03245040803d401e1000e22a0703507420b5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 265044307 1250 265043057 265043081
    0xf0210050a020d0e210106080f06130303021606020706060812070c0e090703020607030f030c09030305090f01090803040306050a0e010e151b190e0f0a05060319020408060f0901 77
    0x1040d100c1c608621a04c2162983c40020300315001c14140d0350320300c40c120b2100461148943e0341d680307400c204c022410440d40c15401f0b11007000d880326003009060090501800c07a80038061580025003c403444000c03880c0b4032000c0e40c1007c4119100c054900e0100050101403103400183e2103400c102142d040c41140032901c00c0341d0701070140ca149034640502125880170090181d4941d000d940c40c004056150031005214140c82542c031898000401d10000c0c08a8121101200800105c0c400900010360808102c8407816011940c9075144031405004840e51089a00032411302c0c00081400410801160131a501618206a0500c841241032800c10f0880725281e425003580c5e8032100c0c661400000c03010304a07402005038201d01801601203919130304994414805040454480510b2600c0c19a1200003e0384881088134901e502c8004080011003a5030035004092191100002080a011154000d1110042c0e80c1805645840d0740c3c40d082a2107020480d4406400d0a00d0000500c01c010180708105100a03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 265045557 1250 265044307 265044313
    0x906030105100e060d050a0308040c060c020a0603021308100b01021b03060106120b0607030918050f1b0702100e1503010f060809030d0509030405031b0306070507020d0f0f0210050a02 80
    0x3143c40c01400400c036024264540041800c01010f0200c5c3d0103012400701039000b074940000a0420b4544060603416076030004040108030305042c0d0059440000c4030045907501c1ca000b50300ca510b107115083c030440070b59008060a01c60700702a07401110b0541c014003120903090b02a100150f5540600c800162040710400380e040e0050801400054000c01c0342200c41e4001050004100f04d016000c10902e034007a15080d00403866604c01000205c4203285060f4500030254024010340c2000d468000d922074011f84585102c2c80304001220004802005940f806900141400941c02ca8041c1c05070170801c01d48061401450300341020000c60b440103007201e0490b01e05850000070145000c5044070895405403601c420341c00108440c20040c82c0f1030103118041c0c501500910340c0c880c43c14081616041c0c2c1c1c1c01e0311030503242841d84015100e50300820b02550200a40c14003960f610344920000b209010a07550080c803507240341142c03009011803c0b0000a1540c0309840f01c0825004c041c0d02170b40e04d409001200c00040c0c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 265046807 1250 265045557 265045559
    0x40203070909051005040b0f07020c01021b01120204030b1b070f0602070c080d031a01020a0c0e04020d1703100e01180f0209060c0c03070f051005280e090603010510 72
    0x140c81d42d8003400c0060301403401d903480c600c0c1012002c01030f0b440946046d604401c0c00004e11200100011103203030019698001003017040d940100103521400e51115109000030702e8200e8100310390065900c0c0d01c2c1400b00030301c110742c0c8070348a181449043c2004d4500124280748101c00d49c0d40c110341041214411a081500441d010613241d9414019510a00007102c4502090030300040f03c040411120143c0c00c02e070303103011a4be20321244110040b2000d881150381150321070b01400b030100d80d180610a0036640030341d401c040b003030b0f540f030004c10f001c5030f00d148006140e1070000c22120f0003416000099802442140303c554282651400400340b000f500b8040d4107042104040c07001e105003000d81c0441c030041c0200b5030150401200c02c0c00100c07190018241c80700c1da5084001d010180d440d00380103d801070301a840f40d00510314180000315020721035521303400e0300b480360010b50210454280c0b070282402124005070052103804140c2c0003416400740a06850145401c04007242a07440c06010b1103201d031070311042e445203407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 265048057 1250 265046807 265046819
    0x9150c030c140106031e0201230708160803040506010e01050901060905040209131e0b04020f0a0c060603050619050a0b030c060901111509070e06030616110a050d02120304020307 78
    0x10303010214890455650f2510004001840d000f8001106c006c0400c54800e030500303c1c000905606422901c51540d0029071940c1100400384030b0a481c1019008010f5039150102c040c5064100000c03800003501c407401c0402004100000014624165807054401510701d0343d8403000c1c090749071003c2c017030003001c500c4000e803d200c5030901e0360180c10855801400849105d003400d60403421a007001c2404111a060300903104240c07a054001c041c5151030586045240c000711801c10381f40e5020b901144c60401100114901c140b1101c3e800c0b41000d1500b0000f60340d0700f81802c0d0640020b01d8003181c3e01c68503403070901002030103a60241c826011000f001034003800022039014100100c3d940130507200380c1402403115807071909400400c401003040036083c0d12003086040641d0018174015980e4804940e00b41c1307005c10408262008140030350404119082074000801828040c0c0b040201e180720300340c80303201e000140018003074005070750b00c1004625002c0e40c0308000d900418014034881110003030b416511520080000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 265049307 1250 265048057 265048073
    0x71406070f1109010816080a080703140f0f030402100e010c020105130b04140102010b0303041202040207020d05030a120f06050f0909030f070804030501050105180f06030f0d09150c030c 81
    0x2042e00c00e604040e0800c2e800000225103800c280c0100c982540440c4075421011007281800d0058031030607005000440039642c43c1c814511a404000b42040b40110607810141c03400401d4800c06580005001d0326110447c0320825560021035050f4400d811005060800b41d0082d003174521a914180d480640e095140c3d0015122540402c0c150b1841030300d0301e080001c022284038040d20182001e40d0261984142c230170002800d5541a1074914480d4100f0407040160410710903010407201c0c4e06680150f02e0f0303009800050104440e804000e84075002c000b03000002d01f80d1205c403884480304a0202004000420442501110f005000365500400d000320514124540b40c0c5900d42e000d000e41085038a054400280c0d5041c6821545084900200110b0b05104100080c00344a02405c0709035182514410202c0c8440040d00d409466003420807410404034285031401d114910740035048200b2110001c10b81600201050807503c035422a2804440591101621a200320040b886e0540d6409400016a4413005070b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 265050557 1250 265049307 265049333
    0x10506120613090b04020f040606081f090c080604050901050702030d0b0a0f03210e010c060b0d170711031c0f030608060406090501140633160507140607 67
    0x15125614003030654040b851400b4400d4428490404907440f42020b205024044e0b850348090340c0301c1c9003015400d0180719408bd0000d42d04c41d0050450342c04004c041d40c0d07600b852140c6030304410f1002d403d24241c2030803d5009410240038000c107031801c000a5480c00c440c0f0b030884a0a450b55401070b041004a0b02d420095500800041d100051030068416520342c00d0b91004002940129058003071120100c4410039441c598014140a90410b001e0000300d100000308928034004004080ca55078000344d035056203c0c0e1081c84400c0c0c0e0300825100c100c0b450840e200c1059000580c084601c1c842c071709191045810b0209040c0703000c9030f420150000401c0c204106480400702010a003080681d00c0900040782203080040c2030299000d0407000403130844905003c0e080d19080c401c406122080700c4203000140c1c4075516030180c004201201c10036002601c034010a108040d000d5060092100031480440c0d0101c00380851681c20320a50440c0e2255a5030384802038025040c40a0642c01081072165001003604400401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 265051807 1250 265050557 265050559
    0x5011b0804050f0105130905010608070504051809011d16060905060a03051317130e060315180601080f2404020d02010306090e0c030d020f0a11030a120f080109050105061206 76
    0x5d400d1910003d18004052183e900520305540c0f204010085075400085107500008141381851405040c00d0104603c85010010312035014010000035801142c00e40c03298544031010800b410010102221a903511803160f2640003c104c85a0800100540180c061004030740000d001c8da828207140c07000540040400901003d103040c000d2440400084001c018010302d605040346994940c0706034064144100c5094100c520300c00c090806002c030740d07600003440380d1540841c0c4c590341400d40d85451200c2e944c00c401d00010703240c61248000101d040907000c0303506102840f40324210350060000e08148480b0b01c00051120082c0340211000c2800742c20010382210040c0d006060106150390ba42269100309c03009002c00c024160080c02d2403500b02c0c0343c24002201000d0040c0f0007070201440c40e24046e0344585d00304200a102208110007898142c07011f0040280d5540c00c05000d0b03003a8008980090910304440d68960000f900443c004a41002c0780d10665040e1507000d07086030306003001d00c020f04c802100058809 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 265053057 1250 265051807 265051817
    0x3031103010305100f0b03031b0102040f030c03052401150201090b18060603010b0f01030230010806010f03031b052d0f0604111014070c05011b0804050f01 68
    0x4101104262001503000358495001031000100045100003100c08001c030415215040000807901ca0b40d0000035504079164801e100000d5007003051010f802441241c0c0101c1065045840010070301031503555500440b401801518113001c51043e8402007417805200c0070180010403001841610744518081c2c10a45060000060038401a1110141c2c3c0b081101e444012420b904005400c2920a12603590000b00580091082c00903a6000598909906107910b040560104808052006042e040318011000500082411804000e0070411400c2405134101c28883c980c000506070340519030043c00c60f50181e844104810342240c0780e00d00d00c801d2160660707881c0f15908000d2099440081c891000160300c0400445920840c00031609214a01c4050344c86900001c08000100b0a0060009103604040b243c481c1d0780c442d50b0000780c0c0c200c550062000b1041d803004c900c49081200d00340d41e42042d1082600c4060b205010704581d12a0341d62005002041048140000c024608124907005e46040050601c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 265054307 1250 265053057 265053071
    0x106091a030601210e03120402120c010e1509100521060306010e0406021b071401090b2b050a05251e0e040e0604121818020d1a1504030c0905040303 65
    0x500c5185807c41e28038070b8015a210003d000461502d0a0701d40444040d6102030720a003000c81c0006000ca24850704024001d0783d801483d030208001c10b40458010000040140e52040e69110008149800c038203241c5d02c01c5801d950026422540c0c0081141c03151100500800d810303801c1048030194598042c0040741ca0316000c2c40070082400c02d129000c1001003c41b402030041d18600a041304849440f50b034100d040c8001043c0c140251582007045a404008010b0314044910b041044405069404000c1d0703140c00340f500b010301c003001c80035130002c03406042000740c912490304110b00442050b4200340d07403910205065000d01140015003c002c3c5c0c440b11a10f0401940c0c10f41c0c980c021405032450075200e0021130300110200800c10140444c40340040303010f40b03000c03200c0b002c0d0240c599400c0c0b00540504440401c071050055400c120f941c0403a188036042c080c0601910185c030341c0102c0448a804a500d200302c0000003010141003031305095604a0b27802000c070003001450000c441000303042c058015010591100c45c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 265055557 1250 265054307 265054331
    0x91a0301031721060a0b0408190309210203010b010503071b0606120302061b0436020c06060f19090905190312050a1104030b070c0b0106091a03060121 66
    0xb040720440c0c16a400000303030343c1341943c04c1050a008582005040003000d000c207104041000440d0500300326140200d401940c0b050500b541c0d030130020b5201e840c4070301c4c1082000d9003040c086000082c02904c00e40003486980070540054031140811a50304001030324003100c85c640b510a1441e0070440714040d1070002104c1d61a4040404910b902040640c0568442000e112124036507a2468070503c02e40c0c1c144038101400c0a02c511401c908400704030904001900501c5000030400b45e80d40002410408119a0342124085a079291328045030214410b1002c1c03121005141009420a070b00e402d00841c17a05207060403e400c40006203142c00c0241c038140319000c44504902d4500c031070304105500a89500c08600300c29500001603c40c0100304008450514460398070820f4441d0640301525800004000c650b40c0d4000204c07000e20226a000e0720038000750b80002425500104258151035112400000c02c0b401182c007490130348016585540000c8e02c0c2080e03103408450b10b2003011600103909030041000010b04ea = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 265056807 1250 265055557 265055587
    0x615050a082503020a08010906030b010e09070915060f02060f0c0708091314090d141b0d030e0c060c070303080c16030806281503140108070303091a03010317 69
    0x844401e010136400283c0015046d007040041d4010488a401805802e04540d541c0300300c100d06100b410144060000803075031415041c403102c4094402d001040000340001b8840998481c40b510460000c20201141030f850588007140035032003102c04250300c1c04e0070f85440203980d00d50740c05041d003920a1301c0144400703440d994a1106029a6410088005c42c4010340e802c0c01c1960b84a0240011005a010b802d02c2d11840360040703002003960781000f282544554080c140744101c44810b240020b0580a01c135017a040c0e0ba07400d54031841907101c800c401c841406188005114a41c0328501c04420658481d04042000905c102c1160740d1024813020703400e0504403082001241844055401c0340843d54200400c511400d210480543d148010300c000f00e801030380c0040d1215405414010090190300200c0145102ca020790082c9100d071036904101170156a4482202d5100e4032180001c400084c00024000346560558049000140041c60318a2440e4a581c0c0c1c3c1085a00c00c40e070120080c48014000c01807042d0010f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 265058057 1250 265056807 265056871
    0x10b09151201090c1e0e0a0509040615050f1c0804050d06050402012303061e1206150303040501050d090c05131416020712050307051603060615050a08 66
    0x201080020b50500802c102620365011440b800c200400140340c0b00740005090100309000c1c1401c0029440c48a0b00105241c0540c0d600300580100101051000300f0626a104a0080d01c41d411041c09403a252b00820800c01c145204444d03021696403c2c00d5922402203110410880c070039040c0070b00d000d580b41d0100b5007041e9100c1d010b5901e00ea03900d08100555030001211401c5001e45405030510400ac1d907a10745041c08090400350040c01041c0e40d0707507940d0140b400380c1c070f01c0044001d10783d2160788001030300d0641e00c41c012034603440200010060a07010341000019a01a624141c480340d00305070085c400d50000f410b40940941c3c116448420000d00f64560b4800c1d8502d91041040c00300784501d040c10b41c0f06a00d00060601540310185100310408142d000c2196030a446401400341034020541c181689140100b10024185000d000f0700088940c610301119011640700380720521039650fa600f0a0541440d00210745000305104200007a680d500c65854182c3c005658044810540014401e215100c001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 265059307 1250 265058057 265058077
    0x30d020a0510021c0c0329010e15031803040302041d061e1801150f15021c050a05070f03020102180d020604300813060302030609010b0915 61
    0x802485402405002e11451041c0780000c0002d5180005064035200d05040b410300d00903007280e85000c10b12441744250048542c0f0f00c0341712411400e6010750b46181408503a40c01c6450b0100e044000000704900782004000c940c10784000021381103507960403144404000c455219020b60104000120050f41d40e840f41c4581c081010104440d40b2011301411032519001914441707409004017880281c03030030300450b803603400302552075440c019414051400c1e002d00860180900c0e03100301c5d030300049008202010030b84122041c141e801507607a140081c06984441c90362a20322144643c3c4648134210500031002816a00880e1410503d0405251544140d1484001c0c044005075000903240290b1060510426008103044400e00c0079800316030b00043c0d0510451182c0c3c2001ca42d80001c41e0800030400d0900701681400c0101e65500500620f002c103140d07031001841741c00413000342c0f40201d1041d119100f0f991095a0141c00015940d0030b0058080141e0044910b55911550244015015803420005850b036510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 265060557 1250 265059307 265059313
    0xc021218210601060327060c0c0b090109050c0d1a06060c010203100f0918060b06040302090403090303030507050304050a0b10090c08180d02030f0f090a080a060b031c1d030d02 77
    0x4100301c0010140c2e0040803841c16000c642c21b21203090a6640400006001d80c0210b000440d94103070782064500809000c000760200c040c06082000603441034018502c0c80d40b1885c141c3d20200351642c20481c0802d1b4501c005442c040110305242d00d800d00f42d9200320b80100e8001c1100703017050202c1801e80e09a074011681041d00c1c400b141c100b00240c242c2c140104000c1d12142d80140310801e05000c05108004035160302410441c1c460807403031060f0711030104a50107103070043e100e81c1481c502402c4c0501050f502d48002c41c002841c142c001503a46100740c083d80d00465002c80a4580b68101d600c1c1d400454101030140c2c24a1011003000107241e040a124010340814640c940c089030385000107007003510b0f5180000281064000300c0c04840718543c08400ca60760321840040c4191544001f112072406070045200e001d401088250303003c11807400005050b503000340700360341c241b1805561106060315004c500e01c48406803049541d01d003103141d00403144844480e138218440c8c0a1080704400082c0f4242400d05c00d280560 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 265061807 1250 265060557 265060559
    0x30d1a0301060b0c12030c07300302070809060c0f0304090c0e0612060910030b010303030207140d020606010c061401060c03120e061303021504060b040c021218210601 73
    0x1003402c0c0540e0b002015001141e0782400ca159010740d4580940d140c05030100f00001000400b000c0084042d030b2203080c0c02c1000042e41b03120220820301204400c05602c0000101c840000481030b00c82d00844807a1a413006840c5c2c01d2006050600c00a90440a84601c0780e000b42c90281c06090707804c0001d8001088a101d0103c1c1c21100306601414400025200d203000d40b03c200600014491280403403600b20106130381e0030500341d486494039031200c0450b41009200c41000c0000209240d81500075010643c020310a005020304c80200c034982e1800100c484102613000140001d02560040341410f0b1198012100400c5d85c02d52107a0700c0044101c01d030040ba01041000420f1400e06070302004c1801100cbc1c0708201040f5011800d2a02603803070703000810800140807058500d8003018402d00072009080000159400141801d240842c050850240c032203001e6407034410132422040c070000328503c84145d0342000d80c2c43e1855000300114150503080e25182c2015000400150b400351003d07035a800d00c2400e50103050f1b15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 265063057 1250 265061807 265061809
    0x20d140a060b0702030c090402011e030b0f03031303020112020705010f0608010b06040e0c0307051c0b13180609020a0e16032306010f030f020d1b03050f0c0705030d1a 73
    0x307990942060103840401d0081d0401030700c1c00580d024015000b1912119155a54401240da01e955070700c268000048107800b4040440e019004410115412114090041495414140d403805645020b91907280403080c10405540075104906400d00a00d40c0980b50217044d45a603425154803800001406659a601300510303c2c080c4660403024004076252841c10740f410540d09403495026121003c507000000c0450f440a0086040b40c5010321440d248000e203100030000c072001000c4400041c0d02440e80806c400c2c40b2100c4078840c290440780000c103580880e00d52030b03e58900402020740c0490b008801d01c840442e00600c0342c0d44991040080415a18405151010040c1510600c502c0391401c01800300e85034012078051820950300caa820300e084541c159451f01c3c100e014100c4410b42d20041c07440050380820803101d940003640221854289801c454600b03c0b0700318200c0b80c044413040a200103000200c0d001d200003000506496005030126800c0502c1440c0b03a2007180c03880012200001100d880c0f01c002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 265064307 1250 265063057 265063061
    0xf1609050604141c081b010b04060801090c090509101a03030c0a17030c03150a2c0108060708040f050a020303030f01170c0108070c021503040305070506010e22020103020d140a 77
    0x2c1001c4c0b00c14013406424859031159910301610320380301081c1a410f080009001400d50102001607030080042c01103680e40d000085c000c02e0808000c1d105100240e81c0400d80140c0e9004681c083e00d40c3c24010407a6054a0940000130076140304c14100413500300d04580c0ba59942000030700002c03143c46000c1c0c208010946003c0c00c0c0c032108030b0045a003250081c07003004234800c140c0055950013a0030807448646030940320000f030b58400503078100c80c5045441d0101007505000000d411401c1c105113800b85505a621000c00741d540f58821170b44003001a44290015000030040144039429910401c11503105070019130005c1e0468000301c502c400e603e484600100003d03040c0c51003815000c201301002d4155a100400024220240107101c3c01c00d0001d683c20103000c54490403d00c035818010761001d1341d01d0381041d00c1d00a001d588031141c00da40ca0b103d000004607804440900c0300b400346040303291006242e150000303658014003031680140d0516500b40041340a00b1800d0040400014280c20000802c2c0b03000380341c400c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 265065557 1250 265064307 265064329
    0xc06051b0c060a0c08070b010e0618040f080c0a0b010b0d061202030604020f0d020406181506050909070e0306070905010207060309020f062a0307060b090f160905060414 74
    0x601d60007014020800d403510800c843d492070a41c5803445050340b00341030000710307845142c40007080145800c00000345880e18415150003050101ca41000541c0c9101c80382d440c101c2c0c26036010b000c40054945480006854100401c900e842c1002520345460040d196480b05840c03da10414170f203800001c2c2d4030b000c030300c461240c47c000e00300c6001d904110620540129903502e5004000070f000343e0442d65220750959544030340711030762603005005204154030303141c0844c00001e10011640559042c48181c03120b00c135080310b5030000d44c4c845076102810b00600c2010412084006008042405a1943c041d28076031001d1020911649050705d40405051074907000a103488811750000c1c0405162103103d40050361002251502e000c41142c0c04c0d92203001504005850584107403415810405010100c40c42d000c011014001190107041c040205c090800144540100102ca011076880b1502e4000307454500c205c01e886441852526180d0000c507110300103d1080c0d4030580104c801048400310700c5030545005680c00d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 265066807 1250 265065557 265065607
    0x406030501140103060602100b040e01020a0302040f08070e0a02090609040501030f031404120807061116060e0a0b04030309030c020a1d131101080405030d06030c0509160206070f0c0c0605 82
    0x4026450020000d441e50b800351080007208d1348981420302142c1e03881c2c1000d540014080300855a4050841c4080c00a502510074844905103d207400600c029022407254229440340126042543c0c1d40280000294450031989034403040034450304049031601c0c81428041d612480300c080250303001d8103028118a420b111800000715007044140900d0380980700000140d548030003c40d40f07540440c03900402522086482125030303a0042000140c0003d0fa60112540c03030b00844080001c51550444643c1362104058044c006140c0e4030041f0f00000d00c294816a2600e0091604200c406846d07030014a100004d0750001c101180300200400c0000303201d40d602c40c2c11181ca0494843c444125a170b4040c40e205050789054140000540003506004d81441210050b0356224010000e9584034034101310328180a008850098080310001441e5081d9141d151071078280300d03001005280d4a201d0100d40003201600c0000821248d000d01c08000340c000b07131140c0c003d040103444954031400760070f044010065079000d4003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 265068057 1250 265066807 265066811
    0x1404051605010e120114131406010302010e011101021207021c0c02130c020f0303070c121b060b0d0b0c1207050a050d020f04031202060a060519051011030406030501140103 75
    0x4005581c0c0141d03000f0810720040d0344001a59011801640c014424185485407203d0708104020040d0684402071149520898915510000340c4078480c1d0340c0c40003404000d01046141c0360030401580504880030095a28a0015280103540c9500364a00c820a80f004405a8040b8070ad096070321071448a0b419035031500346441c0c1c1121050744c00162030303e581c0c80c04264000b640c504803e13812074030a000e41c0800e1802c0c2d40481341d807810a080014120507200320240c0e80b142d03820301030f00140340c1f0481d20407500c080b50200c24001c1c2d60090716007200500000103e50350005038482e800f0b0004000c2444a03109541680c3c5454540b81010030b035104843c40181580100902000368120258002040d901d61800411005031980850791010741c961103582c0016145402e0b101c010201326500113034051045414101c10f00c01c0c1640c60040c4014040c8041119203005900f2400344014206100031036400141172409002a4601e8003029003580d20a402a0001a40318001071185628111150b58030210070311701 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 265069307 1250 265068057 265068059
    0x60a0c210804020f0a170a050709050106081801020d09061a060f0712020106030b1f09060b04061b02060c030d0b1503040b150406080f0c030a0809060d090614040516 72
    0x200030710041005100030300c50407984144080b140c40310162440501480c131103058514141614040c1c0d6603002c1c81044402c1e100e0004045281c2c9403d00601341250215201c0c100240c5074103005d03240c1c42c42d4000c0a4901e0359402e0000c48400ba40c6030091062207030040d000000d241c6240342c20040c00c81218000380b0300807482086061901c2c1c0c400001c40b48666088602c1003e0b0a1151004a02500f050380c4003400c2d03281654148140c1e102588003210300d80c04540204810036658140a0050f614580f054001d0f102c018001005243c0c0150460200c072004030411a0720320810f0303800203003140c1141c5e8040123140e1001c28280d0420446114201243c8000c45230204181030340c401020070741c031008000618401859002c9641001d0343d06103040e0a0780010010710010392036140065845802800030034203849060401a21820701195004005801502092820340c3c0b40c01400701f00d5100d956450030b143c1c6d940041c0c1003c1015445002c90031062400f80d0002d504060810714680030750846411203031090701d44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 265070557 1250 265069307 265069373
    0x2040f091e0c080102030f07020606041104050103020f0904151a090d080711090a0e070e0f010306050702070b0d02070c091406011d040f2403081204060605060a0c 71
    0x540c0c1c11441107071211141a1405803070500c5080d100c03070b84000c2882d80044184401a0f056081942c0b081c0801d40c200c3c3c020759251020001520315081250303013100b80c10001440554460b40017000140307100101d4504d0150003c000c10211b410a0742829841c0341c8102050111403850b040310301c20303229504a13660501003c000003802c1400400001003015000041400410024240700844000020891130301c44ca406000d01d0007500c400d00000106005441d804039400c00d048240d01d00130060780c1d40d003001580c2959035044c02040c0142c5410194411500c000035100146c40c01441f1030f0340c103a0030240e1a0b074006e2800041c03024a03a0010901e103800e1511161905617201d0b00e0503802102443c040c65240440d825800d00e104000c1041600300e800c1c1414140038100c190881c5070388001c10a2038209240035400c41035404d0209010080c030a0604100b841e200184082800381c2060040d0400140b440d030b90000607400c1d9004c1d2841d4000f040d00701c400070080c0401daa8004402c6010b5011050560010342 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 265071807 1250 265070557 265070573
    0xb04110301141005061e07031707021f0902030c1309060605040b010e010c0303270c0b09090f0c12040311060108120d050a1503260a0c0b04060e100902040f09 69
    0x30140e13500030540481c6143c0c2c02a42800040c1026060340c042e03642d10506410020030701322440d482004105505004200c100d4400a0340d020496085002d81d41c8042d04921440b0141c4013842040e40d01d486035400e181301030b0b80c1c1c116140c10404405c5000042140c0b0f18503046c0b06032501d1f6409035200701d180086d03038107143e41c0204101c00d41e0303034091a015441c90f046140a03001000a141e0040300c0e503801c110700031450088600460b00c0c0900a903a17580c191540e42c04400e04c80d10a100c600c541144154010654115803164a603030403007848448203050a040c070108245607030080344c003600007a8000810092009041c0b140e00d0151481c0320241c888903020148840b130724441d5403c0862915540d03400035a250003035501801d440000c00c0040e55150344d40341030202c4900a9000701120134001c1c00d003e4400da615400403244640020384880c0883c2000d5201c129030f02e800104107503000c0d51103004103c1481420b12030f41816661080300040d040c132490040c0802c941003010f850520900e030800071004a2200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 265073057 1250 265071807 265071809
    0x203120601030b0907112104091109220908070303061502062404060b0d060302130504110f040f0e0607020f06150603040f0b0c09042d180b041103011410 67
    0x5402d051b094440c09002152511100c0390300d40c00300c508891003514200424400600849003280020301c20701c856403515916503c120303240c3c2d80c2d0291801681c0340414035030204800200c40050310014a104664403050b40a5100920880000350b42e802c0500101e0b42d14250341100038187c0c401020f09150811440c0c140c8450f0080712561100421002025940e0755040030b009007124415040c0c0700c20004208002501c4903000892045041084030703400718410340300d614031894012500b100d0030306c0200c003880f507609e5030481140d4000380c5440c24132000b0480d034011780801d41c2420b4014603c41c03034601c030000e0420840b1140100c82d03400480a0100240b030400f103228056a04861040d640d48035031400c07034040c13810800018181c490140400040007230050152100306020340f01400410101c4072400c4203c8481c40c4136401c1c42000c81c0c46501000702d50b500c465000391000814201c00c1a4503190701a403160215011030f4002079113404c3d4039403802c00303000300f060ba0703416440101e0003403c018030b9110b035560381 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 265074307 1250 265073057 265073071
    0xb090a0c0206372a021009030302070218010602010501080309010c0b060616080301050a060905030d03090311010e0a0528030804050313140102070515250209070203120601030b09 78
    0x903030040c00d0910421061004910900000351100201e0200d01c0d400680864000091600c1c40781260107010b0b0751381805040d0300c580c0d40d406015200841040d240003003155aa058042550030300401c0300580310200d800d0040713007201000c044590b1510303a00a00b91201600400c030f86030400c0c401c1d4038480e60007058100109501035910b500ba5035601d00070500601071014000e80000141c0000c03428040c01000660595100303450300701c0520788404060710f40c021144100d40d0141d0283c01c2d450400e9119600102d0054483c2c60203662108e1003490300c07425078100d003005103011f8104981190800004010904200794881040c10800b40c0000d248001e0048614016091100180018082103414030442d03c0700000403002250f15510340c03204440201c3c0499840b4058803802002241c03038604070300380b070302040380618400b0f1800c40391101e5660000c103022440003004440b54401c0d00103944151030703144240e0281c0d0045450342c83c0080d0820220300c002d02018145450041e6004c01500c0c1c11400560100e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 265075557 1250 265074307 265074331
    0x7060b060f07020f040b150403210906030f060504020a050c0106050a0e070507080c03190e090405030316030e0d020d120903080a05060f031b010212040e040f0c030b0a0b090a0c0206 79
    0x910300300400d0291610186c01640000b031440c0c54860b450f4803c0280094901030008070307011401e400e002c2290b6080b0b0044d000c02203621520100000c41c4250020000c2d511040c0700411f4250303413280410141d0b0850350510380803078804210382051490920030301c001440220f500503c1c080c50203807910101280034000303008011000800006101080040b21242c2101004595031000820710544d0650160400c03003000a4055419804a29000d000c103405150018007644c40e50329864805410440752900301014141c944859469482052000c541c6c151080c0e0068000c58088180040c6008581c2c85092201464010308001095002c0203840c0c1c04000c0c0c11001510b603c5080000d00703400305202400b82c1c5403080110703a00c08019207050380b03440c0712001e03000c550590b101510718922a000b035028400d22290000c00003804201d051484010403405401c0e1203000325120340701c1941010040b1402400c003919542d9102d4903007002408540d01c1078a0711001c10801d10f0f1600001c0d1a04400790910003008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 265076807 1250 265075557 265075579
    0x114040509071e050103050a02030f0f1e010803090a060c03050f0f1204050a140a031b02120f060402030c0904030507060f0e010905060604050a05130305032203030207060b060f0702 79
    0x280302004608003901c0522400400741681c4110741c000c0300c00500131075000a00305404110180d0a90080d0381c0180c414844100c00c0340c0d9040c12504400308000c210910b80d0030f82089445890548036942da01030702101018590703588044042c80301124040d4042001c0050034450800401d5100301541d07944100e02c10009d40e074956000200001d801000c0241052001000134402040300000390358014601c9044c45600c10821f14550340d84800218801401003114010185190803d003640031403001d100074141401c4048205040341340c4500740185180560201c4188000e5140410500c41840b808039040001c61400f650300a05500540e0740061960f9100c007080074811010fa0824000d26031001c00810040c00c0e5410607542c0d428040d20880e02032458080030a804c0394103400b60601c41c0d15598080c1c0b110760656034040301c85900007410b19100c82d2002020030307000103d40389210340b00f90280d034026817220440c0c1030000840390400c1c0e490384942010094522800100803d5030711030364040b00c9984020b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 265078057 1250 265076807 265076821
    0xe0307120513091b0801090e03040b030a180b01080c030307030f0c060618090b0a02160b0a0b0312040e0f0f0c070f050105010f030c090b09060f0d0f080d0b03010501140405 75
    0x50800c2e500b1140e04030303003401c4100c03d0222400c0211480c00629503207211300ca076602d141000031218403080081c0c1e9600100800e00c00d2200c00340040d40c003d5480400018910341103230188d0342401c841002219640d0014004003c440c2c800c010180ca0080210f0280d8600103449d9409031000355080310800c140b1041e19640014400568011b034010045030940e00c0700588001e03810802410200402c40300d0960000c045400181d103442a02e20341142c80144900d00401522140503c600c000c201d00401e40d140e80040c07a4a49040c1300da20010144002d20782e480e1420310780c0d1083e050300010480d10781c140f95541008007000e40b4102a41c0c10614461016686240504000c03007003005020b40a0502d6081100004891103030905035000c40e401448440c10311900d40c000f403c02d8510140341154045000b5001c82c0481c540b20788102d0a100d0000c0485031459066550b801d1481d082e090192001c80010a0072080240360b4050412040000c8008200350340c1000c82c0b0484442c00c0c505003034061780d0703114002008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 265079307 1250 265078057 265078087
    0x18042c011103271002030a1104030506151f120b0d0201090b1605070f05030f06011505030a020d051504150f03080a171008011401030b04020f0103021b0303010302040e03071205 77
    0x41041d02c8043d42d004020511241005c1e62060300c82e50f020a05c0c001211f105012804161000d8039884005400e15449405040c0c00c0410b00d03a1015034805080c03003400d840f0f50030f082442800100c85448a80d0034920b01e200a40803108090b200900031080d130350300340c2e005030784c0200d010040d503520510858031442011014011362044410042c142d210310036000c10307460000c250010440710700310201c40300c2c1c0d40651004c0f619002c0a12410350700081840306420b01070300800c040c640c4184540801810320dd840d5100c0c0701030340c00c15036584509030001d80205085040c0b500510450100700860a010b60346041008106616244001b821009000c03e5513001c6a200d0300319401401e082c7c06c101f6459061400348040c210005205403201903290480103c0300c1074030030307455034104d036002034003161207a581e5000c5c08000c0c01711a110904243c1c0c200450400041100600c20740d1000c1c034001107480e0760442c410300c000c6440e56031019003150300c284107031400683c1c805550205040705260090f11100300d448a418 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 265080557 1250 265079307 265079371
    0x80319020d0e0105060910030302030a0804020d0b0a0f0e06010602070b0d06030606030302060f01090b0604060e180106090512281407061e0801050109060518042c011103 74
    0x641042442d03a5011415040385004610444106032070786c036035024042512010f8072000307015030010b10407500c0060140440c50362041c0042e19581545160b81d41c0d12080d04c0040b2603040300f10340e680102c541e850700c01303102d01810501c0040007007031694103007030000c0e503210010300c03640c16490400243d0b2a444001500a10011a030102041c031280ba12132070080e40300c0f001120b400040250450000803103200c0360042c0e51421070040c1c051460b050401204881c60452100f445420107444682a980c42c0c007400030842c024036540e620003d2a50420003002001c503100d090300070f05580498a01d00420404411014122108141c620703600003051515520280b82e580c9170110300c2c003403400002081e90f001400d180072242a4031411429840101e4240c0d0a60402e004941c0087d0180205202c51401200206240501000212010981e1b4000602924041030480b095280745c1e01d000700300c82c000c440d10948070b910018024004070060704a400528040140301401c24003c841490300300303015510400e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 265081807 1250 265080557 265080577
    0xb0d0501021204020306151005070f0506090c030c0402030f131b1e080609070303050c0c04060902041a040308090d030509041b0906020d0c061d0d0201090309050d08031902 75
    0x16403584600c0498031000310003264180e0007401b42000040c2d140c100500d803410390400040469030000c404500c110b4031900405011660341816080000218104016091107210b440008201841d6140b05050401001314180d502443c018400e1000050848003440d41c4080300c400321440e0b44459081c11030b8841801246048501c20004d008510240b2020080b40c088001404050105582d0906030350b0f00c100450700801140c20460f01800000c0c0309000070501400401c0c00c49411030021b8000800b01d501c140d00c090300e03542e80042c081005400b082c0c1900d54107003e00d4030342c038181850f40c0c0f0b81568a102720300c040e034403034030480d0104000c050160083c0d13541040050010402420080e80d410103030306c400780d90a008503503455400540944001240001030706980e54607200180729030f036003201600c15842e40c0e0001c0f240280900030140b200300304140d55002d1683c000b181da40c480c1d0401512900054103c54007620416020001041c480801c0360341124001d003800598510000d44140240a648414 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 265083057 1250 265081807 265081811
    0x10212090c04051006050711030f150603070608060108011a0d02030406020903070503031c180503070c1a190e0f041b090b0304020102060103020114040f0b0316031e0b0d0501 76
    0x1012540d2000981e10224140c2a5010042030b2034940a069071850346204440001d0410044c41c0c0024261090030f01c04008040c040300e04010300d010001d410542c0b43d100d207503280c4852804001706031900b00000402010f030360903c05154103009000074602c0324140100c51400c0c281d4800451031609100440e4031201c00407000f1500d0341424940b0300007a43c0054240c0d4400d1192003070115180c50f0200031a1080c41c3c0150040c41c1102c140b00503031000d0a140c0790407007112070b44031100c8008644140018000b9611802c1a400802d043c2845801001015851201599402d10400051008021050b810886582072070b0102c1c802c010000341d891105040495005400c00d2903201408200200c03a001100003a107500c50269100c0d801040640002c0307a000c0e00680c0f041d4010400355000d00c2148c3c8050314203202c07151400340c80344d2410083d440150311859010030004100111001c0701881e010407003046140500c032840c4002084e4181c44000000b43c400145d84509040341580d0b100020304440b41d015000f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 265084307 1250 265083057 265083061
    0xd0305071209031104050f06010e040e1002030f07020106080d080c192610090b13180611070201021002090301060f08030306010917100b151204110a030312050702010212 74
    0x4000e19058402200c641c500d00c01e500303e0505c1c0c1030003071502c2500c1c1c05c1d142d100c2d50340e42d02c801140c0d20455402a517030060340c0c0d01c01c49510444240500071041c0d03002000541e4a04000321001007440c001840281164942841407029100104a003102118145080780c6151105074000d0040d1180603408946591082448100c0c0c079088240c040f10040d202c402541c80101c8440314403e104021100c1810402d60803806001d100880d60029904240142100b48070303d0f062568441150300703a99440e03d00c1541c00030144d00b00490381c020050010111503203d42001e20a60020350f603040c0c0110102001c43d0041068081500c0c01d51000c2c0050031140401c5202c1540d071410b82d80c490b84151002070005549140202c0c4d01c102c8054a013088603011401000c1800b2080803000042140302c41c031641c04034101c905c40c2603045440c8003030522610071710b251800a0406280145005880c01c2501d8000d0703c40b40300c02c20109410807107610700807a00c4000801c007540c41e010f04070300a10544034070386656035182003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 265085557 1250 265084307 265084343
    0x5091303020106060e1c1e03050415030b031b1203040603020408060702070b04290408010c0305070e0109120c0806040804080d0918091103060109090203010b1e0d030507 74
    0x16402105010390000c10146443d85000c90380c0814065a554010070000102c50340d004464024041a502540301000040d090201540c12179094290980003e0004a01401101514020104500c0f058101044481446408a0b0700c0d812003941d0044030258820024000da22918031400b024100760090b681c0c1d541d1039110280094016000760001381c4981030000d05045c0c00000c2c55070030b82c0d09603198141010315004503d10307204c4401100c0740c294114505441c032543c00b4040640b0240c1201400402c40d0841c0100088c1101c0b4014400c1d41000440280048c0b543d0b00304851405807420070b052800c403c005810300700b003840025808600c0714031a075402c11051003800e001920070748902d01c040e54070010410350222142c48003801044500821100701c000c40110700d50180c400507104551800b040f10f15000001c1c00c2c59402d0b407180c4440c646031000c0030114502840b9070941c40c40c0440d8aaa040020851091144080c3da03480d5409540001114014180114140c90f034007079212100804203001c1e22 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 265086807 1250 265085557 265085581
    0x8060d0606030c0605120f0105310c09170d0519090b030405160e100b1b01060305060901061212050f07060c020a14151609080105010308130503030f0a0c0c0509 70
    0x2c200040700076a2070000c00ca007000c7c5088154101c44005102c0b104629442083c4822300078415241c0890580300b15620501c95283d00410100c10440d4440b192010300e003203001c03041d000001581507100c2d00101d90200055400005176a864100320041c03a50002401001b5034100900350031080c2d60300c3c0040104820840000741641003440b8411030541201e41d2030380f00c41d000c0401901c407054400c1c007222041c8108030104014001030725500d4101c60b00046803909103807c4820b250425a5203070000001c01203180c5090280c40c00611002141c00c5140d240364444441e00314591480300c040110000f0f2203e20696048240c82019410071410000c15401240c042d56a040780d500c11540c20401c2100c080030304d840400c00f6142440314140005556480c81d19268412a60450701c44c24070141c0840810301c100c091207046e000e90301c510181d81e0380391401310f0040c0c019211640080e101e54403c06c080c426a041503001d4410640040c24001c101d54118a40076850f51640d4116642000d07207001000008500a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 265088057 1250 265086807 265086817
    0x70c05040b010206090c010e01031e0501030b10030309140d020a0e04060524010c1b08011a03030a121a06030403020a06051501020a03050f07120203031504050708060d0606030c0605 79
    0x44604200041c0100016601c03004200c450100c02c0e080084030502031750103908000401070051400041488050005c2003c1c04803020311116034035620001401007120403085d09400c031002d4082c40340003600d0340c1c0e40101954103a010344406410a0007c07a010780c0c03510240310410503801414840703141e48481c004816454211016600d07142010007003240c40540726a070f0f5450308449240d003052041c4440055894541d800300c200c655150701d64008402082841071800039044500c004103804400a89020500740c0c40c03000070388242c0003005840c000d83d4001d504240130700100d000129078030055072984641c80001e42030203500310600000700020154081600000c40c0d200320802c122540b904410181a45100c0e080107002d0f0707000b00031042c0800e001d034000d810108038012820780b80c141c05544202850140c0b600d0180907074004018029806906070112486c003509030b40800c5203240c200c800800700b24018220902a40d4074800d0364080c40656040340c0051a044050840482d80c0c60000600b40c0e804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 265089307 1250 265088057 265088059
    0x30c06050a1a0424080a1b0608012102030f011515020d1d04090309090c030b060901030f02070203070f05090f0c030703180b0f100e04080711190f030201080702010e070b0904060902070c05 82
    0x524200e4507031f01000b503c26181525060b64400d15243e0034503186a9044042072a5460700d44101809203006130f40820040d15117502400002c202d8581a801c030000c00103031504851100300d180021000002d50001e25074003501c0807880d020b41407404484240b034800c021030600540040c00c003403086041c107410840020459081100400991103409021000c503108003800396408a030070044060a0741c460380040d60002c100c0f1600601d050403903800203103888003960000148800c00b59041041d440c01080b0701b54040e0080125078043c1c075002d022110144001003d803001d02d50344220152003440301c0705d07054001603485642a4524280003400704180d00c01290780c0ca460001e025004a0140d0381c2e45034060085a001e0030140c1040e41d180c1c0c0b030610f5801d980d400240c0011400c00514110780f1004400002050000540c502907400c5000040800c20018074400c151380c10001203000c1c40c280040d020f0102c4020200140d1288000400503000d4500c0e5400010a940003081398400e000015410300e0840d04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 265090557 1250 265089307 265089323
    0x31d030720010c050a080c03040b1804051e0403031a040915061403060606070618260313021003021b0309030c1002070e0c0412030c06050a1a0424080a 66
    0x81d480c8011070390308020031001805900322200d17880004017254090090740c1c400500b601d041c261561890703402a00036060398038a0900181c20b004140c01c26109042d0013079802192200880d0390068581026000a040103040581d00d10440c3c4900580900600b51588014400c1c8080e0b0040d0510007048107140d081150714038649100041c41c500d1801110030f464002601910b61603071840b04100468200580945030152520801c54028445480d800501e40c403545221140c0b40c80700003500c00b80381b5074008030f410500040090003401e40e2140031085031117904450b00032b26030801c00001c502078051403000d080d40d0014020803981c0124003001406400c0820f8003110307545d0130751904001c50302007180c03049809a00506010b002c003101900410342d0040080c40300d10b00d4566502c00007c54811030000950000392018126001c2240a008040d0801c442032410b00031030091030070010b050281c0031030152040380d90340d200e03059081821310900840000c8082c1650b00c2559200d001d2f072920f08050302206c1c116 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 265091807 1250 265090557 265090613
    0xe0901020708120402122a12070605030a11040e13051005090a030e04020a1e35060a0807140a080f060402030616080a020c03070f081c0615031d0307 65
    0x6d4005031303108411a544081c0c00d981d0750404070b07614040b0401041c158002200d2902d050b881e003420814030000700f41950f40c0d565249050240f02044401403500355400304801c000400c507032856100d14540100350600050754500b203c0c58a6072600461031030308a44282460b040010440c004540c602070107001e80c641262228000003013100b03d200701c071401c90216481000c1f81c6500126006000180070283c10420340120300c1a030300344135050030490f504104590f400c251032100201d464420b9044141580e0601885d0306210301c1544885050050040180401c141da00c070341d513549e0468000038000e41017a5001841410106500d80004481c264000d00c200b2020035021000d0b011064003143c460b076942d940e203803281160800690f0000d1850501444144044001300382e050300d0700b2100d103104000d00b681d5520028950100c1c1c040b802480034820b46000c20030010038603500743d0394802511034030b40098a03110760b00c0c0070f86900395690303400f0340b2506c00403070500108140c995100045040241981d1644 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 265093057 1250 265091807 265091839
    0x5040e0606090f07050c070f05010306050f030d030c0311040824042103020d0c020a0c06020c03060a090206040312020c010801050405091903031b020106090c05130e0901020708120402 80
    0x421081d2003164201d03541500003885880310180c8140c0000d01c034076041c0d25014140070302500c0c201854024809040804200704060347c0c05105c2c6a001f04000d40f4101c610300450750002c0e81316000c2e18101000c0c180c4801c05100038600c681e024000c11075495100c191203030303111850540c2c1c7d00d20002c543d080034800715010006420103082071512440c0d004004d15002d8072040008066400c0303070110f02051540074020b0300802c5546008052181009500520b04001c241c00c202144500942c40002950024040424991008164103070b0100700200302082070507d62020a17050322a59102928100000c41030040550740490314070131110090740d80300481c0c1d03240c404000440b107082c0c0707095032681d0002c000480c15010042c1d0380e000c024020b04002071006201008030032001124903404d00140d40d100d205002807602885074101030b030940e00c2c10300e0500011060040e400320f507074001c03698405001000528403480940442c1c184550120000361508210130f8070360081d0703509540891240b00d15541d0441d134 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 265094307 1250 265093057 265093063
    0x1306030c0311040f02160b07112a040606050706051014011b201201020c070b0c100f02070203060906060105090d06180c15050403051f090f0c05040e 65
    0x55903040340c018031000d803030342d502d0501c50030800501e00c3d005a181d075180c8180500031320180c6150b80c807a18400301040740c280340c01038201400070b08803002d1200d803800484840d40002442c15409114131219141316441c1e02010841041e0080c11a0b030040c2032000204100368400c0250071034600c0341c071040c802515121201c402e10001406206072a500402c120301c07144d031040d81c52541103800d0103007400718020143c40705240740602204903030392492a0303410707170b0258107082d501c4030500703003000000314100030344a901580c0b591960b12506280203004900c0d504003800500005c03607a40e2913070004002d0700b8089001035029400c41141a4803074002e4100044903103001080542c031a120586d58945000b8600c820000c0c1040e044000755103540d9195940803000d4022801d104209010310345401c03540d45400349204100d02035040031810408248010000500006403000081c01a10503d5148160b002ca01c00c00070003c0000103848088a03401110030b1050400c0c509061b0342c0140c5044c8410602455120341d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 265095557 1250 265094307 265094309
    0xf03020f1207051507170a020415091a1c0e0105100509060d0201050c150405060919320313080606100804021c21021501030201080f0606090a080307021306 68
    0x803c50300142d4034191010107a0704050307401300082c280701031111195041c400103614200c8216a4540e8001000d2140d5a040131044983c0c0f010742c0f80c640d076031504055080d0b20380004016074010a54021910ae188032140b034944040c89880100c0410441e00a401c0a43c00b0380350a840f9072000741c06100000c1703030600348160700c14855a001b400190100e5207135401141c01d030b48a03200f003072a20b01401180e0f0025542e42600d244c0124004da000700500e06180000f1030130800c030990f0824a40c031060003000005415200c1d4056403402c0902075800050070303003500c00b20740c10540340d0100d0640000110a8141c6c00980c00400a0b9800d80302211341c5665100d0500c1350340740d82c0c4000d02003c0b622482c0090b005103411100e0000550001807518003003031459440c955107c1894201100071165926400a21356040004201d48441088102099450350700060180b01001c1c0c01d200840080c0301c001545900da910440d04c0c5800c0150507501108d540c0c08003241c60790000c00c0d00703e201d0b0b214004c081d6100c42c66801018 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 265096807 1250 265095557 265095563
    0x8030a05072d181208030a140603190305071406160f051c06150504031704061b02010e030303090106030b0a1b0f090302130902010e0306070f18030f03020f1207 70
    0x3002d6071107040c415030b814074850030007059a00c941c40020882a045841444e0030a00c2406040d40f68141001c40c8829a01c2d01c01004034000c00000400040c0d90340018403003881548100c404103520f130351742411200c501c110280a408440281d5090700c18400028107284114400100140300d007590301d4044860b01011240040000e409028201c82c40703030001941c0960b524001d1300010707101c2c0c0c0c81c049030003a40c07844298100450740118080050004103050840e913650380702e03d25485c0508040e009071141409104060000700e4610b40c200440e4050303a500b0301c25180040440307840340b902d106654040e044e40d0100720b03074004200700491030704c071420700070a9400001c1ba4164581c02484003c111244402c901800c010041103020020140e03c0720084140c9200c0941008585508540000b40040000705501802540301804110f0460740c0a10400008510381c5046804031002500d0681c06039681e810107021500810f06000402d60005604441c1000d01c03400c3d40c40300e07070000721079a445005500d005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 265098057 1250 265096807 265096877
    0x40e0706050d061703041e030201020318120a140705031f230114040b010c020a031e060212071421060409050a03030c0206060a0f0306050a0908030a0507 67
    0x52080e1800740c009000c611103a5000014481d0380e820001c044a82c0f002c00c82200c2d030b00006070500601c1f07444003090402d25203807800742011614690000b5664802d600031070b2400000b001100b5055038507810601002190f801c12a16120440d040007000d00010010461642c0f0649900088500340458104000d42201c030301101c000c02102d5441010b00300a0454506e400f1141951440980c402100640a000c608000102074669141440700300c500c6102500d0600544140302130041c0d444d042e10302c1c1500d510046400540720000051101c102c03091000609071800441d6125520052201d002d01c10071499582030891107012031985007a21460050301514055010211859100405c1640c0c000c400504001415000d5031203007420700b022602c080b000252240d0107a400366a04000040c1c0200341104c0c800211031078000e1940c81d1002c0e84c8002080b00e500c03100066203000c2c03d039001e6031500e074006081540c0c0c0d10348220004002d1000300e8840012840003242c0d9030081d0742c1405510755822100c820 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 265099307 1250 265098057 265098059
    0x708030d05040227060102070e13061d0a03080f15011e020c0a030305030a0e0601050a05040b060f031303020f031207030b1315060201050c0a0c080f130b18040e07 71
    0x21000603160041c41031360015204082c100010007401400c0f21856081141e090f0941001e00009082c421140d209c282d61003608814060203101600d1101e9003180c0c80000010110a4600850300118a80950140a010b41000c00041c16007160550b0300c1082a800d81319015514100b0200100c190b40c84070a00140c20040b4800d030204101c04c81c40b030b24212a00440d0b02520f14031300040d2a807580703070300300300d0002d00080240321000c1a11b010302d0000207015001340c00c3e6517041801080d003804451041d03604c0b0700d468000b0318030681c540804840716440c039514100d68030b18050504880794050028120010310511050105036400030065a1203803000c440f000c2c0198980010031006080c403100c5950b4065140d15680b112682103118540784c80250300c1407070000c0340c40c01402908480b40100351780301c42401000003403111903201034510541f41d8407126079921036404000200c03207405015003082d1040c0004001040310510705024003000a07082200c802103042c1401071009444015514401070f1b840004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 265100557 1250 265099307 265099327
    0x1009050309150d020d0207030e03010b01141804020c1c0302030c031305010f141602030903030417120a0305010e130b041104140f011e031104090206121006030608070803 74
    0x14501c8406603109201410141e4003410a001c0784e200b4141703241c90035400141c260805402106403c5800c4040b402000b00c4180400003074088608000f201d9842c100000e0789402c400e60100070503480000c060000c645a030359000445d507482c0403003000402d070710740c1a0080409582c030074000c4030301c12280561000c0c1142c03034200210b0582c0c18212001c031019500e07440907004210052007000c0307000c000d40c2c2040707c1d14140b8506013006880c01d105a0170442d00204900b10003510000212001c4035000c00310410340c40c541c0c1c05a1411b040b6a030301070002004001810214169064112074141c882c5041000c4450f00e480030324000020410300014078542040000401107201c0c03115600030907801078004554030500e03a4041c800440100c40018102c922072006002031034914480329801d0b100100d288240504585480074241028030305d00e0710a5855041c0c210845d101c1e5402d99004401d40c60102c0c160342425001e40c59a03c0782809200b002a24061000900c5000080c0d00c00c00c41d81e207500170b5481d00d10301b90 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 265101807 1250 265100557 265100569
    0x8031008070f030602070249021c0203011508030307120207150c02100603050a0b0609060310110d230709060c02040b152b02070308181e030a021009050309 68
    0x1e0301030703a0108c2d20000110318003414610400348106000344601c40c890010300300d003c4a1100101600d80504110000001030721020300c52034241e05500d6980c0144901803000030f025080040e03511240306403400002410302800005180600129150051848a01c4041c18224001d02c00d01074141c295207080301406001c558008504070500b0710544103840d140044800684e845a4400c03225a80080c0601d07007030003011244680c201c242150f198484e400c0c584000b0f5a04c604000301c1103001d0b0303030396038286c1000340e5080121400c61701c41070000e1004036520317102c41c1484c0c506912800d051210500002c0c54240c07041c400350f000d640b850385800c940c459258003400020b040b51090744c1c1d0032000b1b1148010203031f03a02e84080e00d107000954900032040e411281ca188103103105503121003030b058018002080000d800075900c69218510400000c50103551410613882c1200c4100f00b020300720900c10b01d5803030310035000c40113005031001502114110081114000c2c125840c03804040d065070018010100c4900d851 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 265103057 1250 265101807 265101817
    0x4050609070807030e0106080c01030b06040b07080a0908150a0b01020c030d0f05040f0308031906050a03170d0c0e1c120309021809030403020f060306130c0504030f08031008070f030602 81
    0x4c3c500014502c1540d189a42161a0740e0092192588007031400085c40d0390600a00c4902c0f4000c2e030341241403c0c545038100b001c2d4013400e40020880c160102d000303c3c14600c00c491440062a0341c00c1119a910482000440611016101d1b200350500f000394581995000040810940b00083c000700303450071500d2011510801e40700841c90400070104000a0039400c9580210044c501800e2100c3c0c0e01c1c104002d0802c1999240ba00055203a41040010042c030b5803402041d5048a03000600c045400c8148140c1503064800c000803247c03501d1400c0c1080291543c400300100c81002c0c00e03a180d00c2c140c40c00c41743c0325203200d0032800000e00e0103c1c0c0c0400c80062074425002800c80b2440074200341d504456001603950098001c885c0320080b5400800c00700300f540b405a1203030a5401080d5121031071800d001001c624500a810303240d03001d06440b040c1030080c05102c0c004131401141c0004e01d501c44e02c801450000c0081d4016142c84082c150301042c04180514040b40d0101265210321102920b1469940c070100070b9040303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 265104307 1250 265103057 265103071
    0x41d0601140406122f060301300f1b0b03040b0109060b091f0c0203060103030806030d03020702090a090c0503070308030114120a0311070b03011502160b070b09070819050705040506090708 82
    0x64070a1021130303919070380d01071f601802280e2410031800440c06500e05c1003034035501c56030701c02e503007240e20750130108400c005080201500a408248140c0c500030803c4404403195019254401c40001004280035054440718140c4070342040600a0560f0790a035803205c0d00404c00941da01036400103d003045003404840303400303c2245509190040064940000b410501c0907442540451a00d80800903a4913080c08052020822070508500f8158540c0218a00fa00010522811155640d1410050000584c2c1c1000200001000c0300c04660301c0e0303d0300b80c946420a2144c110503100c4003004010707074070741503104030b00700c02da000010002c0c41c203507480c220f42611041548003902e010307120001c20000711281c000c4d4040c028424a07202c0c2d00c48408402443e0100d4a403110782e0001540e4420300590f114241101c4400350001c10f007049586400728881c0c2400196440f01d2040d200380c503904440c10310f00b0011040300900400907900304607540d0381400203540080b07922551003030030000026480e034001c0b00c002e500504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 265105557 1250 265104307 265104383
    0x9050906131d07120b150127031b1202011409190305101e0e0f010608060105011808070303080406140f01051011030702041d060114040612 61
    0x4500c1c81c15100300d410044a842c0b14204034001018800c404220060041c44400001148844203031642c550404028100b003e400c000d501007036001c0e0f8841d501803031340490100c4900c044025241295000110f09100c1200c050411032080b601141e4200c1ca143e04891034144014140045a801103030765141072a280c501c081c8040c4156007541d280c00360320000207500624003044040c21070074201e1070704129030a4582002d00704180010b6000304440c0d024100380c0400b802003003c03c038440046051a0345c00060a079950320b4800001071820340003401504a5600782c85800280c0c007020f903112140c003090302405210394071408041000901c600c0031154001e014400000701342c0d409a82e80d1078241c1d8140d41d641440300296006020601d401d861411104041d810711008007c0d44072281c60300c0b806140c001034030450750342c6141181d103a2601e0090010003040004d403140356071682741c2e401c1100412a40c85000e40d282c1140030500c9a610801140602d4120f500440c19039030301048801940310340c0300583d01c001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 265106807 1250 265105557 265105579
    0x203030d0218040f020c0d08061507060209090c040b0f0304031e08060906040b090402060a11031207030c0509062703030c06041406040312020a02011103090d030e070609050906 77
    0xd500e44003501042e02c0c030009690305001101c042206444281140c805128030401c140d0100507400160522601e00605044445ea61030700c0000b042440703d801c0200c15940001190402c002d0b0079401011102c00848040185885001d4805110b00550060a880d020104150400d40300070340050741d84140702e4500003416a000d6103940118141c240002c1d0040b6240005110040c60324548095012a090300c080205400c0d03580015003001002c0c2002e4064080000c48c519014456000026240c00b4541140d64034040800160032999046440000080ca04900c1850f1548598125030790440b00910080c148010880b801d42c131a4481c0c5420900c0e00380003d2190b4181d2002d002502e4040d0b0b41c2d4002d02401c0c607203130400900401c0a01c602d1109a0040402c000003c1d03003061440e015998a14801a25100c407103500b80d00501e0100400041050040208060007000050b08a81512950340034014900154501075031030ba5079020f65804618501c030140a1070030300720203260340031100504e1400384e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 265107913 1106 265106807 265106827
    0x51905130e0901090609120f03050403090b090f0405070203130e040c170c03150103060c09060e06090301140c030f011d060d0203011d03040f1e0e04020303 68
    0x80103070700102d0102e0300300b50300400c0f640360702440810000456082040e141c0310020b00c20800140007040c12086113100e80166806594151280904a800c01000012540203004c2007900202c102418100351fa03542e014160081415401460341c0d601030303d0394001c01d00ea4580042000c80050014480012196400d1004442c503142400aa807402c0381000342c204900202d609902d4840c645404051203038820000341240e105034000c0000c03c0515205503840c1c030340352107414040b03420460400c4244c1007040040000c194020000102032109207402d0000310030030350308159402800b00070400e08118054040c2c0c09015100415880720f40c100030100307190314006040714082c2c26141c0040085403400d400101c005c090712011070f00c2c10b04005203456078a411070710803510b510402c8480010700d0149950090143d43c02040700001d400c0c02c010399208002e0003d0b204a0701031008021180c95 = true := by decide +kernel

theorem cover : BRFrame.Cov 264928057 265107913 := by
  have h0 := BRFrame.cov_init 264928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 264928057 ≤ n) (h2 : n < 265107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
