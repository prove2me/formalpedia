-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0021
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:24:17.925575+00:00
-- url     : https://prove2.me/submissions/e7df96da-d2e4-404d-b9f0-697b864275e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 3597130 ≤ n < 3776986 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 3598380 1250 3597130 3597133
    0x30f010504050601080d0903030e09040606091b081008060a0b060403020a03030e01030609020307022104080a0b01170d021c02010b09010305010504030809010213060c0204020403020a0807090f02070201080708040201020703020909 100
    0x500c0f005d40c00300224030400d602480c00406175851501c028014a20f0171211600a240100008041c04401c0d000b500041107410010808821790520b01d09211500f00c03a604001510310b80426520a0750120083c2911150f602070005512403202c4d40006016201c5001d401200921001000d6915590040b00a50107610345502c2101c0d8a000101280d0030754000d8807400b803051052203070b041d03030000e13440204c514a100d050045440c1c44a2442050280f03921522903445191a43d0341041004401d140c12a0080e0303011030103a09070400000c0d151280a000000141d1021032002010076400411400c515002c0c000024407110040201d004914260419a10350791920144010590b1200100f40d00049072002142084029003400070b20030114418501008804128135003550b540b86d04071801584d00820a04000350b5441659460342c200d48101d1b0449894007a07800310301c82d0b09000311004544d05a4821600b0b070f54104041e54180b001400590451007005000300c0140c56031008180504030040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 3599630 1250 3598380 3598393
    0x203030109141b0d0905030406050403140601060f1805030604060c0806040b01050a0302070512030405070e0705040308030f09030c01050a0506100905030703060c0c0f03030501140f09070509030f01050405 89
    0x46801d02a20303060700082c0152082401001030400c40300804010504030071403d07540c1c41084500b1280540249900688240400100000c09a4001006108481c801e00468111003040c1c0030050322000248210808992030502141000b07225807441d0250107490140081820789840100340b9015007143c4c21a03240e07139035001d04010641c014550b82e901800c226014080112401d000030081d0103003d0b414814150040344040402005100c45c55180504071030042e00c1e4034040c2840742d076441030340c8205924003200801054003240315500b00c0301603a0b0456611407542d141c440d188a41244001c000d842c141c0428000c40c4c240d002c00780180d500814126001080c0e0b07041c400b00b00140ea21540d43c84100b0301920031401c002a0301c012949da0222904070400041801c05d01505680c544500b21005001081c3c001c1c03c08101a00f5900c02410303260380c0e0150400d0030a0b07000a2100c2c022504841d5507000d8a124009000c0b0751040c2c1c0140b4031543c01405441c040184d00e0111400e4410903102101e80380c0000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 3600880 1250 3599630 3599639
    0x10903030e03031005040e0102040504050c0403020a0f080303070c020604030501050a0603020301050a0605010c0b150603090718020705030714070b16060c02030310030b0402010e0603010e06010206150312091c0302030301 96
    0x5006038a1034040c2040036510f1810403107441d03129021103108050141d0780300e0000c0c101ca49400e50640300200001b5000340710903d042401c14006500030300041b0703c1002c9241022070b0345000b04445005549803200110704e142c440b45002e9901128107042240d000c0020400800021028043d007809110048000f103403c505620406013555402000300d88105d03c2d03c1010031540c1c2c0d103c1d15491903550411040b03545078444003c0400050002142035400c030700004203004102e4000504402143c4003801e04248101140c0038020691182c00c2c1c028045034024084100415480a110105500ac400848500341d594000102194004c20400c407600d100e00701310a070500489020300c082d94010392000d50b1840ca010301004241000900014220000c280300240c11a4003030318840c4000302c0020401e81d181d6a484c0c1505120f2081150614010701a41c00460b41c24062035040c0610410002c015040035134042d0301c228203981010f02002d0340204860252100b03421103120001806000303501440d580d6040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 3602130 1250 3600880 3600887
    0x15020c0102091e01020c0105030a0e010c050a030e07030201141b010e0c090108060105150a0905040207060603030e0d03050a031a04090305070b0c0705030904091505010806100801090804050103020f0d0c02010903 92
    0x12141045000b403e100d00c0c0d880d1a81c0c0410180c0703c1c9102400c00f030b61661200e820b941e000b04105030150150b5031030045c1810355190400c010705041107031545e0920500740c070000b0464540c1400d110080c0820310b007200a1550441840c0500082d4076008086900c0015144090782940c606001448450b04140b0440e8068101403403082d014000c401d00800c01549060003007516603058100c0030122070342c0854444800d5205100c00380050400400a54983c40d203424107000030316151100f00c2c045074681e2421400b80c180748034503100150f0140c40d1141021480107065000e005090780036801100c1c4295810020765403440380c0800c5500a581300f036119000392428100300b010260144071481021b10640000401c004216070f00b880303050b038000c81e1075081031809103500c80140308801202414000086039022000a40512a0644460580001340e44d10122822034081b01e50142071880100400e1110394002d40041961085000100d0b2400030780c0308211045070503140c07800e40180d450314903030002d00d4dd1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 3603380 1250 3602130 3602149
    0x801090608061003030e01050c010c1d0916030b01020a021504080606090903070201030b1305090a050c010509030307060b0d080c0102030a060605120a050a021608030603160501090b0715020c010209 86
    0x144000100201c1c20700f2440204001914440101003004800303003c09a80d102c4d038155402c01c10080000e02c00500d040380090136070309100035204103040408130350f00c946107031207a8424011006030b08512080d20310780710200c0160510220395411b512030030b54a400140c5448202040381403455000c2501e890410a08505094014001a1003240c4103070501c88420300104c2100e08859090a0020f8650354007004100e00503150810504203d203850104061503d021650200c154030070000d0316081480c0f04015251801256421501584288030b004000340442d440500d991a0050144070648a980c0d20030316198012800c090350781e5004414420080c0b5640185c01c090082428224200340407032402c1070030014001d00f00e036aa10703114804202c1c62a000d604603040e80c88042200403142d8038608026001303a00688005000341300300103010500c0380103a20323542d0548005a440c072052a142c05032107400b98100410680700c83e4030700700001d0822441071000308000307084080056107421288042055808 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 3604630 1250 3603380 3603389
    0x5061905010503060c0705010609020d0f0c030216170702040207050d030e070506070303020307030b060a0507020108010e010e040b04140601060c020f011e0302070512041202120307080406120b090708010906 90
    0x6080c44010701c21070b81c01150031a4050200c00d1040c2e2111101e04003d4003400c002e0303101c0c60a4503c0081c04202003100c0380c01460408074040001d0281c480c201000f18104e109280d8403001c1c1c0b15020a4460000310080c0300203030001d4841c1c0f035035030030181581c0005e001c030b0b40701d0001112140d20042d112488907805016031500002000090400e1615190224525200f8000300504059000000401d507601980c06031000c004040d00341521584089009002607111740c005a01291320440002211403807021114169165090440d440b62940d40d2202d100910160003141d844115800e0f02c90744000801a42e8002d04035a9030b6070705142024014040110412409581008402c54694201100700f03222140010752034540141c1c1c409207424581d00307068010300c1c45106002e0018000980001e0101e55602c0320340200c5d03481005440c02124079940344105440100281011300040080d03d0252484800026520f580491202d510000260503010700f04d54505c08586500018480200c0602c112006031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 3605880 1250 3604630 3604681
    0x5030d0305010501050703080402030a0c0602010f1401050303070204021c0f1506020f0c100909050f060301050108030c060a02130305010f060303030b010309030e0907020a050d080604150605070204050405030f04030506 95
    0xd5050400017003043c42403100c0039041c012000e0101d421514100710744030003170390011415010715490302e174001c0c040d08651042d0340e00d241c2403003d052003845a051143e070480302e009000714507280c0103500f4000030303401c0380100d02410012004e0441c1154000d00403e00600d8415800040488400c00c84034029151500114115840301d104032030502000640000301507011074041441c043c1102003141c0e1400c0c660003200c40c107810b040c00c1c04011f0351005406070040320224000d0000f680c942803020f540b8000c0301d2a0800c2940503c000c071316006102c0e4000e01000e100701c1c2c84801040d440f9201c1c82c1c00d503100e2030f00c841d0034180e4862003081030503803611440c80203410034030381440348000c0d91702c00070450140840f8140c4110f948102145001d03000300030507007256038440c094410b14120440042c1c014641190128040c0b401c1c04644000401c14003507540540d0100d403901c504000440c2c080c040217200044c0304940520042003505451403041020b000254030420041c00d80c2c3c6030584000c40c1c070805608150b043e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 3607130 1250 3605880 3605891
    0x30207080702040b03100f02040305060105010f0801060e0409021804020102100203010b040509180a0507030506060907050a0309030c0c0f060314040201020316050715050318070e01090c03060f060905030d03 90
    0x3600c41000c88488680441d0041a403040000000e13003040350000120200c14a80410001040d15a402600c1100d00070b0042e601e140e030380c6400556800d8481040440016101e40045c0301c480d0080340c0f81e03810001e002c1d20000e14250940e011401d00c55402000a0029952800f08421980d0405c034440d5040500d40055045500d88000041c86011f039010b403a00c01c1c040000000c41500d040c11042144030404400c80d2180c040d0f50600c161102c529000c180d81c10f005500014826080c4001414016801565110f15010588004800600d0041811001c0103090303500c1e04041f4900788070300b40140c258030100d500058a0b000d4080c0c203c039040c400321040c2145613001c0001607030f008170594450a480410f04c02c446040c40c0b80207420a0b816800040b2202064600404216440006103108104002e00c2210880c1c0606a0300e640f10301c40e10641c900c0640c5940140409180c582109420800707500b004120a0348958402c0c0c94800d075500243c001968003502003101b4541000441c0b084074041c1000c204 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 3608380 1250 3607130 3607133
    0x1061e0c02060a110c0d080301050901060806090412170702010614040603020303040504050c0f0d020306010807080f06010f031508030a02070b0307020604030507020f03030705010509060a1109040c0e06030106030606020d030207 99
    0x42c0f4015a00d400080c020102084074508030240001010340e0030040c107842d2600403038030308030030f00760002c0c01103a0142e015007002007046030040e00c007280103120007462007401d9503d90fa28a100d1468920124080008038051383c00404410003445000e000356030004170312541030808a941d0414034007901e900c0755081000c03c001580b4007104840c10b9450a59000c2800e503104007a8203080d110305004182a05030006151030020703825406903001d00800d0740d54920380e07290782d80100c64181058550820341ca8101c404a100766024101d4040d080c1418180410700c000454401800e110680d40440401d4100041e654041d55060104001034040780e041c032401c5080c103480003075590384c005100500b801800101407082d5600d8074150940b8120017000c0f030780e50fa0560b1406a000e008155943c5403d0b00c078103400b0886c108075900440360010880100c0351305210003401000054030501681c0320a00540000601d680d0700d400300114040d10954501140d114a8008024034140084580d42c040502c117100810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 3609630 1250 3608380 3608389
    0x3030603050f0c060403060e01180507030201020601050906030c010804020f06040e06030d03050f01090e011d01020d0501090608030f0d0609060303050703020601060f05030406020a0908060a060807091a09040609050601061e0c02 99
    0x1429640c1200c000035104001200300d0f40100b4000c0881d04a0000b02b0103108100f0000003400707000d4034400c2c3e00362a0390b80d990700305015100740c1c01d07614a581a0071503070080c24654032402500d9845400282180141f2030b4407004118180d0245e0410304600d2019003c201090408100301c91f80785000c0c0ca0100610310340f800542e1400308040c09810307502500e0350b03c1c58100c107009411842c03165600d184018a6400350090290003503220f03002003201c0606040c000640c2c0360482c4100c4c0100c55010740039604d080c1c001110600341d41d10044540b1700042e038840300883c2c260703511304c075031006503100c5d44480e955032489007400380c60030303030160701280810102c001428000c0d980082036030b4000358401405030311142c480905480b0b20b521074010010354400c10702089501c8401c3d41014085801600030f41d1140d81d110382e01c04083d1003201e40114000c8800d071880350010309010703298940c09401844006840d900e983c1e900d0341482130a0740b2100000381000c599800540c3c03c0780072101401c04600f0f11091a90844c1d0105d07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 3610880 1250 3609630 3609637
    0x50108060c03040b19020d05060f0301060503070506130b03070c02010206100f150c05010507020303060406080109200a08030406020c090106080f070809030c0703060e010b01050304080d0207020607020d03030603050f0c06 96
    0x34640d510380c1000c184460701c851901c07804a4a815011b40d240e00d00d01743d00c0f1008110480b00c1a1150744518442801d40c00d041c8504416070f800034019054181c100410702016502103291848803048100c40000c10409100107140904c913503070399600b40403005000085c907088020701800158421140d04005040345240c0d400b080792a98a0b188001039800c1c0703000e440b00104002d01400075401d0808025541e60f02000561003400111420001a074507810004e007211401800106100324101d4001e0711900e1002d90060314080c020114001c903606c4030401419900240c2c404405613000104110b401e203840314038a40581403d151107481c43c6002c1c0c86400080350080c0c0201c0900c1098000706084140070300403250040600c44c120346085544c1d00e0003100030304a002000b08903500c3c0a06024031984036000b20390007190080da400d0b04000c154941a0001e45c0002c500b02d134800c034100500c50040c2c945451b020003003800383d20b00042061850415138103101c0c0200d900e00c1c050300410030784219030b910001074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 3612130 1250 3610880 3610883
    0x3010f06080c070b040309030210031103180109020a08010213090515041104170a140105010e0411010c0b04030305040204060902090303070303020313140706030c09050d0b04022809050108060c0304 86
    0xc200d56071203600d5401818824802c0142c04501c1030f004010525401041003008c80f40709480b42c41010050003002c50803a24120980c072003c01007000401c60426021210b03642c1c0403131400000610081d5a03002944c01c94103541f010302c0594012489403003d00c1d160340f444005141c108420301651626060000b60380c0b449007000d40c03040740d4450b142e02d0404088800d48001e01001e9045001c03114030884d54954408100204031144102c00c0046211020f06001e101d0407641501540205c0c1c1c4c8656a520180e00702c200303001030410a82041ea9070110700c210240031300460203501d0000d0310703090600500080e01e9854002c8004c0a004102c00d00c0c0300e407000011106001c0c0c0602d401600c03a00c80850111150220500103040000c41c40310482401002065480849100380c9007044818440d01003520394132200c0c40f4a50303211464890340c001140002c025594051320080006a20b0034a0f01008544840d0040300c449080a07a90300a1121034030510815001d0098940181894075040c41c01600ba0b1200600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 3613380 1250 3612130 3612137
    0x101107080a050d0609020307030f110a08010302010807030e011514030c030606060c0703020a03050f1005010506030103060903110703030201020417030f0f090a030501020f0a03060608190506010507020301020708030103030306060503010f06 104
    0xf0250035002013980510301505410a066580382000100203010380040c00808413650318004851860010b110101c0d050840e00d911a0007040e803231900103480200c4c0041000c400e05407034440309183d11900380304074220814001e400e481300c141007120158410303035103881240c002e82c01081e41c04501c0e500050740607400312044400d0b0743d480410a020394100300450784025084002007a010003004001324403101c140d03041c1c6003241c1c40c3e000d001c5815030940c0d2080c42410b03004041040103201040d05034000c140203030300078202084a56000418207140c503113281d2083d8010b0751701240c107000840c503000c106041040b200e0025410705c0040240900188205e1541c1e05514800061603c026103882e55004029500034000f191102c205003071100d90303944828081c9000900c1c1003004140c55010703401d00740c0110381004848011580c41881e0704001c1102410141c140007040c0200001640c00f400100710b40c074882e0710095125451850040c00346c900a0700701c00148003040c401404513100103030300101110f10524 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 3614630 1250 3613380 3613387
    0x4020a08011e0308030a1a060a080106080a02160c0807090b01020705060901020c030a030504090501060f08040f0203010e030d150504020a050d0209010e060403050102070506090d020705010315080a0302101107080a05 94
    0x250348481c020103c0d03100400c8440c002c0700b04860f1040e036910120528050307502c0b1240508154042001901c2020701501c082091180107206c03461052440a50000e01d82e800185002000c00c001100788200d9041211130311240c02042c40b105000b40400002040b0700c00c010301c008210880040c1d1241d1a41c080c19001d904003080202c00c5d42e00c00c000304901c0301006400d035804000c041c1401803559006000d0b26040c203081c20000101e9900c20b644414108440f80e072514095111652103e0140f0b00d110300983c1d0540d01d40300c2a41c494001400106441d0510300400912007501e003519011451280e48520f1040d4414041003c000350054200c1c3d0a004288000590741d80c181d01c0140d4100000d4110980c00040c082404002c0004c15802495400d01880c210b0340941d455800040d40c61a0121028005070800f003010415540280c020344901c0e40501c2d81c0f00710043c0c5279442c462806080b42800e500681c8501c0c450308000b07000307100e04401c20b10201c0c213040c58403404d5160161588560a044002c005002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 3615880 1250 3614630 3614669
    0x60307050d0f08040e09010b0d0201050306040f0b041b020105061219030504080106030c14040501050a140f0402031303110f03041a160303060602010606050403050a030c02030a0b0403020d0e04020a0801 88
    0x100e1800140c030343c4018041e41321519250890000c000481d00e800c901d40c0b138022000d4035440c1c2000c5120a050381607451502e140c0d1a9014403001d042d084104c02c442a80341c032944500c0e40c0c2e99008040111020601c1c0c1201c00250920007829244081d20f5a401001600040541000046030340440b9401e07440c1040950384032440d0444240c819079205070115403900e030300803040000d00d8660000315104240740b06154490a010070049941c28030420780c0c0888030001c00c004071450b2042843d0001c80c014208040c1e10600c0c000b08090740e10840c0c8500c1c0d44114641000c041507040300b02d803211150700074000c00c00a03003020840ca940380f03c0c0d809504c3c80c0d000416842808546800100c903030407400d581c1c02c40182c61491030050060581c50080b10059404c1c00c0020445511800544040740d4220008020780406601d003a84c04030549101a43c2500031581140041034400307500500640c0311750300400c010110314000903e20301c10214014031890042140a4203030794805801410f6844015122042e103501c0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 3617130 1250 3615880 3615893
    0x201051201030b010302100e01020c0f030a0606030f05010501081c05030a090f060606020613050c0603060f060705030c0106050108040206031803130e0117120a05031003020a0803070201030c0503060307050d 90
    0x40c45a0000c85100980000c0204001c082c1494100d0b8400d0301c070a041440c20f00c0060b941444002ca04500503482150102c0c0d180c03410340840c0251070000790503110500110344411042d40d0640e001038031800d8030780f424202006030900c1600e0040c140d080107008198415059030741d00000350100030080003404808110b0420300d43c2d1220840a900038035003010400e09140400140c0658800c820140c01071000084100c1e0700031003400071580d4400301400c888000030703007000501d400140c142070b00500c1c0d22040f17400360b4071203000611801e4001c10055450f8a5809041802d44000b50443c40c1005060001c6c000162a0a01038030b4005050648000c03418421030a0a880c2d1301481e0301c1d131800c0555504002a400c4d400365440c42c1a40c20010760450f5503001c20011903a51021006401700c0d802c0c04101354038240384114055600110005030710701c2500d960b6000103c0784c181980002c1003e4000003880411581c140c860810201c030380381007107400c2d0314004001a4881b0340138403030b03103025075206c0b9482c9080021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 3618380 1250 3617130 3617137
    0x3070b06030319020a03030e01060506040308030a020c030703120c030b01090b07020102100c0c020a0b070f080c030f0706050601020c0901050306010501050904020c0f01050601020f0111031306020903010608010506011715010c020105 101
    0x11943d114145034114440203646901502c800d070702003803030f201500c409260180500e9007071740d40c007a0240385001c0c03550703403002c626500003000100c0d519801e00203061000010300c000c1541c140640e6955109118801d0120119071040000c1070a144c80c0059403034203139801c081c81008a8034020754454443c80103000603402c0900410100c400940303042611810182c000454941c5a8002d0314642e55940d219040494140f251003009841200401074210014440c1030092102c0c00040c0181c03400c01840044008040d00003243c00c0f03400988440811805580c10080350024040448858a07a945014003080c2c503207506010380750410000281102032074070f0301c0c0c04070345400020300d0840f40003c9219107100e008160aa42ea07900601031100aa14460414010201044070a2070030300d1540e1601007a03407020f0120184105c1c0d0064003440241001d50382845001c00a12010001007410b00c0c00d44001428a8031560001036520026018460480d402c056818400075082c00d000c054405e082c00144e80500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 3619630 1250 3618380 3618397
    0xa020a020a0303050c010b090c030c0304020d0b07021b060a090e091204080c040e0307051b0109030b0f010f050303130909030903051002071106090d0b180f030c070501090803070b060303 81
    0x1420041c0010805034018020a9442540350007005518481e02c10452000d2050350b007000c88410910204042a4000d40115005440100418040065503a030110415000c40e01c160168000030816a1004668005501d1202d801c603038075458400c008901030b05003030403805400070340041000020034001c0c08010302201d000303003601c1e0151a985e8a190403a5240c024007562401142030050310300281d0800015120750700d07809030240141c0343d501c4082601b2107042ca04510304000c41800004045038800c00d01c035000c1c0c00420b0071800715604220390f0305843c207450340c000c1d4000e5000300b0a0044075240a1494401c0e20b981c200c0c081102032190600b1501d908564001419078092200d440b5510282640105800c80c0b113070b40c41180070300200c42008968082d80c1c5086410036200380a14002600e8082d4141e80700c043d100050f8080c44000c15100e240203964401d81d00a0f81c80002c0640c52100100300e00703401400709103001000306043c014142c0d06d074003550200600380131401001c500d884d541802030f111042c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 3620880 1250 3619630 3619639
    0x50102040f12020a0806010b070609050a020405070807020c010f0f1202040b0c0312070914010809011104090b011701030c050d0507080a06050a050a1406010c03020f0d02030a080117060c0a020a02 85
    0x202e40740c07145081d200349040000c03032207055588000954140081075150403503001d0009a07003000c0842d103d10020f0720f09071404562500407008044010380c3c071803054900074405a543e043d120314050002902c1c04007890038843c14001c0d003a20014030300e0380c0a4130000c903a035941d00d000c08041c4031590045001c0e000f84e4208402d40c03000842c0f60340c1e42d000000040e003481d9a41c40c3d03101d0800c0e02d400c04203541078035140c000d45599408181a03800c50354013402160340c2043e07115000040b01c01400007991503641068205145264079032210034829039100d41c4a00180ca00603050100551655955401042c0c0074429140160081004030007440002e2000c54000c2031504255071604280345044801000c0449044490344d1a19000c80d00c010020b03c521229207201014040c0c0350303201c50f801517610f0a0031080031811031064451050907940b05201c000306009280d0002c40e107407007010701c010b0440d2105070404000ba10200e41400584100003408941140c3e0b250f86166035500100c00c100d050054414010350030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 3622130 1250 3620880 3620909
    0x5070512010507080109050402100309030210050109020901030c0318030f1103030406050f090a03020a030302090f04021204020102011d0c0d030306080d08010303020106080309090c090607050a080903060a060302060a080405010204 100
    0x58180c19040140310700034039540e401d52a80c0341d07480403044034800e40f03000e50840400400c3c840c071240264007008640d4000c0c012100071041c081008030940e0001d812172446140c01007211615940c0500507800300440d18141070015a013402141c45207070b0000c01020381040400c05017a044a0f000340c5203022800701101c01d032030f680d262505115010b84030681c0d41c0d0040721104800580c03104004a035007043d5070b525074050030b900f5500d500d088010707412000c030541d40000c0341c00c003c1c140c0b613032a480100128a400c40310507846240034000a801c6404046009810141600402d03842840c04110010140000c56402d03400841ca030508070024400c580000c0d00724841d0780001d50070103421040740343c100c9210364028000c0d180c42d040b01585a0080b0042c031034004a103440420790411508018013601360780540380038184200381c0c076518a06502c2c1ca03070035201c43c403002680b41e0b010b080501480d6800005090700781310907403566004c075000d4030844d00340808200d44900070504014081d01242c00034903040003010a0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 3623380 1250 3622130 3622159
    0x90506040602040503210703080711030d0e0d05040e011a0d02040602061005030304080706050309010b030a080301030303110412060b0406030203120406030501090605030703020111070308030c030411030601030b060d050705 97
    0x254041d00a4621070300c150101d00b22a44100101d00310801b86101015040100c180d4040d500184050580d505014200d80c444020f60400c10241014003107910380410f20038002c81e02e050030540e00060880412030200030a000582200842a04650085a4810021071071050400190103000c1005902c0f0b40001070000d805940024054050440306000449481e5901d042559901c9644a42000c98122403400c1014502900c05103a1103604400041040b0031000002030900c507003054110750b0204003000500c241030f03142c401c5c003400f0642030301d2140c40c280c03d00e00303209141d841d010401440b071a224050a09151240e810200045a01404a8405184030303107110220790850300135540028606800016845424002d05c421648080c0181c168142150011071300e4162011000455120351600080050b629000451082000b07601d290b481e4100380c6406c414060342c110b0a24070a5120400510104010740345041d0849821501790100c480e0618000c4c0c203004060b88129440b4028201804 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 3624630 1250 3623380 3623393
    0x20708040e0a090b01050409050a020301020705010c110102070b040209040201180305010f0c030207020f0108090717010501060908010207020a050105030a14090a051501030503030604050709150e1009060804110409050604 96
    0x819a49080c03035000040c0d5488542c1c0c403c4a81c84040544541d200f8401004a0b091075031000310b019003d4020348029040940100342641c0c001034044a450395602420102558001c1030b94030b840000c10025840c000301a01d94a10341000680064440c200a001281c210781c010010402c4046007019405969690303410078a00a0240241d407070b58480c2072001c0c10003000d1080c821180300d03c0d40209032a03009010311004488414000300303008031a00ca010b00100d07007a90550803040701400c6d903000110340d641c14500c00a00b009003a03403122400c1c1c0c3c0144246001039560b6424a02139038030a280082d202c1d6640488680a00405c6034020f00550900e000d1005124020400d101c0c8540214101c480074801488107a025010900c00502550020301c0070401c0343c503154204031b030041c0452034411580c0d41c0380c1443e9003c62000ca4507038804925022601661801c04052150f10120641080007155203800f4014280c444000c02c002c1402078075864502440c1d40b6984240c00e51a0420301712242c0703250038907111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 3625880 1250 3624630 3624637
    0x409021c0507050a080307060b0d0b090601050a0e0108060601210c0518030607050a0305060f1011070801110d09050a0506010e010305010e0a030e0603060103200706050c0717030c070204020708 84
    0x3540d4a0040e218040f81d40d00b4501e58010403030f4850002945400c4050719200001e040c004592580601102c90000108410054050180c1940b0b0b02074803007545004200070400300c01341e200c41030030b484190041084c584003242e00342d8800c1c800e080407089824042a201d4081403030f4500c900102d1302d484c1c400c4c0d81055119000e0100955099030403910540d0307070030030103550300390440c2c100b00050350401c1000c1d2454440d404c0381d030308200054001c5460340e13600b000285016007943c0d007000c0043c4e000030512030381030810480e6000501000c2d008000758000d8140340340c00c61243c0c101e094891a11013101000f041410005018081d8101c01503860030b58454a603000103140030301c026286503013032014200d101d0300301045c0c001c180c1768036131111130f250302d100000c0c0401508001c0400303040c5562081c6010407400440d8a0f10020325400381d001781d80344000e240050441b03c1c06009400c0717070240cd00050300014400d40586255041d0040310307640741e5a40c080c0800782c41c480d00e00002d40150010480b0420000060040d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 3627130 1250 3625880 3625883
    0x40303030e0a0209070e0f0402070206070f1104050a0203160804120c03020f0106080109031103040608010e1503010e01050a0f09020303030106080910060f0501030501050609090a0e01060302040e07060e030a0b01060302090409021c 100
    0x601c147ca000c500100b00c160f00801744040e40c0508100400e500203500783c0301c8914036600c03c1c1d503400808480e1400040031240200d850549454001082112654010009810060250030404210300f8541c54000d611642d807240c80c401c2c420600b00c0001810b008115046290211300002d000d0240c0f901f003180d000c0c2c80301c0c80c1c01b00e01060380d001105010400200546e81510a56510805d00383c0ca000911040b03130324098a50b901c8402c1c00300c000d69244d24207009510380d084c4441d00200e071505100c1d1846044030b050400d00c8060a180070f11000c01a40c011044034110fa540307140000742600d52403016403c00c142440340b0ba041e14a02240000c410040c2c0da0313104100d54098904000340d81c5c0e11400d02856124901c100c5521080c007000050090b020b6500424034000910000641640c881c0d0200e8120382d54501e006009078000c0c607040003080d60240c1841c80200c07065016281014542e034a2245280042c0120340034140c011421a0345034540d50302020388a900188040f03000110b03141920030f40c0315603200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 3628380 1250 3627130 3627139
    0x90902011103030708060906060903150103020109080a02010813030201020c0d090503010c0302030f04020d03090503100209100f0c0303050402041b1d120c090c0d050408040e01060e0105040303030e0a0209070e 91
    0x24408a00040031007501d1080384d080d01ca052880da01c500030059031540042400b580b180e0140460203c980741081181d80c09034250020b13030003039411400054480000340c2e0250119a10024620005036401a0340300d400050203001081c0129940c13030709074003900402004106c03510420242091055114001900325001a0001c114005403504114182c0c44211030b01ca0241131510040340060400240c503100306402032510642242d1100b000905203008281c0880100d0380201d407031251440c180c2c10800038218170781010b44081440c45406041008108000307014540c1e6140002c0554503240c00003140301502d0b5681910070061500702030b01102c9000450800740d0301100000302c803400c0c1910450340c058428001420034920700b204000c404600108541c40b980420300c140e04000b182c1c0d00400d07005522030f104641d291401c00003d1204410b050380060100564078444102c140d030401b08503800d070f80e050320340032130741e005200e08140c5404503040e002908008a1800c00050f907620500c038420a0100302e5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 3629630 1250 3628380 3628397
    0xa0518070e0307060807050703091502010617030304020d02011b0204020d0219020a020303030109090303020409090501060501120209010909020f070f03030b040b030307020612070908030d050f0a0527010e0709090201 94
    0x102850b9607080d03a4000c160110345c485020581c01c3d4003c1d40500b1042c0d00c80e1070514850794841d100220150174512241016179114201400b0300201d00344002d0120443c10007c500714509500092110560b21078003905110404070420344540034500034030780d80c6030050008d56444144000400080d4050442c881511507290342c01c80e40e481c80400c109850f00d800500540c296400c0a5801c001821007050403010305908001c0040d00b800203014101e042400364000282e02c1d441d1600250004110030300441c9890310400005466070382240182d4180d801c043c1006031158001032404d1241e20a40001900b00320700d45020104043c1e25070031850712036000361014010b041c150f10034180c0e24098250b000350b0105040c41000302011004030110f602680510781003204654880c80c032411503002203803541c80317a601d590400c154214458200d9402203d0004108000d140130307c0c58100c00c0312461031007405000041d801d024840c509401420004044034140c41c4032075070340c0740c0040040140c200e089010a5154 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 3630880 1250 3629630 3629657
    0x30308090c0108040303020c07050a03050c04110c0601090911060d1e0c0212030703060e04150501050105030601020a020f0103020418021905090a061103040306060605090102100e0a030e0a051807 85
    0x85000780c800c04040c0c64890140d203903079500754081c1d0000b20803003000e4420880c00003030384e51314500d1160082d80910302074494031441d0420300058921485000800070010008102256000901e460440340003d000269403a02071420135540c00403480310783d61181001c2595030b010080d035071294800030032080c00ca120704413000043c40e082d20106490340c00541c201811070300c0da00803048000c41c0e010745207140c001071894861049a10b203010036101625402155040401113080754032803180500001d0802a0651030301c100000d50f24600190000d0250809810600444c3d00a8060f603010340110080411000459040700f0000d4000c0c0d16004000401d100f04c441680740590100c812615000e000901e07400e06101e016100c461100c0456102c900c02084000040798091081d01f010780305d0313542d0340b035980c110003c002403500c05007414054009142c0750081072903040008048840340c0d4103044c401088036410000a24003401988040d4100c0e0300021900d0302c038208640c65178891000c6445407803842426 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 3632130 1250 3630880 3630883
    0xc15050a0f1b120b0306011205060708010f06030f0e010203010602010902030105060d21020c061209010b01080709060f02160f03020924060903010f06030b012111040209010507050102030103050703030809 89
    0x10111032261001c03500e00c510030b9114001202403c0f07521503020032001a41d00101e80780c41402d03170042c07842126240e900d00404c04184100d603040b41c0c2d1440d04096550403c00006c119190500c100b605056640e011003004004580205001c5505c00000710348941c1d440070f0280c0640602e5400300d20951900001480741c2c5402000c803010039401070102c0c10001c1c0710714504130704d00c0f040020716019807159400308c0d800fa6492000901080407050100b4403941007150b841c45c00d4802d40649036060000001c00c011034141d0000208044611520f00000004d1038030f68103905120005481d00aa410108000321703c0008000100048a00c02d4407010020340d2045c42282c10071000c034480400000240c0d810781c10a01d0038002a00e0004c0b0000d00000b012034039401800100c90b030541c001c456005118004000d0020600d03148000320b000d035009a1345105c200e41d45d04500480c0408554071891303000c100c00406900c25030690b0121a17001008550303e5840b810825520b180d240b0007100020103010008040307840 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 3633380 1250 3632130 3632141
    0x19090e0105090303040201050a090f030f021201020307080606090409050709020406020606010c030207050d0c170105040507060203070804050913050a0606050a0b0a08040308060f030703060605030105090109050703030c02010c15050a0f 102
    0x8441000c3d50550700c031540119a568456920402008003034400402d00301e46c2900030100a611800400500d0780d0b6a105102409001c6081050706903c18410401d0721504941040d0707101404480303582e03070f5550001c0090020050140050214400c074840403482c20070756070050080d01d0b0395800711000d41e5a07003001100c803054010300c0100180c00802003081682071a1840c5003106203c0c03403c0300c821030380316044a2000c203400b40c06403210342c2d101c0c0248400d21406210070750192096102075481c0c83d0068581c52458841c62084138028004a000201e03048141070300709034499401015500e0507049400c1010240901e40103e502c1520b01150004447c9503070700c1200d20030303485501c604103e940c032a1000e880381c03040201829000b60548108035801d50b414000c1401440c46024000740f014285406d1508446004040c5116a032524441da4042603000540e60100c3c1d51500d40301c1c001c0c503010300c0101c804c2d540380b64004221100c0c01c58200c660500b26006188204052a82042440e4407910464107944 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 3634630 1250 3633380 3633391
    0xc0105040603050a060e09010219090b160f0f03020303010905060f090f15030d120f02030609041509020603040f02010210090309120c0305030403050604032003030105041a19090e0105 80
    0x520402007002154041d0b0840c80c1d206110001c0021160b81c0c07070550050440080b03072990364a0b50b00103090114414452070480304001c0318609281c40c0c9040105d0009a480307005003c03140004d07901c800d2010028a80d0800d521164409005082d004103403a02a58a41081c0122010981801300103000782c00c00c0c111500b440c3d80024803100b020f8030f40780c5000991400162862564144a00c0315650f142c4003005034401d043c4e402e5503010008501504900212041007003a5101f845c01002880302c1e640c0d44034145500f064000f00040c0c0b07062181020074004140001c0025000a8044200700c1840f00c240c03010000c0c0f90007a000d450803802c41041c0d0030304880201c4002400700d80402814080d0101411800c04c034107104141081c0c440d80c60381c559629540180d0300440d80e41d408042040101a44019070740506104250003808203150744410702d480380414000c2c240203d94078585006146a00116170304135032005015121100e40740b030900491035040d401030450960070125020710390a0140310705840b0700e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 3635880 1250 3634630 3634637
    0x80117150a020d0b0306010b0309070501090513020c03120108062e0303080c0708030103150b0d08070206030601030204090c110d0504061706030f070b0703030c08011805060619020309030705030c01 86
    0xa81d40e0192240003504050468601603a4a0140030440d80b01000014084d0035000c00d21038491809c00c166624013a44d03608071a04010015404005544405c01817101080041402603216001c001c2d441d4518091501800703020581007000090105010401d1340c0940e0040350701b400c42d402c103402d400360280005010454141049202000400e216401640d0003440d05d01c811480c12055842d008140e070000c3e081919260803c11400152802a108040d050070b810780710300d2030044294403180894007403008080d01a450000025256030702ca50304480c05000d241d68200b208a016800c000c000481d01c1031030728458803800039200c4205000300141e9080b2502583c03015194121201c0442c42046c01504113034061003072040c4140c1141d42880002c0107004181c040946071946410300509071907440504034140280c450052000c0c0302c0d500c448000c188806900861640c44d035a001ca01c55100360b5440302d4000b11001c5c031400313034642d002c001480001d108a00f2189e0560704c0d40105500d40a4449110340132 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 3637130 1250 3635880 3635923
    0x105010806040903050d02071a090d0210050c1314010305010506180d0812070c0c09020301060806040506030a02060c010609050109060e060d0305070605151908030a0309050c030706080117 82
    0xb440d0580110b020700e413292501604121601c10540d041c0d801c0f0325802c403000000807040e0b113810b10711390108030380c0540082c5c003d0030228410a0041e40b0745101c0710180d140c0701e07112000192540d4000e82202c0441c019602c0300e003000d954507040b0f4031508000c40c40b4140040d00348000041c8501d003020a0741d0845005000b40038014015104200b203505554a04540a10003405000d04a88503401054070465003911007104060461030078840d2012103402c50301c400b910600061200c0365014041c542d00c1001541c002849455440c0084d01d070020000e4003d501c540c0000e1808203820741034204000300e03200c0c0ca005100c940d8036a08103506460a42c0103004121300060002000c51410399044044e0b20302074105189022520b448103030584104540841c1c0004010400b2000d50600d9008400c040d0b00a4550010179424200c034035859118200f080e008160301d94480406006041c8079541c540c25004040b24034907603032418050b240c030009205080c433141c0b030544903407a09000401d5101241ca18501410304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 3638380 1250 3637130 3637141
    0x21b0102031c090f0503040608010602030703020a060b01110d05090109060207030b07050901050705010203040c05090a05040b1807080105160908060106020d0c150e1509010c0c060f02090319030f050301050108 91
    0x41041d500b42c1c1d885842600c4011590129803402400503000d030190004c1c0da0740c1c5c0c1c103080020b00102410b90000301103600030800d150203e58045040404507602400100360854032400403945c0503502e05059006014031403091b036600743c200e001484045400e89070940f0450f62880d040e40c45801c14480a000400300c48009582c2501c0f503401421031507814140705041c5038186d150315007203802c100e404440080c0982410320443c917003040c8640d48201c05040074080340c0b41984e200c0b0850710018008403c3d44503c140540024001031000d00c000d404503500030013040c5400c487c2da108103544c41800d100820120100441e05210110b1458181d412940061204428141040b500d100c042c44094a40c1603081c120066403280034080e104114001c04000c10b000041c3c0600b0f0044004098601d251586c9403610b0044203c1d00400044002c94001c0c100141000107007044002900c0713004000c41d410f0181a54011080100681c104801c6000c9e540307104901e20420000c0e2500d02c030a0080e00c3c0401c450340c0c0000e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 3639630 1250 3638380 3638407
    0x70f0b030c03130804090507020106050603041a0601020309100c020f0103021e0307021002030411010e060c0705010c11030105090304030c0e0c0910020106031b17010501210c0e040305030106021b010203 88
    0x150816000346403006811865101c9402c680c03c06e801101d00341e41c980090107100f5609014440141c001101c189146007415a6411a503031418608079090405580018285030b009005503441c003440a0042081204105001030080034462001c030f200e102d40c0c003000076095100c0d20986108801410072000c3d81644000c450340e4542000b0b00010452007034240c1e014503c041400514082c520810048001c200000009400c14200c8080c0d5800b6910912642d08404400180902214030a09055503c400c0e582440008402c80f0b0364025010f41c00e120a012070604000b0080003140c0c010f440c4a43c2181d2260401d115060702070341d6001610400340511855440c10580c045149001c0e4000010480c0c2d03070f9602c240902031520041c008401107a041007103240d0381111140c8542800302e000b0071456040089450303d0000d03031811540c00d09181015030701001a84521640074260b00c0c0400c8050f850030b85002400742d4824010340c030040c020142d48984d00b01c607401000a0002c07050b005141041c04d56000d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 3640880 1250 3639630 3639637
    0x11b020c090c040503070303050306040e120307120603051203010608090307020d03080a0213090605120102090a14030a080d09060f1404060c0302040b030405010204090605031609020306010512090a0203070f0b030c 93
    0x3000b5414040000040300d50301085120011403103500c6460701ca1a10f20700700400c50703074200c0f1864020f0700301e00411004212144101c941c801c100c0e0800703a270245d545494180081c88150001081442600e040103026a09000038504840d00b582d210102551070034000790300ca0017402e1300290007542003808940020300648006a006002001c01800d2286c0c0040003411029154802440741d1b0780e40c1000c1c0b0807402c0c039101d0050b41034200c2c0000d40c03602c144100031804040301c170b200700c1c070300d50300703403a400740650b9405018440c0079a400008040d1104c203010401001000464400c9a5462030a00d05141d96915400f90001c24010104a040241e40360340ba10740181401410050400d9820000420310781c0c10701010f94002c502030000181c9650504188100702d60584c0c00ca68840c0c2c0c440e10b87d500c81f00100750000020749001c180c0158494560b400142e0b40c1c3d004e403140905140074290200f01c1612000610004a40d000b2801c454009540c1c3e40703c1c03481e0b10210f01907407094840c200000f542060081004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 3642130 1250 3640880 3640891
    0x1060903171c140609060a06120905030f03070302030a06050409030203070b0c1b0303040203060108010b030601060e01090b030a0203040b01050103050717180a0302060109050a0605010c0212010609051503011b020c09 94
    0x200b6880d82209402c8100c0c0d403814248403220300f619080c48031a08001d003459900071000d94401440b6814000054203c1618201460085031220b40c0d810412400b1b0003034031424801c444060b61242040c29014010390011100c02a440d450080c00007564a0700c2d00403204850b4264029516002054403524003000d0014440500100d08000650000501c10b0203030844403c0c1d500070f191a41400d204141c02c0620681c0090902c0e1305060080d991580c000c0343c0b02d03044a12904100c1c031002401401680c52825a91049000321404801c001700341109400561007144100328031902a0b0301c5d00019000c80340103070f450000280d41e602d6411411950071000d150064451900c0c204090485294145040300d14a42140183c004032700400202d5213502860341c00281c0740c80c0c1030111505000c00205000303042d0744060b1091641c1550b103142c10000794881c00c0908602031042c005d919151044003100f0820000300c034000c0d071a04c401c0750540200503c100c0c0c0200d819501508681215101700400d441e0003501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 3643380 1250 3642130 3642157
    0x7080909041103060a0e060a0219080a110301060e120a05100f0609050a0e160305030d1a0301050703020901020c03060105130203061f03060608010b190f0201020708040f09050106090317 81
    0x10b62800e2994100070083c407821100502140c028800e180e0241485406040c1401c44d03801070054030000300100c19002c08080c07440c98940b405a0342d5041c104003510804070340c802042d02c0000041081c985c4610f216840200565802e2406050b46805c15980d4200320000f40a0303812400c3d0440000040d90490141c5c1060507202041080d141c644540c12100c06580d4501a1a42c4408444040740c050280b85150840c1e0009002250b00c4d50311429100d10500c030a800041d55a508400d0001c45000319020340820054000c02141c03814010181c001d50100008074050b101d032010a058a10780058280d0507504003a2200c0c3c440044101e01d40c01035080a000b95900254100d15128900c2e4502c0300c40e40f0203001d039640400d142d4030f00710015100305810b8015083d071000801007a1500414110541c800000502c3c01071151035000c80202d009015800d401490281c4c0000c001a48950300c4203050280c03009003e04114a0742e031020140c0360240b9a1000506407040031646004c1c40b100c13417002c0c002e540705424 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 3644630 1250 3643380 3643403
    0x20c04020c0307021c050307021507061b030609020406091503090f0c03020a061706011101180501050f0109020304050703060b040204180207060b0906060904050402030c090c040602010e01020708090904 88
    0x2405a030066a509802903101045071401c0d441c08007030003054a042c0c0c0041042a203c1c0361070b05504c80c810824003074000d000004104407903240040440c0c654a401c9402003107034890121500843e819070500351070000f070521202003180b4031548201d0381100c00540b104559680b0344a0f80d02104910b803107401d01803590700e0455a01003040200000400c0c2c0c410761400100034150302c10460000e44076000442000140ca01100081c0351025880c3d41118003428005001c035070301c004403405000d41c00e0740301c601001303540500820010305401090040011401c980d44603070301c48866500320300040fa8082c201d680800403c00128013140e01c800000140a00058981519070019516911004030240e19080d400203404050004a201d0b4828011044405403000d042100c005407250003401d90840c8510381c2e075000310b0119901008012880400600006018500a45115070f560058070500d80176500f08104c000c03110f01c0605c201ea41c500d03803011310142801704007070610154003401807048600c055050f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 3645880 1250 3644630 3644653
    0x302120703081b0709050403090603020702030a0c080a060b04050402010903031d0a0f0501080702010b0114090d05010c111501030302060106030c030902120304080c010302180d150f050f07020610140102 88
    0x10300200340c0c04008121044590f0311035078000b46000150b6004c2c220340c074a0902807000080d8807002c02d1088a40d071f4507002d42c5940d26800080c0c140250703090002c02d00c0480071000540c030040800c20404a6010700010000000110144029140c0880700240012001c0e08180002401000c1e02404811080c1c1000310903401840810f0800d40380750001324a0f124008400c10056074003c1b15160300800500c020f100c0a034140001804a00356414180e40d400d0000c41e40301800c1e1074000d001b001983d0400002d00280d00c01c420050010504042785030420302954804403041014900014100c0368154000c02d40c5030310784034040303000b880550342d008100354a848101d0003683c0c8440040c0242503207003019680c0c40386405101c92a0007010f5907007905150040c440000c40700110340802c16440d6040d00c40320340b8119145072900e161401009a072103064075246403003280c207409500483c811a4010234a1010307450b2a802648c0d104c1c4100c603802001c1280c8031042c03086100c4800076440311041801202c8030000c04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 3647130 1250 3645880 3645893
    0x1020c0d0f020321040b15030a031101020d0204030c030c0f060c060b04060503030309060a0c020f0a0807060908070605040b07030506030c04090201090f0e0f010510021b06070c0605090102060604020901090302120703 94
    0x292420b08401d00b000d00148406c2c050b8440003503800c11050703070035481c0440218000c0303512642c4065001e001d100c005070303400e600180d0070b40440b2245003040b0000c5503165124074000b091b0300000d02043d14441e503280e01c00700b00401c001c840c0400fa5556a22511070240303442c0c0e20074029298600350550815102e200000e0503031000c00285008500940140c601860000c0c0e241c02206c40c114116401c56110b410504413415012803100d480380d80061825030343c2c038440c0c2080400f42005400c010061040002c0300c4023402a65440980200d10071605034000e62a411800c0742564015224140d0681103103989604511b869480321030030902c1070421540701c5540300f0105082c48815844214401200303004c002260740310700c4a203405803008a41080c062403008500940c1c030401615915213121840b0950681d5660310000d5542555100003800790720380e204c405c0189550065072685000d88510b80c0070600b04e04c1c15000395900b035541a903680d010140756400b0001c002c510600400ca017402004030110100d40c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 3648380 1250 3647130 3647167
    0x4030209180d08060604030b1f060f030c030b060d0203150909030a03180b0c0a0203090307060c0501050601080f06010e010c0b0a150608010e060d0501020c0706120e01020c0d0f0203 79
    0x44058800c203140600790309140c1400c1c910001c0001032410000655034000540c1d060780c0d000a0b01001c1690380720141c84c00f00d1036070800c00302d21175440c000019442d03900400f511108200c6070f800b80b160311000c40d416826100c00228996000005100708000c400a42d4003a5901c50b00700c440310120700c2c140724003040d07034820180c407080c4140e0400100f103110b280c2c060151242501c110105103030600e1240e143c00c038821101400e402001b50000035040000c92080082c5ca80c0f402d4000d0682c7c142179907401c0003a0003500608000c641c030703501b01b1001030165806200c0281c1b02e0620250051415610f2200460f014401e05c0701c0d1a05100c81d161004022440b1a10038030b10502104500240e400e038200d80d46144d0304041c0d8400c200b00718000005122181d900c0600b1604070301e040c4c5402190068524110f8060b0051301a1a080740c811100d001400703560220001080801d0000204103070fa82800100c1d00340d10410500f48515804440c1080c5900e100302d0340700c0004842c1c0d206417402c01013044804c030340010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 3649630 1250 3648380 3648391
    0x90615030309100e040b0604050907030c091a03040311030a0c030302130306060b0304060e03071214040b0c01061502010902030714010507120806010e1008040b040201021c030e070603050903040e060604030209 91
    0x1413200c10a15103a04181c440c1c004200012a2a14107051400740003662010300203010000301901c503200c0c0d0007818080ca4110000d040503111400d81c40e0010303400707144a5081200c0c1038000070940c4800203c600408021180003520558074907140091035241036002c0d41c0513080f0300c08041150000000460414400d41c1d000d00780030100720f65242000d05048050307808660700b14119030810801d2100042540e44042650162411310342044445450510703400c0c040e981c44003261807000240307800d640b80198020400d540442c0512404915074003412401c0361201c1c24025013542c41502c0912a188140b4000c2c20345010514106140001c0782d5200d01d01c007072180c2c801070080740d0b00009001c410340c0c20184034159444160b401e0b001c2e076260740000501035640540003404210500012406592081c4250302c040c0d980750114044080d604c6070020000d041005c0d40d40a1406210000306803c2c3c0729001c0e150061507844000d5040c0f6007007401d03880c0c0d84a0301801099100360704000010040c2c641c40706c40c51040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 3650880 1250 3649630 3649637
    0x10020705150c060106020c0603040b0a060b030702030706110408070303030e0c03010207120305010519060804020120070602060903070503040b0a02010f0603061a03060709090903020709141b0309061503030910 91
    0x9142d100045460f10b001a08404150b410640805900e51201700582741d0040d0440398400380d503101c10841000a03c610f4108164601c070000030030140035000402403107242d12550080180e03041c0f02c013031031140703014900514005800c00795003000803d100750001c090680c001401ea540344041040000c0c00c903840b000d42160320380d03064415040400d070544072b100c1c0108000e450020302030a0750401c400c42c0b1f103002d001d401c0c240b08600f801320741907900c2010003000401c10001c1120208954954040d0f44802e41c3c0703d0500180f19031000a100701c100401a42c0d613890b13026004508203030411000e4100d941050034480b04540d81d8a80010b80c1c0c1449000d40c0000714002c000010340341403d032051405400c54103580c98043d40c8680b050104945c0e102e201401150400b40d00080c6100c8649030807070605c00740f540b02015107410004220240f4000e445100e0003001030142103044400285002c2c4141d001c100da10040c1e036007001d40010b03192420114100da80690040c142ca1030241d0f24000940f071900070b00f8121001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 3652130 1250 3650880 3650887
    0x1c02040b090405011b08070207090c0507020a08070524040e07020f01020d1d01090f02040218060415030c0207031101211806060f0b0d0b060c0304121e020f1002070515 73
    0x10505c900285924852451410702840d151001e006551103282e40f244024141d660040c01c451184900e05031600698014829501695035102d140c5c2e40f400c0300e020b0b0902c03c0074007020104c0a507411405e050b03909540d08180f241024a1301c8600d081e10400204450107602400540d0b8520700340c2072001b0018028030b02000510703405a5030001d41c0d44a490300c0b10403620b070f2519411101181c941c54820740b0280c1e045070003595030020f503e0b0481d5145e0021f005c86411402c04500810152818049101e5105007650104030340d81c103000c0d04903511840c078072010f4850342182211a119511803690400c0e64070f480840700070750012180000049400044420f019407850001500c100202401038500030709500148854160902e0290b4082e07100b0715002250007130f9a000d9078002500d0307000946040f6014141560f45489c2c1e00ca4100c4032001c4009001c9134003c40b100d0f6009245e6030344c131500a00c00342d006811800c90a99030410301031413000c1d40c030103c0c085d03105000c000205943d4144400d0b040c4a83e034000340381c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 3653380 1250 3652130 3652151
    0x602160b040507050f0d060c140403050105010801050c0418020a02010b130b0109050102010e0304090e070512030304031b0309050409050a0209010807030302060c0a0509060d0f02070303020c0f0c1c02040b09040501 93
    0x380300c102d070403145c0304400b99180b03490340342c0e904111602c005030071010000b0b500803408010364100b05100f041407400c00c00401c0010500c041075100c241201c10070402400540e45110603054144164040d40503c4250030a8154035071459902030710015409000005800c0f4901000580300700c0a243c2c030a00007519004201c3c825644403450340000c080070300003401081c2c0a007260503224002e90080d403810b29910507d007409048204030640c0181005400382140208615180f82c0f60b600403030b03080d400b04e450720300c038081010303a60101d03034091b00e4241d5100f500d064107100c1044080c003204501903ca5200f16611100541d0b24072850702d000304281001841e0382e91446c58003a040500c024070000203544140101d140c8241c10004031030741c80341c080751002c0c1c1c2e1751140301021000782800002c40c0403080c4080b0380d060801d9050790081c080298000120b40c1c80c0c0f4011f00038296140c0103111a59042005400e00c0d036052120803c0041c855480100b0101c0c8a8480038041441c00a04840581e40e581d1140310f00074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 3654630 1250 3653380 3653383
    0x3040c03020a090c031b0504060e0d0803070203030708010b0403080304020904032d0e01020601030b01031b0b0f0a09050402091818060a0506090601080c12070905040216020a0b1804090602160b0405 86
    0x9103124050426186d5081d40c1000240050240b481064140304060030381400c15070b1100c2d1040358035176014510545a040020009580707400440e40b2402144101c8004108129030310181da0803254040c00c030701c0c07841c0d540e5030a00c0030a40d40900200c0510000489096440c541044070f40d15015807844080602086214010100c1d600307005000d0540d08100d0051004c5503203521001d065941100d0001d8140301c1c56021032004000030b0f4010900102c001c00c1403d09424803034010f2108290b01d50710720b00f0a5854030204000c922501d8045640000081464000016170002103540102e030078041200c1d800c0b000c0501c0c0d0910300201e5800c5140b950329020000c03a460124842c5810035003e10703001c051032511030b18545551054064100828101c81c0c0000e03445840f0f0002a006008090015504c0340c08441058100c0c07520480100c1c801c6c0748103440407928507126010380d200c5140e1146281003070011101840010010f403841581c64607002c00880504002009192030309604c02d181000b2103107802d00307000303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 3655880 1250 3654630 3654641
    0x70806010e06030c0702030a0203030301060207030506070305010803090f130e0601090609020c06070c0204060302100e0405010806060109140a030605040b011d0106051207090302030f0d02010b0a08030f03040c03020a090c03 97
    0x6810301052100c0484251a041c050701d80c003044013500c1c0e0b41d0b9011240002490140398200c029414480080041241d650100300001120310400031551141c4403500c060302500c0b02409039884682c0700340214030342d42c6060203001001e090302170200d80d04143c595109409990300c0e400e030100d90360701410040014a00c50720601b8000c00070b08600b10b003095558604152580406004070301000008206a4155519540080c00941c1c0c002c01e03500110120101c003071b1444030043d0707030742d80328a1514000150040021502900c2450160f48252000d801c04041018030a40d100b842074000d10400008400960340744900e900950044028001541c54a240d40d038201c82d202078450440d00310400104266034000c1d043c0c60141c0d00d580c44c40412503440c03074001c80d1411103503407001e54148201c50306081034a81c0445c00c0c509401244d8001e0112003460b1045c0055203481c2d00c00ca0384251700070020301c070b40100b5280c05103030042d2042411039695981c940000e5280302003504a002e816075500da64185041d0180300f04e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 3657130 1250 3655880 3655891
    0x1080a060b040302130204080a060e0f07030b0705070302030d0c020a1704050a030303050406020c0a060506010e090408070303020c0f060103050c01031404020108010504180213020409050601090f03080f0f0a080708 93
    0x5208a50a10004480702d000741d1000038000c3c00954040d41c03a044168047e100076001140450b40d600c0c00500345080940044216220b03a070181020b5004290b1001c1070308426a81c0010135a481e40d110003104031161b070301c00300d001e07811400300340101c489401d414007440c42c80c1c0c400d590050003c0d64403418406400003000c04a0540701d44108020030854481c407a103103040782d425081c00600c075591410440060300c940c03c1c00315481d002c0d4280c4401041101d60089024007800c1c0e0f2134030700225498043c000300b18030944d40501440c105005240c0000d110340c00902d40c034080c1070280c031b0301c15192840075450218280c000700c0e100d810040c22000d072540e05100d940c03008003000034050401d00740351300040c00221060088600a94440c000d040c40005000306455002e540070b042e4801c141c02c2218440c0080d0814050900401e042c074010950b10742c41031840005541d8454207002501d841c541c0c400707407181c1c40b1504140105000380501000040c0b508042c1035026000d41700c880f10351500c40380081140200a01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 3658380 1250 3657130 3657151
    0x2070506030f07030209060724050105040b010806060a0302070c0e01090c0801050f040c0509060a0c05010b0405011d06010c020603070203120c040602030a1404050a120b0702010203060105070209060a08030f04050108 94
    0x8000d100060310710302d10381280c403500700140c1e16440c1031301242c214415014060107103c0c510400c0c1c40000d000300401842404d20301e10402c40d6076210700401040d02d07008820395000840c004080351841c0390038002404450850b050061421245a03214140981c0e2548160740d00e46000c07004102d2040c1c00d0140800e401442d25040c040b07581000300041c0d1440b0420010390007180c1e0f5440100455002c0c3d0700311040344030700074071641d1a035032842c01c02032040560000490303180d42401210401800c2c103020b1203040c0da4007414505070410300c0c0301c1d5240b401c0b0030051540741000310800c64074015840d080300850042030941d01031907699544402084c0c51362400740811411450401007003242d1640401603804072080d5242c8400301c44400089400203010340d4002c0c0368010300d40000000c55515070042c030400709100d82e42c10b500583d101441a4200c0c04210b6002d4007145041060b000185132808071690301081c010b2406810302e40b2080300e907180d078101d00740704c9610b03d0000405214640c0c1002000d503004620a5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 3659630 1250 3658380 3658387
    0xc01030b01080c0a0c06020d0209010e03011401030b040501020d020301030f060c0c050c0111010e010608071d010e131a070201020a09080303100902090a03050a03030b01030c1e110a08070c050102070506 88
    0x50008001c2c1c003008041400d43c00c0003180c0348030705030f05c0b030711511282d10b80020042d52201903810720100258005e03281c890104807004208140350030103000c8d480c2001d41c01c4008403900da180da2641080d04c00020700403038140d54200103245d884040c610203140614050410144030348140d1030b0001c126040e084c596003c1c8684005c040c0001100002e440d281380703d0078a00009208039522150b405403040e01c1d10241c4550030030001090040c0c0000f19101203880c12045404c0e0758000c90f851615140d42800740e160854a8013000503d1a41c5941002111320310904c1c0c410b40124400c03803040c8401e0402e03541800141d4000400300c0b0b078240d0140c103070809044c0800286155043c04c00c0c1c0c45502d101d030392013a04031f000d8004c24400c8a941d03500c034019005580200650b03050743d203070f03180040040c051440882c0c04627161442d04042d061095401c00012031150080900b84040c40c80c0c00e86810110110011691041c0000b00c0000740c118409400c0e4503210345001c0c0340240c01c1400180c00d00442c0d41089002c1c20060 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 3660880 1250 3659630 3659651
    0x20f03010902090c0a020c1e0306070f050703050901050d05040b090d020309030a0f05010b06040303020a0312060513050a021c0b120109080703030911090405031c060f03060203061f110c0103 83
    0x3c210075080007104c010700703a40c1c03408684145d040290083c0220750081c0d9858151039000001d01c5100b00d040c1c02102603a0385580c9040c403e46001425501041c001075090200800090041d801050065414185070381068980c220b040d090301c40454048401c03030050700038804071040400100420800c03a0000d107061a4803100466902c18070b8141c040d00401710700c421642403100a502115010f80c000d8480b0b9030711a140c4c100695580d47c080360450002e80003420b004100c090602c10030051b1034004108001242c4800c0a01700078080141880728100da00700070f680c4280d20710544560422480060120b0803401e480200554050300305101659a41007881c0f034000180c040341150743c1268103007030019003980981051400d082813103081c45e03004010881400203108000021b80f030003c1c007030010300c0d078201c809100030b0701552407a2051b43d40301d40c07560f04103200040c1c69801455008102510f07000c50340f12402841c0300d10003007055000b000b0585c2001514943d032000d001212032000282020301c0314000340c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 3662130 1250 3660880 3660889
    0xc050f09040203040602040801060e10080601030f0201120f051905060a030f0f0c030510020304050609070605030115050904020d050601140c060106030b01120f0c09080609190c1d04020f03010902 85
    0x100c11200c1e10031540040041d040040340d5064030007030080f1030020403844d620785080106100c000c8e02c800c145081e04600004280c000059414162540840440da101080350f0042d42c840041e413010001071030b01c4400c0c00115034114030071117210384a05030300d0402c58001d031840704046032009840ca40c00340034506401d10104502c00421401994407030920b6050343e09a00704401c4070368403500b00820314080c900302d00803018015000b9500581c040c04c1581c085440e020785007079860344513208003804642e0a0004002c42c6440100b03180d00b25815040852800080400180032a0701c00d045203050320380d8030400e000340c0d543d000d881044400700c1c003540e0f5403810740e8100d03455581ea00140304100415860320455161a4401e0751140710958520500703009218160541c00c1c05046200001e20006034106000925003900041c0306018080202c040c107285c150011000b070109050800c15103501c81402000101001035203844490300c040c214403104a8200307881040001c3c820941694826810810060003580d207 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 3663380 1250 3662130 3662137
    0x40c02030301120311030706090803040b0c07020112020a0c08040305010608060708010602030d05040305040b030a0608010b060f0301030b04020307080d0305010906060302040e060108180102070602090405060d1a1f0b07060c050f 99
    0xc04d410031501c141891070405145104408000340300c1c908100200c07082042c0a4007550055109031403920180d80c039034248060500840e8000fa001030b0791f01032003078450b17404e587c000d0600d070550b881d114120000d01e803a900301c2540b250307004440c943e40d611400c0000308010f118482d0070104615081c0c00c1c6501d000300081da40d00035a0f460300021a6540e010804141c02501210010310110000b030fa102d2904030448002004540701d03607111542000121741240c0f800204803114641c000510f103003580d00395205c0740c4d0f64000003041203800d03115071140401c001d101004050710940300c2d51750200340c170b6060581c454180d504650041003032500510061202c13203200458550302c00c02c02e1901c00402e541702440c0203160040c40680c4500755200150030801e0140c40d40051415403400d940c02d12664840500b0722860805070344003c2e003c00c1048407810b14100c0f004400680041c40c125591060b40c0001e1b0b0000c813154402c0c0d12504070503c00242c400d042015034007414241004604210303040c1812071000412920 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 3664630 1250 3663380 3663383
    0x5010b03010923070e0a06021204090b0310050408040602010b030705011d03160b07060506060702030a150b0a06030603031b0b16020304031208010e01150f0302070206070f030e040c0203030112 84
    0x143c0382d800c40d10502c1449042581d619112648106180c104902d000d0040c2c0445d1400700d000e0088100045400c2d80002070340890002440443e5180a1801c01c09000600706072007203607414052540c11403103014090040b54080c038021803086c1c1d42c445c90000040e08586500c003455011b40c01401003041039a030044140003582d4007940307a4905130024800020304018880748680000b001c62800403580c040d0002c050031260b27108041c104030395200e503401c11020f0b002c0e1840003581680981f0383c2d0700000380c4440606070130401100010400c069841c00040904450341c10180000c0c5e40d911301041410f43c0411001c0b07000c503d0003684006d040340d503203403040b0042c4020018103802c080700c54034403115031080048a000f50b0b00444600f0008041000040000e072080c0301d2101410000030010800642c03421006100340394544518188181c01101034020b50445a0180d0b4413500610501e40840c0c45201c0e280302c1988241d44544404114004020444c0d0201400d8021903000b440103111050b219030313902d004613 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 3665880 1250 3664630 3664649
    0x10e040209060f0a03030503070906081b0c0a0c0b030411060901080711030903030301030803070e01050a020706030b01050c0d030603030305070e0117040203031b03070312090203060a05040606080109080c010501080105010b0301 99
    0x10307620324000c10320070007000f40d08680100001100100303055001000d9409214030b82c0d14080e40319075030801225120b90a560300154080c00e00300d44c214400c025030041c154082010141c40d4080ba07607032074420f005000d662000c11041800420003080041c0b107619015914001c907a200e040c003c40c4000244007000c0201880305008450080a0201c03404105a82032142d0040840c0c1e41e941e160b2810300201e400076510000850040c0d44409001c0d8012410340d501800301d42d0007455900d25001d000c17009409000201814408200310200400c0410700403580d01d5080c1e43c801007481d601d140303801000c840c0c0040c000020094020701040300c50383d00800700d00e05d14000b040701c000b05480d5800000e087d03104100c1d0a1680c5903020100718000800400501b1800e40603890302c00001d07100d5003080c01918440c1c14001e5164000000195030454507074400340e003060160f1000590641c46410039400c4071020030040e81c0103040895015801e0400740582c50250005000030300c034951508108180c140010702800395403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 3667130 1250 3665880 3665899
    0x60915090601050c0109050109060e060609070e060d020c060403020706050f07080c15010609080708011505040e0a0611040302130c080403080a0905010504120f02070506030115020c0402070602030618010e0402 91
    0x55a103d84141c40c052604080200603034a100d02e400d41c000c000081088070721741d0500002050480c80841c29038030a07000075160b40019660721b28200c81c01c04034000c100d03520280c2484403199108071031014256079881034004122504080c10081e00d4054298080030401c1b0b82000714440d0b10540b041038504c043c1e40300c44082d85940101c001c541c02d001003013150150844401c000050120350105001040b503200c8002d440525441780c1000d8241d413950f41c051000b00165040c10401400d180d4003905041c01600c2c15180c2c50b4046981d1403040c0d800d118483c82800c6c1d40424144154a000300b807000384400c0108082203104065800a030800e01c1c000c0028051000300c000150114007107400c80c1e04107681c0003000700032034036051400043e40e15900005a00040181600d004a82d0000030030005072440240701c0c41c11a843e05080b0a80440808003070710840c080c0f925140400e45a138000380c00010701c60040540c40780307000f205015401e802003019021404542c001040241441500281c2140d01521414103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 3668380 1250 3667130 3667141
    0x903010204051e0a080303090303041119060906030b0103090c050105030403180303050d0b04020723010e0115030210080f070503040602120906090c150f07050f07080c030606091509 79
    0x2401640e2006400641c0d40600c0c0c1240c03e03101d05000d980300b10498074000a20f460741841903882c003080383c80300b0046d441000418046051490300f10a9101c0007001c10014001e1540c0064652038039501080104444140900405815000300000c0c40ca080c81d080000d143c0945078407200c040d42e4807500b03045c000000040740506210701d51303c804c00710895072092030312a520702d001403841e8880d01100c07008628007604600c60703203024002c94507102d07000140110741902c440301c00042c19000c540d072020f440d07680e80c8490102c44001e00a491422102c1c04c850b201003840c500600c034002014213030900400002d1020890300e802c9001400d50401c0e0079181c69501c0f541c851810134001d209655031007844010301030401016150020b08640303c0c85500c0255005517107480e0500c002c0b204c80c403091500340b11007400614902c81c040b2002d02000750140c82100c182c40751000000f4103088241e08841c256070091074500c031250400304100c980110061317400400034600000e81080380b8103080240361050380c03070300003142 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 3669630 1250 3668380 3668383
    0x201050c09091501020f0706020d020c0405060607021516050106030510020a050a03050703020f07051609020307020d0c05010204050405010806010603050106020304050603070f0315060314010e0c0909040507080a060c021515060903 100
    0x42c10000346c0b001c80c0c1040e41c5949020359a0002d5800070001403003002d8904e00c4506007405a40c2c0101c4010b8061420503006608100003074140325440505071000b8441c40b512103440001c92800c1e640541d000240b01411400c0950400c1600c00c51485030b14010440c030028980c0c09030440d6048681450000b130300780c88120317044010740f040c44410b58840308040b03801403c0c04000700741c0906180e200d02e900610160740311041e000740d0004503143c0c805600520f00381e00c085e038002c000c00420a44030b030000514180e241d0001a0440d4001e0304488401d500c000014071801c0d8042c0b180300d014088a0004600742450100069503d210042c400800c000501c012940d19034029000400b418070b06d1200031a1090315944010024000c5c0e40502040321160701c00006d040405100b000c0c000c0c10003030340d081d141c51410f80034008440c20103082220a4866000001141902440410592882071602207650000c080b802881c044e07081c1e500921000718403090040a5142a0003410142016241140c0311034411000a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 3670880 1250 3669630 3669643
    0x504170a020301110c0c030703030909020a05070204050106020f1005061011010914030a0216080601090510030503031e01090e070e09070506070614010b03100302040f020403020d11010201050c0909150102 89
    0x940644c28101c0c0c04d11009041c1d4090f1050101100403035441009580815a50301220311000e000700c7c141c20424007000708107400800c0c1c004818240720345404800d80c0490110f074001d90000c80184c00c030b0305036965204001c2c850980f40c010f03c024148207600302103001600082039054040d052007103070000303041050300a40041c51540e0300450032200c1588a802516220b6119000c0f502c018000d044100d541804450303110b00640e40c0420083c1034a0313081150104c01408050460341043e080001c00200258003000114400c1150b00484502807000210340f450044040c0c01803540c40d8105a000d07800102d000409004946070101c15000300d4a89c1d620003400c0040b25084603401140005510017480340c640c02c00174410600301200c10513680e07191010003d03070101b40c0709019003007904074041015190079003040b00f20028030f45005180070b940b54001151540c0021089910180b10032914615607021f104840d44074018244480c602102d10001500c8800010850005a808601e0a2489074800c1100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 3672130 1250 3670880 3670883
    0x10813080703090f0603020403050309091005030a03030b040501050411122e03120e060703030906020d020a0305040204050604051b030406060e0403120501080a020f010e010e06030115030b0402030402010504170a 92
    0xe4a079100d10904005103a400c503405148081c082603000016024800c0c4212011643c110014509000c6e6250070072914040140c030103060044111000300b0b03560703002e0104000840c801d482c0090050500c4003070105840c0141d005510031450050454112142281210640c03440599280b850b42d80d003584442101c0010004c2c550034444402c43c2c585101407508980e42560b000f240240600d210800003143d20700c8041e284260840018420140042c0c000d80003c06450b10481c000750800d011125080100d801400c2400002a115028001581000c3c880c0c17640240c015607042c8403e02e4825131010861407145c41220012400000040512009601c4800600807030303500b406040c2090b0800400c4081a01030040c10140391000005800c040080c5460045601500b0f0b080c81c80020780055814404e4400b40c2d905021003103010b0701d030980c0c8800096018002306080348200707210b0984020110341c0419019402a03104000384005030780c00c40f06070313022134030320f1800c20121100c1603001500b01a0748420 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 3673380 1250 3672130 3672143
    0x20d030e12030a0504061d01020a0f0303060305010f020703110109020f0d02060d05011202010906030c020c01080405010b04050702031306080112020409080708030a05061203030708010311030304050310020705010c0c05030405010813 101
    0x7020501a5130250007841160125502c040e00103c400504050700030305900c040340540e100018220015018048a1503142e00030b003000038841d952034407140d003940c500261008070f0750f90005441003015000040d0151200d000c0307008101000c403c0d80030805640380b100540784581d4040029400315510541107900513a2420030510065030b660f14540e02c500c545000403400318445210201e4000c0c820b02c124901c1c2c004035401841807295010065078425001b5009540301c0d52034681d02285034941c1d0041034042c2c410f543c0110399840c03c4804a400c0090076030840b00800008900400036818442a1000003e8040303c000404203d14030f0b18410a1288600c0240a51800300401210304450f500c101d10400081d102441c075071410071043d0340c80303110803202070700820604001170000c02c10003c205c4402c175101a0859144c281c58400280c5080301d81c00000c8041030700003a05100300242805107052008107030411111f001040d507103040e140d018034011036041010440000e03126410316410489040d41202 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 3674630 1250 3673380 3673387
    0x40b0d050708030403020103110a081f0305010c1e0306080307020402090a080706050c0c0a0e0a05150d05030409060501091a030c16060203040b070e010512060d020402030718050607020d030e1203 85
    0x42c07078480d0400c1c401a408249020902400380b44000c0c210382c2c02c54115501c4201a640305840d070050500301000702c03105105000e0300440021824441c040d03075200d21707031a011100812080980c41480000c071a060816007004010007081e40000252a441c540c1100c2c050784901186c03001c241c508600740c0c0201250301c84c1440000d6484e41140c02040d10300d0200c0241c580e88204070b004e00c40d20704141d00c60400103103074503c001101c82020f41e0006030010882c91021010090b90400100d9504155006440940000a003044240d0840c45041d0091000b1708110718068600032070a08051800850305d61400c0002002601000000341141c225984400c1480a103034540d0400c04001d4000312401c0344e8950050000c0b0703c0560080b100c24289000581d1503610708410b545000181c403001400407a00718100c1d4416200581d01d9001441c403400d50b95490b5801d040c0032244048201c1419401640103145c10018480035031902060072244c950181070001c2c0344032600780860700609104412610360f01011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 3675880 1250 3674630 3674639
    0xa0803010f06020c0604030b070c0203070305030d0209010801080604050a1b0509010306060302120114010b0c0f03030f060907050310090c0e0a03060f0b09010b0901030507110304060903120203030411040b0d0507 92
    0x484101c816140c0b0355003200c404280b01c1090040344d108501001e003801200d00009004644158015041c81e0f00c0034050381c00302652a40c4035440d6800441c00c08622039004200354806580c0860014010082440249031034101a101c040d2200341e481d0025082c110000d4407501400c1004141c0c40c020314001d4005041582c1d40d0404100500c55408128400c4210030310f81e84004a05000c2c1810307985007100751a040387d1a10f00c03002c8241d803003500082030b94000c40a00c0b0540c054140041c51142400078002c000324607040c0108150204000c0c030040c2488401d109108614525244450a0b285044030010b030300b00c841e100543e441014650b50a80c00700302a5804020003080760849603002560300010321030b101c219410418450003d0103250030240c424014121a0741c07280c0c1003a5040849030034419405c24951001900307650280e0410800300700c01e00e008008003c8003190706010351145101a50440c00c0560703490b03000c521941c200600c910b032038450000c016030302e0705120301e8001e070721904503070659684 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 3677130 1250 3675880 3675899
    0x11e0504030204050a02030f060609030f030d02090306010b04030308060d02040e060405011b0c02010e060703030207020a080a020f0904110d110607030207050312090306040303090303020909010305010212060102160303110a080301 100
    0x40c003040f4065810040440c45641c1a402074a0044a031990b2541d8142ea4203414842507811426405502d441115280c04007010240024161112001805aa1240800103251410300181c2c8642d640d54800c2000b0408a03510000d59a0401021a018044074202e800010040c1030700d0b40c22140d190003a5400e02080000550020400503030540995003080b884a4040d52210561400640400c45a400040302494014000c08515219050050903e46a0b802142032040960000d5000c0e500c41c142800070f41c60710b030000002000007240d2a003406c0c41c0694458003400048490340d4042c0c040005240d00b0005030540c01d8192410143c420340d240c07141824002c1d6595898450385009004021141480c0d0960b4030468691010180c001c0409860f035039400c80050501c000180c00309582408001e80d81c1d518038041c40c0c000c1d401a0005a11000b889001504c2001c000d8002c5041d9072040200c41000600d08035103104036600360504107003e0340788802050509541c4075000f0052a000800807a05088 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 3678380 1250 3677130 3677137
    0x80a0f0c08070f0f09030201140c010203100807090504020105040306020304050a06020d020a030b03030406080c030c04080703060905060708010806070c1104050103030906021c0207091d01060303020303010513050408090609011e05 100
    0x280356503c00c00803480324010ba50003600703c40b82100140307540f0b0040c070165000b1810100c1400b40401e407986810010080350382241c109490900c0151541c20041240c09001c0003c40098002c0c12030400c1903003090390010744644107900c001060560040300080c1880f00a001e49044507420810a554800c0b02d042e90350000c1d48110800c0c0301180c9403506502c01c6003070000580782a90082d455240807904d0b00c0c003100c41142c20040120b00022420000071545850603c8100005d603c95080403030040030b2440d00c2414020001c1c80442004050401000105c400040391340d08000d140c2400b211941141c14182103107034a0603409900141010000010590b001c0c0300c8008640a690035240c0b04032960101015030030185483c4001030307000403400d20070008964002100184480e01d10300031441980c94075030035602e041d8400d50150b040400100114140310800c2c1c0800214038808000d2803500b0b5590b114075010b0001d03e14024100454014216406040030060188450f0886590100c05880043c40740c2d1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 3679630 1250 3678380 3678391
    0x10501090617010506060d0b0a1502010c1407050c0f0a0504050c03010503010b030a05030405041104090509010b030c0102030903030301030f030302040b03010305010504030314040f0f060615080105030d08010501050a080a0f0c08 99
    0x40b0010480e00e080c0620446000783e100030f0000740b60128500350700016100791000f26900c1550b428001440082c40e02d20213684090340d8002198521107003c1c06040340722b036110003a40c02e20f4100488400264007150241614104440b01d01c1c0f000903a0011800d03084003a04407503000ba01d08000e01000049003c05941201d104400900c488101d140c141604d91000c10f030020310690040c072040c0141e1500780c0008030015801d615650130186d40705031f0300054031015558039981d41d6403040da00103281400e000c0070000c440c080c002940b800001c1004281d0303e00c4148070141003100e40d040030b5010148240c044800038441c4502058030303541c480c14414000c000a590840120b032030301d007106840c004860101485107409c08d001c001480d807142c4414030b442c041d4400c00c1750415070303947c808a04908038810b80c1d10350140c50b560b02c50301581008207240ca00041042c4590501c100d1800400841e030380a821182981c0f07261405403010744580e6950009000c0c00c0d5100036070642001046c2d480a644404001d1180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 3680880 1250 3679630 3679649
    0xf030f0c060601020d1713061e060501050406200705030304060206010e010e0c03010e04150f0b03071205190f05010504060b0f0906030c011107030b070503070807020304050f01030b120105010906 85
    0x1502c0d8240166550306a00717401c9000310b0460255131344040180988180d04c00051710b0144094400369860b08101d61183c030b1100c0301d0852040c880c142a80c558860751016120031b00b0041d103041e042100142130380220400101d006140300444202000007840400002c10010301203035140c030703280c44019403140303024020a070300102100000104140242c1c0d006002e01440c0203100d1a690a254954240e4100100281c1e40381503407500020b01280144144c2d003916042d040d00240c450b400008240c102161035000040c040c440e4a50304011a0001ca011070000c003400125030000d5580d460885020004440c0150a9520382003c00c41403107a141c01880640404442d01d0828601907001c00c0185070054070095090342c0940005425540a01c0c4031403d905010822103e030503a5941c1d441036540d200700c41b0130340001c0b004418046625080700c40319400103030f14000340d81001d04000c00b01e540110100052410142c07510158a00f548401e1080903181c0701e850003c0c8219030319213540c0740207081a440b0b1513428 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 3682130 1250 3680880 3680893
    0x1060503180304030c09020a032009010f0e0916020f0102030703060906050607200a030804080d02060606030f040f0311010f0b1002030c070b0904140109091b0503030304030807020f030f0c 82
    0x11040071044030f090300c0d071080b152411641003043c108002c2d00030501400034540d07120311000e0760405441503401c0120608846980d107100d0f40c00010030140d000b049030341c01e0200560b203500099940801050f8800307a803c1c030070005070b9900c201c128030780000302d0240b01d4070703520020910841d5079050700700030188c0340c0d400c009009050b03a44003800f906210b0128094441c40341c0c070844000715460811000b80481008006032052034031391300d8145d403d034829440005298054210094088d03014802282e00c40d104039a0740f401c52401d003001e8003507910010300c014020001074010700b04140c000c0b10855011039100d4000c020340e98400c18500300501110640d50b2003040c3c61a0a2411310f44000304a503842c140c48005070501c140780954140494100d00301803648030b43c44001054014079682c812a000b40f5101c480451f8400c0749007409000070241e15044201940b6042c03080c0a1503e002003180e400c40c0d030515003d41c441d42c640d00c04905010060488403a14000002c40b00d174903058034000342c80c40c0d04681054402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 3683380 1250 3682130 3682171
    0xd0b09010516020a1202030408030c030702040605040605030d0302090402190305190e03120a02040305030703020607030b0d020a03080a0c0210050a030e0303060306160306051809010c0809100e0703050601060503 92
    0x144511042c01c0c2d40107a2040201000141c50a42e5604050813180107d83c04c180c0c40b0b04109045400c940c1c01550113074000704410081d850701d40109401018107481c1001400d0424000c01e03110240185a40305240e000540300380c10b45c84590450700c102c480881d10100c001102d800041c007400d4142c54050410052040070300030700c206840b605082e59281c0e0010351078110340e10007034000000014000d84030560700303100010204030140300a01c4810311a0303025203140e15101102404650803e0110360161001400c580d005844404a80701a203030004038550b1280003140d02103441c12005500250050030041c103072080560008013508241607142c0b014841001c1000d2500da0320302089a4442e0b05034080b001088080a400307175400d10034001341c5404180c044c5c5a0020408000b481c140609502c621070003007088445003880340a540360704e18034100b00301d42080001d0380c1c0c0d02c1c1201500681015681c950b500c01c072600400c40d240003142d102c1e003a20745660351100301070030030f42040350b1101d4401e07020541c040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 3684630 1250 3683380 3683401
    0xa02070201030c0201110306010e03070803040b0a0206100608010909080d0603140c040504050601030209180114010603060801090b0105090a060f1401020601081f05040314030a0c0e010e150c0c0d0b090105 89
    0x258000d9083c6e1510b0659484000440320b115204417040c0c3c060040c80713400703d00c1800510081000c1c2941180c040e55820304400b0081c501400100319840d484100030080c082d07c0c0c1d011032083c2c11101e04460103d01946581846040c030f01c1844c0c4040061843c01d00004200200b89030300c903258207200001eaa1121003c034041c0010346c1c004641c010100d800401c0103100601d8a1a03416400c00e082282c0c000f0030140ba103100300d08541480040ca448540c010004000d0f490740340c05060042c0c510b0b40d0003403200f00110355aa140c48141070048a106051040021b88002d416503c41002800c9403070074105c03510341d83d17040701c0103c030101001c25005014200020850600001e1048000641030b003401d00c01c00e00c3d4500f40301c0101b001400071020009054061395440c2c0041c0301848c000d070800c3c40002109501304101420345607000c20410705001d2841080742041da218000800e01140e83d0803d2590b03903806204190801840c40030107a03011720ba001e030b034009006d100c3c000140f2543d200002084540c0b01c086a41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 3685880 1250 3684630 3684641
    0x60121020906060d0e0a060501050f04020c030d110d0f0b0405060303030405060705070809100509030106080d0e0415080102070b1e010b0306010f09030c081005060d0c0e0903040e0a02070201030c0201 87
    0x307908489094003040305400c0a2008280016811a0008122403400100307810f00e0f41e40a029170769aa1600010301651901c03810100002904132821032914901d0040a40c8034000c003901480070035a00c2c5004140700c0c003800c1c211099900584010016000a0311039600284030700d01c0910b02541c0f40c80001283c5080000481e4016904a40105007a80e036804081f00e0582c88001e00722000c040078412091103031200c0d411494082e41d161511781d1a000310030145402c40b100765001d080c85601c042001044160403410038029010706a40100f0001e40745020726414028540c440c1c81d60b58800102c032014840750783e00c658001c001143c0c024100e4085000d0ba42c0c4000380c05c2c00f40c0b003c03245040010683d150f0090801809205143c10305100103a902e80b14081117018961201c0240c0d0403180c41c0054280003440380b980d01c0b080443c0d681d118900503031a849004e9030140544103013004404040b43c0f0b000c41c10002d40d0300800341718880900c01d01e88440380360040d4001c3c82040b40070070304001050311001e0060044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 3687130 1250 3685880 3685883
    0x14030c0303040b0d0b030102040f050102060702010506011e09081002190206010305060c07060b03010609020d0606030e0a02010f12050702070608010501030b1806011b0804030b06090106020604110109050d05060121 93
    0x80d401c003400c01c03407400c03484e40c068494540501c3c0e480c1c0340c1041a480a00107000109125034020380020302c0c01c0c0029080240040c020030440e45410100030540e038000000c00b81c04030132007d40340d10350a903042055464160036000b80802d031003500380e105402d000680080410300103424440100e02040401683c0c0c5100a000c010595000040000c1350003c82001030508140aa68041240404100820708440540c6c1021b13200d1a000504000950a20701030703000140380c940307000c10114400051203501c41040b44e00090420500e4103070903056038420410709a1410084104004504044902039075415181c4a503402182004000084c40d42c0648a9100c620b00040c0c580881c0c4000041e000850304c400510316818040c2c04c0d240751070041c000c4280900c8141c4254a40c07903549086081c03069000744000d00b81441031103283c0043c402d10743c0c0071032b90769041980401c01840b1034810f0300042e038007404960401500207501c44904d4043c000300094190480700b2178186ca1031041000403400e511710041510 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 3688380 1250 3687130 3687133
    0x51003051e0c01030207060902040c0f030b0a0302090a050601050c060903120a060503030d0906150605040305120903030703030903020a1a180d2c0405040503030403020105091b090712020301060914030c03 89
    0x2c0c0d04585500030380060015501c6014001141402c60f400a002c8500003000500007d0310600c001c0031464141c451110134490072100c0750000307407440c4d00045409030001c002c1003000f521100032600743c7c3d00072810b031440f41141c0c0e001d503800c03072411151403982e9420901c0040440d00b0100c0c080b801d01c240901c0760394240c480c05405189480094811000030702118501129111b41c1c45d0b10583d40e40300c0b01d4901c0b002515031565070b50b59492941c1841450302240c031207140e0f00100200b12404007aa03002003121201641030030f011803a19010f0400740c4c1046d41d80d000c0684034031401c17680781b1403621080000c1803294000c00540e5120405d241c401541d2080c2d11400c94000c01c4210720154400c801007140c0c2100c0b0001100110341c407100c100045000d441041d0390483e5980e0010052008268080c020198401041e8006000074046050300c0243c0d421881040ca02811146010400d20380c0300703060304100c00100c05030940d500c2d40c1d6040000c0c001c5006100e544013809120913003103410302d404240e0b1581000002c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 3689630 1250 3688380 3688393
    0xb0a1208030709030b10030302010b0306130314190806010305090d0e010c11030102040602161e090507020c030f030a03060506120703020901180303020105070306060302070b0a050603030904051003051e 88
    0x192156501d50028000c0d8040c82407010b0700000064907010b026100722034071218641100e1035450040d09540045d001c061080e0400da040042d00c01003441405407550700b600c1e1185050010403041a0113114580c40c210645ea2080c2ca06800c0c1a004250903004420a86e020400d681c2c601c0042038580c0d451040110004940d490034501ea9032142800142c154011103050b03c18a0031100001c1c226403055001902680004d2500d003d401190907011000b00550810400c071142e000c022a009040e4a0003401e0701d03da030314400b080600340f00300016071555202908517460903c03c40304465584c1c02400b131040010f81050790201b0203040c8102070f200c10991420f01c0351042c0d150380c0c40940c0a904a498198104000c0e490740c9030380c40c01d1080c4c07594000c40c029000007a030b90038407100080565038290003400c207050040014030000350704158115400042ca10700042c0645032040000c0c118468410b195078028285403c0c80310340020400c4c1101124400c4080310003080704144500c22000e08480a80c50540246 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 3690880 1250 3689630 3689633
    0x504050703060801090b04050d050309060106031503020301020a08090106050102010209010c12140d050703060b031501030903120212010f0603050606070b090a0f080a080c09030a110609030105040f03030b0a12 91
    0x940010340c00400d1401d01048460300d40c4411804c4441d07040082e00d0a0b50303414280001d101003400100c4003102c00e45030243c654501844604d1341c8035010311900c02015580d84114103411003260707502002d590f0050080d03540395803284000b0620380c41658102c086528045000a032507005108031030002c00d06841d403151421141e102d80701c0c03040812403800e050000107034034030703e001904200411071034154000004c1c540c142913100400715020742e00002c00019040042c0070080c0541d03d8144840fa609103402308a880d464501111000c039a070300390003001350012440c40d400d000c005000b40c1c140e5054800d40c00015035148400c8043d1081070701d1a5421a0701002614041280140c0c800d0744442900b0413144d120042c2c3d51380380313403442e041c0509881c2428040707480c4002c42c0d4052517064000d8050340d801420500c101e00002d446003008003004010a60004003a00180c60310f000313a420b4040e000b002080b1610b001d062446001c80201802c40000e0b04c0c00d40740004c9458004149400d41c3c80070807101c040d01c00c15 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 3692130 1250 3690880 3690889
    0x20a0912080d090302060a2003010e041b0602010b0301050603120f0c010207080f0301080d080103020108150a050402161205030103080702010c03020a0f0507080f01021e16060203010303020a03080a090c05 89
    0xa040141e4110100304100c10b0340e07403154061040303100d00c240d0003400d043c6080100720089441d044810710700e60220008103000b20091100740c0c1d05460401d100400c031038803185000310410355800508180c1c17940c22000080c1603901035001404601d0f0507002070145a079454200f41e1550310400c2e02e0070b048002848804c08952400700540031100c900343c0010b02d00820f5458402c0759402818410171081000401401211814840300020040a0907c9802c030f506650003c1c1000c0b000400e28151003642c02e9a05220340d48040d00c2100810024204558a03100595200f240744602c000540322100c2240c180303400c1c03a21039070480e4105d03074026201c107050034802d070700440342d551800da0150114400c042c0300c000450006e072541c0110f18855402006240d00d4034044604090305424a810142d10611412810b03412041c0d1100c0c1d504810145180d0b02e0155801c07242030000902000791680348044004010990002070780b081d064003d8440c80143e82d50100342c1c20940714000c1c1c000f401a04480e03400c01c01d9041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 3693380 1250 3692130 3692159
    0x70b07080c070803030406061401021504030302090103180c0611031e030a0b1c0c0b0a0210050c120901050604050c16030804060219030209090a0203130305070203010f0e010902040b0103020a09 84
    0x1c40703405035030b609640e0b600303000d14641003500d040c0c03140d644d036080402205184102c01c0c02c040c0c200f030000d410386007500b85803142c52510081028043c1030b00003a12f030810384e100390b00c225498404502e0b40920240f441c145601c1c0c480c9a4003440c0c020601610595000e8440042a100001c102640d03000c890701aa0604200e2604050400c1e03100e59210a0490740613541d003001040c40f25030b400002140700d2650b0500c0000d002e0298444003100300c04000c044c10659010810b034010a0281002294a49562004080c58410400b12144440d480c10078080e030301c117040d000140641c030210360500050310341202391440b6215400d0781800c009250201900040c3c0182c10f1958010300400c40103080500b00464081089a052807060009500084220003454112000f41c0c01a0481c0c50842c00c41c680152180866001c00c50050706112020850300d0440d0b4003500300140e0103e0304d01c4180030100408d24603031701914a520049105504100c081032039540700340300395040541140d444081e11481e00c4c085000054 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 3694630 1250 3693380 3693397
    0x617070206060307060c03030605040207050307031205010b07020409020a080a0803100b09060d0c090305011104030201030501090e030906070807050703230109050601180204030203010c08010608010e0103080a08131a06030708070b0708 102
    0x5841c0e427800141691548003030000d481c00364001c0c641d01c01ca5840c0051411802000c0c0c442000c0c078100c01070004075841000d0382c4225a06550015800b10640002800b003442c9910403036491145c0032106040011010286000c0d03a0380c594074000168942004a21500801c0382c40d0f5080b40302444007005914098000380400724041c181141c01c10b172203454090955078036101e00030310850300082c10821540d144c0301c2c55004188a280030045034040c1c10314940c0b60303c14a56001c3c07141d07101040b22028030000e20100d400b01a841421541080e999181200e1a162000d850b2901e00f07a0803c0d68401801043c094429900c0e0710030040c008584c2003d0031040250500c0c0c5050701c409509000c0407005803005d20900b1961240b5071180c6041d5850440010a0001c0582149030074130313869801000001d4081d42035606190031800e11452a41d81c11040d00c1e650086494003a01a044c0c44c07001e903544413000f034100d44c01000140d055803082030700c0d03100480c2e88203064800c07400a02003c2000102254140020300840c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 3695880 1250 3694630 3694637
    0x10203010605070b151206090f06040804060309030203040f0e06090609060904020103050c0f0d02030105040c02070b070312020c100603050c030109050705090601090e010608160c0803071101060803040617070206060307060c03 98
    0x103005d010003103041c44100e020389030702075407146050151840e010092201c50700400d0000700000c6c43c2507914461a4082c80c03090b04185610703840c81c402054003d005a401074840754807120441a5640c0d0f13103412209003035036914081d11070000854402d08064640b10300c1520054400241c0d500da941c011402440010729006020030144010b4280c0009000202101e00c5282000b40c1c881d4145001c2108031500a4107004c29507000180410401044200f07584485425040c24581038004150440180c440c00b901c03009680a040301000c6807038401d0303202c901a60301410031243d5648618003490300f20354442201900c158400380b000c120529200300100e50082c0d041c5010110a6a02c0110354117a0000fa0011004201c40100b0800401401c1901a000e80a2494141c207111000d8695040c9440060b0804007040140d00d4000c030401401d4000000424071601260759443d904c180041c80301000c1c0000f0310301c01a0100c00f00f50064400607001c0c1c0100070090140c00a6843c0041c1510b000d007400000303c0a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 3697130 1250 3695880 3695911
    0x20604120b0406050106020703020a060f0201090204020705030705010c030b0604090e010207051e0c0d080a030e0f03030109060e0108010504030905120f010501060507030f020601080c04090302030d020403110909010203010605070b 100
    0xc4250084042011621844281c140c80c2403500c0e2082c180c4105070054001c640c4001e6040000d656504c003041d0459030b10b400d08400c4010426002c90140c03401d8400031750068000100e00c401c01900200400c4060f000d10020020740c08070010440c1030320903009105600140a000500404403d80d206a0340d407594000010310b03005040d40c45505007660520f0506500318040b03801c0c1010304c0705010349000083d0444000c5c14810031661080f189000e07030303030501082580e40c0039200702c140300801c00700c0e60000c071400480c0d4581da5280804005022507020b251030003038054000060515050061900803075141c0c40c1c200e4400e0a103070900264907040d1050301c1c1070b40709070800310012910a10070140030f0300c4180e075500d81e54117040c01c0150000000442d01d0b011907101c80c0041003004404102041500e004a5002c6050b40150408a180d0300a1440d000a4584001000030030811400d000090300101903400810300c6c3d40b0900b01c10300301e0002b44074030070101c0c404000210004100381201940300d620443d20120 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 3698380 1250 3697130 3697139
    0x30b010e0904060c0813080304030c02030a0f05030306010306060309050c101808030301050114070201021c020102120c0409110c1504020a0e0a0c12090201020703140114101404090816020604 83
    0x20115000c0e02c09a5195540d000b18250a0b43d0040e0704d503500c1318100150b2444031403030b0383c0d40010740d01c0b008001800b00640000a04119503050100e0b402864100c0cac0825020301d00e80c00c2680c0c50341d0003076506c103010918014001034914068000c0600d03854024018011400c0007c060102000c1140d00010400501040300707002d600085640324040c10031007000310340300c0d81424005842c038a130320084100c034006e00740b201400507a80080c81c40d2403030003542100f61001181c900d060340079015201c0398800803044c00c0200304e01d1100c808041d10848807106c1062203004110034581c0400e120703c001c0281260000b1801856162000100c1a04184041c001c00005561004c9040c00b81c00c2c03e481c8465282c3e221a000c16503503512504008560000c9101040720003c5640083d40d5003405102c0140038050788481000d55a82c294403a0740034400c8924040c02501c0c080200c01041e90302ca01038421444403c1005000c5414148106007a556100f40001c1c9042c420ba0200e0380003031607811040703a01070310810005c038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 3699630 1250 3698380 3698389
    0xc0b01090203060415080303010819080901140904020703030b031203010e01060507030207030c030302010203060f0402030907050f0d06060f030302060c040e04060b040609020409020711030a0506040201050c150f0a0b010915030b010e 101
    0x2000340881b0003d03503202c1d418808218105600580c2c580a14018400550045540042145d4200c3c03000d0812075a80d0034001c11450983c040c405555a100b03101040000c145074064000c200c0301501102600c03240003100001c108a404207029140141001800502c0454040c800074500c00740603004641f005581e036034400d0541c1055410440041c0d4012080c0a400e0034003203480200e40a04503829811403503c40316150b03580201d031040740d1042480c074485440700d44419447d4032046401281c180320160715260122411241c40c4421801071140d0000555003a0f0400c003507500341d03601c200040c45561200d45407038029000c8211040c0e0301c90b0751a240010420140e2008100038000600c001da12082d07617041403c00c0700841c04441d0b000f600090b52200c0007a1011845a50207642400c0540e280e42103280d005140c080c2420504110a40500601c000c050020007414800d8500d4981803000440f000700444010b210ba00c541e102070400409a00660b501079040784542200601d09180e07440d60400008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 3700880 1250 3699630 3699671
    0x4050301050109020a020c010c020907030c0509042a031a010c03030e0d1107060201020903071e0308030a1b0e01020604120201021201030609020414070e09040c080303160806010c0b010902030604 85
    0xd01e6580050302a1070301b9018032175880011000d081000c582c51041e008a800742c580200440201685c4854042d25280200192101c0b07900c044c20403c640a403001036048050150802d42203e4241790400019040c46806411284442c08800050500402005540c4118005021401d041c2c40d00400c5031101c200300010f00d001302013581c0d603c0406004000d843d0420055410401c11a401007044803407507200050010200d8014101048001e00d0b011560185041c0c1da8200a281c11400400d00881c6010350300000103200c004242d001c015645060700b512f11000c0550020f0150b08a440041d001c510103c004042a04a50002500d03000307101400f23990b22003003604201c40d5903968909080c1035040c01d00c5032030280ba0b2f20806c0d410300b83c01c002c10083c0020003041c00061084035503a00203820400c04403000e100410f088021613450b4140840403460348100e0024000024040c8800138405622a640024040d40c00c960f00040c10307400c1200e0500658802803490350403035201c6044031400d4084c2c201c030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 3702130 1250 3700880 3700889
    0xc01150e01050406060203030c0c030403020a0b12150f0108040203070807030803180601050102120f07020607030e04110406120207050106080307050307030206010b07030e130902090c0403150e0304051203040503010501 95
    0x418580d0610324620480c42068002d5030141c0e00e031040c1803003900d4001044035003180c00402c04503121007440f0607a91031441a030b00000d40101d40680000f13462148135000d44040448111030300b000d42d813190402400382082c4065540e0084040d00f00914a50085034210340150014054034925078a8481107454080154412903007540008200710945d0b950600c4803500c008103001400c10340d450240000d40c0d40240058071030924400103241c03422404140101c4403200e6000d0711340c07034480100c1d00340a0440803503091014081c80c02c0040041950642c2c2c0304071425106a622041d45040c004a410303802504142c00448140d0f6a600001c203c024042020700b03200307880384000b1682c03080d052400904182041e40014416035042c051240020341001001c02c00392401d44641294441668a80019009500020b501301c400c0e11306001b0b280e18520010000e490283c902011120819400b1004840c260b440080150300284400c2c03003245011241c00100d01104401c480c103150722a000a03003180d40aa21 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 3703380 1250 3702130 3702161
    0x30605060c0a0209090304031101050d02070c06080a0f05010b0a030e0304030609060c020f01050403090e09030d111e04050f0d08070602030a09020a05010f020703110a091104030506060901030f020907050c01 90
    0x400004618220030980d5011005c1001341d0301700b0303140d40c0e0384c055000d00e80a009810b00801003100300c203c0550b603060340d4001c0d800c0803520b40e05558ac0d9002808800d420744400d5507040c24980107005002950040c1030407515203c0280d0b14000c0020300171401400000c041c5034490004210000100340c0c42c0c0549e505450003020002208003455101901d4480807142d05400340e4100020040440d400c07007004012104111004450b0359201d0002c0d078114825006004403c40c94820a03101581c6414050f28004818032002c402c84811703120401254021880380c20ba006401c5011004142801d44c1043c0040c0d1048064500304441c907603890087c0c1e042243c280c0e0768a5500c0d07510b4015860040c414078000c1c0801c2c01c040340800840c3c50003e45804150002038004101d00d44588016121000304400030001c18104010340e00000201310b00f42d900510040c0c1c0c0398400c0303901003074552400041003070489030f00105440c0d40d40001d509100f82079800801d10410320806101c40da000d400e00b8003400c51102c00101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 3704630 1250 3703380 3703393
    0x10b04050609040f030c0317090d0f03060806130501060e04030c05010b0402030405030702040c0e031204030c0506040506040603090303090b04150608030c0a06090c0302041118150a080403030605060c 87
    0x4140400c5400040403036205060080920002c500300e1122602c4503501442c008407020403504041e01d00322040900844002400c50400003004008980e104602c5166903840004444100041b000d0740c0903400b520041d03401130400704052184035000c90103050321580010503c107664158140ca01c4408581c1034010640c2d00c0900e804100c0700f0f205540510404440442c00c41c2445c1d00da0076034901442e00300030301455550380a41c040c00e000d00d142c00c50000e030080484002113441003c00c103046e0040e1001716941e40320081c01184a03e490300c1907a0075210007800d15410185007000841c081e20458100f50180341e41c82e001040440c1d92034041e54031a0340291041109154800d010790b080b11060751008420746c10034040745040d1100402c0348030560350040c0340410f003002c550030550030406160344000c0d4040d1821889044201074a005002032244d50440e42d042c030089801070103a48100c1c3c00008000032410083c61035454040c00795150428007a141c000b0701c10340c0b540041001d5601242c0d0349032240e0b0010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 3705880 1250 3704630 3704651
    0x60608010611010501060e0d020307050a140a0f0302010c24050103060b0102060a05060906060a0207090c03050708070e0102030d0c0c06090305040906061d0402031b04030c030b011d06010302030c0702090901 90
    0x18102c01094064020040c1e985001c0000700070200071490140301e5512459070b002595010031a1102400b0000c0030010325a950345c6101c0901445110664002c458130007000421100100021080743c1d010784074180309014554450350800b08462a03000d42c440d0518a0303080c00c40c124880c013406140300e2480014581c4ca681c0019240040c020070107400c40d1300b4a020002a500c94690441d000401510403985900c41000164103025640d0000803070703a45403a40040d48240d00d60401400f4105980320303070300691a020421145400d8220039240582d0082080441c40200d5500802d540381040c902004030000c00e5a814080d24860070090700020004682800945402e1050303000030405400c000201215050715106800c102c41c184d14403070359000c0009041c200d142040f060300c420321031103401e6071940c50b4500307800264400d004c280d842060001c004106c0811000540e0400500e5030386a40c0155900c10044000c1e500c001c00340e07012400c081c0500d07001600d4031422107010f000110008200c82805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 3707130 1250 3705880 3705887
    0x70b030612010203070903060f1e0f050c0301030b0c0901140c06040516050a09020306280f05011407110307051e0301150617040204090b010305060601020c010e0f19090606080106 78
    0x450400215a4410805d000c211508085d0110469a12200100c5d01110710031514009220b040100b01c0d41078202c2d05140e840c1810360780801515100080d0801290303c0344185925140024007008000c9080c4101240038031030142c02400c03250700145004040e031b180450181d550354000b8500d400030740d40728400b4481002814080c5114044c18507034501025840c110000d00303901c140e441884413035a03001010642d140c4402d002c64200030b21103215100c200c1580321030340ca0f04440c01c0c844c0c0400340505010200345503115031051340705081000c841e2410725400e920307020f540143d240e0702258184640c1c2c0300000c041e103680e2a105c08000030409140d800305042c20a150070344802454842e0f001c0413030401032108541003000f07502d41c0304205020240035034607440400c0083c882d01d840680103042c500300000070071100184a9119070f10a9083e20201562100103441c0c1307501005919506c2501c80b403043c0907a003408003100005401240300590203585c4e441996080701d0840c0c1003140024003540061000742d40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 3708380 1250 3707130 3707149
    0x40503090d0b190b0d0206030405070e090a1104020306010801090c020c030105070f11030a021c02010204050d0803010602010b040b0901090207050a020603090a1202120307030504020f090109060504060b0c0318010c05070b0306 98
    0x1c0548044c041401c4980009810340d201a000900c5071802001180510408102c40b8001c0c0001000c100301c581048240e090340c40d181100100e03005c034a83c15290050b41014000d403405080180c41c2c0340c2d0940d00f00817152004d00104030202086219210300c0d42525982401144e00602c1d0390340ba50740c007292941000500c00088401c44480075030081014541d290f034005603842c0714100610300308a00c841d2281080b40603101e190301c203070740c040c1040c2107600621801000841c100e801030b0300200314002c0d8010070b11081c1d8a078001e200307038009101401000400c0650300103110f6240b00e842902d500c0d00c950b42c005190303600292060407196104107a080204089004d603564003082c2d6000904441c2d4000b9147c050a00c0020b15110401d9240d01c00704045448804200315440002410681c10390b0710b82880000605041c816144144d0130408001059100c80f0100d0b441420f403e00651303d0041d60440500c20320210110290400c01040d41a06c0411011302c0341c40c0140c0610036011b41d59081003402c0002141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 3709630 1250 3708380 3708421
    0x6070b040602030a0e011b08180601060f0809010903140a02010204090510052b03140403060504060b03010606050a0503010509040c03020303040305030316031415060c0f01020309010c030203060a0905040503090d0b 93
    0x30f141047d180c16000104003c1d40c5207c000340340140d0b8580c0d40d031000540801204401031254820a000850280d4100440002a544aa0390401d65640e001310362400d07604121405000314001040c00d440081c000c8004255243c22400054a07040d82c0e80108001c0303e0701196031442c0108000403e03c50340ca0150362f0203041e00d107052650326050301160703082c1000c1584814020b00780501b2220601208010109407001941c1011040110b45040e06009010301600c5001c00c0c4254a4200003144140c060300560b1440121583c54904680c00d04080c045000c00c007900542d0f084031f1500d00080181d03010801400514454005036860b4104080d481c1c0032408a184804241810500d80c41c00040b503440b1140d60160b041d0600d82c01800100001c41d1040c81746e000c41c00300d0b0780078080c40c008200c44150002c50062089030001c00045050800031001c90105503200e9500003a540000c00c00003029400040d0840d0141d01a240b5090074070340058560007803140f0440c1c42c0354154003006840b13400202e07070314103a1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 3710880 1250 3709630 3709633
    0x405060108070c030f1b150e0105040b0a02030a090b0a0905010501080d050a03020309100603120311030f060103020a2a020306010b071113020f0711281e03020d03110f07050102100b06070b040602030a0e 88
    0x3814280e680700b416140c0244102c810dd039010001804c2d00328150404500a600b1115000031801e02101c0d0038060000f50001707844039824800000b0f5480e60001d62081178034010390300e02c2e081088601045000e0750001d8141400c500c0340341000304182c101840b51800440c41048100c01c02a40c034400a015500e060002d0040b5031800e1080004030405240b00c00da0200e401d180040e6a4800700740103441115910b5001143c034170101d8050600b0504000d400d1000301e000300c040301c459030780c1d07640c4000b41d42c0b007a034100600090f5075980708030880c103040c4407000803154038041c0582000400344521116810100050390003140d4601d40d9940c0d418201da08254408030f81c1c5a18140142c0b0032800050a07209204184859058120354980902da105600c405180d00420180000c0a1420000d209140c03101100f01e80c3e01541000007660400051030070102c52040c5c02034000c10031034403078040042011000301e6403c0142005034000080c42d8601c0248124031441c001620b1741410350380f001c11101c0001e02280036 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 3712130 1250 3710880 3710891
    0x6090e0106050a030504050a0b010f0f080111070609030c080c030301050405070507020904021011011107030806010f0206040b10090c0309050705030102040e01030f020406030215090405060108070c030f1b150e01 92
    0x840c1d030b0000c102d6811010301d00b030108203a110783c68541c3c546201824050b03c13030421440081a0307a100e014090341120149d070005e015041e00c0b45503032401c0b141603200f2041c5400d800c001100000740240c102180d958000c0c1081d1624660726241d0340740079800540501030a400003c0144917524145c454039030090200e20f041740c00e1041541c0401d104180180c4041d00c51800c1c0c882ca9001944950b0200004040b40d10003484880d450300c40c03820490b08118011008510444006840c95100e036003440d882c80c0f500c0c1c1c001c00d000c0e00c0c3d035240c00480d01800b90451584800d280d90101e524445406800080203240e82c00180c02522818850b08016140d000540700f40d0042004020b044111522581502e030480c01d0408008603138070000b00105403d1344000c0d0401d85424201c15180c854201901c50b41074290380038040d50b940c040046802c084201c8000e00403800f2400d8000c0400d22503d007001e40c010036400c0c4441c5070003c820040810510b0f10300304440d840c150b0f88203008405028051641100c0c1c0540081c4103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 3713380 1250 3712130 3712139
    0x201020111040620030405060406020105060a1d010303210203010602060717010f0b09060408010e06040b1006050409020306010905150d060801020405010804030f0c02090a020c0606030708030904020706060302090c0406090e01 98
    0x41c960a11000301c0301a83c0c1503440f07585544d0600484004100c02070030310b507440d652654042c0c0601030850f01c4030303c10240c124002039046210242d0300717410302030a800c4c0f2180360308599043d105201c80e407803c010f08041650301954014924802540600b03103a4008101a15001d440107111a40d000049000001400010000a03140e044007500344c03408588030b2a01c521010380400c0440c0290341c0403142ca5030238030708080101c12012880d00d0040b030043c2c18820680e40c1d0f80c0b0408103500c0d654420301c00002c034200000c11240781668040c58000d0030524043c0c244070303611400608564803100006010303900008000e01c0b04040c0344281e0000b881c03044002e500f481c0c42c080010703214050040002c0e060010074001e0a02c0a441744401141496009007408554203101650100030f404c080c00e0417034207100b6070f00411114130b000a07103c01201c490400551502400000348030187d0041d20040701d40036221440800142e90702c0382d18500c9244030b40341070303524bc1d1714086000300428510380c020082c45201500510 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 3714630 1250 3713380 3713387
    0x90d020601060e010c050d030e07090b01020705060319050406021809011d09030c01050906011403030306030703200301020409021201150909020703051c15060201020f0304060e15040302060402010201110406 90
    0x1d0445500c3e082100c3d180d0202401600c059415504c0244140a01002e21113030603015480400b43d40000700440d05104c1d101c840c01822540143ca003039001d40c0c400d2008001c070345000c200540e4003080811403807503003c2d80d1684600079103005850480700150007144065500442c032580050000088502101c59450945908680c014070f0008070410380000c0e0000c0c0b0502801c0040301c2045480c0402000645402502940c0b619400e002e5000c0c00030111151340c3e800c0c0b400009036400780c00010080c04401d80f0316580d011900c4000d030200132030b06a5000011a0700c0e5403c1c809400146a54003001d6070740e000904040701000c10582148250300340e4a400c1e13900450380060030405444d4003650069884515040030790795800355203400d0f19003e0514001e60038070b81c1c03150000c5090711020b24028941580705c0000ba400d074054042c84a50700c4c141400002c0110b2940d401200f04200a001528880c0740541958094641c0454081d4056440340e0240002c43d642440344090b81044104028241401d014004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 3715880 1250 3714630 3714643
    0x13020a12030302070503070302010c0905010504030809010f030f060e01090e01090803070c05010204050d050a121b150905071d01080304051003150503030c0f0c030a02100804030903020d0609050105090d02 89
    0x2401034101010300400c0500035812146455080b03405c0301c0e190b04c142d01d0001d01914411a82074000f0700035502c001900d5004009560640341d10180e4075003041000001110342e5914044240704241e100c4151403145849403007800007400d8000c030140f8040d03040400e03c505a81400ca03d94026a242ca005103000c1108001a070f50400b4040c40c01e510740c2c070514202540a07001e81d41043c1c3d40070700c0281c070400802034009140c03c1e0a0340314546501d14050303c0c1d00183c0e0580b21100c0c0c0100f008021400860006000092140707c0c190641e0b800640204951201031070139440d9003108003021342041031410b0100d141c400c024014036030000210702c0d00f030400020403454465a41498240740e26142c00582001d19210504050500901240d17162940500c003280e480e045560118024040c4500c08203c0341030100c0c2d1400760316000b50175000c2860880c8012a0784410040054080201d07901e004801030313940c5200c0014041c0030300404220580b9a003030040c03c45030098041c1481d94420000e03030390403030340101c0c41 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 3717130 1250 3715880 3715889
    0xc050607030c060507030504060f05011a0708040b0c01020301180603030e06030a020705060403020309010e010c1e08040f120b010509040c05040b060f030c0a0201050906040812070e1305070813020a 86
    0x2540c490040d0315065640c50b041c024010062400c00301000007055040c1d00a610440c0548414012a2028a50745d0308480080c020030019803d040b0300d46903041c04540c020070040d440707219001e103010380d5442c49043c15041803d103015aa50000010441000003035141c004140722040100130492841e50040d103542c00d05040107000351000303c0029041c05169064502070354000c030580d011844d01d850004e440c0d52007000d205000c40c0d04000c0d102415489210f02c0d4103070551004500d500310401d2445054910402d070350844075100e08200200d80382c0100c0359480003d244807050f050003070780c041c42d100c1c100000581003507006261410800c4041010300f11400125a01038030001800c00030717000400d130300307109611800496180000c01d01800c803420400800340c2c50241d9000700210f448110046440d03480980307016280800620020142840c1d80d44115001880303400c0c20044950180c01080000642d240c1d109541903a13074081090b00c0b030f040264154400d42030340c0b043c0642c90140d8005011a16103008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 3718380 1250 3717130 3717139
    0x8030307080406060b0a020c01090f0b0d0b060412030e0108070503150409030302090a030c050310050103150506041503080a0311030105030a0305071115030106030b0603070909090201020709060605040807120c05 92
    0x202e01445143d500c11006401c071102c005541d100c01d01c002940c2e540701548941c0c00990680d0000480c40c0c1900900c0041e81c81000303030189080e4440c04224064889410040d0b070080040000207480302e0240799036101148252186d06280003010000b40c8001c4006210a084c4581041080640c803041c0d90358841c2080c080f10000b4404415040480003406121074242e0441c04101d8041b0600c00c1480b003000c00c8500c00c90440e086100c01c00300144c2030b100b0078400107114180d1060320320b5296134980c100355400480076100003090528412100b9202174030340e0003035501c064005115035140c3d5060284581e803c0705804104d2079545800c0109545844000001d4100f100119442c01049440c070a131080601e0028035403021903603112554140340e4001e204140210b441c0c0707007880d200c4d81054015207114407841d0b220604060b01e403032064009032401d400e080381140200480450440c5070303441030700e011385101d1740c4031511182022102883c2480795000399402085400302000010140c10824007500c0c0183e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 3719630 1250 3718380 3718397
    0xc03030c05120406020c04061a030f1302060f03040203010b0409030e100302090603010311100e010e060307020f0610090b0105030606030c0903030706061d0606030405070303110a021206060f010908030307 89
    0x920030b0501405690031a880000050001419580000e0400310310380d040b542005456603880080d2a80101c040c0c0f0044000740502c00a50350007600620b141d072001038111098a08a142d03400034075142c3c0301d00da84041991000c0113200c2982000d100e400e0315038800380c40c00c10084841d84c401400741801146514840c40449000c07000701d42c400d0301500c0700c84d8030240c016a1a561280f600d003006c1d41d1841c1c5c80500622003114402462031043d140f1104840e010b03101c00700000d6101043c0b102551004200206610440c6003400b0b00700c1042052078400d80c4c01d02005038440d403d11140e001510304544082e41001402c2c002c1c010280c1d91901100c0d0000054a1320316924850080440c2c00c501809070040c00d002d280440000e404070300003550124580d8420341200c0301d81d5038907081003982c1c00191409043c9910034202840000d00640800c090041d4180c109c88903440e05500203201c4402d41506450150403083c1400706500b07214488010004c42403c0c407811544c10042d550b662400018003c408000121 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 3720880 1250 3719630 3719633
    0x13150903060209010504050301060e0708071e03020a05090d031101050901140a02091503040303020304050601050616140102130f0503060708040521070606030302010b0a090b01090605030a020c0303010609060f02010203040c03030c 100
    0x45081b00d00414019009004456803820b01c1d1044520442d03a040c00700d0100000a40380d00c0c410380e0150303501d0012684101c0303520030f482c0c8101c0003500f10708980402c0c80002c00c0b1a50301d40d50313540c80c03080c02c0521a03030350b110760301707a141c4a024251003010f0259410b507810b040c83e45090203140c208082d13000c2c000190060b00c40682c1400a407217042c03501c40c81c0009460020520007455415001540f141d40900c040b80c04690f619001e106a40c481c82e2010540010b442168200089801519000101c1e151001504102c3d410401d00186145948110a0f4403030741d500402c00c909041c00342031343c0043e860800c40d0391840e01d030b100c094803003980e20003c0103a0025100304c400f103120000d041e241029000142000005e0f1a03190281c020000900740a110ba50820400034224410f030048000800041c1d6651912a1034501c084d90b0603007014008203403064090040f0031040300c007040650300030403466440c00030741d0703180074030152940c4c281d0303e001802c42e40100304000100d11001c820500300c982c1840c1200b00c140c1503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 3722130 1250 3720880 3720887
    0x303030b03070e07020f07050108010e040807050106090c020705011101020406080f070302161505090a0c0b18060706060e010906080c01050c01020903070f0602070e04050606060901050c060108031315090306020901 93
    0xb690032a4811480c80c006010105500003501b6926003101404c60702d00907140c60054034808401d02c074204400c8019400580040c602d4400703004124800c1c0700128a0640306c502c503c090f02c011034a00b100591162408000540c1c0c0200540504040a40211300c0d00e4140140203003c41ca00400a0980c209a403000c1031001c0d11030340c101d4001d805800c1400004004a10b41f000ca80d0744404190808a820480408d00c440000300d00000081d900c1000c60400c00e00e0400c3c10442500700c0002d440310350904503003081c40d5172504c0e0001c10760300d0300c1040005465070500044032002c1806030000a0040c0c9004000e000d102c90009801c03030500c0003402c050b17445040080300b290192080c03848003034043c0102400011f0404051000c641a01c90310b80994150035220403501381001c4045401500a5211074041441800c000009064124040c5032061800503003200d80c914044080c0d101007202c2d400012403030b04130348600e082240038110a464402480c1071140000703000380558040540407550000b001c61882c0e01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 3723380 1250 3722130 3722143
    0x1a090402060a09030c0b04050a060203031303081f0e100b030103030903020919020d0506030d03090503040504050c1b0706021b03030306040c090f0e06120309030a1203061701090c09050106090303030b03 88
    0x1e101704c202c0d410b140c45041001c1c4981181c400e05020b40c0c00482d010900030b0004c01a24401c1181022040044800b6281180e0704040945281511040e0b41c6102c50000c12503885c40016010640400d041800c080580c901c1501d0554800f88000300c040c0014130010f944486800c044036011200b0101c292142140c0310a0406802019a682840000d40b84030400e03c9030002ca1088001f10300351209186c8242c020344c00d403603071404018030581040109101a10342a40182e030072050100241c2c0c1842004403c41c000d06e580007091080550102c18200b007015410881031504c028008242d8201421010100c0d0b80da000140a4510554a800c005582039104240103801000031500030100340755191055004e01c003043d03880c140207140e20301c2003d240702000803c85000741806001001c1b070514544440d1641d031402d41c22982055180c40d0000b90001a014008807450301c25400014a40d44620300b40c1321443c1c0c10780c0402612428500100880b40d009903d90040f00d4040c1004111000d400c800a810440f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 3724630 1250 3723380 3723383
    0x1020d05090c0307080102090609091005030a050714030703030801060806030a05010f0605010e060403020a030201080405010f150608090a0b010b130b0301030c050901140f0103020a050702041109041a090402060a0903 94
    0xd241404000070030000190708814888141d003a40c054540b640071440c02d138400c3e040000d42014041004000c00e00b003502e151030348960000d00760040e2986600019062802a207001d5a983e40f003008103008031000030159044d002406c0703000703200d02403031594003400d000ea05100e0141808014800519243ca043c0405100954404001c00c41d007401d00ca00f0000515644c0030b500d0029852140a039098240f50048a09482d00107041c54070f014910703801183c442e41c008000303c416540341d14070000c1c500f02c58007444000225800304c00c003170503040c40d1004006071002030200e0020f5109a10341004190380d40b2180381035694501a00d0345e1240803011010f640c0c00707154030040c000c003000000001070180c0480c83e08107582c022501c8403103690f030321140824000103000d12a0350040e060005041c1540c000d074018149401d00781407440c2440e4254000404440c202d180c0c04040308000901641603182c80e00c101c0004803005000451029180d9003c00c03495800140f000f0f00400700001c0b2924028002c0f080d1310001c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 3725880 1250 3724630 3724657
    0x40902030c03070b04140d0c030b09030403060207061b030902090f070207080601080f010b1005160c0b030901050403020c0d030e06030c040e07050a0207060c0201020307030c020a0506070503190c0b0115020102 91
    0x95503c00c95600954818414a400306c0e0350f002542c1200c0c0740003c60440665000621001d420f170441d1900154004040c1150351340b4841004000002844c13030015250311390041c0340009611a049000202c6440981c1a0004141c0f800c00c3c40c0b001661298261500003116582e01440c41d542c1c000103900c0e0415a070400c3c0210300c189000003c1d0002c00003920240441c0110003484041d4000702841119501c0e41c03000d9012031028800c2114000034040000c8980d8020341d46034102c140c1e00c0f0020a03582c0d005840c01446ca0351074104010606030100700d102d0300c19070705031102d107444161340e10020300d0010001c0c01680710300c00c0000032a81c4903034140156030240a4004c09441c2604007080040c0281c1c1c030000303c00000d4000c4050004c1c103240594480da40c0c191f01078025510745046030b40d084030414507510040340d01c4400e240c404a001d071107910190004901c40c00095a0702c0b0f100c22250400e40c1e03900d0090504102d41180c1010000d599800a03c0c110307110380e408841324040c05001640a030284d01c1120508 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 3727130 1250 3725880 3725893
    0x61b02060405030f0a060c05040803040e06010c0c03060b04050c03010803040303050702030a020301050f040b070801030c0905060a0305060a0b01030b09010501020312040309030203011109090a0507050f070303020c0304031b080607080402040902030c03 109
    0x2610105d44c80a05512030300d002c0103141c00782003095400e402240f00e0000c1c40d8200384810031032100301449550703102605241051405c416540d0b048040c0d03071141c0050f1040c940d103901c0e0840d2401c0c075108864001c03245a14150566140c40750551340c80c42503010040c10818040b400c0750454504208101c191a4000c009100510340f04010035a405407c0b46d043c2c541e41c1691000c542c019019090442c141d90b001118508058203002205019100103170409410444000c000004200e05005050082612a80104141e421407000505480c00009054810101c000c0100801d0380c0000841d16100549078610f03d039540c540c1401c0d9040d41655001079015420000006144c5019000070310940707104480b100841c0d1240807280c000c6500c11905100410303c00c010040d51100703c10007500e5960301c02d20b0054900010464642c0c20b43c2c115038022640e40311210554941c5c0400140540c028041c4003000b019a4a0001c000812034800604068051503031468081d040d52014400710412900c054111142c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 3728380 1250 3727130 3727153
    0x6090207080304020114030403020a030804140706020c040e070f0306050c0d0f05010501110d020703020105160c080105060102010b0303030915060f21060601020a0209160525020306060a061b0206040503 88
    0x60b41d004590881c005a03110329200e103100505810380740116003607401403000504583d810b81e440e4402800035120f05815440e4012420740400242c2c0250410354007512860307680105010655405003011300703454003c0d98043c007060b1507058903101141d411180100b01900d40351541c00713240c0b0401c070412003035130b0900703005034000006170300054101d402c282d9694402404401c0141d80b281c00303140102c401600100350400c059031013400500b007601c525443c014400c02540ea80c0c642480c607130364446400c1c1e94491040108030360f0280706401c00e450082d0061441e51400101d001e0b08e0b4440b04804803481100c00e404500c003074403903052006036218050041c2c4401d0080f0200c541c80d01d800001c2082e00b43c810f103000101c542d44046038001c11a035018000000c50340381c2400002c460300505180741d082040900c020310000b1801c05022146804440c11100700078082d0040c07505042005006a005a038074000410007907a000501a85d1f0742c02c507007584206403502d0f2000501501c242d510080e40752094610528 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 3729630 1250 3728380 3728393
    0xa020306060c03040f14010305010b0304060902030f01020a09030b0105031204060309110904030c0204050105040218060d02070203010507050a02070605040e0a090302011410050a080c01020d08130b07030f0c020a020a05040c0306090207 102
    0x24280c40703a041c601c906d403c511100440594809011350310800a0a00100b00010f110750021a292880141502c0c03686003410070f043c1c01ca8002c00054030015075094403c00500c00d4014110703000d000c055004e031140c040640003224861103144103071010190b17104403d600307201007c01004c040301d0b00104144101d050038200109842c102d68026441280340100002e05840c1c40d1089500c8019071000700400c05406c08100711540c0c0018501c24491a02040400c0040c2c2c2d003881440c0c840c07036460311696240d56a6080081c40d02d4840d40022052003020042840300305900d142665021000c120040b503c920b691030f0490141019801002031a8000000d110098444496500949409490f2441000c6e500d0039400c0c2e954042d032102c140941c124118000490340320702c1141c0c1c0d10526500441000034425900c1a45204040321070000180d501c1901c01c6101c06c450241c3c0403440c60034801060011404c2e00010058101c2c0c0c410540b0850366102451440740c003070740100c8020013204500310745469490030903c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 3730880 1250 3729630 3729659
    0x90f09060e06010309030801060302090a03020409030206010e10060c020907030213080607020d021203070e0a0308070303020a080609060108060603180f0f0708030301030308010e0a0608030c160501020d080a020306060c0304 97
    0x212248445040002c42e954407030b10844d100360b03816a0760348801d40d10300b07a02500290f011445007a0040258540800962118040c11010500ca98020074081d8502410040c0c403080181c0008001c3e110002c0800044e64441c5100a02135012a0f4601d01c5480d0300d038043d4002d2150242da469010707140c0100280004021420601c030300d0907502a11040e102013101240c440031400c42d000c0f640501400882c3c100d07885440c1070110b0800240158840c40d480b620b540392603402400c3e089000a4000403a07882c40c9510032211900140b0035079604029061840019119500041c1141d003d410b0200004150b802c0c0606451002e94801064804410903601c419450385105840b19106108001c40020f14405c00000c82e8101c03a01981d07400d45a90825480103140c401c0981851441e549650380803540d10010f000500d00d04561000030061492158041c82c00114503600042c199040211643c80e5a50050680c80e40a0b628103001039603503807060f00140285c000e480101c80b5921012801058002030324451 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 3732130 1250 3730880 3730889
    0x9030309020f030a0302150606090307030503070c0b09010206040b090115060503090105091c03090501060b040902030402090106020607020d0c1a040b041703070c02011110020f07020405011a0403030f090f0906 91
    0x780100c082c0000145907445402c4080140182d106018031074080400240741908040000e01c2a407602c901c4400180ca405903a4000341c5260f00001180e10400034007851400040030224940c43c10310700080000703034a83c50010400740000a29a0010b0309404003944180404070a445980311416110700f001850341e04111020205986818007241c0070f0308000032503070709a0280c81007000c412002d1010803009008100d800f05c660f59202c410202c3c03c2241c08007e0405044038010051300c034a85401041441201070340440c055400c40001c0c00002640410791050031340107402c1011041866283c1222822410603400c1d140b0f9038005c06100422492a00650059025840300d4840038103a00090013548010340310740000c5004045090010750007200074040d400815230aa8011901d174401c0702d030076a44800703c5610100c0c0c00246403030442c5081d00c100d501401407400030210304080300c0a800c0041c400d9001c003606100486442c4017040e8418101c05019140031401d10b58884d42d200710120151005004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 3733380 1250 3732130 3732139
    0xf090108090f0604080c01060e0109020711010c0b0615040902030903070302060f06010504060f021f06050411040b030f04020a1503020d14060a06030b01020c060403050c01021911090a0207060903030902 88
    0x4034116040000d114480442c0c460b001d40442e0702c0da95070b1513041d0b43c040d042005440d52642000114003d403141e00a00038000c210700541e0310380c4030b480c00d0104a056400040c0c14800100c0c005404070b100c0c203030250750103c41076030015a0078200e08045400750046511510085000004005403000d0100107001a58829003c03178a040e120241e030300c400c58000f19062400168248810400e1900c90115954002c44a0041c0d6030102006a40300e0f200c15030034400c008130316450f2401000309003001e00c07641800300030843e9601d00701410114011103600c405080000480b00170345c00701e029560350f250004018040030180440350580e030907028010390021800c1c109c64a04d045281c070400300c0841d04542c8101d6000303200058841c1060780c240c00404001e0103503411441001e4100503140c0792080288007075400f48000f410700c00c409200085c9442488443c0d48030102000e0400e0001450b02144994000b0040f0740c80b410316580c000703056009001e62140601454100301802c01451340503408070f0350f918000d48 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 3734630 1250 3733380 3733397
    0x603060c14040b09060d060905090a0507080106080615030f10150e04020d02040903020f0d02071a07020102190f02180f010501080709050d08090a0608071d0603070302160203030f0901 80
    0x4031038800c1d9020710b00c00c1403000d120030000701c107042c6802c20007811a4283d800000034030540b0ba04418080790401c403451412a4805003840d010701001b08290001030820500034403845060444103500c500d00500343c214203111420102e4800c0c0c2e8140000e007003010a060884140e0003000120102402100300c250064100010b0003040f40d035004254140b1854014201021a02c080c1d400e1000901c40c10005404501920925070303141d9205003c103488201c0e051703005040a40c10721900110b5100d5503908207500320000c0110500503600403841b250811210110382c02040d100b420301d08606004044000c0d4003100c3c156100e00c107120480305003070040f00004201d03880c60707807100c00550380b00302c05407550004552254030410a6250421520440c28401e022450428491320081181c0078240e40240c800f1a08420070424003542c0440303856400162514088000c6441c00080340542c0b002910b050f08154000400109180c840e8001350300d010350240032207548a2002c410740f6056042030031728500161405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 3735880 1250 3734630 3734657
    0x103060c03090201050702060c0a050d0309020f040504020f010807020708030307050a08100302130b01030906090b01030b0903070305040e060102010b0a090e0d110304060f021603050d0e010206150609040209040603060c 95
    0x70711039550020f9043c2c40f4645461507903006c1000541140c1c0814615105114801c000a90140f00740000102144ca001c103400b120b0b0303c10881c28210000c8401e029616141c10080540e42c0d00641ca0585402820415019110707403204a041c955160840d104a100000910004580c00030040041010b5541d13240242d444010303c402c8a003403c0d120103540400c0060450103842c4099111031014032050500085140413640c5900c25103100840581d000e0503980010824412182400703a44250080301851610f01c040c0c1e00038140340200c3c00351309100c110402c001865a4000d5200f0500028000c182c03004040c1e481401401070102d81d220345056005007004211803d001c3c000c1140078048402c080c2d41800c5c18900d041340c00030111046040cc62217542030344000b019520f1841d4000d14002c101074504022407002c040c00e41c18014103943d045511800c1000b081c201401820020b20004843d40d99684284400240103400b0b070040059105141010020402c1510f1707101e0070040b5003d40364a2180c6615 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 3737130 1250 3735880 3735887
    0x603020307140a0504050a0308030f09031905030604090503070507030c0803180f0a0302090108030c0111030c0315030708010c0801150309020901030303050604060f03050a0b0c030603070611120c060103060c 90
    0x1c0e150840450300a0b00d88001d4407081d075000d02607410303540c0b50031360030540d540000039503101c050303807043d5028003000092114844111202a030700c0301003507001b103107080d58100d10101c1d0030b00e0065000f000c00070048082003c92780e4039001205103a07046022a611000c0904101c0d4941039a13120868001c201284002140e000c08400d4a10074102c250714082018070b00c0c414801c000d0301d40300345194031010664001c401030790b6510105028011001c01517440c0c4004040047c0dc40d0520481518000c2086c4104000c5141f540e089030f500090b905440520340e0401000b0910b8841c1580111580303500b8450058165603101c0c01150403220181c0c00085008040c0200341c007162010000070350810340c41001440880c0c080c0c1c20050f08110301410010720315544d2228100c05d00070035041100c007030704160404030500a5545901c0c1d00030b54011310040c40d504102001907a1200c27a8450b11084c0005142d01080800050000b55602c03a00e205880e6502c14034030203040d4464200340812100c492a101484100b20720 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 3738380 1250 3737130 3737137
    0xb0307030b0405130f060b04020c030703020601090902061902011b0c0308060a050306010314070302060703080f1503060a0c0507020607060501050102070803070b240d030f0e0301020c060a0b12010e0307020109060302 94
    0x405005001c482c0607140c2c11520451703644280e03174058990a90780f41a4a851000700351602d0b500c8095a10750b182447d00034100032060f40300707480150a00902c0005a501ca50440d03101c01910520a074030841d10000c240c0c050b001c10070448101582441c90300ca0303042d0308561a03d00c024802c4c0e03075075811fa607114000c2090b40d0742c1034001d03942c1552054005000107401441d0700440003040800311032085030b40ba40094103e502c000800c03400a4540d4003070061403041c42c0600ca07082503180c80c0107500440050082683c42c84024100302c0096143c0101e100064043c0c0d00b02c601c402c1d006400c0642d150a141450b44c064a400e10401e8018442c109000415500200589034000d503c07c004900b9a22a44e210321030345118050b96180c050b08020071098290b0b6950f100c018114840c2d2501d4081d035890490190480a1502c50741e40a40d0040011200303614010440590011207000001048001c04c004110307032600c0d000c6558015031800c2070000c83c90800201401003103100341ea4120b131050b195142241a0302 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 3739630 1250 3738380 3738391
    0x1e0f0301180b0702150a09060605090402010c0303020310050a09051005011803030c0c050306040c080105060a0513020a0507080d0605030c18060d0510140115050a020a0605060a0e010b0307030b0405 86
    0x350009101c00010707801d2002650043c0c51407040700c8100d0050b0a9680c0c1a1000742c0305420101c0d5900e4540c070800c03103940907140041030700b10380da107000c1e10702900041c0c0340c8003000c4001000c241d40040007401c046a03103107039500a40310140c04032420540769111180240002d4071296400784660000242e1584645450842c2030503034804405110315542d8151414500224104d079a91400b083c0412030751020840035100b2030051500b9001c0a01c1c05003c50708641d0701502c9180034007201001480692500660b007511040d075080b0040e960070400e40e00326024011010010100480041d0800c0d2100f82078111500707442040301550418072000c002c20048074199640700b0b441c01314250002d030301d52424040c2202010702950540300390180750380c0c0760780441d0007a042840302240c0d04030040c04050460380b13160300068502c2c03d00da0715001010700c01a40c0c80d4042e0700700a08081d15000010119280c450880005111200003207406507150010030744c26402c21105180040d1400241d40b0036031806000e0782d030040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 3740880 1250 3739630 3739661
    0x601030309030b04030e0d05030a14090a1e09060303050a090902070b0408090d0b100e010902030708190204050301052403010b0a090b030102160b0609010605040806060d0f021e0f0301 80
    0x781d2642d5501004070a00030026410312443e841585281c2d115000996290392041001d196944404070000d00245609081c00c0420082804500e440d80c03a200c001c0d205860b25915130b030f00c54031005620384041c0d113820303006002500d090070400801c00d9004000342c18100520345800940c02d8460058008a00540001a182c5003850010a0119a280c40149030f25180508400c1c00031030701340c40303c0d600700700141d40c007026040340140304120003a2002d64440c01f4040d055019880d5040241005249101c086c1070208030030501400800d569001d541120f0003004064028040c1d854070000c944407140c00100d00e559014113000c070304019442c061140d080c4282c1c008114115090401c07201c1002000890101501598208a50346162019007a0b10348041c0c420905030040345005418881e034204e042e4441001d1240c01d210604c0b4041021038000d078000d10039100c000c01c02d42241020701400382d040401030f40209615070f119603d01c912000c00400b1140a8400e03c03441d0a8a10900d422141100d6046055 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 3742130 1250 3740880 3740897
    0xb1f0303030209060d050103050c1002010509070515070f0501060510050702010207030312091506030201021504050d140403060c0309020f060f041403070806070e010201050f0405030a0c031209061d06010303 90
    0x81c080d5014182c820000382c200c500340003d51403030000300c64080c0c00c00e651551106002c20802e1508141e16a11601c15100a00083c1001c20748281e4900e000e0241d280b041c0c502c0c03020240401d4140c401c1e902d045404c4070960300c110107682801ea0003403645005081c0560801503d490a040c059022280d405031306900611005256031000c640c0d048100780c50340502619001c1d1400818011201e48170342c0748400f1400a091451407001a240641d03034850401c1048441c2c04001c0802c4011644910800b0350381008964400052415401d07441030340c0009242502c0d00101350070142e071692141000c02c0c42030700c0001804005030208402800390b80016800080200302c02d21980070913224032210307048080c003224401c0361a645810f080550840e80400001d01c94007504c0125a42401400d41006100c40b9a900e5410a0780300c0ca40c891003881c8008060082e00b002c20410107100e18606803040d120254100901303581d03450954040c0c04880720090682920003d40b40848402140c10b0341200d0341519000750 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 3743380 1250 3742130 3742133
    0x5010e0d060519020403030e03070501110a0f02040b12010e060108030309030d0e070e07080a180218060109050306070908010515010206130f080a031e0605010f030f090203030c01020301030b1f03 85
    0x6042c004044070050010450300c0c00300045180041c101541c0300c0c2d00c42c800c9080c801c0c02803602d495050f40c4420704114203543d01c0d80e000100400c11002442d000707543e4019801260012401a1681c010041e4000710342c1c040040308070f007040d444680011002c000356845643e035070002e00d07601e0006070360450481e0400c10440c0c0801e40c5681c0f104402e07030030000594418540e03070300b841c00d0b4210701111054003080c04141004039500140c418001c040324440d8902420004035004216981081300b80c102074043ca80c1c0c04100c2c1d0368050500f240c01001c0041c200c03141c0345080b16000b0400c185900c00c840d025030030400880d03403824005d50000c2e000300042c2c1c0140f606503981c181004c1c4030031070b808007550b04520201006001c11140c0c00280400c029688002c103426000700792444c250b0200c0d0002104640c035090381031103542e900465144810403585400316440040030202402850007040095245c440000c111686148c1034000e141200c1c0610035600c0c507030350740110a41c050703440c201900100d0307002000c0510 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 3744630 1250 3743380 3743393
    0x20303070c02031f0507020f0d09090b04090605040c080d0c050d050f04080f0a020a090b09040201080603010b1c03110604031418060a03060801050703021815070203030f0403020102060105010e0d 85
    0x41c1003500041c1102d02100220b510842114040c0030340c42109030305d500800c00031940400004481c880c0c0300c00141841d12034100018000c052a0040d0082d03280c9900083d180c07a650b64019805542d0040410802800c2618007202c08005912520449009401082d2803241c0501800015036800070050003e101c181041116242c0c009101c01800b07aa05100201e01a0300402109a02c013680390000c03c4098002d004000d55424660b221084280c107000c400502c94582540c1650440e40c2800c0c401030039207981e40041c0c00b50a0303845c05a90059000700b030910600d00950640c103d00c501a0b1100300420b600241196140c4078100c50143c0803c1d404c83e140d02403450304400030300780900001d4110300e4903d5100300003981680308030010310000c2d032610020300180d02c080c490950480c3c15800c0441c038044001440f819485201c100d141c0c880d00c4e6080403d50006a00d0048800c010b500506686e6501b1549906040e1a041804181d00504c030f290004509540604882d05601303030020003424141c0015501c01c0e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 3745880 1250 3744630 3744647
    0x30601051308010b030610080d030e07090903050301170303010506040303080603071502100f0e0a1103010609050103030c1101080c0909100b030a02070501240314070b030a020a030f0c02030307 84
    0x15041090410103030281024030080c080240c8044000803c41070400800c1500d070440107041d94444411001d002c01010200142c060710100540c14041029100c0f0b4590500703020039030f4444242c0c1810040c1c1c0708105588003008605850680311080100c004501c407003962400700b4000c25800500401c014070100303015110a070b5000c6c200130b00711841c507600c8040b0401592001c9841401503400001c4402e41003010380641015407906042c02c00004401c00141b683d9804032501c0076081c10b0f07003d001d1501d1502d0a40081014081481c400d10203565680340c000c00c0640e0081c015207281482c001001d07003641c815a081d40c0508006550b2505040e081002c1140380180604a070380d9545841200140c0d205220000c1d62103101c00500068036490355003080c90a40c3e80c8000c1460715030003005500c03000a404900780e14243c2e5040040b1102c3d503404800c2c001d1030107031160802618450702000700030440c4c280d9001400403514580c0c05204100b400b5038014140c0c0c6c00a0b0b40800543c006000007440c052064001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 3747130 1250 3745880 3745891
    0x1d090d0819110703030207050c1207140103062102011205010503030a050d0902090406051806090303010b03040302030c01091b060203090a030206090f12030405040b0607030210020904020c010c0e011202090d0803 92
    0xc0b0840c00300c4103107055911507003089003c030780c002c00d034201480014031211102c0310043e1071070202030882600c42c0307403694460f01a0200300d640c1c0500c03406503a442540004060301c6600c001c00c15000e0307094240c3c07890320140e0000300d0000790820f03035182040c865402164104c1e007007d0000c6041c04110f41054405e03801140070508a9941c508042c0b016a880c00c007128000c50140c1c00010341e50134001c0104c0d142c0a2140c1c10580c41c0d9208034203000403004004200c9044803502c440554480e15175250880c11481001103182c400e608240120091112a909040300605900700700810759039500000c0c2e8490249083d0141c1c4072075201001c00c09400d056000f4080031000415041203010058005240d03004074030031400c103c0d0700200f0144280d00b0503100c0e42a01e8401110b4a0341801403030341c0c0095448101d10746246805030040b0300e0000c243c40301d4060b00c9501003807000134080c840e030010006004103404001c1600003600c210040d00c202d42d2030300c00c840349920003404050a01d90703943c407040700719403000d0013 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 3748380 1250 3747130 3747181
    0x901050d0203150109170601050607020a0806010303020c0a0e0106020303150f0a06091a0705060c0d060b0301030302060a0b06040b0901031104091518140402040b0102070506041d090d08 81
    0x2260400c40c40310720046200d840c415090f4100c8014580c0014141170854021070024403108804c0300ea03204002032514111442120405c3c1d40c1d485904c0464115106a40104050710170701c3c001200700b50700801c900281b90001c0ea120805190b0710524461464001c1c8280c0004d60000c0002c10701d10040300d10b41a4013041c025103043d41d0507010001140d140d0b80b20358802d000061944105100c6010001000c1102d03140b441e84060814019889513070f214400a45200301108000030240400c2d0040d403c250f0091403904407030b03922036032f5a0034080c0d1103450803100d40203414170301200b000c200e00e0036000740c078251a0110324850402c080100150010070f080c8032610300140b4140000191880c0354041c000c8591540d02005c00100e29150761444074070305d600440012941017045104a200100009561003034040780c007c10105082e20040c0d0918401c0d81066400040005020030498204006400f02c42c0d003108003441c0703035a1000410b54640400405400000b51920b0200c2ca0a0038104140807614a00d101d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 3749630 1250 3748380 3748387
    0xa020a050607050903010608010219080912040308030411090108060705130e01030f1203050403050315040f050403020309030d0203040302060a030506031009060501030b01050f03061602030c01050103050109020a0609030b0c090105 100
    0x8840c5440c100d0100c0721407000030710010b207050050400b0300501004108150080d81000440701641d2100c102e621180810440131400040003d041044120b40c49900da86200e41c0c1e8030349a0070b0030b807041d52085405403070340d41400400400c981084041c0314104e03400900a011513454040013103803580e010f0f44c2c0702c01740004410300201e003000c12401c609000354440d05542038910f41d10319158407202c18452000052602e090100000300390000212548400c2c000982c210f46415040007030000c2c00103108203281c0d00d1400080004043d0000000c00581c0021030403554400d03030560b400c9030390b40b0036400004d4000c10140700c040c2005001e0340020343c1080008041d202c503122030520f0030b0100e41c224032054072074588500040003408811019203000d42030139503d0013078000c51500841e0740c540001c5c010030721011005443e0001248240107403201401c0c024000e100a594a040190103056201307001c1e441511207000004d1018000c20000c41100c0c3d00944508082c1e9403980148180d4010920b803d05010041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 3750880 1250 3749630 3749633
    0x10c08090111070f03030f050307080601030f02210405011107020607020603060315040c060905090705070308040c0b0705010504020f010503100311060d020307080f010501030204180504020406080d1101051f06050a020a 95
    0xa003d15800707881140300000c0c6a6103181001001107100c0c0c00314800b0721000700140280c45900454480c3e000000313080104900d4a103804100081c40b0b1880030344000b24407600d40d840c40c40c080c0d400b00c601481c000c5009224080c1c203d00240094800c840c3c0003944090104a00f100600b031140103560722010040640b584c04000cac14030000404011282108d84480e01007040c400c044e0480010b01c050541518808141d01d00b040307014180341700d076990140034014004001010042d20000c00006044583e11054a8101c2883c007a4041c140c10b0350101e02c6600100020041075108506a074070130450344c070080d0011460b41c3c0b5007030a070400061949801c00c0c000c1000404454080c0002c60244c40c0e5603441c0003031740c07901c1001c8030300301e40f810b801c41c130704060042004010310300340007101d90026810014001355540340c520000300106601d501441c00d45c001c0a280c000d0140c1c04c600c070b221020040c04003c2c00f640e1b481c2c0404031261040c00b48540100b802e20340052041c0d42c81100603217144001c0707004598010145 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 3752130 1250 3750880 3750883
    0xc03020405070c06060f0b042d06030f05010806040206030c0c0703020303070f050c010c020303030a0209010c02040f02070312060b0307050711040501030507080705060c0312040f06050c1206030309010c08090111 92
    0x4440b1034002c01c03144600300f010040c02d4813403070008140d1250400c02030b9060a14100451141d4424401081c1d9480c9159424200d4100c0303403094442002d40c4102420b9441d10050060450070003d035041c0ca00d0305000044a84010400d07034492a8024030780344c03070359039189070762045c2ea000000392003907600c81c089001c07006032010801440c0f198000d031140c202e03540082c60201e262018039070b000e50400c1107501c00c400050318008241d941024403141c0c0940c851000c500100c278a9400c1e00c2c5c0180d4040c0c1085642052401b50303a0003090168000e42d180c3c481c1151101c0c6100c1a1109071003001481a810400103492603c1500505106440b80100302d21680352480014146c074403c0e00107a9007500502c004010003442000780500500003524034500300403242c4520b07030f164003841d80c0c800050303000000083e04120302c215500c1c500720791000d001c1005003400c40c00041705404c40c3d00e1000640c06840d0204089140000650303030701c0581651004005900c55507200e071130350044800503040c0502c240e040840d2900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 3753380 1250 3752130 3752141
    0xa02071503020301030209010b09010f030b030c03070b0703020c1512040804030615050301061d0105040c090302030709050105130204030803190209040608011b050a080c03060109090c0302070213060501090e040c030204 95
    0x550307903025850b541940101310717065030180d10425603e00c2c01c01600b48036981218030401c00300b046082c00030303200510401190170027100440e1980c0c54028a0008540a449007000d01140740c02a400c49241d410a00c1c18412440401e13840030340e1440080c041440b4084845040952251107035000a09007a036030303595141079400c0013921030000105248280700d0b0f0700b824411743c00280040e114481d0814441d1000c03900780b1006005850003103844003072009101c0d004040740b03401154041c3c201c400c419900c0b00380303400501084c002c29100e038070021481c0141301e50030300030b840940c1c0e0000c0c02203195481d03110800030030a10312481882d10940078400c050665980384a080c000f0551301c8004107803078500802ea999150001c902142c1409814030a2481c00381d4020000c40e8030040302c1d0f400d41e64a4880f0700058803141d42e90341c8000b950358200750f0b0145085a258015060306803003642d21103052010210004281c0308603020f09800500c0b0a2010072200b0000c00c0c2d11904140941e01880c07425440c2d801042c251072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 3754630 1250 3753380 3753419
    0x5070302091f0f0518040213170a0302010e03040e01060305070908011b02070902030103080702061b070f0509060109060212090a030203030c01050106080f07080402040504030210090c0503010e0f030f0a0207 90
    0x914091800250541101d002d02c4040c3d03140c9010b42c40d120122007031034042011351714142d0040fa404140284080c0ca151115406080074003d61441c55441040c0e1071341d01c80400004a005500f8200a200c840e81c0000c19034050f52010842c0d204680e08284048004000007020360040180c44240018544400e1096900346803d641c030740602c060898101a180a80b90f40c0701e100110710410040000c10b040701c05a42846504441d0290344184800c4010001c00e000300218445024141c0b000400f1342c14041c1280850b0303415101c0103110b664480065808512900c035040158010318403e441e81c80002004102c0e503440140b0241c4840e07140c1d004285543c0207620403020036955440144011030700301d0f034480d521441905208240380f6015070000c000403009071000b40110740303c00110341018000c3c015014080d4101c03100b0441038540b030400000c05501d81c032442c1c1c001e5183c4540420f002c00086406003165040c50010b528000104007020542d60050102c0320850040b6a40440c0c50307002001c8485404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 3755880 1250 3754630 3754669
    0x30209151909060f060806030307020d03090b030c0301090c03021c0b0d0c0f050102060115020c0d110607030c03110304030f080a110304060201050915010305150c0c030c0a060b0108010303080a0507030209 89
    0x201d0620303421352140310454118105000300801081070550f400011038a0056043e074904241031031628003911051129080241843c001204100741d40741000d01544c1281c40860003840141c200500c103600303d00c10411030b0041860355501d4040c0c0848150801c00c5840c602130300300000010191541110000d45400220204061500c100050340e81002010302400c0c140052654000c00c00c44040c0d5111600704005018400c4034034a00d0510202948440480002400c10ba64450300c902d4010140f0102210450200d49118014441d5041c00425030b003d480d44080001c0f90b000264031104510f130417800140080001c40000980141d10a10103480140f42c285c00104290800c0d140d42c1e41031090514612103103400100040011440004100c141448400109411504c075104004624802e111441c00c942c4400500c840102d4000681c800000c0c1c002c010130440a4150401107074150303405e01c4058005540080410f08004665102940001190500620305080b0a02003500c0c50406200b800b4907 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 3757130 1250 3755880 3755891
    0x1b0906070303021201060203030601020a11010915030207030f180303030207050109050f0f060a020f040501050d0b040c050706060e040b040b07020316030905090702010506010206011206020403020a0b090307090204030209151909 99
    0x200394054400c1805446d03240040d40c20b524102c00000d55803020480090225405e00c015040e869001c1c80940d0054402034101e810f070004c0c01ea80c050003a50100c2c1c030450000c1c0418042c1c9a605118180c2d4000aa0140c0c00d401100c3d403840e20200e000e5001400280e841d556211148400030703400700034554102040001504510503140030240c1020b400500040c8400d00400200f02c50b240610f00705c6050350401d0030986e44900e0320007101001070850500b102e030890310340400c01e90f6581e008005000d50038450b0006008075500c1d001c2e40c81800e01c0c16a00202030ba0110000b040000d00d5146009900c550944102c07410703c004029002c903904d03135502c810303000b00f500402e041c080740c2003414115901c45413900080c000c03820301e0701c0001d5584005100b4460240c106560f841c04001d65501145c00940d0020503a001c3c4079101c14404100c1c5c6e101c0403045120740315604c1c0004015059000703480c00c40b50010300c18091541e03098160075940c82d400d080c090740028840384220600800161721000f4100c01c2d04001270 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 3758380 1250 3757130 3757147
    0x12090d02070801050c09010804050f06100f09020f07020105160602120a0b030102090906090c0706020d0218030601030f08070c090903031d011404060207050c030d030f180206031b090607030302 84
    0x2001c1c440e821074289030341460308201c5001203010884641d40130a00c1c0144080c2e0b2181012400d01158421440c454022441803085c003030100005401502c90403135900d040ca550749c0c0f01007802c034420b0010000b194041407001c03501640c020005007064217075281c10381202600d20b907640c83c1260300c03203090702c40c44580034404d0014a80035071040d00e11140c0c0950085190603252400070303080b090003c050511440711000055800458a800d40b07001a130b000c0029500c5954103091480079402821010401e41140011490b603403800051650489800c400d903190f0003040780e1903c103d95030100d641130f529407480900000340594248501e40340701d8001c1d40c00140d40d4410380c0380d614086000b00a480426810304801c0b401c40c4134282c0110743c00070347c004d10050340d80089141c05420720450100450b41401484100a03105400d50484040754401200410000d1040b00c04902e9201250340083d40000c020f000103403100380c0c10b450906107000c0b005415401e05002c2d000084c0554805001100001c0c0c02141c80c04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 3759630 1250 3758380 3758383
    0x70f03050c0d03090f12050f04090506030d0f050d09110d0302010f0501051906050d180305030a05010e010b04030201120609020315090f07020a0b040f020a06030501060e0f010e010c050312090d02 85
    0x100c4940b40c42c0500c0341c4940c80e180c484c000714003d00f010713100f050301c40303000e040b01170081c8200c6014100c8019115261039403101c2d100010f04d400c1f40c20728000e00820041080c0740f4070400083c2102c500c00d03146d05042c400181c0b03184000300145c1e02c00b103400103030201c2103c54564401c5d00b003001040c440e5001103544202d140c9407e050394010b0340714030301075174520b0032061540003140f40a005546980c41c1c06d43c4c40c0d003405e40301980a41286244100048a59100790f003c1c140e018000314844c480704002840107907691610683d41d100d09104e20880402e0620040c00158411034101040314084075000c2481600c0311011030417a40300396a500705c1d8500398400c000d41c5003400040960b01040b45882c9241c2d51903c031801135100c0360b988070f008010074a00f100160400084030f5513200c10503005030400e10495213601001d00204420b004040c08207100c031880c81000d1404000d00c011082069445107800c0241700010b65681e4540f403000ca407280014007002c0300b070070222440c00384030710f5140000f007000e6000c3c0e0002a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 3760880 1250 3759630 3759643
    0x60a0c030c1a0108100e0606040b0a0302211b1807050d050109020901110303040b0f09030c03041202090603190b0c0c0102070c03030e0102030a08010e060f090901050103061a010206010902030c070f03050c 89
    0x50240d10300302465600c6c1d030100455115808071042e42c000c119003040c01e00003030b468001600002d600440035070103030800da84564040005451924212421040a44090b01540c1c07a8110030651010070b82041130b194200f803001490b049000c07401d0007030030240c05d9500b0f80c090b15000d8002c03102d03c950114408030300c0e40c1d1200400e400003412801443c03450400c0d440310302107007100520021540c00c10740c02040c0c0e0300350100200d2b4110600b0340d0a43e501d540e02c034030100080000300201030340301e103c0b003502190349441c01142034029800c9a00000150158550f84c8181e6076000030500141000e00348a00c0c0440d43d001c4c0020328000b4440c1da01c4503807441c00c618002d440510b10070301150443d030050001000d81600001c545041d9083c400085c4056580c690000d40035a0b4038000355074128007014244115040b0540046068038403da40902024104154804152050420160042e407042004002035229580250380015800c03800d685016003544800c0108003014108a0008100103a420030106060081 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 3762130 1250 3760880 3760903
    0x30c01030e03030f071403010b0304020f1002100903030f06080c04050108010203100b090f041119030e100902030a021c14071404020c0709061202011706060a0c030c1a0108 75
    0x401860303008105076a942e000040030250030728805000315402500403940c080c9040c182c045a035070f40303684800e0134205a400030b0700c0484c0114400940914603141c2810141041e00e15176009003d03d40900d5040005004074400580c14195584e280440d001214010300003d485510018141c180c1c5804c240421038005900c5403015910606c18055051807800c0c0c21022a28150300654986030210006046500345140c00d5034410f240c6144d00c4921020400600707100c030030340140c070010440703808819070a542e9420712040840d0041003445816100c1540001d056034000780c12240007061a502150f030440134425142000325503101481c04010100c00d0300485400d0140250200c40d00d44902100c10503408201184241c0c3c003c02c1d01400c40030b040203200020701e0f075401c0900c00349a880c80003c1000e0300c04a02079000820f200c0901c035240901520507800b07030340e015000900d0860103040c11141c0f84041c103411820041c186c11007001155484000c150400c00d8481002260751424444620b003075441400e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 3763380 1250 3762130 3762137
    0x6090c01020c120a0206030415060603060603150806180f03070501020c0601060e10030f021303060b100e0a05040905031204050601062d0e0406080f0a020a0509010f0b0702180f0402030c01 82
    0x401c0034801004900d800d20030358161029620ba403a14a80021281407041502c0e27006407408000084599140e00004100c1c1c8a90b1400c104a0b084d00740c01c0515064a400b681e502a0f11600100340d5603018103a40c0800404420141ca1280c0c100d0746030641107034030420341915160f4000c42c10f00c1d508042800150700401c0e180c1042e60030f070b0700c2000214810a4200c990a07090507910721940e6071840140e01100d681c00d0190044c140c819440b49800c000a01c00e04038814060056980948100f5000d4030340c0f10b40003000140781118441c078000411000d400c179220210380d00c0c0820b2180289000c4120381c0e00340114844c0015007402e6042484c024011144080300992a1000c0112640307610000740b40c0c0800d80c402c0d458071203085128100800c002d8041e980c00410b1620820314040881c05020880e0391501d4400c83c2d09082d81590b410412141d80301c203000d01c005081049204012580c1010014141c1d0b6201030404078500c501c1d07004203290b007003003202d00c01d4000c2042002c00c4218036082c0800c44d4a10000d09 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 3764630 1250 3763380 3763399
    0x204180c09050619030b0d140d0306060201021201030f020103060503060406091106070206180f060714061003020a150201110c0102030f01050301110403030c0804050d0302030c060604060b030c03041406090c01020c 93
    0x1140c0c4413040704d4140c1e8038041c56a65905007800340c94504140f0540d50b00f10980341500c90320901041d94515150b985003000900d0050040b90861060007100c91652001c1c01041c1645d0854441201030712115108906055544900041645042c00007900ca14080c140008010015040c0307000c20301c0e400c51403540b081008000c4000140e5560040e04c042c0036103200800d4031808200e010443ca29540090250f211001080c070800700034000282902d210b00101c2503440c540c4600180010181c1e640c00025440920810b041c02450a8096141000442c1d480081040844c084010802e5400042001c540341d4000003000101c40c08203102c503005100540003002590105084004a401035000050420a040342e25405200000056801409c00100055401d055510300655294004182104540034607800602145414070560302203031703410f1400703d16540d40c6c0c0c254080070303a10082c81103a1031070069041c4004000d040140a10030b5120300001e0905910084c00a8503000a24821922031804039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 3765880 1250 3764630 3764647
    0xd0b010c020913020f0a090218040608060f09010204050405010b07020301050702120d0209060705030d06050a0e04030203030103030f12060b0a0306050f0d0204091403070506060a080a120809010204180c090506 91
    0x300641503000f80710403600320b01c450b041d00c0020411881500242d5200040342d9011a4030702c42503004000f0742c0e44965503c0c5000782c20758107020a0303490b544244035854000b1400100003000e5280159445003001000528040e121000641202d100b80c01c40304100d08040740b11021402e0922600c0d0f00421720340002c110031846240c18294520800c49a01025600803419070840d440e20015643c2c66030307000003030380c0e1108aa400303080010000b0384200d600c903540085001074491141034601d80240c1d015030103549140e085807001c1e5955010010600c00304440100d180ba604c41891059001030305c202c11985d41c0e5050100d0008082d290640c1189202d411074a500000c0760b92441c03080c950080d819078001c6100c0a6600b00503c100c10080c140c565203010003d121020064042415441030808640b443c9101c0d132121000c954503083c1c0c58004281922100c19103170601d00030b00382207502201d040d0000d45826215960040701e01e036582a1034100310f40702d84c8250703565500320141078041c0409070703046030401102 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 3767130 1250 3765880 3765889
    0x611060f0402010f0203040305060a020306030c0d030c030813120f020c0301060f0302040e190605070207120201020a03080603100204060513090c02031204020a03081b060a02030105030a080d0912050d0b010c02 91
    0x103007000341032000a480b07071041c4600038070944008541000039a80c3c80c1c60306c400000040e41c4100d4096119010f041c14650035858010640071000c3d40580c1c40000c0c1c0d540f40d940540300f01c14080c200303143c400d04464000c40000c0911541c4512000719540d030342407100752554003902d024000d0005502c247d05040c0c0c1400b20503200c0510f60102da40480303000c80c0100900790301c0c41c14442075500411810700c0d1145204140070075078005034060781c0e09600711038080780c2d00e1000044042170b03083e0081c0182c010001d0f20000c039100700300190308101c009003a11550141004107104990069000314089080414042546c6200040d0701c002400d800034140a019051200292071388180009e80c2c4044901c44041000d42d214844000060b41c3d001000c2030340c6144c07200584520341110880d440b040d10a120004079480a2030095904862000d0010700614400d556511140c3e0400d0410500d895566260300c40803d40b0036001e03007610100d58940507a213004030005081520300030030301d10b81030040c420034030300050b140c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 3768380 1250 3767130 3767161
    0x150b10050d0f02030106050a0206070e09150a05060a09032102030318010e01020a03050a0b01030902130908090306070c0302070605070b0105060306040207060c03020d0b1804060c120606050301061106 87
    0x91411680d2100300250341c00052002c2d82c407070003905101200109142c0e41000080c0403600711602291130503550f80004880e0001e005600d0368110444002041c101044800040c0540c031b0000c1c0b000c9200b6031a10045441d07a080344010b000000c40b1171a0400030322402c416035403401d00c1d58442140740c0c4205280c010b0354030301c03010f0004041d100d0130307401101f030301c4000b0340c8000d0019081e84000d560b104000c40d802006040e050392001c1103a464040e04c2480b03503000b032180e08641039001c0d00454641c0c00400000006040c1c024044d078651004104c0714800750340a01006105003d80d80b03940e0f0325140d042c1402494540240c1081090103030410255010410415103641142c0c012030b56166a07985410110b000b03405187d60003425281007007003c4141c2a0150040c01c0c151140b0700c0c08100c100d260300704210810302150301c00744440c030280d4040380c0840c115411982044400c0d0500038805044071825400700d51403507000000107080070005000881d488007141d801c8025100041003142440040c4420344d05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 3769630 1250 3768380 3768409
    0x30209070c020109030507030b0a0b090907030b060105040905010909050f0d0203030112031b0c0e060114120406020f04080105011a030106020c0f13020408030c0f0d050406030b03010603020d03020a150b 88
    0x80c501400c1c11a03115040c0da001466109040d585029a02d1801850015099640443c0c0501b440264a0fa60034641c2d113240c41400207800420882d4510384642c4581e0f00060034550400c0070800c800303e014004c5015441c000e110420000030302c0e80b02410000e0a100b9101c034441c1143d0450903034145019030001c1a64192684c0403c80e002d050118502550000ca400602c841c140e02c513502141d041c040c00001500c120303580c2070400304079542e8000044034824901c039050f1000c14070078030601e03c59110348111035501c0341c0f0034640107242044221405845420941c41294660346950060003280c0c15490100500c000b00c00c0d60318115410000f000c2c1d1100b00300c01000d4010001014100d440b82d81d2030715940700b06032031903c045665507150f001058403607001c20121000c1d48644107220b98084000905000100e01a07901c1c0d0b8106810000c0c00c030054400200059030540d250705010026a60300380b400108548690020030422499161030649030420f001c1e14041240390120f044401e858684c105280036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 3770880 1250 3769630 3769637
    0x3060b03010b0409030e0916090605092e0e01050f0301050609031f0c11030a05030105060c071a030411090402030606010302070c080601030c1802030702100e01020c010906150f03020907 81
    0x14241000841e0042540388002a40a41440004c0c1d06054008203800d4901c1ca003912107806981c0e6600c810840282481d44050004540110401080b40309001425600c10014001a454100000d00c01034000d80103050800380030a5548040e1010340140c1003120041003030908905001030b41c1143751080c0014070440380a0034002070031103c550350612907101104410600759900c102c10b88510802802003142e02d1000c01c655503545c0b01000c03000004e4036148407840d5117240c516801c2800740012a00001d04951040c8038501c000702d039031448001440b221502c019401a01d9161600f40140c0d00400f005076030f030240c2d44103420b10016817404902242c0c00a000c0c00d000d42d4441e031b107140c03041d4503106d1503000f07000501a05001104000c5100d4920046801e403880d05901701c0303080c84000b41248015182040940d015540c0c4000704c26170303908001c1c444015000010705260304260214255003405804491741503070707104900240350380700c085507018041100a1081c01350442e400309080400140124052 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 3772130 1250 3770880 3770891
    0xc0203030d050a0902220605010806030307020d05030d0509030d1b0801060f09050303030a09030e0303180d0213050a0c0f0f020a11040221090106051002150a0209030706020304050a0803030c040306 86
    0x6a881a0000808030f54081c0010024985034808101c8021b03540e1110481d40741440c0740001d0700d6200b1000700740164001000365260a0280d800c11510380340014086034075000501000d0500007680c40303075070b21441441380a980d0f1410454450003c030f40c0c2d9003442d2074280c010031800c104003680c003a03070719815280d0505040c0008103600c03200351011f55055010507450320002041088001c01030b0070000300380c0e11a4503070084903590001090b46034000d00a0902d01020303c41c1010245141c2080440b400a00103449480080100800c031000e490301200d08841c15525024194085a840090525064030900d024409030481040c000c2d00c8110003400980016400c0d43c840d5034564807541120380d0324070710101d1703800310f080700401c4030b90a8402100c0500641d480c000000a440c01d0100044887e0103040d405001407203441e12740ba070b43c03c0700040e002720b4449900b40320480454504010f9280600600d030000c680700d07480e00d0200125420700c0e4018081c550000d0040c0995940309009490903660300a1002c1034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 3773380 1250 3772130 3772141
    0x305070504051003020d05010b04030b0408090103110301090c080901020a020c091f03030903290f0403020703060501080304170304080c010f030216111f0516020103060810060807060c0203030d05 85
    0x81078010340d00120352101c1403007101501990580d008081c150b51740002442a030b0390301d8642100034019440060702020f80100000d00052802008001c0d2103c14107000840c0d40715001140c2c0d160301b09030003411a07507503140804c000d11600503449a6100400000a40c5030481c400300082d121200d00743c046000300000c90100b000481d04101070001c0441500c4150342c000c1d504e080007043d41100c0d00c4196180c804040d0748040e00f1040d0071480303aa14544d0560031481e40c43d0050854000800180260110b00070400d000c80016000d014107402403032403600458846080c00503451004c0d4a01c6c0c49400d0541c020001001450030120b243c0d81d41240c2420301002c8041380902c181d0191107031880700302e03900320041c02d00390412030b50b0082e08100400c16201d40e8208604000e20642aa8002c01c4070070210354280107010281c814134080482d41d81c818540812507030b0341d40e52600d00c0c294445e4490340e6526100c19040c854401d080041034010174403443c1800c1500700c50380100c1d03203078851400d124480c1034442c0300044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 3774630 1250 3773380 3773387
    0xc0f010906030b0d0b0403030203011a04050a0302060304020607020a08060106140c06070c030c0501050901091101030b091503070317030a05070207030b010504050c0c0d020f0616090504020a0c050a0807050105070507030807030507 100
    0x4040c2d0341c1017034540c0300c4c514051400400940c0240100b406003201c008400800221b4402a1002c2d114003404002c1d14601315020040745402c010022030b88a84200103000050b180c0100c154010844040144031035410315101411141000340d40c910039882c24051140d03260344c0052000d40202c2c0b01d0406400056541c1401c907041400720202030025806c110904c8640340055111801c2280910010018401d41000440a40d210000d250f9809501704011404581081c00f24040588005040340c10040c0d5a580302c3d44034285d0f690059040c42800300800a00c1481406440d070701c03561510142007490b04568904404040600440d4040c1c3c0d551000145c100e000344089402040c13041040b03c81e040c8004034000e5440c412a8907107081402a840492942d6180031020b00d83c51680761910321005003030800780701c002e4000107040070070070900740021400b01b00140590f031034003402544e003980d4a01c0e660501030f0070359501501c11001c00c1130401c801400f20303030b1140c4200c1e040758080c0740100c2c198880a9085 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 3775880 1250 3774630 3774649
    0x70f020d020105070b0115080105040207030e1009080a03080109060503010603020312031e010b0903010c02010b030a083001030b01150c0308090109020a060903050f0705060702091b03010e040201020c0f010906030b 93
    0xc0000703407203038008103000022887d50440300203503940381c003001ea032940c0620050b80038581d0000e01040c100d102c903441e145031007400d5078034910701c0b031508441c00da0361200781b5840c20744010405d42c00f0900e40c00050141d84841e0060310042d02e41a4000d100c028a15070200e030755800c141d401407a086030080080764484002c410b5000003058214012016540c551034602e1a992150301298480d41c641340c03510700440c1c018010b101803081c0060241516000c1602c3d128982e40c000c566520313511041d8001c5040216070021211094074245242ca0b10540c1946081e00078444180c0100d03c0c0c0b08044401010341545c41990140c031643d051502010585404605601500c82c4c4180203500503000c0c180484c190794442d942d44122030040c0e00f20746020241100305074448075140119900604100900c00160404200054021808900c61180060049200039441e04203810a515529102c0d051209640e4104103e02d150941220490780010645c00080c0c03d071151071096005050311030000034066036400402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 3776986 1106 3775880 3775883
    0x80c090907150c15050601020d030b0a03140c030f010203060301060f03050303060607080c0703060f0609151a0d090507050118080303041e0602130509010506070f020d02010507 77
    0x10001248205414000d0440364900002c044c1200d003038803440d8207800003410742000030009090040d001a220205410200c040d88150780700c103039200480b0b074045544c4602c00d80e0300140d141030062040c0c3c82d940c107000f641c02c00c4030805019002184a100300b24001c10540b600c902c48242000c03070500010b442c9500074000182281041c2000f4544940103900e101d040c0140c0500c12840c1c4440c90700116a16500c60305990b180502d180070310b4000c0d103e020030601c0300d0641009002d600c4215885a516840c240002540c00300302800202c1d0b04565801206020001e501d0914a50b41c0000b0b101d40c0c2c0c00103104917201039148510105101c150303444840654a16111038a50401405c2c9c0c5054904030398030000d030f0010004207688014076129200a026040d850301d88000c202a09005a11103400380704c08100b01c030001464001c005026690450304001d0b951018001216540101c0d1070 = true := by decide +kernel

theorem cover : BRFrame.Cov 3597130 3776986 := by
  have h0 := BRFrame.cov_init 3597130
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3597130 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 3597130 ≤ n) (h2 : n < 3776986) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
