-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2658
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:21:49.063455+00:00
-- url     : https://prove2.me/submissions/0d5bfea7-a72c-4d79-a2aa-a4a8fdc643c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 477877697 ≤ n < 478057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 477878947 1250 477877697 477877709
    0x50d0c0206070f11030a0e040f0f05090118200d06020d0606110d021e1221010803122409100302013c1e03150e01060c0209060424 57
    0x190142007000d01e40718049115213620b4100045007080c200280c192a0100c180c8030f42600a5038a014843d403041080c0541280000a803800042c142461140117094441000785030302e155000103d601c00103003201c41010b200010050880306c030384030020000740d9184c00c00341d00505101e00220f40d1002c0090350740e11407811600c00b41c0755103501f5042c2211882d1035901030340d428400758001c400c0008110b01c027a0000d504136039540c002c3c2c1b084920301001218444d0020801c0d003404540607510041c0c541400310604e8003400c0070700001c0d03041040500c5e414003003180c010070501113000c00d011410000c001c80c0111090b020300c0109607044502d007000d840d0b14007941d184421ba00140b40384800d4644564a9250f0402c10590103d00703600030058030300d4501c5444041c020700c50810900f02424003641c404500f90544031906682c000c12040000f81100c2c010040d02e401550f0b00900c2c0e080100941c68104000c80f580a0b1b06940710411340c4c0c2c6c0c0c040050014054010409141e0301041070410407030f6151741e01c000503964 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 477880197 1250 477878947 477878957
    0x20304110d1a13080a0809030d020705010e060c0708071e080c0c010216060c02210613300305090f0706020d0810140108040c0f141f0e0d03050d0c020607 67
    0x5185850720f00310761061140604021410070200c6640ea1240400507803060503081102d152208141160080340d01510056825941da141030081c5443c0c18071910744c02044181e0781e1800c10300d0f01d89411143d4410008028180d107200008000404101590300c503285410551a1b500c4141c1504065210000d4103809401405402d01d00c0f0b21010207409010140c8441e0f0343d90740e51402c031603802d00c032100126a04211403100740e88401592030078100152446440d0729106003162038441d141c5a52041000c0b4030304003034043d4101c080d404a010340320164400480f80d14002c10152101011942420300030489010f10380204c18021440e1034001885285518055076440066541c5441d80d0014020501802d82c800c507003001d0b40d948540c810303600d10760400d0140000d220074582d01c10b05181080040d0780a818415181030341c03428685006843c40c021141c00c980314102c9100b01080040010707108484c13140c4594a814440c10500d4070a100b51901050051820815064668006583c0d003500710360880000b8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 477881447 1250 477880197 477880201
    0xf0906020c010c08250302090301050103060905062805070e120313080708060106140d05070206040b070315050402130509010909020901080f06060f011b21020a15020304110d1a 77
    0xf92084002900c0b03464201c98070400c0c6850792000c40f410501100e00c920030550280543c0b86556000e01c502070003981b0804c4001909040392410b1400d081d4002c01150080382c0802054062040548582200164054000403c1e03074840409035065240c1400762354110198055101c0040340000c0180b01121180b115410032642c1ca4103000e80c0d0385c0c980c0c043d810250b003290004104130360003030510380e644400000b180e606007100c040c13004040303450491320f00c801684200c09000034001c1580e00d943d00b1803a149000d06c09511221a42c1c0035814071449800c3c0905d50001c0e0040083d4890590b003405080d008114403180d5075540a0f902c05031080f0001684520341284c00000c82420008200f044080706d400685400d5a40100304819520075907846814811503c0003c50120154400c107481c41d403150102a059441c540f408024546003010140305551000c050300c0003050104410707a1b160740003d040560780742d9841c5045ca00004603030039945c1d049191603040c1010025490007050707000340c0440c6403050603 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 477882697 1250 477881447 477881471
    0x20a12060b041802030a121e0305150904050606090a06181b02030c070b0717030109020a11060c0d1505091e0c16060209010c1704030606050a081f0f0906020c01 70
    0x2412034200003907056006c210710b0000510b8065440c2011407041c14441c0f074000c080442c500079002240b01403400640d0fa80100030210004010890680105032003813841440c0a50f2400c0c1e840f2005484c1a210f400701d140020440941ea030070038006040980015201d02c428166500043c00c010102d07014168003806008548510000640d0041268013005041d00c07882d10481c0c0307007190301641c8151115081510015810125078004500030401a10010782e1201162002805030b00048041940e5800c940244402029800147c84e210f03804040000340007a5a41a00e5040829a60010f6044100c0b401040008100d01000492142c01c2c41e800c881c83d0364524100204510541c415400c01407915205074000c11400d901408440f501814080f401035040c1e11460b40346d00e43d11041d006c009200140034001c01002c1d014100007000165840d1000500380703800f091f2200c0c00c40b11044c0c02100602460b4100d00c01603004260704031002c00c02000000a2420840c01962022810211715800d001d000410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 477883947 1250 477882697 477882731
    0x806060306070e010c050c03070f090b0406080601092403110a0806102d1403070f030209130f0b09011b0806181918030212030c0304030804020a12060b04 67
    0x100c1c0b41c1ca90749064804200200540300c6031400d407019203191141969071116514100039403c060040c5600d002c0780c1c00d19180602d400e403010340c4801400303903041034400c0221020001d1300e03d0540b00c88080200e440320b600c6402400c2c1d00000e04d0f4602c6115078800001003070258802100703200719000e94441c4c0c00341303444400d038940c1c80380c0c06e4030714609007a4a40c40400445603200c84041c5040b040b40c4030518481000b2461213100480307504603102c90f0300b10f114018650301d003c1041200070181c100803511003900d5900041d801003001456100c1c2402285410410004050003444400380d00c40c900d00a02c0c1040d0403158003c0181034900c500c650009080c0d02d0000e8003400c0308030b2042c039004055001c85c0081c000c403200400400f4011400c0220400014418010716019a800d183c4003c80c001a800c441418000d00d45800d42e590f000c0c0d6101c08005101509a050040341c0e40250941003413501616540301080c000c411550208200c0350744110040308100c03541c1c101107402c0b00300b11003c0c00040b454540c0c0e1b03c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 477885197 1250 477883947 477883951
    0x7030c0206040f080306011e091e120215130305030d06120b04200d1b06050703050706020a1704060b0f060a171504141b0403080a030e01090c0801060806060306 70
    0x728101d0072165200000c0c107890300542e13021030103148c883c51000c00c81e64550340c849041096200402c1c074a000a00c84180d40b0560100440d40410304468960318202020040707224140e0007a002c1c0306001001200026420700316101e194048072012691607032805d0454a07900301074007a0600c0750501c280018640c1d039036140700342c280e41c00060380d00306900c91b0349da0040904644088800280e10100817080070b656200c001c558080e00a8030501002000717840800b40c115481c2d0441d030148202840030b0000f0941c49815200025400140103940300c07640312054988601480344501c111100004100030001d240c0c04c0a010900d0540341090144100303000c10601d40509000e0000041e04000c29102c1d8040203c140ba07004100300d00b026482040440219040c2d0b00130707491030070f41841900103000301c10721010b41656443e031104804034117050450b5101d80c80742c8a459191401c047c0c481c0c03010490360000798400b1104660000081f80556541c54081340a001c042c801c8141500500c800500141000314044d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 477886447 1250 477885197 477885203
    0x614040308070c0f0b01080312100f0b0c100c0915020606031b010c05030a0305040c090204030203030901120f06141806090a11070507030516060c1a070e03030304060507030c020604 79
    0x41c4440d40c500104484070b001c0900240e4000c106500c45602051000703010300d0180200e0000f86507194101d81c0b10380125880900f8050180c0d031036400070444600030090100690b580e80c00f22a0341d804000c0701703403490b1840344030720307103c0d4940740c808003040503600712004000b12651121311320394029103034400307030380300c03072085400c160550010048184151410b128640c10a28141070030000c01c0c056441c2e403440c54100c640040b001c65170f50010b0209101d0341003004001414910800d62425085501007074482c000c50705c3e0785040c0880035841402454071074005908024040204000d095580c8000b02008094000d0b0503020b01c1da50740035a9006450390861510410020706603105c41c0e11900c403103000a141030407080d008100240b1800c80000c800b840382ea0b000394000c000a00040000c03160b6401c54503081e600003010701c1701d9012807900058001101c01d0f243d44424860000d03903a5200700903141c2c8010901c42c0c0d681070000004020812200d5408030b4062651076a0820840c0c61117a4240d82c5c0d00c40a03903020b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 477887697 1250 477886447 477886457
    0x11e020a030e030f0139050a050a090b0c0109110d020f0d0f02100206070306120209041b0504020703020609060a020c120913020a02011e0c0e1309021c06140403 70
    0xc2010038010b4040510495000d4112481c0204074000ea17801c6401e81502024541a2458408a001400c035641042d000481c411a00c1c9458507410281c10b511401805c01c0c14801d01240720740920380216400c6006052203405540c0d11855250380c14000c007090345045846888104120030b00e414840500d110895020300300407001d4201d202082075210242104540d044c828141c2c03c001038403070400c50b8040114075001400e4602f405000030f010741d0a190007501c0e0784500d010540000d680d6100941c0d0300241c1060305118680342800265107070f0317405c6030459500a4000a40d54080650004e161442160100d0603988240c4030401c85005a1148580103600b50f44180541803100240c6401482c034184001d06102c25400b0700350080c4140e821503916000540d40d03da8001e6030001100040c18280d40c1e500504000e17044102d58042d00e000c160440d450f0088404a00d4a00000c0442c1d02c04075010342c0061040d4030102c0c600d643c5980c5000e840404031113090508107902e0408600c008a5030040c1d40c15292 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 477888947 1250 477887697 477887713
    0x50f011a010f050d0b04060b191e05280504030b0108060106090b0c031c0b0102012d1d101b030c090902090118060f020c0105090f0d0f0605100302011e02 67
    0x849444d0043d207000360000781d07070f50140c000c9135507a0b22640d001419000059916400d0f4050482070a211000b04141031041450241912079110b80c40e03403103400701a080041e115032060144130400380e4400b051684142c40c0031701a0100c642c000340a4021240715041369841681c80303600300c0d40c6032a028882c3c04041441920107006000b0942c019001c2d0340107640450303080c03451700e0041d10407800381d09811040069441020750207d5a081c041c0740c0141646d00e1041d401440c0c044500b1141007030031f04410b40d0041d543c696030b1140101411240364102e80810458000300c104a4141e00100700e0109841c10411301c85400d628924020300680e410000c81d41c8810f2030b01441c040024010b940140c5070541005004200340242142200c054406000300e959000504010900082e2030900310706026070500000b480b0b1a051a51556a4450148015500348058881d58034281c1c000303080c01d04008040c2c1d07042a04002c4100190700c0000c0c201c0e4001d80e01d404c003004c0001040c0868034100030503440180c001d00a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 477890197 1250 477888947 477888977
    0xf0e0c011d010f051201030c090b01031a09060307080a051006050d120e0d081b01060f08030301090903050c030c0f0c041a041508010f020d0e03030c0a080403021603050f011a01 77
    0x80b0b081d1036000c0c44c00d00b9441c1140300c031220268403100760001c51780d01454a4051142140a1141c00c0403038000303080400c01d5001c0c040c0d40e000e03510121010584500146000138500e92030034001e580040c40c101c4100c400c004120301c0e203030303407101811403960070154600040007510389070030029000c41c40c1d04080360206070740400310b003260101d500c0c502e0550440d0f58180701c2e800080d801c3d4010f2036811054180b40c000341c0800e50704142900c134240d100b12081311601105001180e0080f0441c0c0c1110607030700d000a0f00503d54a0192014010307044440e84500012452441c80c0c20081008141e465082042d1494442e4410400003101d4092284007071581040ca260241410150320160b0b0070805000d00f4888103545100450075105548a281071258020464244204881c000c00c144108064080c41c2586090014000c0740e0080c01e85500402c020340c000303e02810700a10001c0c01211096000b20000307612406d03d5640c0b0701c0c542c1920451036180403800c0f51102c0c5103581550540724165a220312400400c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 477891447 1250 477890197 477890207
    0xa0503090c120f060106030204050303120615040816120807022808011509060311010503040303060b0403060b0909070f0b0a1701080f0d031107020409080705010f0e0c011d01 76
    0x3015200244148148102142c0d5001c0408000b10b1002d00246003c0040800041c180744040e444a0141801031105000c01c0d40d01206440b6021903009208200c2c5e5124070005100140650050159540006021512a030302041c5014101200709901c0a0b1541d81c42118809611030100580b4040060100c54018034013150131145040e06025038824a51090100a810a099500252031a95111450141e5820070400a0b00403c49880300300080c91031078442c45507001c4118a80d50401c40000005010103000740d100c0c0004d888502c14468a441d16072900c10010251b40301c4030f501c602002c0e000280f1000c000203000c016180c010a00004151a0200d5850b45820100b03001041c4800e0b04925900c80c1900184a07009109210080c104810803919141c100b810060549041608081809298854071011520503650503903000a0841300c60a083c003039806080c8004066500f07001498020b00550741140c40f84c030980d44140c400c8040c690f001034038030000078900d07131030400101140c00a10358010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 477892697 1250 477891447 477891451
    0xb0703110c090109022109010606030c08160f11030f0706060b072001020f15161806080606190207050a080c09040b040f050f03040612020313020f130606030506090a110a0503 76
    0x40d601441900000c2c0340b480f41c0c034113403c1f14031031000da6450804102d80c66040c026502e47d8605400c2c52549808c2c480603000620070007910040520404203240c11410341b0840640c0440030501042e81d4854040f0042d01c0c00c80c1d403003203c091301e441e41007003c0820009142c0007228907955004256061610049202402108990050300c0c10760050700850b0000c2101804401e1131410107074070300016450000c000c2e01800c8607424404042000800140c81ea14a080b2615400c0d14510b06110030340350f96010010710144510304002d180340340c510500c902845c3d000038030700050700d1040719044942911400407641e20316030b0907102d80e84071481a021901043e00302044a8201e809810684c50100f0191601e03440c2807420303500705c9040c0d440014100441d60b408100780c0c0c0b2500c100751041d4076504011003041c5902c018200701900c01d00b03d101310320030213a6894142e40961900001c0034494960340e06400340041408441d80380c000e05103080003e04482d86403082d800e8480042038000d041190a620468441e040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 477893947 1250 477892697 477892717
    0x30f1b0301050622260730050709021206030607230702040e120307030e010b0f0f0a08070b040f0801020307170c0c0102031602100b060a1206050402040b0703110c09010902 75
    0x580d0700101c5c280c4404050503004410201500034000c0411a9140c5460642d6101c40900400c0481501032000b08000404030382d103015040003100003d50900904000700345c1d0190b603100d4070008104000308207402d186031203120100c095480e1641e404506644100010300854004038044141c6001c03180e4407000780c481c0c9800a400041c0600c0f65085051506500101101f280c440100800c440c050f4075000d070441c0a0349182c005c0c030826914001040118031400c0c00180700751510b22098449440780006440100b241100700c85080b07942e07514003001ca90240c0240c4800d04408107000c1401c000c14000c407070181140d03036210505842d1640c0c00f1200036001400301162000200a100f0351902c090001c2c1d80103000c0e00700c0303452401c01605406403900911250b401259800c05070301c80d80036520381040d20844009810115502c1c00c13002c00220080902d40c103c2c65000e8070100740401d050550001402c1e400344030303445240c400a5500b1040e5622110b800041c1c3c0d0000c070380c10050100e81c9181c1c000c2c105240f2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 477895197 1250 477893947 477894007
    0xe01240603020f0c0106080a02090a090f1e020d060501140105040f0515071703060a091503021207030605130203010c0516021005040506071406150117040f08030f1b03010506 76
    0x110203c0609443c187e80c031400c0264410200c1e4429480c08510040d00821000420407218545d03980e50808030408500142c844120700b0381920066102c03000c0703000700036030041015800c05002e1138000c00a04080c0500c001d46454142100d005500810890f4140e581c9100e4203000c861030f10b020008032070080340d04e40d02110400c4c0328540001e25298140084045041100c81d2079282c940d06010403401254131100300e103801d2401000801ba40a140c0505880d010345000c0d032080390200503070789071a286a1000b41201c3c42c0408205292003ca4001c000341b40c400c0700203208807645200308035078502500e0002a244c0c1100080c000040c13500c410782030b0f40d0043d075040103814140d4a20000c4d40542208400752504142d0b201c45030b002d00c606104c41a4071107218000401d0310003881000800c200d1000700880e1144109102040920040700c100c40010b941c8000c40c26900d10300301241498401040c0c4160960410310000c0003901041030b000d580c180d8001520325810011064a0a100f40500b0211015045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 477896447 1250 477895197 477895207
    0x60c200303132d150c03052a0c011e2d080709050303030907030f06020c060718080601051309031124090105040206031602070503030d0e01240603020f 66
    0x12091211001c000c1c842c0620100358112031510051400401c0926828401c03003403901440134412603a50424003609038601040c040c000c51070180c845100d10524071020480e9502e08400d80101402d03101e8030307041c1e1b050544509940e00c1d001901d90540301e80e11000c0c0018000c00e5000710f1803140d40844004144a4284401d0840415550101c001545514000994500100001e0075001100c0303100030001600214035510307040581f107440320900d00006103094008600e803c240017039a01a5402840b142c030686890b8104040050f00f405c0e040821140d0010341100001001c0d0008940c090403200c0103007088100e00810b034141380c02004c40d42406c03401e000e11034180d484203400401c801031816064030100050040036401e900364601e4003e01142203617050008000041e1128019030741c0201c090000381e90020704844050f81000c0c10f6800c1150907110104800c0603410380c40d0400e098000040000304078800001d030100840c0b0300c40c0c400c0102580000d01c000c00806e4400e5000307040a05c4030341d004508103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 477897697 1250 477896447 477896467
    0x40e07020a0605070f0f0212190c020a0e1806090606090414010c051b0303010503030a0507080c030d1d03090907180513050a320c090603040c090501060c200303 70
    0x841d404e642d40000107071000403403000ca07a00124165070381081030005150041c4460014231040c400d821994849250000340654000c0c0190040c6000c95401000581465101c80e48681301c0300c1c080355032503410001001c0c260444200850064056210240500201c0c1d40d000305220b06404050001c545c41350b40110b522240041c01c0c49484052616a0f1799542d0740d034401e040e51071849000420401043e0000c0004003da507030000100d914010312810015151485420300b8100c901600e6421101030000240240c40001c840d440794a06600700c01032020004020028103949000b903100e10f40d080890007002c119168000d000301e0b0980781e11031016424864440001c03070b103418a04910a185251a281840510441c500a0441c00c40003502a518405450007460311004540c02183d02510b040c000401e000c01c0f0301c5c0040359894440501a075170340b41000d240c8007400c8400da2150504140c5840700218140b0303c164200c0c070b40c058010f6140303a0320300740c10075420203210850141e040c2e040c40100b180b480d503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 477898947 1250 477897697 477897701
    0xd1e0c05060a0e04050a2c070e0c03090114063f0c03010b04090201091716060c030807021207060b040902090f04210c0b0a06030615051c020303040e07020a06 69
    0x9072110342e8603e103048540a06000959101921541d06941080c800d040140c0500300c00080191514403c803640d40040001c080c14603529030801e14011896104000403650620001e50107448141c000b001021410380c0741401c05030065550b10740c4844d04905604403000c0100c03200711103901c2c2c009041504031194844c21902102540c0d00410380d0007284501d40b0310301d030030312549040c8139090302d0a00000c0c03d40d1340000e00c952014024010380c144180c02c5062007900030440c0c40c4541101c41d2414114a858a01c0a441d1400000d0200c00060100001a400c1480802c002c403e0a4001ca0704504055503a42d9110240c004010b80c190442d95522170301e0056a01d500003103001d01503107a2040c80d03609080c02c110b4199110101004800c0780c04074441c0000c5a8444807000c07950780c11442034034480d21800c29050190101d9030001d00807a08110140300481400003030041122400c0b500510494103a080e101748100e00243c0195140c1c0090000300048400c500c0c155038042c0803441074609000d601c2e0b8600b41 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 477900197 1250 477898947 477898957
    0x60109090c0f030f090206070f0f05010c09080f0c130e0c0a03030c1203020a0c14010b09042406030f0f0305210402150306030d0e0d060203180105060d1e0c0506 70
    0x2c4000403101007041d003521659424042190050000f1400c42d0045892441184ca0080c54411000c0a14080c020400050480076501500900100142c1480103180203594000c0348840d024102003910340f11400600b040c800c00703000e008844400500d92000d00102020412100e03036000c0e030114215140d8030910405c010314825116840750000310f0420900d4000303140f04a00a042c410081d2802481d00110340d00074540c3d0081c0350081c600309034a201400b41c05500c03000c9401c44011400c0c4400c00035a502000080d41e03185102d0f1104035000800307502030360098031001c0c1c070701c44682101d0f50214200903000b16200e070003810814030b050003940444203041d08007078a05410580c90024081180b8002a00001c0c2c083d44000780c2e8110b0510b50002902c590a072075800301403000494001180d41c81b6818410020b6807c030904544038500145003100b40f030006004210f440d460100060340030300e4403207482909290000c2010300d4a004030840c49018100804050380c13040e020281c00669a40e07800000c1c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 477901447 1250 477900197 477900221
    0xd0f0606091e050f0d150902040b0a03030503040803100e0702010204060311040311041d030f0301080f0303090a06020a030612050d180b09011b020a0f06090816090506010909 76
    0x1485858040e0040004103103400c03034807080040200c2800c078048407400c0e640550303d0071107207400040c3d9070f100020003404541100030071040c840318020130174000302c0e4000034016000352414040041d2240412940d5005400010040341042c40494007150340f01c0095035201d00b412a86601c45134440c0001660401c0450320540107070340004090010580c54000c0c400c002081e05c40b40e50500781541e070f51003e0111000c1c1140e011341d9850f00b9a074041e607008100080ca2440320010b0f030755a02502c2801048a900034054882d961048034034489a00400004482c4241a004043e00405801e5514500654017012820081503100c0300003280a0350a014020590b520640080001c00981c00019080000400d090215020305040030091005440308440501d40300f480c000c12409017030400055101410f21b006504410f2100000c5058003214038207009031146a221003090664a0062035903c80307052a0401c0c22440740c08003004500300940005400000c141005040e4546880000f0110b42c1c40410417 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 477902697 1250 477901447 477901451
    0x1511030109061a0910020705060a0306030b240616020a09020c0c0909070b090d060609020307020f16150c0b15241e130e1b09011d0102030d0f 62
    0x104503105041c842c80b40141030500511002000d10b0b60040954003c01d0300e19030040c00042001d0000510901065014081c0280800d880b00b421800c005c006001c04d0000700c90990f03400000c100035400c440720040a885116264840000c13030401805150303000300c42c50400320410200d241005948292403c0040c100a2a0040c0c607072002d0302c206480c18600e4103200f40206400d40074402004d00104440742680c400300341041da1661540089001100c502c030000e09964503100022440010540040d03008200e990300b110701c00d6480315106521114041034090030328140306070411204940c00841d61840c21103052102c400ca4a9480303130003545104032030f005179201ca45a1869030034a0a41c040c41c1d000e04021080c07481c0710b28a000301600505c20385d207490215a900510034614140b20300100c683c2d00801e80d540803050b42d030310043d500e50a070741911884c50040710b180015030100d1000341580c0b481c15050f07484d0200d07052420329408044506403c0103045010801c20004044c0c030340d0242c80f03c2440c000c440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 477903947 1250 477902697 477902699
    0x3080c060f0105090601020601030201082a07020f0910030204050a020714010b042003040611250b070507020d11031213140306041a070207050907080601090b0408150415110301 77
    0x141070308400d0140c2025100390800b80c01c0c0841640d00146545c1520380c20b00300320f2103607102c10180c82485482c1003d03a211a4008a8000e038076800000051f045140c070903281c034413002040c1001c00c021200700b104e0f0028403600303101d800c00162a01c1d070005900000c92810041c03a14803151120001036035040c05100c00e81e0346a02210065040503ca1114005018464008030300303d015610803051101500103010103845150310f10200e25a02c003200c21a15115040035003081c4564a05802c0410046082d5402048200000c00960040c03003115000c5500420144200645942d241140f14507815195090700c521404c014014081c03400500d00c144504400041552038041c0d152a0300c40c422640b1400380d000301d4180b1000602c07a2040300b003c0215881d0801003030f40c51600c102e20f0079038031303a11040d4041d0401e000d0052207038000340c040e4000d0000382c0c0e41d040015111500201107110703601c1207145690000c5c0c04038507445c2480c5629900940302c2c4816001e25080410343d04113640d11040081d9001c580000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 477905197 1250 477903947 477903961
    0xd0207141b01140304020f12070e0a02030423161805161b0312020f03220201020c0432190b03061b0c070803030a0b0603010315020705030403080c06 65
    0x4001c4000405000c1c40311040010480000d08501003920440da4900b00032000c5811036940204000b243d0030054041000464400042540d0b82054400c40c0d080202403030120311a82024000c880c4200d80007803e0304541944009104e841041030f4042d44038500400d00f01009450b00780e102c9070020000f0000c5941000d2030703020744c50226000a030502455499501000501541101020f0300019600c01c0318070380c0e014641019144840080200c410b07091000481000364807141015500030365203010080760380d20851004044e42c81c024080a400743e400411417000307030301d80b9030400504041d940603000e10304007260801d943d03c0d4041840d0046210050400c21480b100001d9590060480001c2c090026000140111783c803a10081c1034070040c104c55895202503c0d850504403121056610121220b0541c4e44407a55201c0d003095a92188450901060700b500345001c40540c0d040c0da0b000822000c980c040c64004030000d40c4070030400c55040c0800d00001000c01c5408010304401c0019802404c03c92030580 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 477906447 1250 477905197 477905203
    0x1b0115140306011802030c0d0c08040c050303070308190f09200105030f07200d030606140a2a0803070c0201030b04110306040c03060f24020118080d020d020714 70
    0xc54590300a0b805400100900d050800c41d5900c10081c2000c0141e0f039440e6545040300601c558000004107034200081045c0603a48034007150300c943d000e21440c2503519101c2c01099200d01c14000050001130340803000c2442180b0118a9005044600c4c07000907491401942c050f09840c046001075888159861208a08169411443c4102a000d00e010ba203186440d6140d180c2502018101104128101c0e01444c1d0140e0584540603600d2419011580800c0d081c1e58010058100d60103a0f9001074038481c070382d20b0011a48020f07505107203486d4546442103201d00340c1c007a196001070741c6080c18001680400070301082d6180d0065001780c0880d074403607034100700034000502614940c034a114095490300e03008050311524041900d4002208541c04990141c0016003240a800300e5000456811102c2c400083c4403c1c1203038114040c048450740009601c815010140d080f039142a0b04c1101c3c400341345c94810001000c090042452450711000181454400131841089800c643c0045801103d5450340181901d410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 477907697 1250 477906447 477906479
    0x1504090605010206010501020a03030903120f050406060905091e07030b271203070f14031005040f05060d1205190905180907050f0a0e15240f1b0115 65
    0xf0b000a108952628000030355070101c080c1c0281c1010358500c42ea0381090710903d031040100c1e00b90003062003912030400003c4000d060548007122aa4500440020865020f006082c4a04080e00180c030160420a44940d42241040c880c04e040e40078a0101000040c01c0d8042c0314024000148509103c64401501c00407a43c04020b1500e1158016500b0700c00341d0020004490384106a85007032141404048002c1e102000024641302c20010040304200748034013000e0603442140c10498050000c00e41803034840c801c40350256a4a03401040304004000441c8008a56040d108402d01c2d000d4a885101480d40840030783c100d80e20400503880060800040c03a11841413011121a010a0110781c2054400c556641040f4450240204038480c149107540e940d40d02d20400914402801c2001858512102444521000c044c0d82c825030300b48032800f031030b510075822580c1c0c00304040c40500e182c00c050f00508906a04a10600c80c003c1c41140e20100000b0804e01500300342c0c030654504204000d003024101101e528072 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 477908947 1250 477907697 477907699
    0x10c0801120803040602090613030305090f090c030f270c130e15060f0a080a230601051c1a091c08010b0a0c0209011d0a0b1e030c1504090605 62
    0xe016140c030301040c1810110f03074105600090040e43d40403a1070110304180a000d603800c039000c41c0b040d400824150020000d0825a0045491500316216501089803d180984101001030b00520002c0d01d6102443d180540103004140118890151103070031201d050340c0100001c41680000c0e050002c41c2c1860008015500d551940500460490301c220560b00c0883c80030140340d944050010030760300c0d240c2c0c614a644040003d4031841d455501d40720207950340c070111072040761098211580c20700e241030a1841c111040b0354400260000743d1900c41089000c5929411400ca00c980c07002c400380020707004c036a40640958078590880842d14144203102e0408400b0140d802d801c0c10840a04000a038bc003d0445040d900104642612400a160b04440c041d4110390002d4010080d800007050702303c040c0c6400003a100305100d050700761750750b410701a0b015030b0185505250040d4410100c60742e010b03800b02c0801540d040103400c0b074500d035004000050380030411900000c070b4050001000d01920711039000790000307014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 477910197 1250 477908947 477908969
    0x161203021e030a080c1606020c1c1b06181a0c04120f0611040b0403050715080105040504051c0e1f020624040606030209030d020703080f1605030c010c0801 68
    0xa451a40035103d104501d203003c20486260001803c5800841c150b81646030420721000d414007503485c00000070340c00013000c1030483c400e42c0c11003100b2811203002214510502d40c5c1701c0e260030040039228103100501c9902101c42540b0340c0d000201030210604400100e900400448404645942103035070201c40103046042c0d00201004184a2220008030140c10705038080c005490706449070500400801984d4140e8100000001d00041c01c103c0d440050429240600d09494040b680d924000303200d0b50301200e281c80402c030030900400a43c03615038001603020340202d00f03407200031044861502c0f80160031082e60003c14800806042c2600740381d030000b0410a400b030f50740e140490701640b000c0e603200c4d40141001c00080301c2c2c1c94443c10640f0300714104401038034040c00130b00c801c6440300c4001e0045d40100c0e484602034410304844c040e0071480098048102d0b41c020b00c0d034074a0148254407842c100d921070f14503425201685140000041c0e8100010070754130440000006000d088200005c7c640841a0300c5541c03100c0b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 477911447 1250 477910197 477910243
    0x1030504051e01020c070e0f0708040c0611011b0810050f0d020f01020312150108092d0109050321010f080d0e01030608030c0f010e12040306020a0216120302 69
    0x2200054114984040488140903a2185000c42c80c0648603d4511009600032660b0010380c51551500c0d00c0c1c040c0091702c20800180da919401210a50001c81c0d000d00501302d0503204000907030240300c48240c0c07401c600c0004100610f000c90801c034990301c00d44024002460903810024902c04c41400031010b070204903098007a500080c40010080180c2d20400781c8076402c10036441c070880e0700030022a0b40e296131441c01242030b440e0005505c00d1401d40e41880602241004c000070b2050b0700d010659650020202d050b5844403111040c7c20b03110b40442416030461503513034a101001040c0704002030403c6000039102954114289000c0000884040c0c3c8481d1440303040c98403e00807184049554141c5010f00c1c50100c0440c0003103401200682269403110a07d400005030518901e240070a801d040a03402c04000d004192003616580d5481400880726400480300344010300c00120030f50010b192003400e910440d02a04807045140034402c407075620140070584540800000c064052003050001070500202080391 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 477912697 1250 477911447 477911453
    0xa0c081911010b06120a0209041401061e08060d0b0601050d1a0f0a1d06030304030c06050a021b061b010605100f0e010203070c090203040c03120c050f070f060f0e0d0309030b0601030504 81
    0xc1d00c1c050001b9200780e030003041d0418a074889038400700300c031104203808501c1561b46480c003805403a0b000746182c480c1980800510080c0c0d004680c41030054002805070401e1201c20740314025102c0d0040c0c5403a04121007040460904104c41c0200c00d000e030016202c01c0603007444401000540111001010b0046007000003c0001c0220131003603466002c10000700401594413100000e080d4070852b000107100720040000454056804009441d02c0310b032036002c80c1e0022031040d000681140b410a090740c0e20500811442c9120701400d0003280c07950340c1500010900c43d4944000458031030f40030304c0c40c5c00028004000207442d10313800b543d4060018400c0c0050361a0511944800c0c100749018003c014200341c000020500300081e82170302038021504004107408085c4090001040c00079803030810765052103402d0602103901000304074072044900511000b40b071589054070983e484800d1003040418004c82074038103540c03911944203c140c40c1d4400e03640c50840c242103140124075010b000d012281007618200c104400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 477913947 1250 477912697 477912727
    0xa0e1e0d050c01060e040305040501030f0506240c120a1e020c10020a0f06051905130b10150504030b0109020c07030615030f0b01030501050c0304080a0c081911010b06 73
    0x418000c41c6041556101800c015501400295000132024522003040205040c0d000018006940003682e0501460f00c00713000c00400d444042e503115a00402c01d40e08003094120340341d020b07050340c43e0015501c7c0c1005c1181d43c01904100300f1b54000502440300003412400d2544c4030aa01580c580d0202c120100d085948000960324070510003054081d0700044c0e80004041e0080040c40300c140d5122003e010010705618003c030107410155083e442d0540000812048002e090061034820030305901c000790341e0760340ca4880c0080700e88060301e0f0b41031250302e041300460100d1004104a5200740f180e16502e40d03407880c5213040c0b16220b9050380134540440c818000040c540d5008640c510031a504480c01280002da03401c42d101d44610076a00062880c0c0020740280200321580024038120f07402000204059500c208070620340e44000c41e0b004003106003c02c0760006842c0a2000340c81c0701c078024465507081c03940c0c2c622114410482988003801180d080d40c10380303190000074003a0303a0883c076050380c6460606a900043c200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 477915197 1250 477913947 477913963
    0xb070b060f03031908040c0e13030306140607021e13140601080c030601111612050106060503072c060a020c0909070f0308090f030a0f050c0f100f03090b0a0e1e 70
    0x10800004c04086803d004001d44400068034019644002078240003151000c40c440112703040b0082414040009100140d00c418a40c020340041c2c200c030f250000c16800c2200701d0f4110030b1b01c40c0e2440c003c061001007580b500e9401e09041891144002806452800340d14031145005041c14104101c2400308691518410140d0f50456030a0901c09120101c2d0340ea080e082000800c2c030180020040c1c20001005130101e81100389050040c00200000ca4403028120b0f030600c000c55017840458413014107401004000d070410424020032a0400302003a640070000351481d031007280501c0050703020880c00c01051511031043c0343c210786070000a01d500792600b1104088042d41c1c2c8009420400085002c80c07141c1c648501e41c04e4000340c0101601c058004614014001411011007a10035200700384080c03606003081002d00720904801099450031b15004542100c04007142c5c5289030030541c0343d08034440040d83c0c080041d4042c04101c9004500c8200c0c0c141d903545046480c04651012080e4400c03900320007070740851401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 477916447 1250 477915197 477915247
    0x40e0c271017061b03101a04090e03040509071b0506010e060f0102060412030e010b0d0305130614121f0801020406020f0303060604050d03020f030d1d01020903120307090b070b060f0303 81
    0x5922561500c403640c3c5100703503d074080181f2118401902005809050040040c2c036038640b010848001c420130700503a28011070083c180c128220201064004bc02600f0394108a0120b011b0450309014940d00c3d20704100d030030380c4036030206507410003030240c0e510b010031100301540c80a20043c4014502a00d440d003110b00d07580d6102c002c3c150745000e401c01c0041c0c29007100d1020040509820300c5800700d0701d0028520390065180d4250300e003e422022035024841c10011108540440d061340c04c042d41d4a0008284403000350180c8540c0c5e241031030800c0c5e030312000b85080000700030321000140c0b181d14080c006070410034401d9240ba840d803c204200f06040d40c41d00180c800350b40094400a0381d4900034a800e901d0192111000401880003260415040615400c1950341d00c0801601548c01407007403040174243d010b881826507050300080c50440c03045001c10061a80a00715103080e40920741e4940c00c0111650010006850f249c0e142c10400c1081d080050160750255400e0700150700d0b100b0745410a002d018903032034180c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 477917697 1250 477916447 477916501
    0x20d1a240d020705030c060601030e0d050409020d0b0d110109060c24020c06100f060509031011090616020f0a180b040209041415040e0c27101706 64
    0x1907000d410156040d9000e81c1e910808607585c1c0d044007801e00c2e9030380500303c078100d0000382001030b40c210451021032010807040380c6881e80d034141401c2c40100c01c042d400901d0f0154074190781e0381c0114110743d2030120340305005024131102d00030b0309200000184140e00c0d50700b018041c0010340d4071140014000384000460001d07240490034045013000d01c4440684640422510380c0d10420003488003c07643e888c00d070070032100b6916000d03c00a03900d040581c0c2601503c1d01441d4550802050782c0101231440d008026440d603041881403400302c4440020f403060f04041d503040600e0f00e40120080450400700021440031a003100c440e2481c40c0742c1141c00c403152500d072102044040d224800004241c4494049e140135030f10090045c070000c60050743c51041404101c3d003008864203552983d6616051a01c20f1410b0801450098040c480424007480039101c40840c6054001d03824070b856240f00e03075030a04114010001e100813455a103141000c62103c80c0d6042039a908181c00c040c1c14040c103281c03c11842c18141015030a1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 477918947 1250 477917697 477917707
    0x9170d060608091b041b08090c0d1211070f170705030109080f18130902040b01030b06041401020f0102030a020c0d0513150507050109081e190e0a0306020d1a24 70
    0x5c200a4803038411484040341e003551b40c1c204102e800000c214800c1c00108202c0c1c81e41c6452000304500c2e18484180540040d50214050103003030311668520f5031400c901c40454500320303654840c80340c02c2c1a103644160710280004603601e4100c0c106210300401414100d0090201801941310f0150034441c42044044101002403461890101d17100b16000c0d010004142070009030050031100050804184120300c21842e0030140609036000340706414074504090001810541400c46e2490941e0300482058154418058000c04900c070034001148601c0b02090701503100e0b4585030381c003858000c0002500081c400c040c40700400104840f404001128206010410000084241980c4034031850b50050040e508003450403046c0800000104003215400c1f855040383d544182c0c074000a400741c200f44000d50881d40c1c01c0546154071031906001c1020300100500545556555004226407014071000801e41d1070726402c145003a003c0056400500381a270381e400204152100304804c5220403108003001c5480410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 477920197 1250 477918947 477918949
    0xc020f071214060106021f02030403120b04020d11120106090602030f030a0603050a05010c0f1803140f0307110a09021809040809060c030409060b070c03140109170d060608091b 77
    0x1102c0402030280344107641d00c80d611542d0003925200081452841d280348480c007413100141a10032288200d4041c1e607594040d078421036a1030094800e1105c842d620503020301000380c1800051043d11104900002c0640c0d5400a804100c6051a8160b00040a026144200f0800d03150044201d03024105d101b105284d41c1d50b5001c80c2200149180d03000a022841151700840400405500981c2e02071800e07200c08400c400e40800850794008103145d0680010000039003080007560744034202c0801020242620403002c1d0030444549550032094080c0c80d4001c1603092140e103030a18000c080007500f100e0718113500c0e01030118180d903182d611004082d40034034580800603091045c2d5800f590803c18004207070300d41c1c2c1c041781226195030f0b42081c05244823003031a01000040e40b0226808903107006503c40301c214021840c68039003181109000b09080070765500c0d00070342d05c00511400c0100312215201902142c6a151041a0004958040d003051040c07142c030b903050040c10480003600314240780802e00c0100310b01007048 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 477921447 1250 477920197 477920213
    0x70609021906021005010806090d03020915130306050105060702060304030f020723090c070c0302062803050403030e0604030e060f0712020d140405060306060d02090a08010203060102010c020f0712 86
    0x61941400c818600702044240d0302040040500221110500069882e061000e856240690364458140d21040c517050200307020344c010307240c02ca000400c81c2c804906100280541684144182000b05126110500030000d0520440b405804280c58141c20311a00d540820f5a51201600140500503514a0b1846080c400c10072040900ba010300c0901d203450f0f010f031080e03007100e003060074462250007101d0010308502c2c105d070256200303da004040421914559001e000c016031050081c0042900170140d030b003000f2610340350420503030550340c3c0e00040c0c03d14242c20028104d4440c980031521a803c81028040840d0344100c0c0b181681c6001c44080742e4880780300b05007420621405c00c2c0204151080034032000d06a4010030100d4207580b1a0311a0904034411a04100180c455070054661000051020911030b0400101402402e00040e90052800e25190005010f2a2031640700000c141c0d000003c000d165603080c0600800714503680010010a800c808286464440c1c130300a6640780801c003880b21062042032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 477922697 1250 477921447 477921469
    0x5010905120d0e0a0c1e090219030c170a020a0512011217120a0f0b03010e0a0c05040b28030b190c0504270e12031f030807060902 57
    0x30403100041810721201886401000041e51018a01440c07555094000318194001d0355025619514041c10704200168104103600000070303a500c40c20010403903406902c010f00b0303181c500c03003280e83d07510000048c000c0981d0b005030346185c108a0340c0b0440c0503072400c40c0b060454000c220a1b102503260610b0850488650041c0b0300e0000b00340e602c03c800010225140ca1118410368000d544000001c012048261920f00c01c2c0300b10030304a105040300044448045c8d52288141a403191404100000030000080c25601120848922030300100844070400c10142d01d840002c201c2520180411001000010710440c505030251490717496107107498251050158402001d907a20101e50851414000c0340d4050000b00d000030741d0042c0d0718000031101224052070070707281100c0040c401440841454400820381d018031080c810f540584034124510010b2091007502d80758041c1000450305c4c0d1900e6400189180302e140e214104200c00b244e0b00b880898403142c1119040c50700101d0114459180e4401310320030781a5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 477923947 1250 477922697 477922703
    0x5191a06031011030412030e03180f09040515091b04050402150310060e2e020a050d02010e100e0c01140403080f0306040506040b09070c0510052e030305070f050109 72
    0x10307100c2950043c800700350141d03010714056043d02040c0c00e131a4905504440c094074038030710154070900841e2188000d0411505483c400682080401c4443c00007161746864240c908842581150400420300200c205c01c0e0f40c1c0c0320840000400c40380d04641d40c1104422002000705003c2e030744580014041d5101c6201007020b081c03840030f000f41d8034a06100240e9007031145000700b80000d00c84c02840c401c207140c19001c0c1c2c4d420910a42400e0019000c0303010303a12208404003105c0d420b6000d030b010407201248007031100d9600c2c0b8006400200d05e00c0d801c0a80c0504004800b60400c00c071038a001e80080c84c4140000b08031265003000c0c24180400500251111045c4c000c1c0d42c8000c0505a000800040c505101009140560b000350340c1406242c460300200420350301c1049a1540040f81c850005000c584583c145001086c040c006540c214445540110b0035a074003195064272f03a844030001c48812150514891214003d801c403103d54540c00d65800401e01e01c40d0300d40107418440f194600c031051110a43c0850701c1558 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 477925197 1250 477923947 477923951
    0x7150f0201091b050109062619050403020f0708150703110f03040609060e0307120807110a08071202030c1f020d05040f0606050f0102101a0d03020a05191a060310 71
    0x143d06940741036000e6a40c0a084d0009110107400182e40b0301404054000d1940c06407904600d0107010b201c442d00d440010301424443d1075001030030a03040828450640914040c2d40a02200303803131401c1903880c0c182194401a20385d8040f03040e5261815020402c5908490340d46404110319807401c0e000c1d4424020b04d02203120101001041c4010421594400c002070746c8101d0007440280144040d07542c80c1d005840001d0305118101e45040446881011620f900032141d0500c020146100414a4035002a144040305d4528001a9800c1030000c2d0100010f250043c0e4401185020448030a05454455840071500c902d090307001d0b012207080035a01910404048401d0400c80381c607090400140d0b4065007802500c040d0702d0820302007483d003130003403098400e800182c0040c1845610b010316000200343c1c480f80041d00c1c0e8103031031055425030395520407800f50b2400381d4000e0202c422241019030038448100800e1005880505a407070021320b45076131412003000c1040501c05142e0314000442d08084413404017003c958 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 477926447 1250 477925197 477925223
    0x90f010c0b0108010b031902030a0b040311030a02010e0c0a03171c021c060f0602070506031503010e0a030905011707050d0f0612110409030804021002031c050a0e07150f020109 77
    0x4401503010400311760302201101c440c601001c801003003488100350041e4045d0840e0b03400401044811000c0381d0054400e14203144a040020a013904640204c444100103035180d44400120b207404100418a241e0104d845c92081c1c5e241d82e45000d101c4104d2110203900c001c0110303284102441e00d0b0100c081003881400700355038418a41c8001c0c01c07404060081c1c0b030b1016150032004101c0c0f1071640ca108003903c3f1203400402d43d9a0400b404c001c65500010011000c0301d032030b00980c104070b403030a0144c80ca03400125001003007591220300e0701512000d02600403504104443c01403d00e452407041075160840c02c541420baa2b1103240110070b401034641100760300c0c042d50914000003410782c4000285200e4034051000221000210704c10042a03461000014000580500200b005498038105881ea03d1210703004492411100041c03070030307040d9401e00701d0340200e568403001c00100e00f06c41e02507160580c8109014240c1c06007425904c0c10441c098542c482e007000b1045082e0544c3c40d000350301c40380505c0d4010200011903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 477927697 1250 477926447 477926459
    0xe1305010b19050910030b070309150608010606140a05030f040317040b070f08090d140d05010915060c0b0a05091f0911010207060c020d060b040203090a051908090f010c0b01 76
    0x3902c030f115030f6000d480b851002480501c10901c0003400d680d0701030158125616003190440c00b500c0200d8099a103079200c096070140301d400511a140043c2000070021451030328158000e0091665000d8404c42ca450400410b40100d41c0601160340c040703000c0851600c03e48450030100c41c1c80541c44800840481f00ea820300050284180440d4030900c00d50361a0805114040f0080340d039900c0a0b20a50b4155100900c981d10700b42c004d00000d10702800903075409043c14401c0c1500802d4890a0380007010352a5100811810045020140b00c06040c0301d0a0011040c2295940e141085600809003040e1a03030700e00c00325203c90024402030018a0081d40400b0400500028a80080454120844000682d40802d142a500108000040b2200f0341c0b80e076030319400b16800740f014403a4445800c4400560b40c0701084669a264070285004501c3c0100400704a1050b191403842c01e80b60900a0b03c0c0b100810069500003040f1004690080c1e0068032180d008140620050301c9800001c000100180d821800110321 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 477928947 1250 477927697 477927739
    0x90e0708090c0609030601120812070908011409030901030b22150f0e0a050405010b130c030507140d0f02040527060f010c0803090c03030d0b01090b03010e1305010b 72
    0x941c409400350780724107100008001e05031003180303101130701a00508010400c08000851404196004000342803903ca0044107018802904032036140c00714038040000e21085000344504d0031800ea2000400c3c482d03040070343c0c031140c0d03900400041e181003540b5030712144100d46440d8000a202c0c00c2c40705d50880740b8011081c124000d400d0480d80016031400400001807104042c410702c504a401811020101e03845095541c0060240244161036039074236040c806415455120407201c0ca28030000c40003c0148291000900f40d0781e018200400304203201e0182440900c401d011110402070080d000148400c8ac0040c1b10007a0007070b43d00c400e500c8034141c0c0384004110061040c0018213a81040c2420303031795840c0d104000f170310039070120410f0000e4008501800080c80c001300546c1c000c031a82003100d0100180380b00182c80d681c06000290300c070a4450103c50b901d0b5800c5010b29020b04004400e90b8215810050898101007000344210310b0140340e1101a4240300080d03002c508004406424501310914019000c03003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 477930197 1250 477928947 477928951
    0xa05060a050d14310218071808031602031903030219050403050c090406090b010303021c020a0519080706090c050a0b09010f0f05090613050405010b1306030c090e0708 73
    0x285160030712000443d07001c528903070944901e0400d003400e449a8070040c0c07501940c0002d0f411201c001c2c1c2502d8280d0340036a49113054042e60054004a00c1000c1c80c000380010049000e0b000c8851149000d544103006101000c0240e0710380c600d10101d41920003045000080c138009104a100b840402c5014038802815451740007803840582d800c1000c1c0fa01084c40b002101c0c248924480030700030750801c1e002942e10b440d00e54903040c0c0240c028100031880c1c4050340ca607010954030030391040b0003684c0100605d00c10500b01d0101c1280d1081103001400c000c4002d13885194079030804448146000b000b14902d08100010002950f04003a0002c47c100500d4282d490000040200e50103800c0c452110a2400036080003404110b0300d41d0a810794441050759813011041c0c1c2c0034180360f080d500a01000b484441d0003030315220003500d5805020340c410440303c1e1130003041c0011100d041c0c01c482c0044804002900f0080341e14030742c4008070b400b20726001034407620030030003212265004e03003006d0a44400c400501c100d6a9108000700c2c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 477931447 1250 477930197 477930217
    0x2609100b0607260c100e16050a03060504081b0d09050a14040903051c02090f030a081803031303110f1c111f0804030f0906080a0504020a05060a05 64
    0x3058001039800c100311030003501c00040041084048a4140038040184554241c1a06010314208195070301c91509084152182c2500300f9964080300d08041002c00144680013103444403600c0399800d0a010862440240c000034103000c0c2c5403004101082500c1c011a08410144840d03140c882e01800e544603264a180c0740384000103050502d01144610f000071031071045500d070361180050703548203809100113480c1c00c01040e0140070b0144490500380150f00f40c80c0c0407100003001f006940328840e400304044601c00001703450283d800207070b040c00040c000c20101caa036a00810009100001041d00103484d52140e0800d030701c154a440c490020411401076101821503a0456440301104004c0d022703c1081c0380f0b600c0b55580c4c00c0150310100c401040c14403a000c180c80c00081e0100065000050315900040c0d0501164030018585d40104814568084c030b031034060992070316048402900e000c00082002c030380031340340d0024960303207501240c01c542d00c03100740c8002002d01401040e1568260344002c2c04c0340d04041101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 477932697 1250 477931447 477931451
    0xf010e120f1c2304030f03030608011d070e01080a030c1707060c08090a080d020c010605120d0225150c0b090607020d0c02060a0503040c330305090a03260910 69
    0x145100c100c141d402c200890b40b101030f0b182484d03d1500c800000480101066080c595503600200d4240028024000310301031f103440278003d4024060b0064036001c05940116000b001c01001402041c10208080c145a90940382000d80300b403803402c15a01d0041d1030b03d0341003441600041c003141002969005044800001d80b0760b00d00d580c0c1d48100d0b058680d01281c000a268907010001001080410780c0941180c81c84607000061158641c80403c0c80c50403c0c1101040660001d41c0203041550304200700032803c1d0000f050302000402000b1400b0804006010314002400014030315940030b0701c6010302c81c1c100741d08410300301320070704110b601d140c1c84171801c2c0d1300d001c014002e0400001c0072601500201038059409018546014081c1c881101d4641018100b20f918079204600000ca803004d55420a02281302c5041c80014040d42995051156041400310002e260030001040301400b40492030340b04603909070401c40544881000315018000c45400303983d00d4407040c00c0c20301c4403e400000700e0800118007a101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 477933947 1250 477932697 477932717
    0x509150f0412030519021c050406020909011a0708030c190e010906020304030305070b06010c0804090506030d11100504030e040606080108070902030903040605130312021b0f010e120f1c 81
    0x30072000d50384d00300d80c40510801810720409000c0d09a50040c43d00c60300600f0010100b1150b18200010749074269401d4408903004512446a413404042c0b103401004001c020365062102d540f00c1e802c5070f0182042c003034070001c0c0200001c0d00800c000c4003200c103092440c2560400f410712042c0050001081c0015203400210184d60105410b80008115010342e41c058550310f0034286c095441c07a00c40ea5008044038100f01e100549000010340d01409440544010b0300040f4040c54035805041c54161030309000e80401c1201c04c80004003020100340070600c0311140d000428240e41c0c50078151080c0050080035504540781c50800a06e42c0e500c07607401c9040e110340009588032241d41c3c80222040e03020070340329a200340d0002c0104001e598001c0b002850560300305480d0210319940c0e0b440b80030309201031207007840242e0407030032a10f03544040b1031700031600254046480703420314600d00000910880142c103165004e1400d000c00d944800c07030100304203940b0504e4402110f222540c140005480c200c3c008140602190003106 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 477935197 1250 477933947 477933983
    0xb0408130501111b031212092806020d27140a0305030f150d06020405030105062202090d02131409030301030b06010c061d28020a090509150f04 63
    0x1030f02e100700e101c02600501100d5031851040c011a14030810f035690501c50090680301c40301421010f00b075091610740c0b010b085464002045402d10040507074141c45441c4400140f2190610703108640301d400c3c0c02620040e00c0380282c0030307228010059034007000d02403100c902d80c04c0711800120900e0b524a46c81000c03000b102241c1c0d9044036036620b14030040180407600a2000800c030ba401807014a902603c45440c00b171881d4101e03404a02405000b10003960896000103040c07250782402d00505401007000c0d1401802c46061115500c40d00d0300307008140400301c2d0000340115142e07075070541c540e80382078004100c00e201036240c50142d4010580a01c00c0c061844c1c42d040000c54402c0080242d070304882e0040e142d000b0300d1761104011a2002d901a0040b203085035901420101d4010340c96040c1807134410100140000c010800c048884030342150118102d4800b680001c4005031144c1a066044441d41200418581c0b0356902e50b82c00c100c4030180502d84c0080b034004000f10058558025030040e0b0081041c3d001d581c000341 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 477936447 1250 477935197 477935207
    0x60c05070b0d0e070329010b0306060331120c020a1e0305120c15010308120a020c060f06120106080c0904230d0305010506030f070806011e0e09090f06041e0b0408130501 74
    0x1204544104e1410309c001411810444000c6600501050741d05a10000c1200d040300c200d0a101074100031159901c408608103e5100500007800200d070410362250082c60380064840020780c003807030340344a0003046046800c3c1500c10750040a5a0f00006850340402d84480003074407a0080d10b0581250720500041500d00504104a82c0c180c1e03821520480c40c000691401212441029104405065080102c00340e903203000d000c60f50099000241042d01c6080000402ca00010f02140b00c14140e4135202e000c00c9103050029140700e146e081031342d21503000d9a407030038513084e0700d00c2240405123031143e50b419184c2c5440700407460781c0c4002030a8904108a036222014040306000403030f04040d000003400b02007017409008010290f40180140362280410305003030505144240711494080201e0140c0015030428507049881c107a104080c00000c000891801010039920100600301030b20950f9001c02e1020085803aa000c00305003a0440c034501503a05251170a01c0155221940d007100a04d209030780441c1542c810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 477937697 1250 477936447 477936449
    0x70b04050607050c1b06040e01080f06010503011112040c03141501060509010912063c09030801031e05010c0e041407050301091e24060c05070b0d0e07032901 69
    0x40100254400d4000c07124500c8000941e1590010042c000091020b4405c8e0246020f02080005040c000300201e030268500001a00454426410101d035540c07400e1980e0182d40c0000d01415013500603440e5400c0c010200806600041c0c055502d009034a1000301c0c000610f04940c42100240080980e6035201c01c90b91400742010041c0000d907508410440c840725818403603030ba24002c170340018802c0c13040c208002590380810100c120000300c1d40a500204002601e280003102e046a10502600c00d10b40e170000c00d0300505000041002c010208840403c143e02c44078241450b0703100300200140164000c001e80004000f1003000d104a09007991010f5200360745514600a4900c4c0d1589411a401c085251001e040712411440d02010b016035160301d1a240d0380282011101c01131070180078444441041c203643d1459400140600030030101d0140064000500b0304100c441c41920a070300c0701031010340324000c3c0c100c00005604a00c941d16020041c09203003050000240c45c900c0c485c09d00300c041e40114400100e02 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 477938947 1250 477937697 477937717
    0xc2203140d261506191d010903081e12070309120c0515180712021c03080106080406020702220e0d020a02120c030a03080103020f0a050f040906060b070b0405060705 72
    0x4014081540c4100414031400d044600410003424039004a50440300c40581620b000002800e030031b04840c0c00758103a40340025240c0280303006580d1b18190740b01c0d6140b5104020703421000b55610314846690ba2507600c00c0d65001d00828141c1c22450404840050160650040035501030080c03071040d00c02c05014080e400041588040603180312450489009240c0000034420203901494000100803203005000a6000e07000c80b8450800c116924018004a0b503032007223824031020728141651010982045403181140c0107032034240d5a5980b503180002c0a4018840001e400160540c0300422039007000c4881c4000c0c1404501c100100280405240c1c1d40d600390341440409a08811901005820035840f900000100e04040300e04084030306012a2030310030261800d9000408032070051046103010041c1402c16902205e4801c002c1c0c3c18a03001800140c0600041482240e49481041c2005810b8202c07900600500004c0754440400d82081a03036160201c50481c1c2e540031b400001060f29024806540340700d01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 477940197 1250 477938947 477939017
    0x804091514100c05030903121c062d050603012603161403070507120c0905010303080a0f0917090108130c0510021203100810050c2203140d 61
    0x100c065401d542d4440c041d070080c4d810780020040c0701b260b51800c000074524a9841c44d48a40c0c2ca1a107016215400f40c03903d01019425402e2031803c000c42809501700e8458010031000442b02e8134070074030b44d100c003880c000c1d03001c190421808000080c2c17140c0c1c842504032800b41c0d00030315012060700340000c047c1c50380b01d59005020380180350701e05080450407841c40f00c480d08039000102d0303107441a940c480a01d002c1565115010161030101e6900402c0b00c411403e02c01001c884001744441e504542d03016141440050003800b9940d641e8089425941d0f6135002501403a030020110102200358401c842c007541e00082d12140402d403180040380405082c0044c1ea002d0580000c1c0d000036650405040190007002c0c0112001140300b045811103406040c0c600540c0200c89030001d0424003460009a9820001880c150394200d61511081141c4600b2143c12186e031003080b02607201d040c404030818001c4800444d00080d05070104503004a10341d03000015240046011903d68035449120001000040f40300c091202401007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 477941447 1250 477940197 477940219
    0x6011701120516030b07091203020606010f050706090809270a0504020102030c010c02060f010b1614010e0303390a05130302030a03080a060605040617060604030804091514 75
    0x94207107940340a4030078000d44000c035402501040e52500c16801c1510400d190106010380180c110020038010071400c0200980d1444030344010303480b000c000b480307181030001d4030080401d642d1080c403c5955050b4000310400c024561410141c0040d00318540c0c2e507008205a102070b1700c0c1d5207d00300f500340821400c942100d00355a1940b482c1d1000d400054012419071109200c0d10092081c203004c1c1c1c03906030f10300d5401042e1178508403490550000042c0d01002108104004144040c03040b0044032464a8208050091096188005600604500c40c015405010201c10f00c5910300d2001610b00107540c100d10001c24101407589030f088040c609001020848c038040004e8000d942c0120084e01c03d0320030400c1c000d5145651303278010a043c44a420301c110300042c004400c10407031080c1031044030060880e81c80d04d103061604040014201c2500e40d00035960b0b5100c0303180015280c0d51444111000346a1044540e41c480c0d03501d40007500070742035070041011562010500410030310920071107048017040003030804a0403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 477942697 1250 477941447 477941459
    0xc010504080714150c060a0b1017070504230f03010b03030d0504110d03030f0509061006030f0b1203070312141f080d02070801060506070305030c0307021c0f0806011701 74
    0x1008242c86a41c11621242c0440d2451084c20041e15110b1000c6014190314980010707000225500108400d100c1c02180a40340101c6502500d46d45012042d1420102d080d00c94020548a0f0300440c0d000524001721f01e600844440c60b00c0060300120041542c00c41e0b040c0010104050a85a07030340c201c0e541503030050100309001c0e042900940c2d0840d0042d000044039460903004564410310504083d00442d8640d4a103001c0c0444500c1840d60120801004e48a18106200390101c2c4800c1c0c3e116403020161104155444400254800000f076500148513209006031102783e142c480e0403900341540807038810030307a0300c8100860780a1503d8001c1000b003407035074940d2003c860a14034030789081002001070790a40049048035007046042c01b06c03c5c0c0d07500140001c5107841c105500b52142d582040c0d000b103505104002c0025044000d503504410086000c41c3c90b5554104100d203001c844584049a91607034091001c1000c0e049202403816100c1903560040c0383c0d60320390055a030308018030700d040800d0443c2001040700e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 477943947 1250 477942697 477942719
    0x402071a04060204030f060501180c05040621180b010806060603180a020901090524030a080703020a0812070801060201091a06061218010e0f0606040c1209030906020c0105040807 78
    0x84540b0030384005040c16142d88071080100903040c800c81d00c843d619001404800b40c00d0811450444803480700307000e1103894900c0100b282c01140b040500307200c100d103036503440030320341c40080018680c00b040100414a0300b8030750102c0b1040341031001d0f144808840004102401c011428501c03807140503210a283d40c8403080d55071901103001130b02d2503050050158400040e503d84a13040d00030424400049a2407c0111722280c2500c00e000c4003503180d4500c51303503c051580b000316030501d00540148107070761506064182a070400c03088a00040c1840710000e4009140d880d8000000e0240409550300c1156a8a5020030380c00c843e81c503540a02000c0c4881107288582c01a04202e55010001800081c10301c031941ca1452001c25043e1190941108407808404441d03409106480f1103d90510051400a5485070303c1a100c40016000d1400380d40c40d07019000100e40128403000030b00300d611100b004014407070304008100c51854080d000050240202c41c0b01c03958030540036641503400320b0002d45065481c089120070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 477945197 1250 477943947 477943951
    0x41a07030e010528030504020103150e0f04020d0f06020a020106050a060c150608010606020f060601020a020a030609020f1c050714011718012d061401050304021f020d0e0402071a 78
    0x100d00c00742840502c4880c840000621484d0302c2c145c802061600302480054180c4400c15034400d8601a00402040480081d41d0340a030020703004864608151150300109088030b40c8010701a1161500c11019010020310394000c010200c040d50081118586410400244114a12450340010620807004002c2451203040900006200c200083c000740e0701e412013425104590300640158001e821194807070b10050240302e0b4003201c2407020b840d101c003a980c0004c074040402d0101401c0e10f60b48400080454035000019500b040c0020580041001c8100c690703545500031031822a4107008480e0300250030402d01070700400401050315000e030882c21030500006201d10040003c8001e10141d0080b1b0b16441c0d0038820304d1010a410301041e4030f403024048201c00340c5101d0884504000303162a4003000703840c0c60182d1f41c0c049400c003440d02d1a40ca440c0c90001890201050110000100d10314460b1302d0055000100c1a080401d07075114003009104000c01c2204074090300034050300288103854000c0002c416113210f00d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 477946447 1250 477945197 477945217
    0x30904020a050d0f1109012601060908060a0203010b0f070804030206040905091b010816032013080f030702060307020c1207050f060315040b0112050411092d180f03041a07030e0105 79
    0x201c015032320b405c89061280402e80c400c1000c81c540d01418408000240400c0d5402941d60209501d194074064000f100b912401401e81041c1101145032801c00081c5e5044a00658000b03115980300e075101c00c8032500030681551070b041c861042005c02c6070317203010464084182c1c00c416103500519036100100d2260088081c420101056a1904210b17101c040c007100340f40c80c40003c91149500e0382c510100703443c000403580d00f01c2e0855500200b0300c805014000000c50b00e6640c0d0507200d5540b00d440300f0b40140c0c60a91103e081d03692140208081c0460500c0005002e400c60702c040300c04603400b010f984c044c42014807058640e00d422891a0f0788400e8503003482d0f04200c0317100b48185000104120f14080520403604140d03011510b603403910301d0250740ca0ad01241e903a50825150800300070710300c5883d42104000081c00e030903081d4400440c0001580301c01880960300c4000b0300081070325035081e01401c0705922980b25000d10100d01707181c0d01f41c14a0211700841603e60b020350649420039400d42081c010340740c0c3e07040030403c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 477947697 1250 477946447 477946487
    0x11d03150a0b040e0609070302040c05190e01030c09050109050607050f1606030b0a050303270414040b0a0603021e031c08090c100f0809030904020a050d0f110901 71
    0x1440c00102610407446104000c000041007002d100c104029035000c01d07400f800e0355011034148a0074080228203102160340c1240c00181035005203805540e0b5005440240d01c655808903591407000340c0042e81c2c0e040c011401d0340d00b00070312a803081c1e054840359000d02516000411100086c8180c1c20130f680140280350141040390070142d030180307405142920681a82e403500c0341e05103003040056098001c401c41010304680b00a090b90038200400e6076801802000c0d1a1309404038401101d20161180310301402074043c10a1000000c136031a0040c1c200001e850884000e040d40d000140908403e101d4001609d070700401c84809400418191085510024030042d0705014100b1321802c41c070011880701c0a0002940c45404152809a424901301810b4528140c0202128160380a40c2079112600700500310050030024580e480d100c902034610b0094080180d00b107880050b841d00c4030380e00100940211f20803090107001140e44104100246c865030b030780c00d00c60341c1c0003441400d81c2e0b90700800c03099007440303204058 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 477948947 1250 477947697 477947713
    0x909050106050406031a0d0c1701050c07060902190909030806090601020705091b0403060b010305090c030705101103070605060a0609050603010905041a010306051f0509010302010c02030708100b011706011d03 91
    0x580861890340301b00d4408c41030003420040ca081c17040b00300040100c0c14008001d00e143c003030400540c51146180041c14a0342d1103a0020440d51045825000c804240b4102d107011610b9010740e000401c0c1e945000d40108065000041c44e500e014601c1d54451a81030b80540300d40d61502041c4034058101901104210360000300082c1081f1811000d0030045024200116103041c01304005021508007800740701c8181c0001c0a210400c0c0c400103807080445000350358100d1725010217041201c007017660743c140c50042e000000b200b41c24404d154000d0342c0100d070304582c0e040c00c6590f83c0c5001d5500003003d21505030400000d0004100d0940142d020650003809001d0f40490b0004c08100642c070207400343c1080b191181d1f51400c1c44000100c4540e4110a0410561401605414070740058018801440020304204145841e00c0854605002540c001c081c41e80803035030519544c10b1381d00c025152000325140000c1c035a20302c0455800c411900380b80140b0042e141e034021200d4490b2507412036648001d6241d014400d40c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 477950197 1250 477948947 477948949
    0x3030403260f0706060b1201030809010201020d020d0c110f0a150605191503090515040503130e070f03091a040c050310020306040e0312011203020a020405160909050106050406031a 79
    0x2000b031030307160301480125944003801d1924004075891038100d010328071780520948220703070140c002c203a0540750880011a1541c0c034500040380a44607641e0002c040d140081303200c0345e1220458002819108281c0c5440249049a005280c1d6402d000725070003450780d00401007100803030046403010101c4c04202a02203086a03d80002c10800a618040b0364400606030804002007101007202d0040c546d098039040c40f540b2840d0711620340c0c03002c01d490a0302d485030406c40070404200003081150019121012440015540c4403103190010104541307100115074101da5101c14103102e8807035100b41513802641d04004401602003000302e4040140100d90364201c2040104140d50700f00036500c55403903c60005a136914141c801e00040d40c8001d0850b1070144e01c244158a007020249800c1415502c211020719448000c074141240303000c0005801a4108d441c08080c460582d112008200da0134415460b040c100c580d403220000308885c1c0c24840c0c4000544144014007805100340c1001000d001140031144e0a940d0081c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 477951447 1250 477950197 477950273
    0xc080a12110a081807060504060540050d02090123090c09031e15130c030308060306090706211103090601031b180e16080d12060503030403 61
    0x1c80003086840d400c00103c0c165100310405855145005048117510340040a8224022030040b101444004184292001801607030411645d900c0c203407448000c84500c03441d0700d03410118180300e001100b42103c0400c49040000401101550213000c0009607880c010a001c608003d080003400d80c0801090303218140d50b41c10001c680541d031000a85a134400b2008201403410528020300621124603800002c508100400c40d00c86441a14031620a0ba580d0344c02d000c0c612101c2540300400b400c40910001c82815032154a00f4407400307094040350f0306502c42c140c4582d40e642c039602c65100000c0b1104030390703280c0008904406032070b0380a411003c1030b140750a24000c0d0030b0b9001182e040442e513210f24010000d100c1608a0400391251031860054441d08204800030707075584070342c3c038102c0458603105103400c01901080381e0314551074140040c0400c2c5440780e8805450384020411007000680010201c014810244518002c481005000390b151a02e150303106413a03c42800147c920f45400e9248034443c8213565 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 477952697 1250 477951447 477951457
    0x6080c0c100e010b040605031f050709120605220b01030201033204170a0e0103021c050702011409011505120106120f05100c0e01030917130503010c0c080a1211 70
    0xb1070004c00e441c8052005c0c801200c0c840c1d40260302c03950104188140310f00340038070008400c0c90036140120389aa660f040903200c0c050180e110248502c004140c2e2000d2100da1340c4518003800c28910054030040c51512800382c560071020019000e041100010001076000758021248079148440c0d040703043c0c0300110841d18001d040c00c0700c0b503100c40c4001c08010410038400c040400031740700711480780c0c2049140da40003050b203650921403605266000800f156070031034441c090682c00d00310100900c041c0c45c0a080080c040d040c1e103080200e06648000224601c103006006241c90380400b121000250f515100c1080103d84c01006200d00d15581ca50340420184541c0300b140e04110301400e982410500c0d075280c01c500e440038000d031500500d460b0628a40501d0342c0328600b03104c010300c01d10340841e40070f00c20b04110300040c8180900072156800081c0e2925402d0481202d0011182c0841c004c00070700ca08004242c0e014a042100103003814020040b116042c1c1c014041944a2014848002035252048200700003942c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 477953947 1250 477952697 477952721
    0xc020a05041e060933150512060f0607080f1902030c0607020321063106090c02060112050a0204020301030b090f0a05030a03020a02030c060103080702011806080c0c10 73
    0x60b07180d803140762a160003080000c002000c2e0400c080000807040c0f0380c02501014403031684c1c40ca01120341e41101c2a442121029024070200c00320580e80c181400303000303070780300c03c580a00300940c040008583c3d150130903542c0c4200c540034183d90701e0702c0d84c00e42d00c603900f603072203a03001603900d241c14000e04000c6c0c03465144070300203c3e51036001580e5500300f404210386022801424841158800c00c05e45642d661110030901001805000d44d00e225114180043c0c0d0280602d842da210900301c021100c840000e44098503000c01c0040102040401e031100070850507614562141d20159001000401480500c850300300c0c1e07031038081c070f050303c5401405500240503a0704c2a882617030840403420901c0034903c014001110080e000a00910450340141d54070303502c90013030440600078542c1c0465144280d900130f004842040c60b0510070340da03566071a86807000341c0707822850040e40041c90740011003440101c400c000c2420750300740d6100c00d40c966540240201c4107a00032079069906006012003208104c5181c024401d07172020b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 477955197 1250 477953947 477953981
    0x12030305011a03040c030f080903152217090d0c0306020a0e061e09010c0f08030109140c04051311030708041101020a020609040e0a14010501060314040201050a0c020a0504 75
    0x11402c11071640500241e15464016082001840000f5015040707040850764082d011618240c0c150500c880e99000b500202c541501504010300d00c00b001d200c810a120700d20401c2001c9200c0090f003841d0303001c880030144c01420001090a416444081d54000c0c1c00c0c0050020301c009105192a0b4403802c2041155000b00c80a54000ca4041e240710f0b01b0892984907007000791800f03400c1c40317146c0549040d4000000d109011484c1c0000350044e035239200e60f20044002e41c02086200c8944014902002158400d10807284458505415040400a07041d9003030f024103200e000c0c0d0350909041c0010041140491402c4003029076603003001c00e003030010402c06184a80e490b911000643d02d0b060030040c05051031200007074110740000d0102c0e40142c0e00ca10544102c02c40507180051021009201a8682140301c2c0000d48071842d801c452400300c0c08150002e605840c2e0b103540510652480c041d007054441c0307060314000d02250050211461083c821a100320080780024101030b00296100040303412031f4005071108407107030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 477956447 1250 477955197 477955199
    0xc060601020105011d04061d01090f02041107020109140118060c0507060206072007091d0c01020712150b0402030108010c0801360e0318010e0a05010918061203030501 73
    0xd80c0a1151030300410040c0c0c0000321003a815825400003200003840200300b65924680d4005094500f10681002001c4000800c5030f031042d410b004241000c40743e0201e205905100300310418a20a505540c8200d038103841307821090b03040c0701c20307141c0300010500c259040120403044e100e600340c400c0c1d0700503005100c541c6a482e50b13141039040030741c2400f40d260402400c1d5409002840700456005015101000d610b00c18503030001c06802c082414a0490f0307000c101e482d401c3c280411140c01100341040030500350070f41140c016544100059848039451310803281840500900304022640c40f80d85651440300d82a0001920107901c80000c08a81003a000100e5a0799520701501401d60000320a034094101500400280b074068154400304c2850380c1c0c007090703800030000702100011071541c019401070607118081d00e032181900031202c0b0100c107a0356a100d000a80000090143d03003060503002094403410f030740303161401c0c0c00d080c0101c0a52130201ca100078034270380d184000101101c0d04451152014402d07900440c0c15 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 477957697 1250 477956447 477956449
    0x90d030c0b0406060302090f1504090215041d0f01030c030b0c1b1c03020903060c2d0910030c0210050709080f0706020601082b050d0504110103050a090f06150503030c0606 75
    0x51f49005040080c1480c03248280880076001001c10b29443c04103c0d00803642241c1807021681b0003041c0007480c80216000b150202c1c010420b600603402d4000a107001401030340e81c40d81051140d00c000c0c80b001e4030006200d9070070300104401030311280c1d1217403203205171614155500d04070100b03c114001040c0d840c0c0d0001910b007400340c4101c07403034030101c600580303810342c100400d4400183e10344001901da00350b250400507500164030381d40c80142d94000c12007040c080c51a2080d00c2000143d0b0310240c00180f083d90118401100341d8000e08c10401a01210740c000c0404480300310100d4010312018189200b032100100d00049c0101c020011004403c11000c00f5041103071070000043d00e40030042c0c010300340640144480e8040001c1c0c400c1c0c61080c07030b00c01c040c550552100303448041d6980c3c800c80f40c01814282c107100410060040d41400035220010030f80c0d08200955030003844008a4132190342c02803004051007070020108446400c00e41c2c581a55500054900351b540c00084c1c6142e1101031802550780044080080c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 477958947 1250 477957697 477957709
    0x160b0a0e060709030b15010918020c0d0309030206060d050f010905160801050115050a03060b031e091b0d060e0604030909060f0b040b0c0a0c140f060906090d030c0b0406060302 77
    0x12040c2d6050800b003070f40c2140e07680584d0a1000703014580184590245a10307a138807a4090000425000c50042c03c803c85000304035000c1d50081208500502c02c101001510b00d20910504510b50b41581c05007015031508410070014140f0080180d03094800d10018103206c2c0c50a1050340712051140c0c0080100440784007858000b119607900c0440344d640760500402001c5c003000803400e81048203142050380d81c8180c2c001500145415007102c41d54a01c00310400603102807000c007200300700103170b060719040d1540c5c0d4641040d5500e50b0414031310014a400fa40c0891103003012034500d400030340304500218524250201040ca005400c032403c0e8001581d460080006058600c01c20f809800c81786110700f0a1420035591403414802c511440d02c1407000098510103c030000c0c44050006603100141000c040d507500c040c480c0340381c020404540700b0001c1e9a001320803803a00c03034100d900400d4003815441c2002d00d10810804010449441078060143c03688101c0001000b088503a880f861180030001100c03401c50040c850 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 477960197 1250 477958947 477958951
    0x3030501050f0102190606081b03151501050703050f0d14090105040b0c070516150905030303130609020d210e010f02061f0e010305030d11070b0705160b0a0e06 70
    0x405050202c800d218283da001c1122840050301c01210141105640f8141c0010109a81714000718092050010003030385044a658920100440840d1411809401e80e1341400c0d5060340c10380c03c420003c01c0f101c4c0c01540903401034100c0c0e90103410a281070044218205c4655400171910018699a0707406001100d0440312100e07030001911402045030385041d644114050384060103180a01c100420324008221080000c6078820640d0700b05282c1a072b5032100c00000301008501d0f10004907241d520007007554180001030740c2c451034440703180c0c2022019a4458000429000c00240d801000071001c10b008580c1c1011030002e00b4840c20003013911034800e0070004106000d8542d4040c100010100c3d001c5104c2d5000449a801c911008265900750f19030b581e403a10300b401c0a6000ba1a01c80c0000b000005218000c00984160405603006004103041e40d094031120384903e00300100544544404170301428031880140035805c0503481c2101c000f2820703454400c00540111281c00410762501c44075907210506101441d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 477961447 1250 477960197 477960199
    0x7020d02030c0c0913081903061502060c180a17060c0708030f0c0c010903030204030b22122309030c0103050c0a030504060212090f2103070804020a05060301120303050105 75
    0x181000c6220010644800c403c20009104182e28408500c0055034240b240e00d80c1c03a40101742d60745e514052105440100754106030140442d00d460000100102c0c540ca20100d40001680a00301994038851400c06540010100e040d0304000d101e040c114a071200d0342c140029100d220b403c04c111081c2601254903020004021110340031040c48604006905035060769000010040848000d0b0381d02054010a8043c128030116258285803c140c14140c02d58028001d50b8040d0340960500d42c0d500310042e900a039a24106403182c01c040c804070b40810015070090741000340ba442c00030b0b1608100d642c0e040041c001491642d04035940080c4001207443c0c108081240f901080c2012300c00c41c5010700c20f00406008112074070081c107407a88002800c00050758100c8102169004140c038060030951038903903540032000b2201005108191040e001d10507002c9080e8076030b600d0b11800718503603582c1c080d003280d800c40007070002c0380c000b100c4100108503a07940c040a5400f800a0180403609000c190600800751041a8021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 477962697 1250 477961447 477961453
    0x120204020d06120b101d18010f150e0105031c08090a050d1116050a0501030b0103020f07060c0219020607140a140102090307061103070602130e0c040302040b01081501080a0905060108030307020d02 86
    0x1a40d01e40c0d0701c0d00c6e610707601c07541c03802980b10200000c860f000c0c09454811844907a881c50400b40c140c007024592041c0040d201070304188012681c0340c4040c1690b8030b07040d0382001009800d46100d20741c43c9103c1c0509581c8000c200080e0350402200390f454600d82680018171401184103801d460001000030081900441c0e100e1481580c01071409012034098101402907030b04154030351050f0081030340aa0110f40c040031801100325030b02c4850f410010014249112484018014240840361004012101c122180d2700100490301e4210701d030391450003400604810b80b4841c017480b4240000706011148103481c40d01c0072000944d694010204040c14003425801c1031060141500424400038000402d451003907500150050351200d1060340048600c500750310101144290100301700080d04d4503000351084900c252030030f100740d02d0070070b0054801a50807925103410a080103061080b41d846020180d810136040440013400c440c454035030701c2c103100d001d030040c2e04140c0c4000180304081e581080341e1803045d0690310203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 477963947 1250 477962697 477962729
    0x14270403031a0f190e10050907080106091e05060a090504050606160b09030702060d020403020a050d0f0312020f0d06140103140c03060a181d0106120204020d06120b10 73
    0x9103081143c3c06024040c0040b00c1c440d082070151044802d010706005c1c03074800302e1441c0202c00d201150155010f081d00811160000c68269401848028140e41c0142c480d84150750400f030414000100202c1604841041b03881c0009640d02d588005243c86d0a40342c0c0d49075007450500f000d02081c0d03040a08020b0090100300500141c4800280108000903801b5100402d0350b05c0380341c1d400d072440c01807850103540010001200001d0342c7d0350750b00a004417031096480c00d06233540c68040002c4860303c00c00c060508032310415020300180c4540d035460765500660740010300b00000b5a43e4010307560003641c185207205035258802e00141007c6039450150410034030302403202c0003800c01c1d00b00c02008007801035050000044003083c15a503074406071002401740d160300c4441c000c0d045610900030349204480701b1445144142010328203003041c040d541c01d4842c03646000e82144119800d002c0251f1080700c458800e0b50b5152400308980d2020240800d00030702820440201d4244101d5564042e07105901c040014121410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 477965197 1250 477963947 477963949
    0x515060301141903020603160207080c0607030507021306080d080c070f20040525030b0901050f010e060c01020403051014070c060e10200f0414270403031a 68
    0x76100e004400c00380d0790408003d100c402c20021034901600000c2d40040c4c003000308801c2144028928404a0842d400c60b40015940e030041034843d00d80011807600f0410406c06000440e0140004020755440a03014026101e14510030f00e00f111841d402001080d040200d41c0031010341c0c40b42d015500442c222002910742160780e6116030102588210040c41d0819080162841d2849071910f40405d500151091106244c400340300324201c00200c00c6807444254280601c11603a11a11441b42d00f544090b1003903900d64200010000a8490500303903038100300c1040058080d5032100d0307001d488031200c003500250712a402c528110b4106500f1000742d00b00d0620b0b084042d028084110110364000305a414041c1c0081d05034200407010300070361032030008030f8841d4208180d1503801a40c80190501e0b525481c11003655505e0b04003a40911924090600d1003005005c01d00075450120103140300704000900240240c60084042c0104803204640d0440090000c0c08000a0607014001d440104c40c0c455010703040c0c60340b950 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 477966447 1250 477965197 477965219
    0xf170d050106023403060e070e09060103060e0f060705030c0403051501081515150904020c06091e030d0c030b0306040305040608010e090a0b190e030c120f0403060b01030f09060515060301 82
    0x11001401440d2030f107d03c000d8410302400080080d0003902408006441d00c0f81500f40d4900080c44110f070790625203e10007140d03906c045007100300d8004000c09031001c0d8a45074070894940c0c001600d014078070041000000006103041040308503010f9154880092503141101c5071341041c441c00c41d00608040310b0700810031916100d1180b9110b45004540d1030001e2010024140d04601842445c550010710001c0c04006614000071240d114000e1401101ca0b52400c101c29818920843e00907240c05900501400764060440e40100202c481c2600c3c000521101141c0042d251000c15103003600403c1c00007901788859503002c0303d024090480024010301034184110507a84e1060f03110701c00741444a0010204007000c14003c820b40302e541c03401c401032110504002402e6182c0d800704582400030301c07490808428034030801058420103210032072440e00381407864a40602a24030291400d04140c0d80f03120312044603005100e2041c803180100d20025231481c1821140e403c48103404034041c8100400d10040000700010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 477967697 1250 477966447 477966449
    0x23160e0f06030d0305090a0c08160816030b0c070203031c05070203070807060203040c150f0201051008060606030405010e03120601020c041b11070504020a08091501030f170d0501060234 81
    0x1490000340d1a0b0b900305100c4d003000c0007154020140c0c0105030b03002840270070000d00c00d4050300032050703580b0300c079559503800c5da41c2d0f9090800101d807226107052040000c00c0307845000c19440243c4030113161420680b640040d045510482840050306d0384c0038001003a151036881629440700035400154540400360300c0e0301200b40200d0400a20060700000042c0030088001c03251802006104050084980b007440d01500d02d4025400d0a00150720b00300c0029030b118505000d007022107108001804d030310f4441e10103210581e480180241e46946d220404151150740400c010003490381480e00510244c10144002424904640c0e0068491030600240c6c0109141d000116900841c090400840181b0a00755a0381050456804664068404200441501c1e0031a862500ca201540281e4141004420300042d115a007030001034100040040b400c0002200c25101030444843e41c0c4105003002030220700d60060b130b0b000340c0040300140c0181c010741100c0c900c8640c440d1804186a950000100f96141c406450044c0e1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 477968947 1250 477967697 477967723
    0x8180309030a110d020a0303030b01030b06031b1e040807050f040203091f0e01020d050406110307120b060721120e1b0d150b092223160e0f0603 63
    0x4001c0d40c600c0f8541e602c0e60b80c05040d40d8082d0410240700c0d56810040d0003044182040c50220b810714420a541e03183c0041200c0c40307411128050b030381c1c0c103544e2644400181c2007840340720908010440d81044043e0706c0806400208003c05c003c000c454104400d1100c18056175a20501a50050040c03009680d80400d01101043c00c1d205000c4012400003451809894603400100043d4400140b0400300b041c5500b21394456401864203201003581c0c844124814802103845500240c501c007166144a105900029400300c802001181040f2440e1101d80c00c040c1007152944420aa159007440040e821035450200421201d01c01c11940c170f05074084e5a12580c092141c400c0903c50b041414104e41e44071000100120b030490629501b450040379103400900301403600c5c0d03200b81803840c001003115401352110580760b03a271a819070044203d1036681300c0c03421010781038200748104800c0a0b4011030900b04001c988016030400400c1c1d405141060214500501070440c5555061080800509850029015440380c0d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 477970197 1250 477968947 477968963
    0x503070e0d020f10050d11040302010906030b04110c0d020f07060c08031e0903040f0e1306020d0e030c0a0b010e010506030103020d030e03100b01081e1609090c08180309030a 76
    0x1c0c1c680300040f0701c00551120f156004548096503202240e000020b40a00714000e1020041c046500301408500e004510000b070001d400341d8130901003984070360007004407004040d00100c0c00f400c41d1a41c0ca90300360840e20f0107001544c0000e4207000d409504122455000800c2d03000b620200e402c018004040d03d401c1d40002e00342010000110700480646466194000d594040301c5149003402d1205640b00d5101d40300c0ca0141da03003403c0000c01d0350451030a41c540105101c0a000707581510503941c1e00d0194010300d0041007081c1e40c8908000c9048400c0c0010700510780a440a41220542da1802c29001c04060300045980556038005218540390901100e05480d01203c80301a100710920342210f290100707060a5401d40a090000013100d44180c101900010090302e90841568400c099540101001441c1c401d91009400120300c0007003010800d84c8007141d507031402401a944600c02202070320040e62107680010120010880d10a185142400e505c2c0782507809945031154403800660341d180e140b00f001c0d140c08 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 477971447 1250 477970197 477970219
    0x40531110303030403020109030f0306060206012310080a0f021e0c0a051606120b0d0210020709051005150a170618040b2202130e1911040c0503070e 65
    0x101210500c4421880c00404507079580c9030a14009028000899080740400c8005400c070842c0da010340070707103426a02d0700d900800c516840c00c1980102e481030819000340c2c00d182c05000103100d444a4007031030319141540e190350030141480c59100d401c413000c0110b82410340c1e00c14801603014106075145070400c40d01405440c0e03210100c60700c01034200020003000800364881c83c8501c80050341c5100520b812a00503803105024220384080410030f40303030402800e40d44504001c1e0003034014980300300c900019440c2841100c1c4c5883d21024003c040b514140c400c003181c4001c15000f00498500030024001ca4800c900850303045c500c95950140442c043d200419002c81e0300080010a5501c1e060840d00b0304414140d004151810142480e601c60701046c0c450303143c0801e981201c000350f20b00d14801080807071360146c480310140d581d4880078401420201d001c0e4429015116005018040d926401140300d80250344008841800c10100400c0b18400d2400e2030911030244100724215400c2030405829000995200c0703904 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 477972697 1250 477971447 477971453
    0x1503071815060e01021b030613080c0f010510060201020f03130807170c011a13091b03120905041103131410140f0603061801020702100e040531 63
    0x5030841da08400d044100c007060010b01d00d54007101d4019803890030780070b8424003254070412040424504201641652100c6e001c89d81d12041c0040a2020078000c43c10141401c1132209094203000300c030b0052031081e0303460703c1c01e1081110540c01b040c001081580005c40c580440075905048a0100030300d1010301c510f002c44100c0c1400505002c0314000d070b03800402c180540b4101805504036410210f01c204440d868502111260040580780d05c219010050881e070005100c1261a809000d071070f030040380c21084052281d803010b030560305140090741c03261004010b204c0e6440c00c0181200b03000c1c1c3c0b04612460601221003e83c941e5074044980000524202804044043c1070084200306002e103028801d00c41d82210518828440d803012260151503002007850752141040d84404000641c2d406034184c02c0b030000700d100240c50180c0d07403002c9070001e400541000b50640015012000c8000a0004100c906401c00e040c1e240c2841401d40c41b075040741045101240d6910044084100d0090043c0210070300302c400018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 477973947 1250 477972697 477972701
    0x30c290a030e070e0124020705040c0e04050903090112060f050d0618080c0c040902150c0f030a170a0903021b0303120c0d140c030703051005030a030f020615030718 72
    0x2520601c11210034a07550601d504c0301c10424440c152104584410f2244e402c4051104010580c00c540e0041411038286403c0000400c414291038003484091680340d540c41d145e5000d114806c0c04600c01450300c400c0a440090401814030103292202071802100b4070141c110403040c407040e5031040e11107484e01102c0e4980b000c020000c41e20030701d03e510400a1100100b010000c01001003900c00c0d03050350040d2801505001c207980802d0002580120b0202500c0c10885c0444040c1c0303034080b002c2c800c4600007404522182d055030b004a110340d000a0f48011280c441600001206c0d8000c40c0075802040101e0158a0084d00c402c10511401d00c004190600001039580400c1030b83d00d0040401c5141c0a2410803140380e40310380d03200c40d00e032842c0e0368206581d448144611191551184000b81c00d4240b1356039a13107404500501c0300900a2508800fa41004540d98408100d0840f1080c400d4841c010300c0d140e03540c40030303140c104002c05480300e01403008000c080603140460200d0850f1104ca01c0c07900045c4403d0301d50b00c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 477975197 1250 477973947 477973961
    0xc060f040602071a01090b0d0203030f03040c0b1903060f05011704030315081b0415030b09120f0c0705100507030e04180525050f0d060908030907030c290a03 69
    0xc60b0312604d0031390400c00ea0150407a03a04a84000c601009145d20b95024020056841c0c100698183c10500000c40a80c0c114070003194480d214001c0400c080c2c0e115400d808164215564400d499110050f070780c1c841507014070030500908865131180c0d601c60300d0040006c004071803551820510000101c0800c1c03c0601a40006001c150304010390a48662240740302540d550001c085034600d00910403005e18241854464013400c80d0300306110800303ca00790b456040c405000948180158403603414145107544c1c10b0781c042c0241800101f440c030b503600b032038940042c606022500028030a0b8010039003003828980000480e6207072030381420036904e04d00410700002d000381a41007120000c0c0d290710101e20200100072516440182c0e05441264044521a0b90194000c200b4040d9607004214000764005910308030300710746000c84c07045d5800700f141440c0740e03150041504161091149035000540500030003804465400203440c80c02004606404400d0045888201145000300444400241c5d03d00c03240c03003500100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 477976447 1250 477975197 477975203
    0x70c060e010c0e18012103121d010b01030b0f0f0109050306010b0a020f0c0612040645050c0409050f01022a0f062202150a080c0c060f04060207 63
    0xb244010742e1019207402400309407684228605100340600035001c64825059031210180203d0080f00c54040d1000034100355015800d1202ca4242e80d641b482d581c0c007881c1910045c508460515243d50614203003503034010b1044505050801c511f02c0019103648444600540c0c0843d104200d40c101c080050740c8008288d00400d4150050100105603015880c005040042465080752820b001500503252a220b011644070345c0b00700100304180413961000c08503900903002e004000f0720700940c005050348070000c8000c120701c200c3d40c183e45818a00d9540c54000040444460b40c1c0054600c90b0b910785490340281282188503607034943c0c15a01303220b0108903092006101d54000c42d0b5500700100460541c24042844280b07914240f01d40c111010f1010801c42c00c040c035601c004040e40d8407041013200410004081d40d101408601d00350781e000d6070f68406d01d09145421489100c1d904c240745030004000850040080c603402c54200800c0e00d40b2200080e07265882400c50720110429240da250810180c030940d2406 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 477977697 1250 477976447 477976451
    0x2010306061715181501080f070c080a05160c060e010311042313022a0a0605060f13020408011a061e070f03110f21130b030108060a050f0c03070c060e01 67
    0x10026041c18030179100b80c17500c242c0b206d61059407400c41c40c000c8401700b110440c3c001031803000300200284901021304084015814a02d04100041514049500414000391100820350b5005c1240c613411042c01000ca18086ca8240b1640c0244000c2145522561180c030415610f412500141400800594092607000900d0840358941c2034010901079000350300d042040003034608820120b102c91040d40e034800050200580383c2224903440700340007801c008001981005411401d004e540d62048401a40004a43c2c001078696091000c000c0c02c48a0780c0e414001090031108a122041d5694003d0b10120920911040c00e008440c0002054501450400500310005030411800705034210440410110405040743c12a0000012255403040807895000d840303203e0800b0041280100401030032015124803113001e400c0c0e070315603020b4103543c0300f6031002c41e06412001c1846506100c80c0540d030740051810601c126175007040d06442d00140b10190008090026100040c0100580c0743c0108000c0e240322002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 477978947 1250 477977697 477977701
    0x20406060503010306270f020420040303030b0405010b16060902091e070e060414030c09010303020c030607020c03030910030b030a060f0c020a1e080c0303130201030606171518 77
    0x81c01c0c070b8100780021100241000051140503c0c210b03c04d40c50b61540e0b0008076030301c46803034694071140a210341050b600146c42e901c404c00180449500a00c500d51801d45c402c1c0c1e2185181002021600d00f05040c0d8403950403c001004070800d09000c1e00d29103030004d0000f03003603020700f46810b034010301400c40003c3d08072804000300300180c0703809054082c1c8890310f00c080d03050aa461240450705060110b410650101007440709100d00c81c080c000000c0207440107011507603250018000035484540c00da0085005034450441a02241810b120301030300100240001d0039800080d81c0002e84030f00420341580c0c0a040380980d000d0042e4801e400c40c442c100c1010f0190380c0701064500b46039000d40803040b92820f009060208100764a8400942e0440250304844202d00038a408601e0b00124080c6000540f00c403071060114003120300c001d100460050068458103001c9251301d2001406443c520740c031800500003101740080c108800102407590002424181000c0caa4003000040c1e4407040900000307600280c120f007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 477980197 1250 477978947 477978959
    0x6050309150c04030c090b090f070302090909030901030c08010b04030b0601031e0e06060d050307080904020c160302011716080c0c01090b04020a080d050d0e07031a06010f050c03180607020406 84
    0x10010b8178001c0450500d1303182c60341221004e0310210810399411541d280d0000e00305030051000980c0241c91860090b160071001e0002501f40c4400ba01c60a0458200080b441d00542e010310a01c10740c2500d50405c80c0040d8075000044940e80070b9413002a010388006400140181c2c440da1040c540032410100a281d12000740384290010100c60010030744a215007408038025141240c0c0d1503140c0744c0d1001c0250318003010741e5100f102c0c9400c80303000305801603024402149101020300601900720b10310980ca030613051035070000401c404980b448003004500000c050000e281304001e01e46800741c1203404c00c14610349030203441103014443c04000d00382a5190445071010032401040c40f40c0118000c854030391034030361030354041c43d150a0f10820301b07804100104282003882e41d0a0b0081c1c2d00c0800f440041d140d503955242c490344c000581c42000070181861020401500b076030421808a1000d0341860180e00301500c1445003640c9200300808200d032060b10b0640c55016684d600211461980c0c0a013041c80900c1d41e0304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 477981447 1250 477980197 477980221
    0x210512030408180105090a0504020f16050d12180b040c0b0d0b030610061e0e0301050c0318060103020a060507060f1418210d1401150f090e010605030915 67
    0x880d08400e403141c103102040f810f41c40754040d20b00206004040c40d40c00c03441c0000b004000d50000401103002e00050207490403910f40168080a85802800607001004543d0001442380074850080701803945401c414071060600100d0158801c4d510940c034000584035400c0c4000c40f0304545d809121940400034210707100650a400040c034401d0103400325001620b5101405215030b007140600c0700003401d41000c2004103220034502c1c01980034542020b9120010340c401183c207441c81181d440007503843c00800d200d9080d2801c0b56000c4040ca802c1e002d80002d506660014145032110310501c4100100030404c0ba042c0f044560000451514540007000a4411848214a545400c072126a0b8001010194602c40c03240071034004440120300c5150000c80c1400b90100f84503420410080850641d00c00e002e14071250080d82c0d2a011303015444d000c4844d140a400700070512190424003404200c150b40c010020409801703210360658002d824030903100e6941d20982d62600300040d52078000400164248808410f0703003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 477982697 1250 477981447 477981457
    0x13050405030d0612120513150302071a27031b0105040314040b0301150e030a0303060311030f030403060203060f03150412030c0807031d100e011401210512030408 71
    0x9030900f4481107a440d1040c142401c14410050031080c0e18807003030f2528611038002049020072461012030740a4513034100c00340071080081c410000c02d030b00003110000d001d00d12104071092090300704690100e180c105051201e21030340c01c0d400680d120410f03903100c1407035100f40240c0303080c00c400d044a01d400106204030240a0300090750142c01243c000300080c4481078a540c211001e072110341945501e56480d110407440d20881201c05e41e03042000c411414031881d0307001c1c03011100c842c0c043da401207481401c5040c00000c95440301c418501c01d500903005c0d05520007000c4191022203420410050b126550b45012a0582c1c038131110b1154580180d8199515040000f42c290f03004501550900e1441d01c41c81400350206c5040002c190080341c2044002101e2a202e0b800c105845002130043c0882041a5101e0624010f81680c03061040307620350301c0f00081e48a091143d0301019078100e00c1c65401e075140051251854480d407412494180d801c0c103c180c20300c40108500499403039001c12041d80c0317280908041d601c0c0c1e004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 477983947 1250 477982697 477982717
    0x60a020711010f231308012a0207121a0a020a120b0411030907060314040c05130e01111806091c06020405031b0f010c080307030914060705040618060c0b061305040503 73
    0x1c002c5000c14058814488c00403600300246d040908190760107400c0e41200f1195403e84114880e0503400b02d950041070903081c0c0091300c11215100320040d01040c0c4054114021300e040307601c3d0320502c80c1100c0242d003c9081d01c0900602840010031043e44d10214014120020340c0c0c0121040020134408014400240d0008882c069941004902e201c20921180c4042c1a240a8903c0071002d0083c055460000101031b40c142050b140010800c600740d82803400d503840500070120031312001c03940b02001038801c0750a480f054801c0311710700e10f040c0ca08000a0746101892400355800604c0c005640108035095048030082d10001781203139403062240440401c6500e404100f603004280428110b4101d50140030011325003507102c0300c040d0455417131103021030080010b140c05440104007610000340c079100c1031004074011480340c1e41d0aa82c540c20310401400c40fa4016100c042e004030b4036142044210340c00200000125400800b08070315444483c000380201c8521a07990511515000501c001c200e0008010466410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 477985197 1250 477983947 477983977
    0xa030507060806210703030f17010303030506010e012a0323030709050301050709030602130512070609080d0f0509121e06090a030e1201140c030108060a020711010f23 73
    0xc400d544002e101c8004e01101000c0350b2080d8000d2001034003c3c2d054070980c40841c64251041c1c0080446408181003ea1080e000701c0d07a104180145035a00848080104c41e081c2022442030105130040c100c40480c851103560307071001d8074205801305482401c0b100520000c401c4800f143c519009005090303980709541e64000310313200300e4000a06083c1130141b60b100e40c80c2a1142a400c5196403502c030003135031050751811200604204007140301d039180300e10ba401c0b06c62442e00078410b00c0c1c2070200241c04d000c1e441e006240350381c0c09860620300c8507600c9083c044088109280c25030b00ca01d01640402c00d0040190450f00444c054080d2003840101416031a0343c0b460840303403c485054984900b80703501c2d090388150240010307441009402007400d1a4060b424265030001c000103400ca01240840c07010503060703402410400c400801002940030030004640c1010058504500d41411f07a602e00b0414207d103050f150612040344040c415042c00f404001491941303503512011039140380000207813079a0200d05025a403407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 477986447 1250 477985197 477985219
    0x506010311100f0c15020d1a09090f060414011407080901060e010510080907090c0f09090b09060120030313030215010b1b030f0a0c0b0601020609030f090a030507060806 74
    0x1900c5a49043c65010007902c500070120b03082c3e00c80021107000d66020404a0b030302041081f24080f19441070300e400091035241e02182c84010700070000400700c09016840641c0c4000c464030052180803602503000f0758449100040d0b01e46088415014140075030b16040f0380c1c01a4030030858000d40118416200d452001d000300301c0c2d0742d1640d05c0595504000c0c003486070800c1940080714505d9008940c0107400c54660000c039444965526200c03410b5902c4002c010001401159601a44603004402c80b4050651100c0038008000008081020000010192810017481c810700b0104140c2c50414170416100b4101900d6491401340300c9100480e6002c44110f0052007803d03107030f89520440c1c4c1d113500e040c0c40541c02003514081a8403020620103658215020441c001041400143c0000c1e0b401000b20f0310898895080c0c0b0300b420b0900803140c0c08028891810354010314104906002c001c41180c140c01d15110344143c8644041000c41c0d1840c81070f82006155102c1c1c0c500c04654030740c00c0305c51188a4070040b03e13000402 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 477987697 1250 477986447 477986479
    0x905010e100e0105310314070506031315060303081608090c0d03140409061701020c060408160b2e0602030d09020402090405150a0503030c0316030504030506010311 72
    0xc0007200401c64001160303035041c080d02e984640d004140318402070720031821030200110448170749400c410308101102c120300d40800805c2203003400e503240ca8407a2005444079916003804556148801004491244030300d108210401c03014555402ca04141c40408200302a220b10f809881140c00740d442c100b8510130981c919080318032802c0f00c2d611030b03a803090103010118202024030043d1406c0303810442c28041d80d13200b000c05950070440680000d150b0100c0100303d00340f0f4007411500010442d0840c400c0380e40104480303408441d0008015400540c420301c0b4a0342e400003000b10303070030701030032200c0c0108048410014090704001540e0b0710203603d030100c454603541545000d21480b203d4402d10485016170024004d0140003010b50780300151650001e440035141c080c0000005084450881d0b4074040649070300d100c03034030f2420302c0740c4000701426017030b0300071481c3c0021540b4407540c17030040c010081d0320b4640c105a600d0405200d10705403802982d0001c111a09561a49407118851800c902100e008103a070480020038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 477988947 1250 477987697 477987709
    0x1e0d12020408030d470607050313091109060a230c2d0a06091506080f01050f01050d021311070506010e0907030b07030e0f1e1002040f05060d1b0905010e 67
    0xc19040001e10001940245c0d185000d0f00840b03001a8041b10620903000402c02c107000605403040100e0040100c0790500031248200d61020b49000c90307818003400a0b0a054a03580e00329440f6028500300300c02c00f03540c00001038041e04000f6510314003011010032180c840d0341e0b0020300d6400c1103c00655820310036040c24241030140c40c082c255662240c1c0114180000b0403001d50007811218011045581900c00301d07031000c0242c40c01940450347c0c0781c0c8080700303c092000307080c840c2940120401404070983d5141c200026140e1890002c00f0f032203003030310060322401a10355034002e06002c0d0410a1702a1150343c203040441d01e4000c00d10841c070000600400069240802240250660341c0c406002041e40c2c1720024110000c088055010b0020b00c2000020b4110020402080d141100c0d0346650b40390480340b07000304900303203406e16260343c8000340184401d010100b111001c003401e480e0160f503800e4135183c448140c100580090b4024866900c0c0001e03101200b55840f0035401c00350392007a00e808201d80d1b940024803032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 477990197 1250 477988947 477989021
    0x8070303030b03010c081f0e07080906070e1e01030f060e0412031b031a12030307020705090c0403110a0e130c06082403031c0204081e0d12020408030d 66
    0x421080006024120310642ea1004480080101f1082500c1d0740718208903c00907507003c80418400340800504030300420103a03910140b5480e200300d01346655008601040b0b100c0d00c41c980749800246a030302d95a4802e40c0041e603054000041440307030700d58984c8106413508080d0360580d000c201f40c600b08414140a0301951f90f040c2c6d2511000c190741c1c102004110010100c2540060300c80c1103071020001c4903035480008000400c40707000510342da4100030314003900d030910031307480789024403000410040300c030700c0d00c3d8151403c680d0405095030300ca08841c0300007205201560002c0001040230001e03c04a94044545001c40620860210340130380c0c0c03034034400d803680901152001e00410380643c042c036000c102c0d041400111000501100e043c038089040c0405205084a1000700300e590106082020440802c808040040c2144805040b103050741c803200e0b10f0751811031038101400a10182c0b00c1200390154110360041c038110301500d0f00e44003c05620000351007494444000200c820480c01900d90700311341943d07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 477991447 1250 477990197 477990221
    0x303070b06010e0303071704082428050a0b0a1401050316051c1a011d0f01020f0d1706090915091204060302030f07090b160f060603140d09181a0a08070303030b0301 72
    0x4081d6680d402101007100e140013000084100f41c0d0b580c541c80e1070240c2d0033a03c0c000d1000d00710100d0490b10b14000d00402604a5012603901c00340d459807a8120b9070004100c0343c0141724404d0009507080034180603100c03481042c5030134640000e071501c1441c15001c00d5105800b01c220403003144442c413402c90700468400541d4105911200c0f100101014a8600688480c12060060050b0303800c3c0030103600002e00b0804401c0c120404644500130320b99010109505050380030208840b000c00500782140c040d84c1e00c3c031408074500c44000062001c40c00340c002c10040000d0140664030004c0e074440d107403600280a5002520301c001e418194a021030170311340c06040c05c04140da8504088605112445a821480003030700c0780c05403a440590041900802e496019041c051340c01580d241c401e06040640d0a4a080348039104101002005c1100748000000040f608078229140c0d100821500410b043e070f41c0c000d2500c0c0b6061980700c3c014140000d0555000b00c0c0c4101140d01a4608010b07400c554000e040c00e84071181205 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 477992697 1250 477991447 477991513
    0x2806090e190b0103110301120209010b0703050a05032e03050607020c1f031404050313060f0f0e130903110f03040e0604110403050d0512060303070b06010e030307170408 74
    0x4090294540d0340502103114051501084500c802c400e144174a078400c4c2c004014100d12184c1c00015818520311a5005100d0440254604040c80d180144a401032485401c2000400804182d42c081040e41e0307100641d058440044c06800689400b1030101d50900c8103c1d014004e100015010034004203122042c100f016203480d0745c0d06101c07055241400600034802051503514492320b20208400701d10a40b01d144200029641d880c0c10b0603080b414034817142c1c4102c0410411150319605254405519042002d5600b810281c001202000507203422009031040401860101d118050540c40750441b04001408003e440b948040344603490348034402c1d4000d05180302c2013400410010f040030340c00300ca455207680c074140341019181d5950ba4144201c1345034200000e20045a0100001043d10900c1d0300300d40c0403001540703048100d40d10238550900003000c040c1070050345101d489098170140704446c403056000e4030001000d0b1032400d003a41c1c0ca400c94001c80c0024852903500718025141c8907413140780f00d8664044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 477993947 1250 477992697 477992731
    0xf011d0415020f031302010e03070605090402030a0b09040c0e010f03020d1b1a03010302010305010e060906042d140606130e07030f141803090a090207022806090e 71
    0x810220001d4008a01c00756542000034608401c001006180201020301c5000391508071800010002c014041c00c148c07294200210070010b05801404440031203c0580f00035807a0369602007506c000b010808000c0c1e0304401d03580e0030001001402d140e000c0940703000300f4034602c0ca0398171480e159842c0031480c00021f410000080c07000c00490074025404c0c8500c102180c801d035030144c0703c9042d41074002d25008107091400000c401070003150303054001c040c0907141c41c10001d00036150140005800c140040c0c01036005640d102d0070242100c034034071409513120a065086220040100034588001e00d040764109040440003000310351189440000c03902011035001c840d0803040d0812862116101d00901500b0615035181503400b28441c45020300da2030303104c442c10300b0f818034a4100a480c1014400c00d0940c0c20640081056111a64495001409441001c2d01c0140c90701150301c0424041612120a117188a0f07001203c0301d0304140080a900a650540d0b507041001641c800c000307080d006064545d14201d00390303002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 477995197 1250 477993947 477993953
    0x210209040c0302031912031a010302071106040807061d180907150e0f0414010b070606080f010504170301051005030703152c0609060f12070603050f011d04 68
    0x19545030824018207041984603501da001034503000c0104401c5401c0c1c080c000e00c54050224491400801d0881801e09008984103034000d610211030403500241859404a0303002c09100ca281901d215041018003166900d5131105c0c0c40310f40d81d81c2580305520010310138a450a486006c81000d40040c4034014141001c4650005400c0703252840c0180055840e02c5040c1c4000365a08030a240c09a0340e6559454003c0d134109240e0a0003221600d0760940c0e03019030700f000c0d2000064012094107a04491000b100036440e580307035140c488003034016035100c0c940a10031440a0744101106511542c003440c42a01102801c05540080c10000e0100340325103603001340b03200d000c805400e001380011584854145000618a100884851030741c4050340c0000296075185180030300126161081d100b20012103c4001040c3e00c3e0000018542840c02070285004020480041415446080340360019201d15402d5490b02611490300800420040398841500f41c1044000202c9807400d0000c1030a0700e40900501d11300d42d80d2a1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 477996447 1250 477995197 477995209
    0xe031309090f05100b040501080c10050f0c07030c090b2d040f090b19150504020a0201020f030903130f030201081b0904060b0405030f01020a0815030a0f060b04062102 73
    0x2a80c181c1d2100b040d01c508100040c000e0100318056041c0c0c1c0760000c0c4500c1c8040900c0b0442c1c0f416081044142e00000e9402030320f03aa4520050009019460820f60707812030021807612038040d00c2c6c141c41c1e030b40c840d4907800b1041000c6550840705490040804005a021040c200002c040301c441c079152401900e2000c40c80c4003096a0ba041e560090054004950380f4150f903040c00885484c0c0a0544410110801b40b00c0443c0000c150f4004003042c03000140103068030040c00120000c031a10a8a20460303000500428280c000e4054441408010301500d4680c600460349030b8896200345084032103050401c0d008146400c0c0c2d85150810b41c2d4041e542ea001580c0c5207140f65041c80710540c4100310004083c042102030b59240d000322070103403d41407002d80c4c95a24110a0503d0308428030a000c000364010b00c20084d41652050300b50382e200c419a4001143c0085540109081c0400b404000e088860300e502c000c4144409a00301c0010204140c030708010340e6030380720400d02c0e03810b0040d03020240050071190f54001501e015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 477997697 1250 477996447 477996461
    0x15070903030e030c0618031c0909090c0b0a020d030b010921151a012a0209100b030a0204140a030507090e0c03030a200d020a03120f1508010e031309 65
    0x43c045400905180b0f00045254105100400f480d01d408038100117141010306c030b008010031040400743c2c505540703108090002c1045000e0210640d0f07a5110709014003820298042c000d000e2901c40b59501c59020b00001d4490a45072901c2c40460300b42036000c401c07544961011001c5900f212001c0020f500240b06d03046400700040c006984ca003540030402c600112061281c0c0d01e0b22900f0220b86a429074440d00050190304545507010117101d00d00080d040742e1005046c0300c003d0705a04860038505545c41d50004045214190069042c0f100040f04005603880c2c980c0c001c0069a280700905070045c1503507001c000c0e000c102404010601d4204080401030310300d035501f140c22820303403000c20b403056030103c0c00c0480d240d5040141d0700400a8420000b8106480142044a0440b06010084c2000611040010b55202c449400c000e0030003240703890051282e501640803614050305004180608011450341d424081000c1c040e481080d442d101c0e086230b10302c1001003251030361440a644503e80d54640782e00c0e40020060 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 477998947 1250 477997697 477997699
    0xb03030702150d06050d050607030b010c0c081b09090d140f0c060f01290d0f090b0f0907050306010b0c070b030406050f010b040302030606120c0604080f15070903030e 73
    0x41406940d0050b92802c0c01001c903504181802603c800c9600c106105440c400d0b80502d01500702507002e40701250b8003145c01640807106003800f20721281c41000403200061212806407010541e02c1010a0103280468040c03038000110f034410400307194100c1008002d010940c1c00c102c090380032100702c41c555400b40c550755403e0503003c100f4505003140c01c9001440c50380030201caa100794020300200086815261412809484284600e51283c9404242c00f0088500001c12304090714000c5101d42d0041c040e504088010310300340f00c0c28005000c03030389418100f040050706c44208010a400000b4208040001c080301240c000500500c8282d02c0c10140c14027603440308410103007a02a490000c10b4144618ac011070090b4864040042c003854001d03007008044d06c043e04040145001000100b0250350300062480c0c018034115108080c0d000c00c01000361901000c0c468103500800c0200c1c0010340c6100108400d40c050078141c01340d0701843c140c00b0314030b4001d20f4121601e202195140e001803000c2440b0b01c02401d410f01d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 478000197 1250 477998947 477998953
    0x21b10080403021e030409060603140c1c0614030606060a0c0807020d050601061e02060606040e09010f0612020102160f15030b040f0b01110c0112020a0c020d0803062407060b03 77
    0x4100300392104a96200011241c13a42d0000908001c44800c0c1e2141390b000f1b103800d15007000300c104400110304400001a029400544c00400c114480d6010303070201a00c404006d00f02040f10fa50382d60042c5628001e440c154510034042c5100040d900d060001c1203c03e41b940f42d0b82c68580d118030f2591030000380e40048806981107590510b00d20300092040060038042d0500751514040f00008800b55400801100100000c40d08403400b4026152614030031380e02982d10346603c440c00c50b61192112070050090038520000241411030010301d600a1300b280d00e4416000fa402e07240b100b9200c40c1041c44d010482d1044508225414204014041e5440076000800407d40740c0403621420b20320003e810360b1010180c910515036170382200c041d150707005500300f0003030554000901074281a02c400030303000c81018000c1c80c000c2a000a0303402600d80c454820f107590113a004080203510b0140703040081c0c59070030454207075010f8641410702098184200c91500c001c04031082a16141c080c155035004060a010f02d8415050300c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 478001447 1250 478000197 478000213
    0x903050c01031d0102181c0803010e04021309080306190f030602030705070606030c180c120e070b03040804050a12121d120a060b010509011209020a0e100303021b1008040302 76
    0x10300380000e04003e1390312060340340e06803416407c010100c406a2103e060b051b031200010130001d01310100f80e0381100c061543c41c560700d0350b0314000b18105507500660880d41900c0c1c030b4101000c0044079400385018030400e03641c003410388903d0f522003000c01c5c10304d00640740d02104010082000943e203400070344d131085040c89d1644c03d0109039902d500503190160011111141505d0703040c0000101c881c0c0d0030381811840e940038044c04100d01800780c0003008030681c0003a4140c8542c0b080c0c90f18a420400d00e0f00808501885a50740e1815080c07800040d0030502038144a030444140001300c2d49502c03481051340c2c9800c001c1990f052600c903002950700702810440d9091264a800070710711141d6400c41414801c086c01c402070440350800e4900303007044074110440b050602c0418000078000d0799006030f8180b00c0100158001409410b41d00000701c4015a50744010003940040040144d031f41c4483c0c5070f18080343e11903001c03038101c40214541e0680030100e85400f1a0080218603403503203150310540030325400900a0066910741 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 478002697 1250 478001447 478001501
    0x3020a06051b070b04031412180f100b040c020f0304061b0c0e0a0506040e10050c130605190504050d2303030702030406090f06140a020106180506030d0903050c0103 72
    0x40e810443d02603e90201140401c01419082040d1107020102d21250915201901020620844000d044448541411480444d010310200442a69801e2400840d000545840035503c06006100600350080c4c0c00d0030700d4240311034000134545c00203030503c40c00740d4185420608110b444545134000c100c12800790301814804a0840c4c01004050410400240340764544800b003817065407000b4003611b008a2402404140e44900410000000920003402240719101c1c1907580b8201c0c02000032400204100304000101d0b01d410000030001c44060702051a202d0f02044d200740e800e03000d544150f0b500700807607000070030010380e200c20031801160440d56600344a81d074502031a8510341084a007074000d03030f00002d41480165003200603440100f4400c44125070701404d021006186401c680f581030069107001ca080d4a00b28000c0d007000000d82000003000c8003c0341d6581d00382004e000281d4106009002e0040550b1700640300340c501390266074100f0000d0403090450401140100740805954150010012107903585c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 478003947 1250 478002697 478002751
    0x90406090c030510060f0c05070302030607050903120903030f0d090c09020414040605060a0f170702240702120c030913020a090509131101050c0f0601140d03020a0605 73
    0x1528200c900090380488025000c1e0449501420007240d03850109420803066502105035441c410151520304904452807030164a40202900003d605014080030020f000764094007402e4040411400c4801c2c103c5025560402c3d403099002132030701a0010010220416440001040413100800000400f0300c25912030f00030784892600000042c5400145c10840d0b400d40720090b10580d08221001c001d000c1c5044005000c0e481794200d0301061000f455402e041070303030080e01c000810220340300300c090003845e02d190000d413140301007400c06c80c4400758034005101c03101d826020203118011907002071003c0c600be88825001c0d5004000315801d90f200c104111a1544c4414034024502c00300000090f885000d16080584041015000325000c1c440100420040b070b02d1f0214042503068110f0090340b6641c1304980125154840c518002d80700c2c0c8103441d01030900c0a40000d942d4100c0340c0c083d0001108441c0071017007125a8000b120301400583c40143d042022851580c0150341104104030714944444e1141c4040d8a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 478005197 1250 478003947 478003949
    0x2b0803090c10021504240605030d0302040602150402030102210601020706030507270b040303111506061c110712021509030f1305150703080c04120303091103010f0b0a09110a1103090406 81
    0x1d040d00d8000803c80342c01c00300700d04402034031b181c241035081500383b020096950256480d01c00c08140c05002103020b54030298110b0f000540c404400740d04031703030800c0d03002c101d40d42061303501c240148600300e80001e05138400d11a01d0300400090751094140c02100c018460703500c8085580412040c1101e80000d480d0b5507840003030008610a8039400131481d814414a42000d480e808862480322460040000719581d840480351410f90040c1d09a0514004607100c0004042048032503c400200007500414800f82c03519030392500e0980d90803100da80a8082540401190542d0301c05490b40c014800a000c20807100043c01c0042d0300074a80c8090241e4840006a40d5000f50300150701d40f100005010060540c86986194022040b5548034682031070801d102c1c0481040d0f010107001c00d40d07035114102c1080400d43c1e0003116400010000d0002c00c0c034120301d034802050341c241820320908000000040d8458540214951142c1b101802401c2c01d0242d00195130300300201c400d4855034041000b031450320355550300c1150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 478006447 1250 478005197 478005263
    0xa06050a180e0328030b090a090b3711160c08031c050603101506110f0303012c0a051b1303022b0803090c10021504 51
    0x84540700c0490084219000480d08480e540c10400942e070b0096103a103a16800c00780045402813465000b10001c900074804200080c0e40300c095038040c0b2090391084d8011644440c040c03a030311502c5445175141c61903410150358000d22102c04001e441605043c00803648010300c1c40f03200d2b001c80c2c4202c030354010080c15032088245140a07007010740c400003408074601000020f0804c5c40c00a510b000011902e12400e91070b0000c00c600116102c0b40080c580344c60a000c120014207540905100502075240034001c51032150094000088140348588682c180028441c100e00d0b4100d4095455a402c0c03500ca0300c01640300852a600260720f907030201803c0c6440c9424035100d280c55000000b00d0342410004001d42040180080020290a102c1d00e8901c0d00f9010815049960440d00f1003068140100c58858015036085103d0003144600441024400f0080c0150b115401c06025140580131800804c80e55442080303480d0b0040e80082c10171800020409489504540200d04400c01d6802c4414001c0c2e207014242405 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 478007697 1250 478006447 478006469
    0xa0305070e07170903090d0c0806100305010506040c0915110307060b101e030c020106080f0102090a0914040807030203090924120d0c0c090603121211120a06050a 71
    0x103940d0100c406043c2d0102407144030700604040060310b650b80078009a4a1046918100300c1c820001c60f680107800900101d03064681714030f0103c0b0130401015140c4025982c95007000009040341c0b42510070407050b01d04030b8a6031610182424640302c4400f00c04440c507024000c0fa6130301b60180010800c062320315648201c4020461000d14404d00034454403404400d010b100c078000300081c0c1346c0c030188d0b02402c440f0454640040d10f8a81c0e0b52003240902001e81c8001024060000440c083c3c510640041817148030558507869102c0da141d2040007140c080c8400f105d0f0706000130000c1000070f00d03545e00515486000b40704803400c01c990300e40090700c40581625860032826a00750328181a4000120200305110300300c44580704000c640c00d119450300b4800d00c0210030442c486901e4010003075140c046c0006041d0070401008000e0310b034034101228502440300c03800424928656443c443e0814007401c201c0388000105181010300d1030f400d0300b503040320142940303c84549941020550ba1210725480004041c541c0b00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 478008947 1250 478007697 478007701
    0xf030412121e030917030106020f0105010e010501020d0f020102120f070201241214060703050f13020f0904031106090d1206080c0d0302030403050106180c03020909060405060a0305070e 81
    0x4541101079610348a10280645849040d0000007000c2c141000009241000f248424680c40c08044040712000d04120414000c4000706000d030f400108070b184140c4260003003000e662200011207609a01f481501c0c01039002900301810307644a8002902001c04900000d4284160760301d905d6600e810442c1c00d0840300b501d4404000b10075609010340b401d198070140d8008012178070142e00007917405442c000c14520b00d4040e4000400c000756000529900c00040040e50900d0a0ad82c00c01400b03460150391400c500140e64010550720700d030101d2421134055004043d140d401c0c1c94101804a039800c02070090301841800681042005028054680f1686e0004041d140721500f00e140903280300c90101c0300481c840c2c50a00c040c4042030b070005940b00c44400407511041050b415140803840c6204a410050195080080000d040714561610380039201c3c0b10311301440a00d580c00d07012030480c020a00b1603641300401c7c00101e94107007425480702d81c00602c05044866001d803691202454070f200e90303000101d00036880742 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 478010197 1250 478008947 478008953
    0x1204030e0906010e0117070516050a1202030a021b0609060715061d010b0c1c09080d052a192a030215030a06050409030e01020106082a030f030412 64
    0x12940e11900900b001409072904000003402c0340c200500d0503446103660800704031040d000304240c515044110032549e20220003454055220300ca09607044420a0a058800d200304d070010007a01d50402e000d030b00402d103031000e4110290701c0840910044c0c1d04407000b004001010b071180c10081108034043d420041c44402441d10300000c468081e404a010300341b111352103802c00000803050724111000251303501c0d168031006403c503050110f0301003541c02010312484190340e040d41060384002124540c00a90b21885030103030b000d95582c801d050308080000503172150300c801c4005444018405000704000c940d200038421100703440c0540c01d44010f0301e070040c0c1002c50442c0f0028103030000303d40140c0d9640c3c00d089245198003094854411510401c65000c010000502240e203a07030001000b030400030b100303000d25501810058101c014080043e401035007850750101d0f150100050517070302c401c1440880c003150003130018004d8188a201c1036482c0d05009001c40480014000c20280018000400407500551803511b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 478011447 1250 478010197 478010209
    0x240604081605040615030e151f05061204120207031202010618090803060d110303120105040b0301050f0c0c0a060f060f0608281d010e0d110a171204030e 67
    0x548018403c90078500c09000c8400a28900800e070001c81c1004201e844149107880d0402d95001c984401018483d010011091281401c8240748842c2c1110072a440b526541401400e20270541a020f0100503c00400c0001b4510070290102c50607910540381c1607030301c07940ca0b207044041c81491074005030346400052004904c088140684008411030804c041109655100164000284080d11801d0381c108024240161015000c500c400001d0540380e81c0d5201e0109003440e40001c4c050700f80120300d07040710841b550505105050107031107440c03800c0f82582c2e136448950304282d0210007468070a0040403440400103440c0d004003440103134a03950214a16042000310030f050310083e4080000c1103030b81c00074044000c1c24100b0045000d000200000740c82c2c1207410ba04400380000e610b41303161250b1020720820800f041980320690b805100c80656407041001d6a0840f1108604409403506421051204001401d91400a9010300e802141c5500b0503510307000940a10404580607000305083c0f198001c8245440b03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 478012697 1250 478011447 478011449
    0x31c02130f0509151311071a040b0604020a0e06031302090c130b13031a07120b090105060a2c011205012405090312070c0602152406040816 61
    0xc54507542100d180c100052050000508080c13900620300000a405842d04e03000860110303000310b002e0004c1034004048a0072640400401d98514015218800041800d01c11060045421412035a040d0300d5a0042000030b50002682c20203200c52a1022940d40c6c444030050740c82811042d80103410a02140140070350804000c1014048980401c41103507102142140d05080d10300b0306900301d8680c00e5000a007480c40301075801c0941038000103c0079000190300e04600301e10825031507540310281412060040d0170781e907001c89019403141e10b0030300512850410102901003084c083c54901408200d50b82c0740e1080b07507110303c82c14442414a003008400303547c105907100c01c0403107064000c00c1598500765954000300170140c42401c000080c0e002d20301c041da03c80c9059a40c3c1c1c010050070f440e0140e4200364a640d09a120b032000b11303125810408009034290012521640c04110106001150b40e103c420700c2000c00d542110788401c582072a410604e0a8480700090000350030145c0042c42204200d010f6080d9440d41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 478013947 1250 478012697 478012709
    0x40f031407120c060806060f0304060203070201060603020901120b04061a03040308060d020f0f01030f020316021c1b0501020708070b07020610140103021c050a0c083105031c0213 78
    0xb80c0d8040024400001401190141e2900d910151507440005a83c1c1c403070039960048004011042c07005019440c1c2c01503000382c5194000f081100c1da10744081d0140e00807da01c0754081382102c5040508004503070400c05100100520004070552192003469079550402c0f01c1128407040407080200f0140c100018940140007200c04054041c05940040c02d0607420306540c0b800303140c01d101120340590080d002801c044d10388500c250749a15013a00f242e82411000c03500d40c03005200313600318500401000038124044400c159511880001110302c9076403010b5048c802281d50f9982003080c40007080c00c060280607002e100d4144011179060507a0020303c1d00f10060043c0c0309407004a002046668007511807041c0055080c21b015854004c084030300000300c0a041c00702e00c8114240020880075605561200c0c14000345500c400f0307070382e481c0d12010101340c200404440b4460300180c107068502c2104c1d045a0b0040300c0c4100c0887c1d2510b070b000c3c00d0380c0e41a009400c04a00c11140c01165a40d0820200740b050300c06088 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 478015197 1250 478013947 478013969
    0x607031e11061915080d0912080915040e0109060f0518160c0b010e01030b0f090a0323070303050609061e0402030a06050904210305090d080a02040f031407 68
    0x248456520303090080c019280f5103680900c0c54000719001e0700644254294a100c9050203650b038001d59889100788060080090200c10021a0110707940e400001c4494104242c40d080c800b0f00f000b030064088503040300ea03190349002d000001e043c604814a8602030031214501049103490003ca14041d10f055400035032140c540000c5401800105412480c3c0c0810000984c0451590840041d99406403104001d01510040c00002c122a86d00a038441d048a00c500850001c1c0c3c0c0c0ca0344021240d024041e00c0204041c0c01c6441500c4c0424810051000f404010310546691403804142d40d60082d03000f07032821000300e920f1754100031080c600108900d5022070f003a40c2c04204640100001c0383d42c4101c0085651040d903010011400b0442c070340e804003002e4580a4124880c0341018100281e42c98583d03081c44a910020002000107644a13015080c0140c0a0b0401414003010b21307a4103680c0ca80c00103003090310f80c507828880064640b500e0041c8500640c01a0240c2e241070710100200c40c100141e80d00f008400032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 478016447 1250 478015197 478015217
    0x13030501020d0f0c05160206040504020a020a0203241b04090216050d0f020c01080928050115030b01030b04141b1203040e190f020316030b09040c1a090607031e 70
    0x254000d07040718418006e241d48960182060300c0041d0240c021a080030b5085440800c9c0c01621076000201c10020034000c404a800350205203644140400700300c407500c45000035070030100713080100d0358040c0e41906100704100c5090980743c418a1040340c0000c8a51107410104501440c28010180f158400300d122900e0943c04d0009040e6029603079400200844c2c0c10005001d000440d1010140b009400b00c0e0002607504403180445181111036210004045d2450351130202c4a680c1a017a0071251400c0740c2d8070401c902096880d5407100540c010000300196044000020005001340c0b00340464a1007102e0315030300d9240001d241c824000809400054085a170344104800d21841d59954030003a40550b140060a502e81c0001c8034450180110704d00080c8251300220602030b00481c00d00c1906500003856600f0400c00808904000310f01c202905c024100003035105c810300241646503115187c100c0441e401c4c0d49480c2e60000071902941c0a10002d4000580c0c0d9148030484e1890340c05951400c80085c6000c00e050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 478017697 1250 478016447 478016471
    0x11e0614090c030712060506030901060303120207030c0602030402010309050616020d0305100515041a0415020a020f12010b09040f170a090e060a031505010302152d13030501020d0f 79
    0xb480044e01e200d09102e0351102c0440c82407059000440504406004161203061058606002e01120300048000c1000500204111140b134070984641540543d00c441b071b02c030f5154480200039400a04103904140d00c1e0740c101c10224108000b80790103001d0850046444119030741000b8144400e54076400105410042480b01410040e801036044d42c80407201c10a0407580e94080702188d21569120a0359154085038400c8007031503400240c0100d40750003070f4010781103203a080c04988900c00220001d500c8102c4803912411410642001040c440324240002180c0e9009400940400812603040710711b0703003200301900104001095001009444407404505003000078001415001c21406a10310040b40c16000801945c0c5d440c03940f00045401c801303102c005d84000070090000e080b0074041a402086000d00030811211800c0c1100c00c40d1105155401070b543c0e00c40d0540810000303c001e5503802010911002e00052030740310810004520800c00140d40d41d0702c0004150a44031000e00c80700301c00313262016004003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 478018947 1250 478017697 478017721
    0xc02191b170c01110313050f01031d010219080712050a060b0f0304020f090103081b070b03090c040b0901060903021201090203030a1211031303030c0309060c0201020a020c0a1a0c011e061409 83
    0x981c0e408a40301c461403200d142c0120010b2042c107075680c00e21035090548101c810bc0640c010001440564608402e1100d01034094402e0241a11440c0c00503580d506c4007040301e1025030080350014080240070415656944803001ea035004003500d0128914000b09020031480d0031001101021000d941c810480d40c0345488401c81c1d401440c2a00c1e201c605240d0b8000c100344802d0220f1009410f6040d000d036100d08040c00115580d8004201150061b450425140510b15150286604a9a00d940d60f00d02090542d401e204000380780300c000071000e648a00807000140d8050014003a948281d6070361210307814207a2514410b07648034a81d81d032580b407002c005101c0c50300b40701e0300304000140d094100400d0014604c24110010964880d02614640c46e2084403c2003a40c190014a84040380ba802c40c0c036161002003c000301001f040c454489240030504003010407070b6200020304404803246000060b0040400e03141d4060207240c042c0c9080c51b035a503540500c12103d030340d111141416001d40e0030404515111400b548 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 478020197 1250 478018947 478018949
    0x1401030b0408030702070515070303050907050918010b0904030c020a14090c0a1701030803090709180f0f06110405090f071218020406030b01090c02191b170c01110313 73
    0x802c020700040012039145c002c11000006082c05400e0780404c0c12a07140d04a11034000c0842100000d0402020440350480080c0600c1620001000f40c9c0c0c8a07202c598184001100314100200b15540b5a1900c060399034038140040c0c071490194603051a00121441001401241a005030022a51003070480800d512822180e541c4400365850880d550002d0060680e4800c002801c8010139403e003c001104004000000c2d5000d1041c2c00100c03403866440c0c2d2400000c1d22011061400d0034000c40c4601c101041070720b640280380d2809080700b001c0000e1540c0740c80041d0b5800d04100801441c0001e4100300c2c0d03003841020702d544281000740700400e60030b090f00d0040600340d1180c00140d03496294082c001d1010318100c0540d002c0341e03001f0404c0024a9592400c450b00c100300b4440e0002c42c03480c1c842401c40582c00860980084001b0b800e4031014110070307540300030131002e1821001c08070304414800030540d160750808a258482060000f00444059440010a031200d5500220000e170810f105140003040b410309018 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 478021447 1250 478020197 478020203
    0x140619140d0c0902031e06030d170c04050d030e0f06070b1b1c050103060c05090334060e04110c0c040914060f01060e0306040b0a090303060506040602101401030b04 72
    0x181494899040400c2d004020380c00420449100105200c198001c12000100c40d20560944c0c030006d650b10700426464005195034400460018100d412011b4003403400540e00c0303100c2c910100e0402c1d8464020540101b030700c1d0002c501280480075a40501c2c13502d90a2081195021100c0303a180112917983c3c02e2003d14007410100200f0b18502c10451245028406d42d1400c03442c08540d00e08030b104854a8201401d420b110583d031070341c0b0300900010440c0c8540d081f030f03045010180080501d200d002c19640000705a1071401c10030190500c1d0b5000749021320321540c0d4014000ca5444001050303007042041300302ca4a0000120b210141000f03d007900000104516080306001c5400081500317003403c01098942c00c00ba030ba95445d01448041290310f50f6009400c90680e00c10f035650301d08502d1900b00341a0344000544005d000c1510500c00690204100c1d04481441e620a250208409a0340ea02140c0e00d41c0058000340050b82102c2300300b900d80381941c0f01d91005825517070781c1c4600d1549142c48100c0106130151002d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 478022697 1250 478021447 478021459
    0xf0203011407020f100b0f060a0e1c0c08010501080a0209100b04060302181e01140409060e040506070302070f0f0317160e0307050a030609030507151a04050907140109080114061914 79
    0x1000b54276008500001c02260080d1500c1d00c807400110361040d84080a403001c50302c002c2811404601c15405100e81d90503600d41500403e02800b9980801c4500c40004111030b00d82c510686001c540c11044102400061901e030310007507151030025020740c4070441c5000c0e0090051074013510007011810442030b4680700d8a020b0030480c1e0380f501b08d105a421944107940000c07001d03e09003400080c0201144100c2e41c0705a0050f8152542a00c074a03d0480c241c1c8141040a45454014a035504c0071494001c8141c2c44c1500c02c1c10b00d514050303460450302001e00b90480780d048200040c800c204c64000d030010704416004004801400c8003d080500042113004180809044070741e4a80c002810140203c049504c0d07103400604044c2a0f20841c0c01b1403028004ea051101c412000302556901c3c4ca05140c0501f43c01b880f010702c05040418108200e81001000c030621b001d04210f00b201002072504e00a100d1902200300c10011810a482c1c2481485510450020f0310400c079000d490302007100a1008841c255440d10840310 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 478023947 1250 478022697 478022707
    0xa140a0317460f0f03151e0e1021050105090a0209060a03030503040b0903041a0a0e0103020c150c0d0c18060801030512030406060308181315030f0203011407020f100b0f06 75
    0x8100e00410b01820320200000860b800841c0c01f00a145900080580355500c561401d034a03008601c8040c0c3c41502c188020400e41031090000b2040c1c80400c8194584900c80000d08000e56241c003401e4450695091260790040b00018055003000042c0c02c0d0b1010054031070000c0c207403550ba0300a1903031100400162038068010041102030600b4001c0300c000f850040c01e12603001c0c03900f04145540790703c0380c175900021a507610840c2e9043c4d402030007600d00003609800036107078010044038401d5082d01d00900604881c0384c200503407020b106440c030600883d8a01541c0c0c00750030700c4440d40e842c61b80c2070303a54101000b0301081c1d1004000290b80000d814000908440d0703055200e48807445c11301c0c0a045260402000304070003080c0895000094455606910411214840c001038401140b504669000c2caa0403070340c1c1c0b840e21050011038032150500d0b52031031001d000090400e55407402c8812400c8292040c02c016080f40c2d070000000c803010030171265202c07041003041060180c42c0f00010b0b80c07100500ba0040c054000891 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 478025197 1250 478023947 478023977
    0x10c120504020a0b070b0a060801090c0506070f02150703030b031222030c0e0702210d0207020a0b030106030501050306160905012f0105060a140a0317460f 68
    0x403840180345400c01c04d51030b86640d1405180c0304104560300c0704101d28004001512000c1401120b502641208100e0021820b0000b441010f80c001c0344140c1d01036070119000401070b201c40040c010420345003000c26480d0b41d240d103030040c00c1c5d91907078400a10a80c40490180c01e000040700880c0d2480b841c816008805041c3c86203d00c000340b01ca90f00243c03640c4015500001c91048218140c4e204400940c2980d491900b00192894011030480b03040406d1101030000c86030b2a021680100341e0301d80020551040255909003000950b40241c014100007526038004000700c0c2000c120040c3c1047c4500d40321030865003051002000402a885843c4c10843e207049105080401355242007201c120304644800c003440000c8084d03000c5d26007940d12030b0003140340010010382035103d150445905ca0340205903210251558030f6030204120250040600c181c01046540e5040508041b00e4803100302060490103407121074041025440038222074070007688208001851840da11015148440b042401c14441c0d20340100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 478026447 1250 478025197 478025209
    0x1104031e05120705033f060f03030d1b140d050a020f030a090302070602070e0606030702010b09070207090b0f0609010804152a030605010503070c03020a08030c1b010c12050402 77
    0x1a0102c81200740004040d8248100800200f01c9080e00140c4035a81c400a1100e20295004055140810311500000e5400000480340d400c0c0d00701c04000c2000c1d82c02401040081c0c02c5030302c2000c050384065580c202c0008040742602c01841c12a03030780c0c2846c1a0340c0c50400b00303922840c807030040300080700340c2d035000001c0402c245507050b15a1804a180b40e203440e480c0c10208000200a444401d802500c01c16100040240c4009024001e498200200d0105910f07658140040b58002900260555481e0042100561200e20340e0313501c551442c1d8000c003034203880d18816604603a09050a03034014460b03040420003685030f141c11622125000e1800c02c4181e5a50700f045030200c94200e130081c200d14182210051042c18504810084144281c0600b07801c0003500c40c00c6e0300711009845041c5c0400e20500010304007034040c000490030716009005481111040b42d0b1452500c4c0d00445815180c800080b0340c1d030b40058412200150034000181c002c004060513000041d0501504103a003000b02510341d0300042c02c40d1512 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 478027697 1250 478026447 478026463
    0x1101030212090a03080a1a0409020609150d0e01090305070308070c0b100501080a0e0a1509080d06180b090a020d020f0a030209090f1306020d0b0a03151104031e05 71
    0x1006a006203041c9125403544410f90f400c02034001800000106040c9201445900b420000c0c010b560b6007203803400418080548255103060380c0c481c0d82070082102d00d803a0900f4034041009141e086994a0811003508030480381581a40345131685004000400a9044000c64000b2601410450b980ba038a020040f1110107000400800700b115480070321070040003030714010054420980f6454050740e01d0814000865080c4442e01d61503070301880101c80030a181c034205603140705603180d021603000c08a48032070780d081d84804990a01c4c55507c0c4400c0115503e5a00c1d2030341e00085804082c019502c00c1000034400000c06081402c14a038001000c00c0004065412603010342041444a6142c01c02da8002800a42018091030b01032802c1034000b0b407001e8090000f081c8107030000140062054002c1c6c039080d00030b4100315101102c10380c2e20111020160f41700c01214008622408044210386031010607801591303d40030b100d10316102d00784018000940e490800b15078841103c4143e0064981904010b40f500e248 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 478028947 1250 478027697 478027717
    0xf0612020d060b190302070c1a07050105090705090a021306270801140615070b040305210405010e01020c061b040b0304080403050d09211b1d0603030a090311010302 72
    0x2812400042007200c03070003d40401c1d4030110300500da40c034113810103500741c1c4a800401025149040401d10022990302e402c8210348104002130b82c100802c0755902c500712441a500e224099004007010001450401d01c1182d00030f048420650521010084a0b48800e5050294505009501e0746600da101102e88860204d00c80c07410b10400788641d1954103500802c00304016041ca030400d80000350a41c146910301095048410005901c2c02607152906e210002c4003038021020014100100030100809064242c07880c01c00c0480e24015050600d450b0b800c5a00351130710104942d0050040300d01c4104049995a840302c1d41d0701c40640d0000000120711064071032078109510140020003071105000c1460060400d523403040c0d0480d5180c1c45481400e45049006115254440c40780941e4011604c0e480790060300c6992244c0c4650521200f500b25900c040b4640360869803445c440c59072044241c00d4030581031030300078a0550140d031410304451401403420080307000123031041c0d031064080d040c182d100c0ea04480c4100340d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 478030197 1250 478028947 478028951
    0xe060a0e0f1009260601060c0606092a1e0806040908030702101401122310020d1d060f07021c0504091b0509040902030304030203030d060f0f0f0612020d 67
    0x72455002e02021010300031000e5506054111300082e81c400c07510140c0d00219000180456031a10b1380440307040f15160012140c140e00c0703507000030740003645008940e070700800110b0040c1c03d0020903030035106401403a00e2460400005403e105104240d258900101d21541d140c83c941c15603c0301d000c40c0250440310030092504800108002580f540800e440351031800006040c070000301c46042150b40000d082c007490032141c00e404000000917440140e118a4511036400203051640406009030402400c08141d0610980000e00000c81c40c2240c4030701ca0203c0450a0b0607440024401d94880d66407100410700a901d07203103980400d0005000308042e080c0072464505a120303d40d42c90400038100c0d000f610580304007034202440d03414502000501f40c941102c00e9a41d00382004607900801015080b2000c0990305400200408409614140004d00c4140d40c80304020408a1410704100f00c4c010340b5a00c01d490003400e83c038085c801c079141c0c00340800465881e0308d4050740082030003006000034030a8400e9800e083d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 478031447 1250 478030197 478030219
    0x515090c0102061303021504050c0901060f170103170310030f0f0204060806091c230c06060d0b0408030402150a03150801060605071203150905090c010e060a0e0f 71
    0x82000114464240c50aa003518096100d0f4950400810b1640f18000e0240e041103030344140710019200f04031742c024003540488600202c98408120051002c0c1c10003c005448500d10504183e0001d900001c2c10115003010b204641c95078903070401e00c600719050300915000010100b40d50308080c03415000695001201c10060012600d052100c2e81c10502089002d1400c3c440001008100800c4c80f03482000d01c04041c0c84c44940d2250f81c03840342540b030380ca130f10244440c0703403800c10456510f600d14004407484403d58690742c00501440918020700200410710880c0d2a0840800103800900005d8001d50f018080903102e44681c40045c0c00c2c40d4445101204030b100204022821581c5034000404805455414004040e158540036080e5201c500514020074401c1001c2000038090301c0c12800e0712095440d00160300b41604820302800001c55000c88001034581042c058100c60034000c0e068009000d00b0011605c2c403034080440d5590254440346014411684280841600c988030400d0031010001c2c60300c1c0d592 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 478032697 1250 478031447 478031461
    0x1090803030108101802031b12070605030a1802280e0903030708070206100e0903131d0606041a07030e09070216080c09160210020a080405150103080a0c0515 69
    0x601c4400768544481420008203074005030218100c2105c854001e405454030914810b0300c070300070040c55002d694114203207003503220108a06004010141c8555595166282032500400c03094420b41d4641b2214403000d142030a006a5074102c111400012015082e81d402c503089110b244241001c0c0e0090080c42000b60420541400120043d403250080d43c4800070941c0380c4e510200d80e81c400488580071040c000110030b1003d1040481706503486150788080b0f078502000311103c9882c6c440960b1250348180c00100341c91203510100c5a503264080d0058460300d0038549000807000007a010404001300341540014040c003031500c107184000d0b16007006000b2030782e117080091000b90384510031140240b07407800f41c01011440c2034001c40c114940c0da04c0100859800d40b2400301e100c0c07000c41400040d400b9441200340c601c4000d503c41c000b07403c0c0c3c480f0503140c094003031a143c1040350824420300c1088203486903c070010b2002458120589010000c28903045195507094506203107410041c000440e085a1814100048 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 478033947 1250 478032697 478032703
    0xb040512030d0f0c17010506041707081501080d0e01050702060d0902031501081605090412170106080a1103040312050c090a0801020a1b0c150909020712030c020f100b01090803030108 80
    0x2c0a01c6175641c58001d420b00020002458a0030300803564480802c0204100301c031545e12002200e00c0b40001030b148295a5206590b10740042e40d52000c0c031035607401004011414040c05100314141c4241821420500c5800008000703104003440248101c8012030708018070700195002410240e405401c5514040034400e00c0002c03d1000d00c40ca0060780700d4140d4103a00b112111083c0011500b000c0c0c030040b003644031681c0301c3e02c20600390b480c000304100080f03601c85502081c100780c0714001e050380c1d01c0745002c3e03082401d060700c191001030400040000c1e0400074000000e82c01801306030b921801230000241da03120705003511254840d40700400e5000c1805403001c07508000c1075005002e0254652100144c0302c9103017521840403145400c000e0041c540b010b4040006010000a50005911501d0808103268a0b81d003039800300c0e00128820341d08840c0e003480c82141c00742c0510800350f00f00038900050841c084003050169a607034a80c8a007400043e19100a8419640200d54503006130030002c1c1587d44075130f190042160307 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 478035197 1250 478033947 478033961
    0x150d15021206040f0c05122208070203060106110d1d030106060e031618020901020c06161b0f0b0c0a0f030c110a0b04032004020d06060809070b040512030d0f 69
    0x1c4114a40040f40701e000169100b08000b07540039481ba07030f040258148007100c1e804070082034000c2040317a00040c82c1e1800192520541e90718803c404660312207a460042c140b5200b0160006c10a000f01101e448503031050000c5e50115810051a041d144a004840e1000a8040000d5000e0b019800c00ba4049902500001050b03415102503080f10000c0c003c0c00c9200722000d5103480b0382003d502c443c1392901410360315078005250201040c0120348800342c00c040807501c181d0000e94002180749241c04810204401d81c03446404d0740c0d442d01041c64000b0f080c00400316800da0203210b640840100019900320700041444171883c002e13003180d4a03104e40d1401d400d014240c0c0e2100d600c1119501b9034140441441c0c540003041c041610365118003181070605598a11800702540b6040d000110710004580c129542d40340020140d0300180d070f00119540f841e058016002d041e01512124280c0c101003800d12203034032080309940440d041145c0311011410030754803031b600310312520400030590342c1000d0000c289001d194006030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 478036447 1250 478035197 478035199
    0x106050706051b07031b0b15041b0813111c05061006020c090717040521161205040b0a0905010f031e0b210a020f010503150d15021206 59
    0x4001561101000f088499035811103000b011020301c03140f804030388200d500c0141156011101d10111905403181c6c01130301000c030f425900c04070003032102c00d806041900551001000005051088095a02018060761001070541e05a040c00c2d004001c03c1c4201080000c60014001d0581c02c08001c0c103445512480311101d03401c3d10684070711004514007070381e100520b408a80c0c15602401090345100c0c200041202c0103400b82041040030300e20721207041101e010007801a071003500102074101d03250046170300c124512000b01044220500c5107140d0340805105001c1c40303a600030041c001c2c1501c07224080c0d845000e641c2103002260310100303800c2140c03074115200409484090f00c8652203103151480c01c40540d00036034540400300e1850118840c00200c50f030003203d840c41c0001c1c0728011460381c09400039807041442c6250022030703000601e00e07415414503101c01d0340340640030b10340035285147c081015494100080850342c02504e18240410500440090322102e0000c4240300355a114810802001481d9040d9216 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 478037697 1250 478036447 478036451
    0x804030207034808150a021e030a1b0e091801020c1504111507062c071d01030b010608070201090803070f020d0203131e050301020a09031b060e040e0708060106050706 73
    0x12134001e00004084103541c81d1034201e4803855403403040702c030080c1d001081210800303c00301404001c45c0401c500035511540101400007202e01103112018403c282070300740c0070180410101c05010b5a120236861315880480e0803012440310000c0351005009129034421100c5500880b104510300d040e240c007116002d24082c3e5240d4034003854100c10000414041d6030003460140c820003106001401b20f03008030350940a40c0400c246c841c131001001e501525032152130080c881d04405000e1180d55070070012458681810701e600b0941c1d60540d65003003004030042c042c881c1030110f9940090440c0c4d1003504034410b1182d001c10666120304140c0c070080c0080680c660188050301480c59810101ca01c000203549038013016071042c20307400345085042418140c15060b01080d201020401091545003400181003144507551070858051860a0920a50030b080901c00b01c0c0c910541c0c0c0070000d09038000010101076000315400202039a0040f11f07240340850b10f500c81c80c0240100400020040e030014003030720525000d6642 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 478038947 1250 478037697 478037699
    0x308090c0102030f03240a1d094e03041a070206061011240c090d0b0703090501090501060816030f0b040f060f0204031208040302070348 60
    0x10380c0c503801202c0b890402280c06200003400c54046e01840b6000122041e0600700f006044001b2821f07079421901b001002c0b2a00c0b0014a81c1e003002680b18581c070840d40301c050304c04a599466405501507580ea541c1c20b1800000a11030329a14948400580c10080702d110780192064a800007603c036001250140c54560034000b5603000c1c200001c0d286c030700c100e6543e4050401556010b0070001482a0710b0613040c01c00c15211524100710303404103c02c99000c46184c1300b60104610310700703c149117010000d10300d40c5800000e00c00e8031a1619888090100103a00000b440d001d81d40b40c00381200105a6044081c1041d802c0000500c01d110065100105650b108802d42c2d24104500c1c04002601c40944001842c0200100410700030406007220250054070034840e11086951a84504058400010768100d2042d80081e0800806c50b83c1c20f514406900030b410407000c90301d09900c0c00707912034030213100c05030816000c3d900c0c503c0381402c01d440588941c06940c880c2d540907007002d0308100420b00f03c0303100c8481d66411054 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 478040197 1250 478038947 478038949
    0x70309050a08060403080a020309070e04050303060405010501090614090f0d11011d0a121703010e101a0d0f0e0d030902150f030109090602070b0c0a0f0305060a0b1806070308090c 78
    0xa0f8040c80789425456901c0b441d100c1c0820301c80298002002000e050080841c08104501450701c080e019500410042d07449091690800040b82c80603800a4107001c1d003103004110395a004000034035400d1040c0a191386418003c0003041d50400c1e8107180710381c01829000e20300100140c00d20721031a2220300b07a03249420703200001d40e11890000c8802d1100d610800250040002070382e1501d05180c07051082c1005801940c45d40b9889040340c1003070b0080402c00c11160204456915050715000091a00310018204414001c03841340c0b851241e000302188184d141c044848d0040d416421145401d80300000300c8403d90040e450050080c00b004900300c0c4200d0050040c22241c181990039500c40542c02c0214034a540d103400120b000401d45010708847d00b903002d1150710045824071401900c1264120070056890791351440c01011085406422402d1525050034040740b03440300c1c4480025078012040082d541c400d90141401ca820741100029885203001448004140c2d000582901400c090000c960344407450320 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 478041447 1250 478040197 478040203
    0xd020c0103150e060d0c080d02060705070201050304300512182d010501060302030126120901211d070b03060607060b0409061a040b030c15040b070309050a08 69
    0x180382e02c200700c00000c2c070a100041c540e000c8107400800090101000b0680d5650b0120100383e25448600190880c075524076007150140f201ca0fa01c4110f40c0340c001c1c509a0954000b031720030f0002410141c005416000700790b484007082c5000d080750201030243c03a8007010319080d000b420340e440702c6800246281c5690110310404107030011720401d41006000b92075104842d1030710303113175840980e089404240280000c41a506030280b0402c0e010388916580543c2d01d6041c00303440400d20504608482002480760711a01603010082040900031039404003490f950303aa0701c1c0040301c84256800c2d00809244040d00e0355800c03841c640e40188000b0702140768030031000010691240c1c64241d144912070025a08000241d05442c1840041011a124041c000749000301f26000c00c040300d4224070216080380d502d80010100130400d0800f0010008116820700c40c4041d500082511002c07000304080c0a01d80d4944101c242d2001481910080c1c41c0003d001d50b203480890400501080e064070801d402500203420200d9540e4002c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 478042697 1250 478041447 478041461
    0xb0405180c011106160c08040602070e060108100311010c0204051005030d050a090b0d06090504050105061903030909180f0f061a01050a180801110d0b0105030f0f1312020d020c0103 79
    0x21070090031a85d9600c01600d44650341004e004010400d809206400080c011409000502503aa0040200c0c504190f081c9160b03600c083e08143c14881001d08101d86100c00307540841c04e49030322005c004e02c6902488010f0311905100b0100960060500c4200070016140c841210101d132400c404032001800300c41c0090303420b44144501d400000b4001d8406009207450740300180f01d02d9185c0c6038002001c540d68040c0d4030440e2010354046440740d4680c1d09000c200e00c0c210188941c0d03c070b25001950000783c515034010304210114401c0c02c0d03190752224100c1403801540b00381006415085451040c40080ca858a996203540b0114204c411916000c00b550201401c00034104031440706844e200c0c039000e030207181520201d1960605d0520001100004140c2c10710070300130607840515480145880b00e11115207841910316840e5400e04010b002e10800500d0340070940390343d802c00e078038907880841c68072440b240010203551100060156941d4040302084039500040c4a25240c80700e80c03d44c0da03100c45140044040e074800d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 478043947 1250 478042697 478042727
    0xa030b0a1b0516020a030c030302061b0a0e01080408090607080301030312050f07121d0307020a0503010c0912060902101205070206150103270c0815010e010306020d0b0405180c01 78
    0x2c02e100326451590240f42e902d10440c001804031000503600e41d140000e210345608100c4c016003040c000d01440c0e40303103021243c10034022074150505151006c03d0092400190b020800d04000303019000c6828001104100e4a40c080d003d440166103402c24180b084142d0320a100031000524101120090066203104160040d001c03019441d010381c85104c000c403604842c45c01850020b43d40d45205c050421000b155250300240800c01a64071120b050040180600265200500a905020070181100d034098000c00540701242c06242040005080410007406a000000d401c4401503119103030f400d03004030705c42842103900700c0180244c0d5141306049860300d03405c0e1400801c1200200441400758000e0300700750403040c00440f600071000081000d0317007c5070701180415505095030060030b101094083c0440700300004824020314840d490b14440041c4403805110141c0545c2d804543e856006025401c007841c4508014414001e900b040302d241c1d080580c442c82407884520416904001c29402040d0300f00c850f100e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 478045197 1250 478043947 478043957
    0x3020301180b0f0406081b0603040b07052107120506040c0207060503070c061b02071d01121403030f100510120b1f08012102030307020d050c0a030b0a1b 67
    0x862a00000686400d00c24154440c149200c03c401d962942e2062400401201d03000381141d00c1d2030159400030003201b01c003e50040740200100000326544030541c03030700600c0c10700e8101d95803e05409444200c3c2e090809100105180f04240001d0980c4024450005800540104419280c03003007004226031120305580701503040080100021400ba0003c1c589c0300d0040e040402200c121903680008646c0003a007448400c410803003110544907810000ca0b0301801504480d0340c0e460a154000d105030410500c5000780b0346200141030010861303010349040e54000c0510031292a814010042503001c841110800f070080102c090000711868400c140c0280c004880d107800d1030b43c1c110503004201410f8001074458104e400c5800e41d0021000c034824030422001a555105a95418051a2603000200400013202417040c1890f0300d015070741c0030085400d40c650403105a1618007070381ca841c2d424400901c1400d40d000840f40c00000074080b01c0c400e0035104d01185002000100f420480010403191a03210000000b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 478046447 1250 478045197 478045229
    0xd081305011d190b2803020405030a1101050432030c0a06030e010608070b0d0c090312030905010f0e0307031710030807050f0a0c06031b080c2a030403050d03020301 72
    0x3040c0807805144807a074402c3c4043d00300c0e80302e4107140c4041e0301ca03020340120118a0400c004050581c00c50380301d240c5003180380a5141c540340000080c0d442d20020000340003503004841e198000e03030145c4103c1d03000300700132500c0d200c00e080d0b0140404d1110760382e01d8500303020848070405c6404070701e80030680c48104a0b000f40b01039000c5007001c5040303000b8004080000c1440d940c445c40810358400030000c183c002d00008804990b9214192014420b85012008200a110a0140900000b0502010018107240525000034403501c1410030a014107884015082d4491034840c10302c00049002c0001c02c03111b40030b5242d15446007041d051060440000300c800c54486a0968401c2c8001141c860040500900507030807140c1c0e8600c0942041c0c1130616804080710a6100c4803030401155416004524408a156242661401c03072018007034070504006150840480703000441540c0c1840f1411864520061007c4000f0751400b4010a542d4980c49400140c80c1031040e4a03862500b80c1c03290013103d041c1c1c0c4603803860030111 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 478047697 1250 478046447 478046449
    0x60f050d0902060d05041b0303090306020d14011503110c03043b0402040605040b030c090a0603170d05180703061e0e0607030513020603060d110d081305011d 69
    0x580000848400894071508503401681d9040040c0c256588018000034040c10145001883ca0040c0e01d81a001c3c412024010000310740c2011441d42180c0e0043c8025030788081d808041401040041030388080d900c0c1030303400405c40c803030400304800c40b00c80152410800200d400700481e40501580c00740c0c24459000304401c2c8a103c801c07a01101e0b1801c0301001d00742220000c250304000c0030340e144075003141c90000c600420095140070700602009110640707041003444460030202c0c1d10303201c010f0315541c05101f5550100d10603d18641c0044021500142c2d440030700c039686052034060350301ca003059441d81030a250200c0e001c0b04240504d00e00b4014010002c0c01e10a15503a259005828203d0000c01860381003258140b60301c1003030083c038041c440e840c0c2c003810340d034502840c014040b01c0020b0207010074900b0b150b50340d0300140c0740c2902700c1e50002004c803032610512503140b402c180e5400e8a50000d58024559280700340c10020100054041940d0041d040a0f07150340701c40c0111103170420200c200140780f15102c408002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 478048947 1250 478047697 478047707
    0x30807050a12032304050a030c0813270501050102030418020f0d0e07140f09060a08010c0807170412030b040f021803060a020705070b0f1303060b01021501060f 70
    0x2018414400c1d902084210707141e0402149545144a011036110140c40d071442c90034402c9007000690321034410030349050546a60780d5858038108000c082c007a001c0b850000380a1064290780c240d104030007681490075118100328030400d070003007800c140042e4903001c194183d1001c0e0140c0d074141d407810f900542c140f03480c060070007c0786880f90403012080c84d42003101c800e003020560000c0c10508402c907004201456800184c0d803610f00c071a4040c102e4414002030708420b136500c0300e461b120f1052088441040c2526004001103205d00320340e12100c9550300e000610f0888680080629200d0034098882d152030b040c1141d00c40f43c10038002c50b40140b1030541078900c003803a40e0103640300f1008204090800107204001000b83c004a038086011030410580305540344050f89030801ca80c5038410310304202581400086e665265031501c00c2e00513000714260102c4c2c40600320101405980009004071030300c10507280c3d40e00b443c174010412a00070a005000e4019030680f4000000e0b41c5504071000f99890104070740c1400c1003224 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 478050197 1250 478048947 478048957
    0x504020a0f140909071709070e0a20030403030905120406050a200a050618010b0f0d03121803120504050c01180f0f050307170a0f030309050102130626010308 69
    0x14900c4061119003c25100c01e00080c5c803a079015281d074164544441078081e00e00c14020480760b825400b1403001e00500702d0340c0a880d5000462a90b0116010300210103281c2060110400c540c28400040100418076038541c01c1000d2480c007402c203440c0200464039446069100300d00401012070420083c08088a1081003008491808020203c00c4040242a9542001c0c00b40b201070303c140d400310040c000c02c03421200c5000c22081e0303028001c02c4040da4000100381584100320100d0301c00c4810420380c0e002d26010380b01d40d42d080c090401d420811502d04c0032041008190408007500081c2c00c02c141445081c06600c1b429028075001001404905110001110030300107004558107626014100080da08010b42d4000c006062801000d08015040c501490315040c0035030b00c03800c1c1d052440f01c000c0107030301000308000310700d1074000c0c000d40381130003003410258041c000d01c0400170310a40c07000504014002c0c0007980310741910796650b692003c07140c5a821020803500704114130424a50000c004000041041c00148 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 478051447 1250 478050197 478050227
    0x4120305030c04080105070e010216030b010e09120d0f05010b030c190e06300f011802040308040b03040c050a050f06071104090c0e0604050c0306011b0510150504020a0f 74
    0x91801c0c4d01c8410341c0d0f00703450040d0380e0140800e0180012000968045c403c6411310f84407001c0c020002da1950700d400001d2101803140600e1864541c0101e003012400b441940070341c0711841c1400340c1d20302004103030200400448200d15911480c10001190710221030040b24000c41c1e40e911003609200ca00ca00080020a10f1100e00060080c81c9004900544825010302021128182d071441856001c4054003114051169106080d020710000c2055100e941c0c07031084d041d10aa00d0284c40040e01844241c0006d1140b5040505082004100041d00824100003980300d18450303580c8174003807952070041c010400d0186c042d50341d000461103121000390901d000035142c0b01e03001d910000140c00380800070904440c0c0a00003603640d1039001805114a4101200e56504508103a07820002441c0c01c11001d8014003014040d5410092041803036002c0103491503104420750341000541c0c4c070b12400111361038000d05d00084610640900b003003001400e46040d2096400240d02a290603040040e140700488844550003c48 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 478052697 1250 478051447 478051471
    0x504060903060e0f01240506190f020f0a060e010b01021605060901120e0303161403010501080c0d140a1d0c010528020c01120507091a120901150501050412030503 71
    0x2c05a1003801d000c0c6c20052036002c50707a16043d08009034440300c1d40105401c640e014900c10000c42840f040640030203441c9500078a01400030b01d009001c200c1c1004d91460240300c03280700d51041c000a12030154894001c0d40c281da002000390b07585907001a0784034400480e45180138000101c003000a0f042c0340e0020207842c1c07130500d4130700d030810369040c2440c0c2101e4100414948507400481040441d90810301303910a10b080341d041007091660000c0002c04240f0050003618100605803020460b01140042078511110760b0b032100b03028040a44419110600b803c032412100c10341404c08015150468810800c1c0d10b400030000341c00211150303c0156003540c03080d003a050b03102c04141c44405d01541c1c86c00301100c0c248110f90107042c01c0c03114640018192441c00340c40720701541ca01424481040c0e001079030728013250102c00004d005c00a0900d0030300c070103002740c40898140200b00700800c4481c1c14117602c50840e40380b20f0389040c0b224a441d0801112640030714040c1031214181031074501c001c81c1c09038014692015014041c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 478053947 1250 478052697 478052713
    0x90d0c060f0f0e07060906140d150302040e0a020102070501090b19020c060d1a18070e0316060816030509100e0102040308040b0d0608160512010b030d1e0504060903060e 74
    0xb07200d080324400c0c09100c1c0150045001803100e00c2d404440400141340501c0c120440070510701003204d2600c10b100c400c840482c0d990401c0d01520a403048854000c640050040041c03600b40b00c4100c0e01c40401003401c0f40140a50b11000c1078540c0a00c0a4006445004001c01e00b8142030609003403040456219150940c07141d4000c103071860341c44800074a01c910140c4004111b0014a080b90711101403800720b1144220982c2001700b59410001003200d510945924001c2c000ca2403810100c1d003424040c6a60301150601800c0129a00d07801c020b05a002d00401c0d02a2810b40d5604541101280c005494000594114890441c2c1400f03c2d80c005040c80680c2500040c50320344c0d40c2e40d40c038510b640580c0c0440710074000410031007092003a0780301d0200100300038400f512000b08241c0c0c001c080501c05008040c07203072405c0409182c1480d400d5011800880300a03080f1040c1d0074940b1009080110091410807170410640b0342020b90620803000c0d10111003080e184c2c1b201850440c1e95030005065203404141a6110340300b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 478055197 1250 478053947 478053971
    0xf0c0409170f04030b0c0313080310030b012705040b0f1503060f07020c0f0102030319020904060f15020a03090501050d0f05071e141812071d090d0c060f 67
    0x100800c031502c00d00084594031480e510306034841070b900030310b0708101003c03e004000200300c400800c562450b9010300c030307a50740340c3e100b4400e404111120340020345a6403140e000402c0c94642210b0708032200588500c41014010140c0915064038021500144842c9002c004a20b0350181d6201b0a130704403441c01c22100500b9400d03004a4584078080381ea1100d00c580910500803165010702118802010a45000d64044003160010b95a840007909024048038600f0148680120aa040d222007540c010000d101b100d03512090301d12503615600800c04070000134040789108600004615075501d41c10740b0303030b0b4541918150064403590080c140784408252548822800007039144182c03072240c1e20b5031f180e4440000c140045200400c8104044800340f0400d542e076017006512171000c1e101080d041d2030356440f90440130000304806286c8000060014812070002148403020407010078451120380503003c0f825901c1d0110306c0d83da00c80350742d902000f19404105d00f1001c2100d0b03401c45640c0551001009c6100c0d00044c3c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 478056447 1250 478055197 478055243
    0x1303060227130c091a0a030605010f1d011115010617040b06010c02040e100c0e010201140f0603070314010504022b0b0c090d08090907052b1104060e0a06020f0c0409 72
    0x83d45c0f80302e2201c001070f100607259018480c0c003002d00020300c0c0c07000084c90b4009016011580c403c400c1042160300300e40e1024107038881c00c070034030481c54020180c5100304100051312400e10000c2c000c06001c6000d00c00718007203a140e0310041500c2150090010b42460303d40e040151200d592045069030003940b56800041a910200030204103120341407800035200309501c0e80202a071040400b041d04690504464000003180c0010298021040a078034020720344500001915120940c1d000905450070b43e41000000390040d444144224026200b000380c0c0c0c11080c01800c2074096202c95003c460941c00441c9001c07810a01303030281d0111003904800d11700010318000540d84c06c0461000c40e05c45c00300003a01d50083c2454800e141d000307005402d00700d0a1440405d80308103180705c1342040544820040a00c40007036030b80e0790400c0382d0f02001d0800b4640d64a03225000244030b55054005035001b61402c4800041080c80000c0e080c400c4140d05001e403110b2100441044090b014108042d542800640d80c035030f580000b01d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 478057553 1106 478056447 478056479
    0xa0b1005090418060c02030c01050105040c05161a0c09040e01052205070b0a26010807170304030804060f0215130807081303060227130c09 61
    0x400b100f8400c014490015210740d0804140091258000c0300a0610b14800d000034029030f1f888109100c1501c0610440301300058041103071811205500000d03104041c070598242c000c040703000450301d40510f415162107da545000400a40c5450f240c819145a400301000030720503840c11700d80c0d03040031844940143ca000d090488a107401c00900b03002d070401501381c885a19844042c440002080c4010040320019603003070110410851290174540e0078100e803070790030003400c1050a08103c41401d801c111802249440300f40408000500b06102810190000b907552150403001c04074001d2030681c15072500388100c000402404000c4200b400d0071000160001d11841d555400751800c1000c1c0e11032000038a039100325203100070080107117a0b0020945156650140361009000d004100c00a056480085511030000110020031a5407a00032002c40b81140c00c0400f502070795905400401c00305 = true := by decide +kernel

theorem cover : BRFrame.Cov 477877697 478057553 := by
  have h0 := BRFrame.cov_init 477877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 477877697 ≤ n) (h2 : n < 478057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
