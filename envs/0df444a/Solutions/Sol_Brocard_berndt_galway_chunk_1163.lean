-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1163
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:32:12.154174+00:00
-- url     : https://prove2.me/submissions/59fef0fa-ba7d-4e3b-9e9e-2ddd4b5eb0b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 208992805 ≤ n < 209172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 208994055 1250 208992805 208992811
    0xc0124060903020906040203070c080712180e040f05011b2a0c060e0f090a0f200706110c0307031106070503010f090209030c03031b07050906011707090306110702030c0108 75
    0x507013002e5550301c034081400080d42c001044003044c42030744888040007428070b0004141040c05038007241007000c1c03404d1009000050106111600d005ca2580500c061030071005910742260b4010b07101c7d41100030903d089030150101072004d2164a200301a45490300b9000102907070f03e0700140c4c01d542e00d401d2820340143c14640542030044c00340a4588414080ca900869101c03600343c4000300303091010f52aa03400110a804111900c10b0090b0321014085207292a07401041da500c0e009112000c0c00c40c1442000c3d0b104c500819102400d0142c035801c4c89820b6030843e130300301c40100ca2032200340d903900d5400b401c020f0018a51036842030850701c121000610694030540a51381641e0090004617003ca207001c0780c550180d008400270551601446050081ea03540030001088808010b00c2d4001c0094000c0300140e0404105a00c11070003120729104004c13841c2ea100c4030381e0785001c00c104000710164680306011a4014241c0c1c10080086144c030b08038a049a01e0344020b01041d5100300c0c120740242c100d81004550000043d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 208995305 1250 208994055 208994059
    0x8131404060e18010f0c03020a0e0a03170a05040503060403080f1b09060a11100510091a100c14030706110c0c0402030a0212010b0304030207080a12080c0c012406090302 74
    0x4000410584080210f03031015402c0b1007000850056041d5001408440c0c804c2c001d140440d90000e19003020542045070044510000c6928004251035a04c809410300310785031600003020000681034020b1030144060360041c00001c1c045401e18601498040c101801c10742d452907260020070300040101d032001002041c100303020450b9500b41f03d81134092003900c3c1c1001c100c0320288400d8040540740100d0400400c940d480004501154a0618050000e01c100c06600030300f08050410300c080120340341a8500c042075403010340d1112202c0310615401c94585030403900007000d04401d0810304002c040c1c00800f9003a442d004450410504a44014400f094800c1a01c40781094009409103051441c1c142c1c055680320f20402c2c005807900d241e0003042c0c3d0010800360404215800040140300915604003c81d50180c0411070003001524100d85601c400d00f00c5441c1c005040001220000e20b83d4200c81058031b003400810b00c000c0c1f000c114840410111108108851392141003483c00029400b48511550411a500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 208996555 1250 208995305 208995329
    0x101107030e01080a060308030708010302010327020909070b0a0f0e092a0c0102040902040f091e1802150304030311040f0e09030c0706020703030f08010b1204050a0813140406 76
    0x7000015200076200910300030f40f6681d030745030000101d00d080004500c264080e40c0c0b513044940c150720014007152160b2241c03182d480706164541c0700d903c0d4113440000c401901100d80c603269a0740d24001c1850311543c1e42000b0203c110204050201076080340200c4071080d02c079241c0d190350f91604801d100e85a076040340c03e0743d1582442211034881c440e0700e4510300600c0075100456840c042d400790115003664001d6204203211540050100b140003429000e83c07003c0d001440342801084022620384a0034030003840640c004598820741008110600e038209001c040d0301600b01c1200000b00c0c899500b0681088030143c0100341801d171685d4842820104460640307100c00c4400241c141481c0103980c5c410300007029062248010000c078403a84604015500040490341c1c000c00c401811440c1c0205121050281c040c140040440107004001c8a4425100300c42011003403818190790b2400c12a140190380080a032040342d0005808802c0b0394811610815034204060300b241e69408403052100310752a80c4a481d4007000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 208997805 1250 208996555 208996577
    0x42d080a0c0e0a0b090106021e121b030909130204140603280c0e0108070902090a0303110a02040509010f0e06150405040317070201020438031806010810110703 70
    0x650308451030740003031007070f000010b54200c51004102440b41c01e0b00030b8005a440446494440b01400018a03007410b5060301600c0704001801d0141043d005207041040e404c210f4248508096108105841003514014600207042c1442551110140c0380c102c000d87c042c40c200a003040e011400d0448090050034040c4c0200500311440580f0b120a603204d00321841482c1140c034001c8003280e0301c0342c00ea0000c1d0841542d850b0595261060350f52038800d03180d03c44600c145c01445207605550311904030001f100d030035003440042d0361814030a040c208000c4000003984545004244645101e0540c00800300ca56000410040c00c40810101da640d40402c840050181114400c09001c074140394004d40d42040c41b03030400781c04001381010340c0c1030044400c4a002d0011307980440e08004040044c2211884000010f5400e06030400e1081c000400f50080302a541c05e00b040000480c00c20301803000008412900c01c03090b91000d50b142c030000c54803100880e0424120034200300d100340d00c4401e10b80c04c50300500d9042d03d5980368a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 208999055 1250 208997805 208997819
    0xd12121407080c090307050909010f0b0a031101050f041203030b03061b04090207030905030609030c011104061d01050f0f0c07060306080316020d0b01060c022809090206042d080a0c 79
    0x84e010500e11605401000f030005015100d0031040ca02483c0d4880000c038a10144c100c3c05001c68460381c52007885074106017020400f144994641e540e4242d02032a11550f40c8001c18596907543c0318581c0a01c080c00031100c844818554942d100581d500400c1f403c1d51180e0700c1e0096440b240080c80403400e110340508000811114101c2e40c010300c3c1700340c03182c1050100b0075036420002742405000c84910495070400210264801c4003071107003003503141c90000b00600b02420b118004220f140c00d00340c09070050034a0801417006a0181041e01e41007583c4481c03190359035562000452290b044038a4070b41807071042180100700c4500a01891064945040c011401c02030040e20611641092980c142e8100402032444001f10303200040042c080c1403a81c680ca02550f002e841440380c00c56000c0014005030340c00f028042c020000a000403000c54103518804100042c003400050018403030383d400385002c0e05582e46680880c007600720b44021114070b00c81038000300075510409070382c44450f0300000500c045490b84041c8150 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 209000305 1250 208999055 208999057
    0xc031815030209030f03040f080606030a0803060d0c030c0b0c011b0203070b04060f14070e0117061011011a0102100b1f03020903120301090e03070c0302010c020d12121407080c 77
    0xc0c0c0002030845e45891508116141036a005401c00c1e061400440000d0200c840c04001d4a41c20581c15001030036030103e03d0b1180c0d001e82c0000742c55103100301c0000c858a070500139001c19484c041c54006444502c05035840f04410302e1680185200b10b8030707500346005203402c41c04952980080c0e40c01a005140740c00c02543d1440c0d00a10010012a245a618034a071a180f215074401c252022010304007400c0d4a041c003080180c0840714000f0110304010206000c1c0c104d1900d6920613079008007081e02c01e81c41c1310900031400c2c0d4020660300c607400d125602c1d09404007501d40d260585540d88002c203800f40c9110140500304802601d09a80015800c00c415009a100c80c0000015034803050201d4507005040a040b500000d040407070704c440644130500040010700c4104070f030f4803514824020702d5004505d0401159500c40d508035a034030010b070600c928030200000703540b2140f000014255024003a03e84000c1810400f070003e08030700d402d100c041807030f10340c0c0c03490361901594040f030058040341c88003151940c88120320011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 209001555 1250 209000305 209000317
    0x706050403170a0b011202130b0310030206030c0426120a091d010906090905122a0a3822050c040b09040c0e06031504030c0318150302 59
    0x400410049501c580022200c0c02d03402080c42a40116070720111000042c2411049002c0c9034906104102445410741b249140004540e200c1d00c909890b9616030104244000042e072000c0d4000b10300008204810740c80030002c0041d035400800300480b800c1c2d40c41c0207102001c20448200c440fa070003516001c802c1060b280141220041d240781000255844012201c05c100d5205103000707003640014014401c00010340151005040314040400040d0f1681c0c40e0796650303540400c4206541071000580d2580c80b80d44441824140d520103c0881c41344000740c45082d501c0d0a4901c1c1520040260119070b20b016888080e0342c082e21130880301d0b40403211718000b1160420383d4003800740640102040b5030046410200140c8500c002c0c040d0000e0000c03400e500e03040c0015582030300145c603c111314210401001642d81203d03081aa120440c41c1c19541e40c0d28800729151480b203000e000e8105107880108020943e001c60104400f62195031520f2800705050000d0414907210300640b210030b403004820b110701c40e10a60107006 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 209002805 1250 209001555 209001557
    0x503040609021908060f090d0c080702060702280b0f03040605060111160806010f081f020c151f05010816090e0901050603160308070305030a0f0e0c0f12030706050403 73
    0x9465071444645201d14051307a001080582150301080a682c1c50403a50700d9000c559100a8184c18082a2000b0002c0d1012880107004800202e01d6400b5511800140c1d260650301400e242c00031564054031a5401e1019260100c03a4440c4107004a4100c0300082520036660000e11558203648542d138940e80589001424541040041141c0c4141b450301013000c0d070456200708220029690500c26a241410f00c142c000503040c541e00c0000304140d580002e24160820350001e140c03030300c0104e0050a070780644540a00180e284c0302c1c1c42c0129500800031940789004502006080881c0b480f1480100d1400145225050100701c010001804600d9117180d0201c0b149000e14018420a0b219480b003d01c610050324204202ea55580c00c101481c01e0804c400e40070400c0f0b124411070350a15683d20002e052041c140000d080100100100703c2070460b640145402e02c1c503c200c00d1082c202045c0c40941d0720303080b0020300c601c54154040b41107100c0c2004104100f000700d00070042c1d480c06e042501d40030007074000948224 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 209004055 1250 209002805 209002819
    0x2060306061c0c03060b0310060e120a031205010504090c06030b010512041101110a08180105090d0303050609060609011e180308120c03060619121802130c050304060902 74
    0x42c04004001030024040011104001100844484002c0071950150416520360b1400c0041c0a40020400000300c00c60b00c81c1d04d23115003200440400300320f522000f038030704200d103115039105402003542060908020083d904c5081000342c1e6202c04100aa80030318502600c03400c085941805000d01c65081400400b106040c030919103221101c111440c081c007201c00744c99140500c40344418540c2d05c807050f800c00010000060035440941e44502a1a1003816640102181007510500d07090b4000d00549080c0c02c1c00821070780404940d0700703024001c0e0808842d030718400d10000380098010728240c0309881200304180d4555038462a41d50b807110b1907854020004007801807a45040c0e034192054088540518483c040c0c554075684141d114600c00c1501900c48000b040080c07042009544603081038900e1804036141d0002c1000b1038a41c1542c100000d1b00034210b009051101d2095804100d001d22482c0520075600d40f60030011150261048543c84800f01c0300040c4100003041c08107405801c544c80c0c440c0014180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 209005305 1250 209004055 209004067
    0xf032901113c06090303010e1306060602010c031b02030904020721021b010201060312080406060902040920090a1a0c03160501050a060e06040c1e030e0d0216030206030606 75
    0x104281040a03004002e2002071000402d0b0031020740c00c24260000d425800400c42414044500da40700d0105000300306505446000080000440100015545400140801c199030b103681d8001d000c4c8c80c280b03120380c0210b418603100c508581e01030305800c004042c240d40903600f401100350170403010b544181010b0b00c0d810250401100040c1220b510900c1e085519001008049006245074004001400e1440d065915001040003c40c0c449092003003001068a01081c50350303035074a4440028040c580001076414030108012504103442d03800042c41e021000d03c03112000e020941102818401c021210750441c0c0120002c01050b2035000c4081200c2c050226000d0030490060f00b428034540044090300e08090910001c041449400e201c0d40f03800c582d4040b000c2c020b847c00c0501d07070b40003140041c150500590750764110440d0b1501c81d000b9450050345002003c01884100c510050203000c182912186600400b019144254000603100c18240307515840c88203000d00c0c640803c03540e80c0005080c150010010020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 209006555 1250 209005305 209005333
    0xc250303170709181512050610030819110105010312020f0304140d0510050a29010c24050405060106080f010e040305090f0301020d0f0f06030807020f01030b0904030f03290111 77
    0xa030030080c0249180d80b08031a106810081d1400902a00d0317a070510a6682c012b03c042a021000c9038200003004118400c100303000842292400300d48803d440c010351800d00048208500800b2840007401c242d03003100d03000350107494096200d200720300c00d0f81c0c483c00302c60b24001000d0030584c5845001a00a001391004a503110b50400d05943c01114003c0806985044103801c003518410304080c100d4458064203030358038202001800070644000c014150141e030b003640a8401c04144c3d07080c41485000c4805020300d08080c5082559014280a2140400e2200000841c8034004c0c1a1050480b02c5284815081b40c4a90300d09840c00d601c01d9043c1904441080074560403900d09000800015140d0000001d10140c0d92440354200d802c0c0e001c454485c0340c2005c1c0d042000c24282000d88895a80469940b0040b028810050b4001c0c8580c400d040d40000d407003002c00051541003c1010443c0c252500c2c14010680c020b2048a000e170240031210180d032405010418840d482410f03104074014000e02107500044007402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 209007805 1250 209006555 209006591
    0x303030c0c01180809090406060b070309091a1e0301150806150103021306080a0b15030a05150619091e0609080604020d02060c25030317070918 63
    0x81020003480001040c8540d00000d1041105070800204581620002e655900100f40b050300603251107910000046001d000e0b8552100f4018000c2910050740e642d0785207005800e8008500c03400744220314050400c803255855400038280103030010305207600c00d4960f207098040001d2038862181c0565036404000c000c400308003107000103800c03000300601541c038280c00c1c203d03031409041c00b41904050044c04003031440007114032603070142c0b107581c10186250b56508002c10300034010b00c0540b40d402040c40180b1402540300301c0041d405408446800e00841d612440c180406201c44203655400403810055040d000600680d9a0b850303000c030380383c0009503070703566080c5100c0003500340040c03141400c07200001c100b144e400c034540700000e00290021700401c0c9480d400203082e507218124068000d050000305805091001d00940300350800c0b1500e816200a2103510b0000054001e000840c04070b0411240e504051540c0c45480388240c0855884400150030140800a2890140d406101564450b0429800f80798045 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 209009055 1250 209007805 209007811
    0x60318010507090e130b0c0d0f020a0309150204031707030507020907090f090605100302130320090a18110d050708010f150b070210091e15020d0c060504050705030303 73
    0xf0365040049401d01c1503006903c0009010001c071030100c41034480001d262019030b1075110741c180c2e001c0c0d5202c42d040014100940740b03461070107001c244000350300c0207029055804000c0d014010200c240705007401031802802ca12481c00094411203402e4160a03410f00210f00800d0494424a0b00c0f50914009502069400358180c8040700800c041e00d00500c001240203207110002c0900d200284840c43c9814081080843c228940030101030700050b1031000a903650100c50011640b00e401e82c100c0980540d0707141b203d2600e50070304d03034441c12804000c104031420b5801400604c2c0900004a074006c40141d0b9900c0d0406404204da54000c40300150711008503605000400c000c0c81040000724103108600f80380320856039904017003007902242d0002403004164004c1540c403903d906175240c91200d810000b060720310000c50361010300c01e03504400040c0101400c2c040c3d800d0454a1a41170140c0b8901c45800c00d9071114404030307110002550760714081c804511550403468000d406981034960444e15000441c0c110340c811 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 209010305 1250 209009055 209009057
    0x90302063603060c04030308010b131a091f080a15090f05090f010903080f040501180f050f0706120b04020f12040c0e06010f0807090b0409060e060904050705060318010507 75
    0x9401d107810282014401680d02500385403580d8a05030665038003600c104410b019101800c140803400c50b035a46e035105103c03c00352103804042e585100a03050003002550220208500800720400d05000b603001c2010195443e444540b10b840c1180d5480300f100b002024041510480500306800c00140c0b1106445400105001d000000c28117107021600c2d1481c00d0824242c51645030f1400714100c000c282c0c06140240c21040a8140903010b49640c00c10314050304900d5201540742ea203c09560003045020003401038513138401c000781c1d981ca14201403615182c840510504c800f2174032900d440358068005500240f82d07218004d00060510000341d94000580d0400e07809047c0d83d400b108180000d2090a4102900502d04071103031307138154a48000000d2409020446503020721090102003000a401141c980010b49400c03604652169520541ca1028160611520100182c5000814107500305240041e21954029000b000b0462502080c48580d500042012001d030002000c0c440c0580420300a25003d4005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 209011555 1250 209010305 209010397
    0x50a0305010e010e010302090a09120908061503070b07020307150e18010503030703031a13061403161401050d020d0c080106050c0703031416150c0f09030206 69
    0x1100005000c442042e0041c400d22452100104200781c003d880e024103581d0f040e80c026502e43c81d400d42280c05081410001406a9030a001c1c45013034651090750042107a041c41d045603210348542c0514102e5003040460f15815801050b41400074120401c014140ca9201a0031158a40d58407020040c10210603131405000440c2440f0034520740c40c10b03040800450749003044c161410b5160038002980ca2060b03c5004060586800c1000e940107068840b0006003080601010746111403190b40800524044c000d500d101d01d4420074001aa00740010101c1059801e41341d05c60f0351a08028004420b07403251118941002000c2012101b00c9626001804c02d00c1ca40314404654810f0b00140035010840503002581001401e00c50000302e2040000c103c42201c0d01402e1404924401c0341341d0760b002c0d110308848540180107240c209820841d25039441c16828040325010848080d05c03440480f040105031500c80f00044051105201524040c0010700f40040c441501c810348501c10b919510106100705843d03014008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 209012805 1250 209011555 209011567
    0x22d151902160507060504080309011404050306070305160201111b0723011202070f0215091809011a0603010603050a0906060303320703030b040b03011401030c240302130902040605 79
    0x1030700304107410140c50282080f47c181801c0c820038590b64001d220311030f0304201c3c801c5510018280800c0413140508400380540304185858100500541400d031480e520103824003e05010003841841100c01c9048041c0740c040c604076030003005107076040112001c8007460151480016005c011884251802c2800120415644000000151204030107071120341c80c02d4010000440060b0004090402050307044030050b900c4c0c0702101000c0145c2c0a851051900816085582c002c1c41081160b003921941c100300090065282641409013000908007000c2e80015013031005124480c044d0300920f80c08251400c1c0000c0080340c2e80c540200340c59013a8402c1d00410514003c00a01c240c1c074143d08100381010392110000c1242d0820503e03902c5c4114140039040561718101d07100c0c10b5172950000012014010020f0024141d00d200c04603c8141c2880101e903100418140022a100e03071301c210281a078000340c440d0744004c6010b14107401a42c080c6411712a44400160007250020583c070140018003425611651185 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 209014055 1250 209012805 209012813
    0x50d0201050f071e0c1b080f0c0906011119080406030b010c0c0621110322050d080405030717030a0605030c090a2307022d15190216 58
    0x7840207000c0c015800944070801c00010340050180107658210404940d10302c40b030030001c80780c0e561890002019020030f00f0344504101442d0600005482030b0500390341040b94040c800c41c0e51500500e40068000140b4400582c00303600171000c1010a542201c00d448407000c41d0000048000b480740001c4503c04800300e003c4c0f24466051064203d600c000f0308240390000f8407a210301c849070341688203800402180704001615220408000e40083c104c528060201c00496510b6030400c1d0811115540741d08400401440d00134200b0420254603504000036041e8965044002c45403944c0081090f295440204818000585120503004200c240e40010545900700a590f207829608981d014510a80c800110700e40070b0b40d60000d03425003104c10001c0001e0801d03081021208603460410001c44151240c0741086074040d00402c2035000e02091f1241641707680000300148020400c03480b107610300d42c2e015480030300c2c83c50354881032150402c2c4240d0420bc0e03c50a010000d0050380d00c201c0d00342400c5240404420100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 209015305 1250 209014055 209014061
    0xc09031204090f0e19060c05040e010f0e070503010b0301032607050f070b0906030a0b0a120c06021002030c07060903050c030d0b090a110f03041a01091406040605031009110d050d0201 80
    0xb10081001428001d05d0312119001400c05c0a140a001e80d5075660081c0d140750300030000c50740140203041e02c408484d03950312450070303141001c0c0c4035400f851590200090a042c1c1f040088070705070350950044038203617400d5840310720006080e0050040d40b600d0b24904118209900fa010b4001640300324010001c4c2e2100d07044030b604040141e0b2180d180c4020500120011f130b9540410740c0c0d40030b80008000900c5170b083ea0001614000c0c2d13a84000024584034030700e0000d1140160013102074810640840d0385141d0b51803040404c078441160800c6100300140402800980142c0044203034074004e18106050031140ca08060840d4025034110003e603a580c00c070500c460401002031680001e00e4071040100c010000321011942c451200f01c140da4601c000005400c01050801d1034105243d000c06d003200725038480040c8402060300441043c1c0c2c00341e12800146103842c0501410040d5540600a41181004c000c884805899195011500c038090805050310079225190085040c50250008001003980b80320f010b821 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 209016555 1250 209015305 209015321
    0x304140c03010b0303070b09160611010507140405061c05092107020325030803040b07020c0f0105041202130e0304050139081b071805010e0c09031204090f 68
    0x282c1d04144140e0540e0740c002c015501450b8001643c4051540e031290194100280700d90b2075003066001d02e1010641aa010040480006403e40200a103490b0400107840246409180c4046004100824805030600e90300ad0b2010003880320816240c60444888041075440407205a44503138854031200e40c44440c407841505039218100c04440c40c004a0360003198582e1084050442c0c0c0303821060030b03012041c400b807072028021030b04240800d44034101450f2030480310409440140051003103010503034040c0f80c170f00e210003c0c011058580b00e21700303071070003100c08030328910840d013641d014441801d00c120b030406a0080c2c0003450f9210008e0b5907610f081034005800510f8201ca03207410711285503080e000395035172040344c0744501084603118450f0b002940f5000c0080c0c801c40c015420f118003066076440361080b00098000903101100d0351800c00d0510500710301c1c200c0714240b1900030034866640c01f2039001801140140300300000038003500c2d43d101c019140c1c101135601c280e205204560342c5560300c4484c00b12611448071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 209017805 1250 209016555 209016559
    0xb04052503050c0f090a150201140105060a0801060e010201091502030f0c030408030708041103030703031a011d040b0303041a090f0d0b0718051012050a02190f030f020304140c 77
    0x4010309200341005a213009000c01035040100004014071103a484100082c003c01030800380300c0261040b40d400034080c100c1800480140b10000f4000b0843c3e1420406031903502c8050780c0e600340c090b0700c0c00d00d085030000c11400c0c0c6141555680d007002030100d903511005118005480340c01680e20305256400d1000c10b00300a0607000d40703000500501c00040c0c8100e00301e9400c003816190191850702c5600f04200354800c80141c0580c14070002aa04041540540200145a030341068000c060180d24006440061046000420324400d072aa1244a4581588803008004000d41141d06051300c0d103030030b40d1451a0030f0303404c1c0c010000007007610300f40d0346000d03d46814548420b0716032503007082c00d607501c540c04044040c01071410b00c0a04a40b090510690352242c10003050000e285914402ca130346400741c5502c89008040b1348490a100000e84201c0c0140211000e611044051000401802000700d03500c01c0105400302c101a19800e000074030510600207140118050215001c41e501c1c04507180e8600103004121078 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 209019055 1250 209017805 209017811
    0x11010e01140708040b07050c01030b06131a0f0a051201120f030f14130306150510050d020f0301170d02010c020706140c0604030c0c1d01090e010b04052503 68
    0x10050341d034040701005501004a40c0c180d1200c0d15464500c501e809203402180026801081100501000148c4420299030a882c2004900c540034280a84e43c880d8000d556030049602004000d0080104900807402c0d540b4140c0b241401160f2072111459481078283c680002c80125001262038541d020b01401488200001300b001960f50352003203020403c054025061104030a060b074519409600960442d088160703402c2d9171080c284400302c1410f0058003080c0c2d0801d25002c160b0038081f1148406a043e660000c2c030052016100d07100032612603205010034456503400784a1488400f880c4000f55010305000300c2c01c018441d820403440d41c41c1803ca00319042c1103a0400400703800d01500030030030400351600c500e400407a1f2101e4070b80501c2d15128144080c00188202020002807662022024010620032107012a0007940d4680020b03440050280300c9440800e640c0042181d0742c0316a00641300481420000b0503013581503000641104c4084401c4503500d03201440e04064100000550f41c48440642010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 209020305 1250 209019055 209019077
    0x30708071d13050604150b0c15090c0405040305070f0c1d0f0a020d0605090a060603140403080f060d0b130506010b0406050f07140d03020c48060f071101 67
    0x160052510b605420140d0343c3c44000c41d4503074886400580b4441c10144968180c15911050840c065016200c0c6825074012020001701e00c0e4242c00d0440d000e070300044000e0500340e8031306082200609002e00301f101484402c00c401030000f54448089910300380100101c0c884280340c5020050012000c00c1d280c400c10740c006041000d03010b0744d101c1440e006010303044016220882d074200003006140d141c001e5580400c141c81045000c80f1580c0098040e035840d50340501c1300c0c5005102920b5543c40c2998000e0104040c43d002901305c1c1c0300d2040d80c03544400c00404500311403203581c40392121410b06a58203001403004003501011302008000740340c01070514100d1907150914161000340b03e4010740c100150003c42c0041c00c0742c14002c03a0041c6e1602d0741d11324405d0300e841d01d0280c80c3c0680203500c001c02c0d4241c3c600400040c009040d40440c0d1070f10600d520202c1906070418101d4841c5c3e4064507405072020110ba032806002c00c203071511400340022003c0f05100791b5641c0072034100b20486600c900c2080341001500c2e048 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 209021555 1250 209020305 209020309
    0x50c010909501f12150b0a030807030201050f0105031f0f020c030a11070303080a1e02160203070807080c0d03270504180320030f030708071d 62
    0x10072070000c90b0142525031044104626102c40b0151103600074842150005007581070102e0702090380204032001107120101e0380074440c40f9950245100d01c100d032400b001380341000b00309410300c0c050b1801c24207103001031150306140024884682c290801d40b01581c01180a800f010340910405800c10100c1c03c0d129110340c58000000d03942e01211655440590400c0346403c81140d06800003280104e022030295100c2100202017592604420780301c000043c1c1ca00d201c98069500465034a0a0300c0d0546d0310340e0035954038940000050702e81030740d440c48406904032030b8141c2410f031440176104094101040b58442407150040604c0c0c91256081400075030002d0800b00007402c0c00044070151000e0a48048500d80e0302420250380c188905801088150030b150161410142d400c6024016180202c1d0100500d005408106120b503440d000d004010400040c5030800c051542c080840340040e008007203030f25256007012800c1003900117480442c0842d0180051000083d00b05816a10180c40140ea01c4450840900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 209022805 1250 209021555 209021591
    0x603010504090614181207110609010c021206010f1403030412020105071403070303050c0c1011090301111213120f0c0209180f010204060210230103050c010909 70
    0x86220301c915500c08504080124503001604841c60508095465143c140703c00881c0c0d400c440c901001600410700c6040116403244283d80e403491b0050160300290311582c050019551000700914140301d000c900d0440160b86501c5941741e4a9540320180000b5454009110249040740c0c2000140c110703419400c3c509900d00005650840c0d00310182d00e01c0a04080c001601e580c0720303c1e072000d09000b41303090000b012100000000e02441e4401e683c04c001d83d13030320181c032541035000307c50302142903810a0100c00c05900f8039400164a044010704070b20b18002c2c810001074211010310213803540c0341300c000c181280c1040219440070703070203040c03102c0e485a030015070713501d0801407a144407031241400014028a00007900c02c02c40d40c0d0825a001e40080002c8c180203006413000768000c48140311070b104401703134070000b000180261811526646c00506400c0f034000862000740002d041964504440c11406a2520454000c8603008501900240480c458124001802d01d4172030b410441c00300341015404103040030000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 209024055 1250 209022805 209022809
    0x7050609130b090411010f030c0206180106080f0703051005070203040b13090c020c040606030b061c150605040e0702071d0406061517010e07080f180d030203040501140105060301 78
    0x1607603041014005038840c4020108507205940010f07982040008100d21082082d070100003d032952454250104411800d42e40f482d5a44030041e0001c5002c203d802031a50801d030301d9006c070b91001281c0103071285161403030418103ea015074a0703440040c08001b404024040120700080e03038041070280303103845100a580c074403544c461541d4080c00046d080e104500c0784030070310303018144010003440050140314000303540e000e04200140c491444c2a00014600340640b00707107080080003800d900d0a00050a400c2140f010300e40140709021612046000950801004644054001501d03030944450402400324407050005100302c00355031104100b84458400b60004880c1e03500840702c050500e503680d182002c00340003154030240000a40c2c00340404510703041000581c243d03038800a00712141c0e0381c928024244003010b60700c500208940c08045404800340201140d4402e01001c103401c41c0e0040203040d940303400706000302e01c40001e6001c8140810400280070354000d03040e03030104009183d410000064110300c418 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 209025305 1250 209024055 209024059
    0x120106050703020a0b01030308010504050a09020a2607120c21020f1f050d0b010203121503120403050a1505040213020c0a0c08060702060609040308010501080601091e140307050609 79
    0x1c190381c01010301c200200418290700850081c82560340f894050103840d001e0203142d00c500e060000240d5240001d104901c0165002840b01c0311080c60080d01200d04618100108040c00a420024809041c100551801402d020100c540144128201141c403e03440c4d070002510750464111188200046c2c0300124031060301190003031010f000e228009001068100c03090008030f210300008108264104015090a40c0703040740c1401400a10b40c012a120710400314241403114900e00414003c400708130030f56403225400344c21511445c1c2c01c0a0842100e41165004513900d51180c1c064400700107904030a050b000c3d5040d00140704604007a030004540f17042483c00807207159800f190070106820100901c200d125088074428a0003503c1e00f03502d640b0f0fa481241c41034050300c5200007280b0709040c03648100e032056405039903d072130907420710004507111900901418100300c000c50003c42c82c120520350a10b280c40e5000f6000c0303c0e82d03181540b10905e808801c0d0f41d440c40ba8000c036070304022a80f903260032900d2803542 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 209026555 1250 209025305 209025307
    0x314010b010f141605060a0c12020f1b01020903030313031b03021c09050409050313120c090906110a180b0c0a1b031712010b041d090a12020a03080c12010605 69
    0xd010b0f04c0f000382d00c03078440035105119100501c0310403009070740a8081c81489079545217640c030741124a0010f900c2850342c049080281080050002110f42e4686889046c2c1c20740050328054446c0002495500300f03440090b0380240010540c0205904450f60b552a5400c812408400d041140c1b03001c1c2d01c9401d05203611105504000030b07221120300c9103110001920b4010001c10001d0303800d05005a5035007044484c1c000900050700081120181428170f408815030082c030300365800342494030000242c00f074100119043e58954541801c50b0a4900c0a0840c201c02030340c5040368010400380c2c00c0321036207040d07006940ea810200030b090318421000c905100ca45d1f8000b6121101d00c0c0c030301182d09032a07191551015042031180070001010400e0000141818540d14105086503600d40e03104160502c10740c401c159281800c41340e846003600c05104800d501c4110041075807a20b801e00d032034980c04094049170050050b007001e1102d02c00c0580260070141c0001000c5802810000d144203a1070f03800c5018090b0302d052000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 209027805 1250 209026555 209026567
    0xd030b030d05070605070915121103090a140a12050c0607140f1615021201080d020703020405060316090209131506030504050a050f0c040f0902100e0a0b040314010b010f14 75
    0x10003001800c7c0100700690821007058055a00100f685101503c10f100407801c201340900a40d9101007564054500d240c05841001380554030190000307a8402d01c15483d0140d6250140445c4060740c200c05030300c00329201d9907036401c98040140d040400083c0b0110611600300d18090800d0707010340980e090f07500c5d80041c0c03c2d82c41c15092844540e08042e12001000303900d01c0e40001d038000226030090300240d00f0289030f142d0180d03240c11820f03442c1c0c00c1114040300103a100100800c0135151542017241c2001c4060b06548401c9c00f90061415142520742290307011a030001141810303402e214000b00b40c007002604007000500c88801a400501c00705125100c101a110008581408814850560002d80c000f0494160441e840882501c4100201140744214645030040c0e4111070300b4000c4070b07041a4010003a886503c030710f850603100c6d4003448100070340005c82c4075400316401c0081e400174000303140681340400c5440c116180d082d09450f11901154104100e04a1043c3d1071070300020325103806a450070121340c5a00d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 209029055 1250 209027805 209027807
    0xc011209020301060b130e010b16060b10020a020306010603110414120d080109050105010e01020d080a0e030a030501031e0f0803070e06030115082404020702030705060c0d030b030d0507060507 84
    0x4400036001950651030b1581c0003e102d9000b0300180040c45554481c0008956140c4a1041c0300d07000340304400481d81d0401007095000c080040b503048071449010001940b0041c03401040c2e060b80208800405a4807074400003095150411000f8010700c61442c05000d40e19140d00c020031140284e1141111080124600c50788d00d0f698129240c1c00218140100c40a0000054008224500a00c140c51a80d441e00001061952140341110030660040c0c000381220480810b00b202c01c5a0000c1201080f240d88005100306040d0510085c000070010780c1d0003160550540c1014081c1c0150b166061700609690148080010b403030812034002d0641003611a9103076542c10030181d41c14000624900d602c00310000c00818282402e1050140180f00c41d52038003809c0e81e958415213216143c80300b14400c01d203514030743d80319035203042d40083c03082d00e02c003405880490ba540c4021440300e030441511818a5002115100c0c0615418458001121806c0303001b49440c50683e28054000d100b5281c01a04041c0c4543c0011405 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 209030305 1250 209029055 209029061
    0x4080c0f0319081201120b060d020a0302130c27060503040303020f12041a0402091302030709061d2202010f2102190c0c050d0f08030a02091507050c0112 67
    0x502d450745050b1000189407004180d40011050010011040e00200384100110564407805a0144400c25180c13550420803020450395203049a1240c003501340440162a89824440f180d41d00c008082801000090081c0110440481c0c031448248540d01d6011002c0d0381c101c2032011500203040881d560303195400d04601a20640b603025450900010701d01c1c2c8811460300f8a28480c60054240e525103240040100a142c03600f610065880183c40002c2050030f11007024584059200404554101395180203180607a2401d621400c2a04208400b800c03032120742c444025030020115448404100d0251410042003ca114000c2c0c10404d202a102ca4228010704803040744064800d0311070343c002c0410600d80081d51104106a0f0fa020b8054440f0800030f014001c80070711a50701c00440b0010724203081c1440071f608901f500584010110b40e0358100402c2d203280040d4014040d032140942d842d0465014010048045a070803a080d080411461010610100c0d03910350200c02445e200007081c910b50b42c0003002e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 209031555 1250 209030305 209030323
    0x100c030203040b180a0506030411120703061d06060303131a04031a151206011703070b010603090506061806010e15040801140604020a14130e15090c04080c0f03 70
    0xc3c1100000b9010000b05414076a0b00000c0002c80369410550746a03800c0c000f50340020b640081c8020000c410600003803130103a04d601034184440e42120610743d43c07500c401e01a10030310100c0062104441c0d80100710403200b40310141d0720150686c0110b1030021740414503405013616110f0050f002c142d0007080c00304005490201da00842d00324403403150031510601c1d500c00c101c40903142035654000c4501940b1590800a503500010341c141009010386a10300f14220200340004c0d030740b03000310740020441d9400017000c031480d5a02804ca83e0358000f8a021403481c001e0700c0c00c0b0b4041c056034070501c4070b100c0b800890100002100d52042c000c2c0b0b400380484500c4008140f030114a4000400d81200103c3c0101c1c6600c01544000c1003491804200b00b0162110300a00040784201041d02c00013400c1e5401d40e003c094080310040140300c0d00540038070105603513100c160035801e005540d01506648002500c0b0b02510302502c0310340d08880139642661401e4600005c0c15940d9034142103890056030303081111b00080c0e8041c407804036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 209032805 1250 209031555 209031569
    0x1e060e0a050405190803310f05031e04030b070e0d060c090f06020f060a02070519150f020301030506091c0e220605180601090501110a02030a060e100506100c03020304 73
    0xa13000941c50000c0d5103400031101141c0c00c01c0140122010186404c80d46001e041c0407030303a41c0c1a002501e8640c0c540c0e54002401c1074455120070030001c40041c04001c020040381000d00e82d80d903155411031501c1c404507030b40513004000708038044001c0c00f80e503510890f0784405c0c154040b100081040300345600355028000c9520080c480d400561002031000d4001c15007010002000382620340300e5440310601812405070360070150040e405124103910304040c03001c1444000340154808a902e4602e40d20075401d50b8000c00c9803d4520b41c000c001002080800c0011680000041010b420045107400c0001100d40168910700c5c100700e5404030020658546080e00303400b0448000080003000752170000a8042d241c14425240600a1034584d03012700820300b85c10038000e420503075030085500e1602e001101c580084440708281c0740290904100140d03000c20044e04060300c035090103d2911a40e000321428100703801c0741e090445091604000321380c1d42d17104545541c1d142d241445a5681083d041c220314500507904886 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 209034055 1250 209032805 209032843
    0x40e0a090506090c030f0307120503070216030f0314070506040b130c03050d02070b0c190305160318050a06051909210b0a0b09070c020111101e060e0a050405 69
    0x180043c0401d0781d141001d020780444201d41c03200030580d84d40307101e0b441c80640103400e02515030460ba4410801503411400910440705400c1100203224000c0a055004a8400c00c4140b4201c007050741080360f0010000c40300039001d0802c052a111240c40d410000d0008007410525000106010100b240d926091038020341000c04864030b85c50314a641d00e603004090405846200e10008042c1c445400f110030122111010b0b04440d00906050302071900c01203400c400b0301100744132075a6812040c151034400320703000f82d6483d00080002d04800b0b1068001b1740019004401190302440b010760003600312292030b035501e000d864101c100d07120100e8000410340c000c01d4900d01d0380c4004030501d0180400715034420b4001c000414141c1c0f40c9194540c210354941c01394940000b10240012101800740200c0c840090041c1403103800303400f4240b4118140614203c0b01da43c0e160355404e4481d43d0b00302c41039000d4002e00310311400704807103400c040609140740002418841443c0c0c64074006410080103124100000000304005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 209035305 1250 209034055 209034061
    0x1404090203011d280c0303030b150f030f090120030c13080d11061308070614070201061404110702150705030d0e0f060606030a090302010204051e1f05040e0a090506 72
    0x2203440d00411500c40aa419140c1c0501c0584140c100f1100744d5281e00442c40c00900d85559003c0d80940014068a82d004046080001041c0e15a10042c940d640c9009aa29940c0c94410080040042c0281040b1401e82c5421040101010605405001000989000303030300c9980d00d94200c0001e11401c0a20381d6641ca1403500000c4c0403c0010b0800380c0036516482c0c0b1100880b0010070290707a01c0c03003290031990b14040c815000020400300380c028410715018072070200b60410628a0707005088802d0b100703c80140e5450300c041141010780960300714602c1c000c8406209440000540c0d40c514050400003a11440d80700720456a6004074800301c800240d40941030341c1e10f4480c80d00718071009150900105000c0c0c06005c0440002800204e603080c400d1100501c102e09645940209200422411804405565081002045540e282c16402d02040705500024010729818001d00c00c0c1848000d4550749203020b20041010001d030460151001d40b001810f484425a440300d4424002c2c11201c84003510501550040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 209036555 1250 209035305 209035361
    0x12060513020408062d0705070b090606030d090b1e040e0405071a090102060705210f0106090623250605060f0f011e11030415020115140409020301 64
    0x50000c0760f410340151806541c42c84000d031100c2c1c0c03c0d54143c2c134400d010850300c82d0030303004065510740c1c10000502e0300c5070800c8003d9541c0604040c080d1001c404540c001010080a8a030400c02804a0703070945c5003018856141c00e9161015000709282c45d004070b0200718100c88108504415075006101c030000c801c08504180c1800754954045004e1411420312400c00070290a0141d0102c42103090107a0003003006640d012002c45464009289a0740101c8a00b83da8a181080c58403c4030300401d458411003410394989600034020180562109003401302d24a0181500c80508960070464105000e82d5076441c0b07050340c0b20301c0009441c42074a0308040c616111a1050141a43c0407910680040d075402e4401c010340c000b00b155404500d18449d00055000f40030040440c007503c0740002c1c9901600f45124010503840c41c00382503420507001410829040f800700b49c90150f09004101c8402c4000a2620000381410300c055268038850f8000c4d402107485418400c00c40d1400d510030503080b1001c50000d8040740702461 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 209037805 1250 209036555 209036557
    0x30403140c040b03101d01020409061805040507060c05011d0105060f0603010f03260301080a030215040804050d05120a09090f0b0d12140708070b130b071206051302 72
    0x200410a81c490711052030814206449000038a0b5401030080c00e070f2850000b100406040303448011183c1c2d030034074104580451000d0002e00060041c1403c0441d0260500c0344003040c0109403c00102524140014400419804a02ca10030381d143c92504500c2d51600707052080c054841e00c820840c0c48210318625201513803041d441117004038401c6a070724860100c0101009540d00080c040e404085414010400c0041c1c270300d0144c58401c41c21100941c50044c00c0c9941d090352900b0036807010a5070340012070f03401d041680c18007e1041c00540200f030054103041075240c400381c80c0201e014403402482c8008504081c05000c1151054074040c191586948500a84000b00174009604c2001c02c406e080100d02100d541d19800b80c15091000075005030041d142580700c110420a85404041c1800b0b0f8a81c3c902c002004054000c0403105d00481d0510342d03c44d5503281c00e00c007599006040290529403003804400144047c03040680261892a003480760321011080d8600030001e65005070346c072002c01c400b4030380d480c2c8040d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 209039055 1250 209037805 209037833
    0x7080601020606010f2c0a06030b1302031311060d0e070602010c1704032a0303140a050402010f0815060304060903030605030a0c18140f04021002010c05160f0203030403 74
    0x2030709440c40c5443c0c250055480c0d519400c1e10700c0c0490b020010003a0000084c80310140030040600245480416000110384210490380003100000e03101c500c010503c0c10304483d048880d110b0b1403011032452a020009100c0c1014080006092003031440d0020320b03e0f51440709480202020b0b00040015100050356159201014401c20003d03508052034901d1040c01100152642640f030504045141d9079650b044480c06490442c80d05004640203407803110f072841840d144100e91080c0c07400906a044060070700b20315203005007119621030500c810000142d9022815003010317070300f5090001454031004011480c202c50f044480703800c000d01104200038000d0a8001004060003034904012041c3c4500515468102c1c2c41006001d88250020422260b18040c0408c1c000d142444000900c02c1900c0d4000e1240d20003c0e100c0e015648600410b000039881c0c44000341c0d444212a0000b0000c0a0300303034801411500403099042200e201b060500c10a0201e8444241d2002d44c4c000c00740c2796256100c1c900414030690b51 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 209040305 1250 209039055 209039057
    0x20301140a0b03010c0c0f0203030403050d09091401080a0212011d011e060b0301121a0406020703030c0504051305090124060806010c1a070207050303040b09090606090f090403030209030607080601 86
    0x404071200d030b00c3c20184541c00f4094160f90324041c00c034140781c684c014081c511550032038042c4010000080812014402840b220704d035035441610107450040e10b04107440c4034000314652205260010051504001f409070345569058580c02d10003004070f17100c02d005180003070788428081e00c010814030210f001076100c101c10a001c0644015000d0b20b03801e00c001104d8060065864001042006110898032484504a0b5900c1081c1c04840081c1c0000070050a140075202110340603004106e1400b05501801550340e500f41030302e0101d0800e03240500080c014481418180c4442d55a400847c03a411000e420455110040d903a81101080c0901e19602c135240007449884002400c10307001c42c05961203915500d45441d0085181200c0c2207000aa419140030081c14240c250300c28030300f00040c181c034240081c1c4014440c3d081d0f016154400b010500103252801404281720701010000c18000355611404182420030130360f030040b600d030350b01d15044d0000c1c420408500e5140c42800f04025041e03512941c0b50f8450002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 209041555 1250 209040305 209040311
    0xa0512130305030609130501061418090303061201020903030307170c0c030f1b0d2604020303160f061404023d0513181d2503020301140a 60
    0x146180603852440c0040024006141080803507603911340f00c03c06640092151403a0440076000d556850300f1a52103030b02192840301290a400c400c0d15261418064405202c07a003000b071031406415158680c400180300ba889080300e002403c001386403d5041e94505003000e401c5a9a900f000700010303000e0590031505d03114900100300002d400721740e00c0099550f010303201001036003400280c400b0f4001d19001415080500540050000401082006108100d401030345038107a400031280700380c0322038107480c03601c01f241d0409190170300c170042e100041140c80c100c00038803501e454803d040c5002da480f5035141c000a4a000d04151018100c80c101312281405248222401000084000c48440025244e24072502d00c0d40404140c10f5100f10101030701c4c03c15003501d464024900220941e1406c48081240c00c00c0001d07205031202c8450b6001c031449a026002880f10b1880b440301315000003203650354103131000312842907005c460030b1111101400c07540000d5030b801070080c06143d41900f208800301c41c04480034005681 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 209042805 1250 209041555 209041561
    0x20a05030a08091e0405130302010605100c0b0403050c0f0c1f05180102010f0e0304031704150e0a150e03060c040b090d020f0604060207030b070212121306020a0512 72
    0x350014103070034215440760305141058041d804020341c0c6031031511200da00140e014281e0754207946520410303110300390038400019000c0003801c0080c21503906411050140000d1200c49040e6904402c0260302d040d4001c00000481e03a6500e0200e074903005010142402d48164694241c52a00c0420b41d070000b00d10079510294031101d0700d00307500b904002e1842010007154007005044c00f4000b013148203082c6c02c0e80c180008610340400015007011146450300000380c942011805204105052000302c8840404099141c142414149508100c1c03003640c54450030b02c41051420f054545801c02c0000041c485050000c40b001e282a40240c85918003c941d076202e030080b03030000351000c10780d802a58240c0344500b01c01814050110240900b01d107901070183d0b441802c0881d260710030358503e402000a41039076405055010300c0c0d80b4100400c1d1a0191880f02950041c0c1d04841e058843c0c0c4081e961fa21280d0101e4004030b07105d42d824030882018480c4081d001e00c2c00002c4801140e40c0180041212070f08155004c03003250703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 209044055 1250 209042805 209042809
    0xd02070515180c0d02010507050114010906140301020405090c18130501260d0c0f060e070f0b0c060a09030e0d030504060906050408070e061c060c08070e01020a1e050118020a05 77
    0x2641c00303e0f0583c00070800820201551080000e068021310502c00000d10581140c400455128242d021003001a2107481c14040d010740702c0c0742001c030f00c0e0043c1c00a6082606210020f0200207009104100c2d50034040b82c04109075448000344d0301c06003005040c9001a080038607404001c0d240c24042c3d095071442c3c4e903080c05200c2084074140c40034000d500000d402c07000340b40c0c00300b102d505508100942e81d981052081002003000e43c4110b001795020035005181403417400301a602c9003e07442c2d0200c1c1c00200148078001080c107012030615885442d1ba0000154400e680c40c4c140c40d4850303180d034141d80220f02070941c2020143c000c001001650001e4903104091550707001c2c110f82d640710f9402074109507045841e080249a80705244ca40e00000300400700400f5548040c030b69041c04500040640b0801e854840580120307401940143d005152454254004c000c00c0300013039034451801c0c00c02000025034952007110544540ba074000c1880d4428020b0040c141141108002500f0620701a0306c103013900c0e940001d141c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 209045305 1250 209044055 209044063
    0x20a02041a0d0605100f0b0a0801050102120d05070504080d090503070f230123040914011203300504140136060f0c0e0a060e04020d0207051518 63
    0x115070700800003450000740b60f80e400094900038110f405101d82080300801c007000d08250540242c601c0d007a0b040e846200303071100140315001c10b034007030790554010003000b0340e44070206d50032510032910052011035503454a1004039654412640209000d018021040c03d807180e101c031040b4200c2e50110100e481680d200c2c1603451a00005100c3c0020342d50306003d02c000401340f605032824070540f050400d41a488403c018188113030f8500035a00f94a00800103040c08040708500c81c19200d81500c0d00040c0607036060110744440c070544200050280040341c500300d28999960341c0440c2c440b03044240c4100300c547e038414640c4003500c0e00703603012110505a01c0c0310342c0c0e41810510400d1100c1411510240c038010f030644100690300c011948040da440603d94801010401501600c039060301558000a030038410340c0c0c001400741004440140c03041e81c0c00501000040c0e4407460707102d5008411140181e445e040b141c10200244034110008005014803009104c8a41c44504031500c240440310075502c20300318451000e0740b6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 209046555 1250 209045305 209045351
    0x90414010f0c170a110406050a0306091b0305060301200702010e030a050705100c020d140f01090809010f050712090302030f0a0506010b0c0a05060c18040209060d090510060303020a0204 81
    0x8410415020020716588019500090f6480740000c000048461510446d0b000ba04000041400019505031180d41485000001d02e04d049003040400740300000c0c50089003080030410101074070303107021403070a5a0a501403115001c0035407080d0f90442000012800355000601c00368080b41001c04a040e86043c003040b03002c2c43d03580c800c000e03103100c5040808110004000205581c100040d00340008010b8445002c1310007400e005101b0940c2c080b4407040c4d003e02c0c0400f15020103065904000520001404110540e102c1200908084400c0303840300b03404071214061020050a009682003049241c20f0b00410b02c0e50649000380c094401d01c580100900d6520110028020100e0740141e004101001d0b02c08003518481042c88196038511070305444081c9040030a0301c0001000400103040c901112074103071541c5044a0654066040451400001e01140140245c0a42041d100c6d040d6604012040c883d10500c1d4600c8481007141c030361a410021b6a0b641c0c4980100e01035840c026602c0a00c3d291007100c101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 209047805 1250 209046555 209046557
    0x2101401140909120a02100501120b070f020a1a0a05010b0309030f0706020904020a030614100806100c0803150f060403050d0f050903071206051803030103080702060405090414010f0c 80
    0x104001c8a01440b007460340003014046103026080d0404032404c40200100619603903a13000306901180000304400304c45040e40881d0302112003c002000049140754a10780c0414181040e201c011701094061b070a125400031300400c0c902c4864640c00e4400b020401503801192031030320410150780c80d20020307200b610003940c60b88071036801072111615074910b0070014100300c0d2140f00c000d81400d942d41c0100e030070703038200e003003841e000c42d1700d907a424000082003100c02001c04404440c020440031340c44d04003420340c6802400707460181810110174030605005080e00b070400350b841584070b43d4a00d003000c4440110311410303894500c90984448803041c50f10b012000c3d07030301307072a0030801519002005c10320541e1401c001450240034000b041c0410b61103540c0c28018500209a00702c042d840c296000c3ca0b0540459100400310015402203800d80707860a0310020640e81541ea0001e8884d075241d00fa400000c0250080303034401940070300a00c04000c00c002d0000b01128080141c6002840504140041d50090300c603003400c064 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 209049055 1250 209047805 209047829
    0xb1302180604020714010504050c150901082205281a0703091e1506030f0209090703150e0f0a110153060306010302090a180302101401 59
    0xc009048100d0a10340019000300700524061040c0c5e45d90701a030045030798407451655141b00f000f0030301c102440041c0000720110b070507a03007903080345034180c04038002c502c0c1550401c0a04000604140d0a5030391100d00707061000001c407480760311460556070b150004440340071040c1c0c8118100b0001003080103000c001581c04807000051010700303101c0004041004141e2400c00d600c9550401c042101d6070508081c6020851407070150003510300b40148060340c184401d00026251080401c0462600b950054945034116205916501c42d8401240342010540014141100022049418210507800404036071034500c15140506040d0750015150350000c540070300480f5030040d100340298820b54010705c40741c4a041c0000640c81c90f441c00c1c1d800310740c00c0004911040c0c01c024444000c03100303a107c0003010000e1520000400b4901031021a440e042c043c80003e0003840c4520114002c41416003150611a01c1e80032540300c04441806d0003556000c44041079030045180880030f0038507410350030155041c3c40000c0c0c407070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 209050305 1250 209049055 209049079
    0x9020111120a0503060f0d060b0103110c100b030a051c12200d0e01020c060105120a03090501121d070501080c04050d021507050d0c020a0501030c0c0b07110a06090b1302 74
    0x941d03031135100501075170340662480501d04a5030303545007044074500e00608000403107207a100c2c005000c0715046001c04c03a0f5204240141c0303106410005416203013141109010611076801000720b40780410071400241140148030403d210001d480200080303e921aa490340380903070704510b0450889141c140c40750103242401d60040404100300303004042e258044400040d5000700440c441c8d0032600410030004240d000b0400400507440c00011900b00700300120064903081035165400340c200007c0e4400d442c1800200c901c050a070403051b034881d042c106104d40211104681c1c1c0f2401a072a41d445008081c04580503a0105080081c51802e0360242e603c041c0040000c0340701c5400b0080c420990a00762411044100708400000350280401940300314503450700404107200c2e104004488490383c000714100351405880e1400998845110013019070483c4581d1925103c41c507046a140c4981001c90101c0e00c10440150100402540308411147c0161040c4166481c4d04010301441c45072444041d50101c0000b5039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 209051555 1250 209050305 209050307
    0x31214030c131715040206130e15040b0105030a180c060f020f010b030a0b1008030f03160804020105160c0e01060c0302060604061212020106090f020901110a020a12020a0306050a09020111120a 84
    0xa01c40d000340c001442c030740c24440e00548c4803510b083d0740d4002c02c41121602e402d01c40f00080c40041e160b003a48040720103005038014140020890701000380920b202d903450f6519001c804019a400c844802c1c0c000503070000c0780d40c9807a03018100020b21a041401485003020103440000113204039103a04000070098061007c40e6103e0200c2a0405004901d40b9000800001207546040000308480c400d00c8081940301d1804c850f00300060f405014144046c0a081d40410006031b03032100455143c01d840b1840700d00d114030706003021741001ca01e64010641e10305660001103022038009c0003241d80079111360308440840d85d0340418001990403c2c03181400708000c1400020004420b001c40c2101d850841c4000102d80e5a90580709040c0c4108485a5151a600045120055030b00000e4403035031240c200010444c40c0880d0780403400080e118031a8001b0010b00c101c00804659410b81840029a00118107000360709100c040d840003402400000ca020640000d085606035601045600380102c1103d8202e00b010b4415030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 209052805 1250 209051555 209051593
    0xc0111061b0d0603030206010e0c040e0c0f1303051b03030412020603060112320603060103060f0608061e0609010b03150f10020d120213031214030c1317 67
    0x2480030071500600031515111080d00c220401140030350300501095141c09086210200050004855440c0c108400e00c80b007500784044030342040e55141d045a07a00d113003003103000ca18000c011302e107011582064800000d1050002e5140301c6020818582d400c0402d105003055601e01c00c2d4490055400d801361180c00262500340003641d0b1012041c1418040030541c102d1400c00c07114480d481c82d03001c10804c808505a00c2111000d000c17003a41c030100385050303410000006651036030148401000c00341c841050b43c00d1502a5081a00106000401c0f00e01600f05800b04901301c4154070040d51041010200042c8103217805c00015041b500c8201c0b4403483c2d511207001000b2108600c481c55074100b102042c000702d250720303070810074003120050743d000d01403042d02e0600041004422070042c220050040c4000360f81d404180103a00102e9601045a5803110032141c415110880003440700803011501208102c4000f111100810800e8070380b40b207898000c0c3d11100c00100e02c8018420031101e55018900d111440e103291a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 209054055 1250 209052805 209052841
    0x70e0402060c0f010f0c03020a0c11040e030d0b030d140703120b060703050d060f080316050c09101d0f0109020705010b030d030e060c070f0b2a0c0c011106 68
    0x10346910300e08802d4100d803d1402c0380b051804400c6a40d103084001401c0b4140c4605040b1086614055203443c0c440d505c024400100d014000d015030481c1c440e4140681d407680d21044081c4400c8003902c1c0c60b01640006003009101c0358405a000b8019801c1042000d4413641d410511000202951820051143c40c12501d0104002c109803542e41d940c3c05030885035507208041d003806442030b40c446aa034200c2030107a500741c0c0c0d619805103284480054013403103202000b0050b03421030540c04ac00c141c0b400c44030341041403900f062600ea0303a402292600c140106404641d0b030b10300555039800131400c0256009044814200021900c4800d5408440018481a056034004003c1ca81c083c01c0003045441800380024180f01032122800c000c2a9994031015044100340061548011070442107400e014035a01e882e04003d03040c82000700310002000000f81040c08002d417040c1c040d1240c0c00e041d0b80150314000449a03652051120306100d120348441c01d50725611900303a10a500c1e0300138010304195111003120264a640309 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 209055305 1250 209054055 209054059
    0x3010e04030207270f0905211204030e0109060e1011030d0c08060a05040513060903180b0301060905060a0c06181a071b0c14010e0d0c0501030617070e0402 68
    0x40c038000501e052601d0500c4e09840d0382d01c60203852200c415000d0a040310400d400380b2500c58106804000440c0b00815090840c618a904125008a0b40144c0e10b2491140c020000301c400e00d2182480b01385039202e404214403101c01e1302c4440916464031006d4640302c200c0464a54005001660010b2803441890400762034500030088909000601851000360741002481c3c03030005103140e0070040585132821440c40281301c2510100060308241900082040c0b40e120b01400c61a1210000d10416108018801403070500050030380c0456164208030540b54020700c500d03400610340d250042a01d00d0182c007110780e0040c50380c50f500c0560240b40c0d83c090103050303624021a0a4003490607014049140401401e02d00b940c00145202681f60900d005031644000007401c0c3c070012041c01071100016880d060340001c1d52800d81081030081005001216200701c0101000d40112300f02c42840204144600001700b5034000740c030148034150315100ba01601002108500c1100d42c004002000041207e03030103944c0207400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 209056555 1250 209055305 209055313
    0x230406030501020d05090d090f03020f030705090405010c030507030501060203030402041e090503070605071418030307060903030c0e031903050d110a02030414011b02060307020114160909020a0503010e040302 91
    0x39a403181401c98114a020808654680d020401e48080a003c4c2c03950840a60615000441c03c0c842142e065005030700009005034688850b000d103e640c20400e4038010030004200a400b0325082ca005406404da1410b000c0120782450085404030b4007a014442c10307201107030300540c10356a49400308009040000110464900c045da64602031403280c6c09081e158502800045913038480c2842d01100712080149010100702c47c03a075444682403001d600300da803250940314004282c2c2641e540000c0c01c0d0710035803000820403840e2004690416425400c40044030340a52a0448551175510078951100d040e820030a20344506100a0b0700024000c00c050100742e000d1000c0010704900a40c0801c0c0b60750320907800e500c0540d2010801704580f01c03a08484100c1c290081c40d003944490b803032001c4a030340d00c1e4403040000e100d114040001442e40d0b101758012034120650340d00c0c0154a040540041750000c41e0384052600080030790f0000710300003510323000f107680079100307035881c02e1840e841d20303001c00002c5030040e00031811402 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 209057805 1250 209056555 209056559
    0x7060b2e0c02030f030406080a06050603070c0c081e0c03121603030b0612010314030c030f0a0203071a01090e060408040509510d020402030601030908070c030b0f01230406 75
    0x9080001244001940c4005e5503200c0c100100944a444020f00445070103050540c18042500c55800746c940000d01400c060450700f059260042209509800c00d010701d1056007202c04c47c800313003040c400c500c04200906407500c081c1140709154461003101c14501180e80d0400070f400300c1d031900002c0440c07041d000740b0f40025846044c1000800030381c404203640840e005580b0040c01405112000c85c0102c0074140015881d01381c0400b0050785034003c60080140da5100400c030404090300a00845c0c010651008901014601c461000d5010b5542030080c151154036200e60a00411030015086000fa500017002e1810079162904001d0540c80041c030a0210607052000c040700b11341621403001070241c400b24080b01c4550700b811350301000200044a50b84800d201d401d0709000c1e4403030b00500e005c210f405490160b543c1da030301360050f00a007400207002400390f0070000b00e5005009000401e9015288520b0b01d100943d02c2e080c040e0310903e4400e000d5840c0700802509581d1081050b0360700400b03100805170012992075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 209059055 1250 209057805 209057809
    0x6060c060109052d01030b0712050a150b07031b03030b030d020724230c03120a0c1103180d0b09010b0a0f1a0f09040c0507060b2e0c02 59
    0x402e074889080030762120107021036056220b5012011000001310a114058a004440300580041c440a85944000004140c02a2185402107450902510300307106500b0b00a60071030080c508940d140c80d150604980108550110700212204950140e488180c02464500c81c43c50340d0244a408400381a038401190704251418003203503e00c40895000f80031143d1800054a40106400428403011034600100d941161703000ba030720758110780351908120700b80030b04d50b40d000c2c009214488044126200200d0b0110028001e008802e02c0344d0700b121030134030011741c003013070700b41c90740c20030a100e1590540007030007440011044018031551501000b418502c044010344c50304442040141c42860440c2d454007844242c0d4105406401c0042080d8041c6140c101d2804154000804010900d19030b1035800268a4600c40b602c00107942032000014002c00c010b180610b0041c219520101040318203034107105558440d403800351142000c02d21f111900030008440d1880020300b5030b42600c40c0e117060044186018000da = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 209060305 1250 209059055 209059063
    0x5130b04090309081b0105030a1508070902130f030804030318030b011202040e0c03030301060c1109070e19060e090a0f060620012c030f0a210212060906060c 69
    0x82d000791500a07643d03082840702c500300248496031000080920366143d40e641d07030160440381d000c4c0400000180035080d1400c201281c0c412640081e1840c03050740c4002c245403c050b4010a010340d041101d0080c001c6d82c443c1c0007050340c1d4071072001030000c007028081040460301520004d181c166641e50020121510f9941e0514a82c10a81211000190320004c1d0011801c062103582d01100f40d10006105c000b0343d80c0c0020f99284014003440c2e00b00245042060104151600d030b03259168801400041a0300d007180e8028007203c00e4540c05803054150f00c0140e801035000e00c00e4a8141d1b00b0359512108908449028000d200d00094460303404241c1e10211320301d1000706c500c02d010103043d4596401c111851168500800101088020011a40341240c0307a0b4070800b00d42d810a0242c5250151140b00308800311001741140103020351402103610004442c0e0a241e4030405002c0302c101a2a408074020524102e12030890003420000ca5442004a01040a03490410707a19980000000e14261510107a000c1103810 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 209061555 1250 209060305 209060321
    0xf03060f07050f041a0a0f0512011401020102070b0a090308010512101a06190e0114071e0203030313030f030e03120a1b0806090c030c1c0f091b06020f0705130b04 71
    0x800001184140c46c803a031100d070602d131450161400500703010076211170351031103001842120f485010800c100b0340b49034000c1d01610b08258009120004c580341103101c1c40c0203800390800c101c0010b00e80500210b45458402c1c1c4454420041e02e004000c0344c0310180c3c0c00c80017040e00c4960f68880211980407440c15540e6a40104003083c01e8203058500000500b101411071020300307540e903050220350f030030b0303168942100c406840040d5000b0a0540b0000301aa2441f40441466000a905404000208050041142030001c3e0340c0c4c0c881d580d206113100001000300e045505c424400000b40d08100041c0c001d4403aa01c0c3e840380c000c1c140d41c1c400602c1c418a140004603000e4034203410004608024100701052800b0080b03940e10602000e070a40c51441c0107c4220102e02c0b4100310541c201d1a140c56220080c40380741d1000d03011001c5c564080012008c075090005149440000744e821890f180ca4000c5400380c804200344c0340244484004002d4241000d0802c98a000d4501c0003852503039a955090b01d062b9078500412078 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 209062805 1250 209061555 209061599
    0x5150403170a0c050a0c1104061e09050f0403081807150915021203040c050301020310090b10020c13020c070b070201090b03041101030207060e1002090f03060f07050f04 74
    0x50765407922602084200c9009000b01400c07032602100c00441034210f070445040000c84d2601d000341d201d0920708040400001c10b13a16400034039000c03001c20354210260123014008162030703109003500e680300141003d482044a011010100f03200200c0c0000e405401014dc0003000b000103a02803106015640f440c0a8440d8030102828146c07540900c0820742140303006000d045e101000d04005001414040d40e074007140b0b000240111400400101801000300e842806883c00800966507401d100d40184000180c038003414103060314200042c041c52402200c3d401c10703529986c01030440b9487d04000c200821003424000d611090702007155020740101130103400e014100700003040f0388440003800010440b2040d50002000c0410030401d12010030b504035844008504240f8001d6a40c1d00d03685003840c0542020701c003c90251007150300b0402c0c4044542c0281c5440c000c1a50710f41a14242c08082594800c002e5410111108680002c2172148d44682d0080c040544001c5400c0d00d000d41c0c030010b441c1c1079410103280403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 209064055 1250 209062805 209062817
    0xf040c0906090608040210210207030206040c1d06060c101b080612030f0304021c0f0b100506090402090a03020d030f020115062001060801140612060106140705150403 73
    0x40701c40e503000b4411801800702807034240a21328140e4081070849010403080381c144414440010088401459501810350310349500355256030462030065a1080c0076a400c0300c10068040b400300300b5480220704610384154003150041c07152111003d0040607802040089010300078850000c83c40341c0c0c1ca00601c6103200024029068020746507400030060300010309070364451003000141d4003030501c1c00425203289048000c1456600d0325607100003001d90301c90045154940410000c0c120034400b50828140a460240f0034400c10340c1d07034407046040b55400324010aa8054810b00010529052a5000d011808130142c4060a8961640c000a4400c00012030481c0014164120050031940c20b002d01144401a0b824a500c541d0408101078842001240080d03030400c81203440c8001403400350014002001d4080c02000001e00d01c03440a501d0030300c2100c01c280039907042c503d00341c040a00098600d040710703000d5454682504e11141403003250340c450710082d01d1620858010405145210040314081c0d4440d071214 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 209065305 1250 209064055 209064059
    0x213030c0e0105010f020703032709050a0506010207180b0f0913030e09160e0d12020309030f0303090304060c0c0b030a0b1003051015110106060e1912020f0f040c09 72
    0xa01c0d9641058011504010440784482c614940014401003526403504050200c1541e0301c86080d1005841d0019042e01449202e0018100c0406d9020324003518948030207120f5541d80d41e0042e42d46240364458000ca01d08260095511001e0507403001c080c0360001044840c001c0843c0e80040c0c0441000c0d0b80600709000050014030030580c0022072070f0421941542c1c18803281c0b410140302e8070081c00303607581ca0003409505803803c00d05035903c84590100a50004003071180e840c02c940025a69000718103028040e00c140086420740301d50001c240c901c9100018015490241003600031101d00c81c2d220303411940820a880046a100010000303144210540c03000058014001000c2104074072612074450207141c0780c00c3c2031184001100c42984e00f56002c020361810800804002200e01202030f000314030302c95281040201d00141e0003441e01030102d000703d909065054070981d060840b40c440c3e2040303041c08150340300180c00504161b585402c20304030040c030b034a1a452081c0302041c19120120a0000028180041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 209066555 1250 209065305 209065319
    0x905010605010f1409040203041506030b1f030c140d050709020306150909010605130504140601080702031204060c0507060f05011502031804020c0a020604060210050114030d0309060213030c 83
    0x243c1200e00b811890119a2074404441103406480361a42050103035070000001811300814095000300300e0301008040084660b6414040c0941c00140d82c0b01c95403003840401d00301c400207a507000205a03a0013400070541b181c644a444e0f00e00716a0040b1840e0024900d0907080c0114070144032540041000d0000940e0300e00c4c0c81030030031118a83c00030b1400e01010091110581c552990401c0c03606448450416030b55800003401e52907a400b15551260f5072081c14a005160760701940c000c0c2c280545401c0c0c0310a001600c9000050f0780343d020307240400030410542000500440e0b5150420030069100741015840c3c20407648582050701e050640c4020001c0d01d9200402c09021000d800c0c008000c02c9101441c20001d603c030840907601075140c80c0d43c0c451070300420750305001e43c028401c4150103a0b005208950340c581c6c40c20701940b00c40052580c1c610f02d03032800c40005100d14a5000d08140712000401500203610300c0d100580041003109001e4428036424008142010568049100070358000e120040456140c0781c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 209067805 1250 209066555 209066567
    0xc180a060f060f0c02011e020a0b07050c06040803060d060c021e03090a09110d1b08090604031b0507080d03060e06030c0603180a0219031407030305180102010e01090501060501 77
    0x8040700d601050100304015041d40241031042c0c440d498500141c804036a800100c0e001581040146001010700f42819040d0380c0000d541100c1c0c41c42040a040f855884c4c000554240c05840002c2080e90481c400040000c0c85020066521aa00070a01c590342c640c02e484400407580e5484400c40580d000303018004c1c0c62051002100d038405240001149000104008549044900d00c50310200d281c5888010030f0210307000c0241c41146d205001c0400004101440d0261070752503c0302101d0200e0b00310004031f01040000300300300b84030b550552140e25204644444400aa9000210541e9240220714012450040601035610100c140340e034049036090a03e5080c240e0424050205c0d4820381c00310074080040d8032068207480d80406103074003d46405240c1246a410060f0b66a0001d40c041b0b01e28085203415807003420b22200b6a400f07a811666071511504601d0750b100311500025001c124180110800c0351905070442c902c940040c030010401161460205081d202094411101350351548030521840d41c2c451 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 209069055 1250 209067805 209067809
    0x4030e01021e0c0d14100207150b030c01110307061b1205092512030314070e0d020f03010905160312180902090607081225021c020c180a06 61
    0x24000000c404400c0b0710281d5071030880034281c1c002c68030f22680d40140403180d0301c00241e0b0909042074902c03035507084a0b040025400b40404445507048130a010300c0e03540c400d20410440c1180600101000c121180c010351340c1002c020035814880c401040b018000802d14060000001643c00c0c482070400c460603c040e1074201542450b4044610340b83c00c00504079030000b136240c05a035a1403030105403405070600715004008550446c03000100307c4180c642c20190316034000d219220850741a9407107502c504808031824100d42042d0b960004600583e40090328141482c080319280040c0005140301e519507032941000034104009071251141542002030100c2034a4030b90036140a481c01244816040d0004070a611081c0a420345eaa40c1c0481c95240e5619404201d03500359402646240d01c540541404250b147cac02100d40c51141e000304503035003818031510341d0000c981c0d4405401400400007450410305002d052180c2c03910031031103089a98034561f26104d80714426011020103204880c034000405001360f400c15 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 209070305 1250 209069055 209069083
    0x606090a020901021213030803131b14040e011503050616030507080f0901111801091401270b0705030d0506090402060301090b120d05041d100e1e04030e0102 69
    0x411084882d81e90200d05194018412101c446e00c442465865200d041c0d5a0b800c0100381c008000284450002c0c600310f40d0b02a1485014200780710720444d01030151007540782c400c9039290425050388104500c2c05800544001010100001c0c240c0007003554203040c03140a610035903a0b504424140000c41c07a48450304407929880f802c0610050a004100030070001c8010301c201d207550080340105281c2c9800b034001443e00501c44206a8403035145110a014020b440d58006001c500c1d001d00000f0700503112050f40340750240c161a00c0d0f540100300703942c28442480241c2c0b050744c01e0045000c045aa040d0420142240c0d43c02000110b807910645640e680403100090701d401d04c0354110304100001a51120201e80c1511928000800c4958103080480e076100429900200207010b0062400052175100000d80101c2e400c2504001202110b41c40c1d94140400640b120185411040000e01c088107203180d40641004c1c3c180c1048100290381808000c6000d13041c1c40440000380340c501031003042d41e4104200c1d45e003c804 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 209071555 1250 209070305 209070307
    0x340309020f0d020303030403080703021204080921070b070303021c0204080601240e0f10030c090506040b0d0c0504120c05040f05190b1c0501060801180302030306060f090607050606090a02 82
    0x62900003981c5c3c0d0200070f1000b02000707420743c00510214800c0e01660724103040c100c1402d05030704045c5000042604a001194040e5081e40c40441d01130407900302c1850603055800180c110ba508000b203013001d03a40700c031a00307800741602040740d400008651940400d0118003d500143c13241d0810241c1810700e40b040c0d0283c03c0003010864041c40000e61075500210b2950107081020414441d40d01140070001401c510740d92000605160744002e5800d5041400c0c0c10560366238440f4030a80390702c05c02030f00340220300402c54400740c20312218903040e02d140d100c50310300d13040350801c00d0a1555031070101d044007a030007004960100c0407000c00c000505043c000e100701c19103050001c0c0894030b4000b2004e01058083c0000c21061519070011140c40e03141d2078046030004081c4c0302c2c030310040c0c02d0905245000e41218851200b1961820140d20701160070314417001a0380b0b40c1a4003031851030b101e240400040c5d07040305041d01c1e6403550820a03444181d8601d4010125284100094807c500d8034008124801c00024140c07828580 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 209072805 1250 209071555 209071579
    0x115031d030301060927050a0b090f040b070903030806090c0408060a1401060309111e03010213080f030c030a08060103110c010f060e1909110901030f0c1a03340309020f 74
    0x20310300001d5800e42a107564000350350b41e188d60307490700908000e6440d982c004200e40141305201200015044c42140500f15100030f9884211084030500d025210103000110524040307852842c1c20b1104640003807005804c9070409072101c1c1841d0a15500b80e90464400d507136881441d085402e030256041c01080700d800c0c204046078141d104d411a16042c800d03654480c3c9504000003620891143c4182100300c4058000c6446d140040d40c0013100316118000c3c50014882c022807a0301e04580041281c0c84100d8007000f441c100305141ca0140c0751100045c04490505860780c070000301000c2840058400390307030740c0c2c000400c410704c01f400500b0850b2085c1e0010706210890b201008600605645900d4140300e214000040100903410451042000502c800d0341c8010a80c0c000010302c10701c82c040110140c0240c008c55240b690310070507081014200a0b0070301c0002c00130301c00100010400c81410b02290b0044851030042c1301d10b00301081c40d1b003900c0070240d000700381da40510f602035091015185418400c00c1d114108000c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 209074055 1250 209072805 209072849
    0xd0812090f011b050904020c0a12030213591f1a0d1103090f0d0302071110120603210311161b0305010b041109090115031d0303010609 59
    0x305c20456018012900042e075441c802c03d0401144203020b03001101c603450380d48012001006076005000da1411404800b1000c191818200201500c80742d9840d2000075a0461300d0080c920000702c030300c40d0790035031400c8214030b031401e004080000c880841c2201e60041910f1700700b2460a03820a070b40d030820340308410060288103a031141c1801d180d081c1c00a007002c50301d6110311a0f00c4c070060b0921803180c0e25030072004004d004072150000703440500e55140c1000e40c0d40054007040c01f18120300030854003402c0c00c071038802f000705182404061038ac80c902541c50228040c85625040d001583d04c035a0044403a01540143d0a03948405c07180c1c00e105290300b40c9000d00031000031041d044454001c0107040e044031101101c020040240c2000350412071000f40000890140d9a814118020f181c0f4aa200e40030340e00b4008660046056401220a441c3d07004184413002c5e424034506000d0f031003031042c2d2482496030790004803a11000d4160034088010040c0019503072507041c1000207200c00b006a00030500440b1300030f0009265 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 209075305 1250 209074055 209074057
    0x109050f040803090f030c010c260f06010c0206120711030403150b06040f0801090c0e0105090a0f0b06160c0b03041a04020607080c03030f090601060207050d0812090f011b05 76
    0x90b0411161034890300e03088030443c1010313144044c2c030f1003a220026403461000701c1174001f041c100d12140c0760021103070598080d02d036050000440412050703450310009003068000c94400354100d00d042c9081c1100b0031066010500d564804401039104c1040ca204100c280b56001d0b03001c0e403510824134051801c0c13030b1450742c92084e4416400403140d400c0f61982460701c41519200c2c2514020504400010782c2c84d80c2e1049003900914400c407041d54452a400c0340400c5450121141a04954015141c01c412382d4030f88141c900202000c5c124500e1541e2108905045035071150040c02c4402d80e00c04400d40031104503c0d2540e843c9007142c1c0540706c40e84050040202040c0240c0361410000c00441c0000c0450395148000f501d10310902390010605030303010881c44500000000a50700ca401032200d84940381e190341a109544100c2482900016400b00c0814800740c02c1000046480510461398107080440c00c01001441c454210707005101c0b0b90101030b101c00008403d00a52114040780810581650741031903004180f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 209076555 1250 209075305 209075311
    0x60c03090603040615030b1f1401050d06030c0f060305130f03200307120807020a0b010510050d0608030307020d03022106120d020d0201060b52020103050109050f 71
    0x1c07940020000605204041e00f11103210030103030f000a54015103070314001c48800020340c0d40e1012540010441d403986c20101c02c501c01924061802600414404401103c0383d0340024542c2c00400d854102c0080040c0f0640f058a01074100c40c84042e1003642485402811207070000d1450360305200c4000510042200111904581500b600d401c82c0340c040c605140c0300f894080e102106a00d0f11001032040c05004941d80b01c0180d81989642c0c204c29600c0d1900100d0b03581c0c2140c0c0020f002c101d1000d00400c2140f400a4601d40308407803605085003015480300c01001141ca42d64004682904000200401e0a5041c041c50690401c2070804500340408034410400050181821303580c00100000407450035560b40300d4080560150750308540780300201040003510741044000820240d8202140031a0488003071003990258200c2d1050000e0420341c940004100300c3d030980780c80c00d000864819080e40d50207401e00f81c0a62400342c901c10350081c00240b0005048420507030110304424500000d0240c3d200382c404c02203030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 209077805 1250 209076555 209076559
    0xd030621050a0506090606121606050d1805070302090c120601030c1e09050901080d080a02130305030a030204050f0402120403030c03020408010e060603070e01050127090207080c0705060c0309 84
    0x2880c42824540340b0314044076900054402d102d04410841013074800510f04d8030800040e40e0300c48407441c0d4031011907681c0042700200359615003001010300c2064402d4001e48041c00100002042c1c03c00d00c0c007694481c5104030502030f0390300d07000340e602402503080121039560013881c0080e4140c40e10b036200345a4901100090a40c40c105a12002400340765481410340c1c41402c1e14807117544070035900139130010380144d55910485020b40b05480001075070481c0801c01100d204542e450f4000c140c0c0d211000ca8000790b0081c104030759150550400800828020000f910b503103545d60310011380d50382c104004c00903003143c85924140b25a00411205c083d8140690702203810513494200480c41c41e5007094180d01901517600500315035072800805210010001070294040c0009030306460141d82c41d149a040c00d00c0090082501040c0764241d0119000c56031413030800044000308500211315202c0d4041420b99000304019541d612002c120034601d07540501100008240c201e68481c60704810300c0202d03440f4016211380034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 209079055 1250 209077805 209077859
    0x10b0306130609080f03240303090a060c0203070b0304260a09180f0f1406030105090d05130b0f04051009030c05011116030506101d0a0515031b030d0306 67
    0x102006010000e03178a4040c0d080f60700d070b912803401c007202204003058000c03110300d03440303000c00104900d09010085554016015281c180e4940c1090000d440d41d00c60342d40100d030544200500011320310310000c0a58011445203016914039603042c00400c2d2070304000341c0c0d00004004100301103c203254010104900f120900055480d0b58481031000e01c004003e00715803030300c6640c1091800c0c1000c43c0e4030b0b800303038007130105a61548146440b024149422610211a18515948401c1b031102c01c4601907030141158094907505180000d445861150803500100c3c1520590b10703020400344124902143c2e49402800d40d4940b03602e256142d030f1264584a5414400d4034103004040300408000001030008101c21400100860040da54a141c501c1e92036070202c60848801218103000f240300d0380003007191000e542c405021800396460f4021584000c04e4080c1020460800d0043d0080e4030f43c6092101c50402c654170008a88005444010701d42015050507041d41018608031301444400c0610000c54111040c1240c40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 209080305 1250 209079055 209079071
    0xe010815061908010507031805072105070e150904050c01050a030905010905032a03030a1a030f1005070e01050316112a120303040209060301060506070c08010b03061306 74
    0x206110b650408142290003400c01004a60410150407080c0200b5130303075070100b240c56900b0b90841103020f05484002c20070b0300b0034030f010441114404030400044804014042914603d41c2d20707117240001d40d80c0482c541200050801c6800624a00080303e00314098586020501e040d0341e90a4480350030b100480e062000104048003441d100f0340c4003100b07040d0b00c00b008010364942400e046650740c00c0342c0d0045000c00c0c2080d15001d2500c0c030f000104046030b50780d01e00560658a503404004040e0200c000b0100c04000d501182c550300d40e03020803524110303201090190003001032855254041e210300601715000d00c200511441c400781d038010b0481e82d0100e00804c43c80d086440d1040111450000900452214450308501c1141840c1442c00300580010031140700c11035900100a20102640410109200c0c2d0801d00c002805800c0c40f2010903840000240001600c50315900080c0c82c0340c000840503141c03401003e2041c0500d80e800d00c580460f44000b14024a03040c5400300c4004c1150600140044c00380e502e407048 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 209081555 1250 209080305 209080309
    0x2060f0601081b13031a0703092006120a02030415020a1b08070b091b010201110a0809120c0312060a0506070210180603021206090f06060c070b03040b0603070e01081506 74
    0x554a130040015800301d0f10983c0c81c10000c003007400c003d01301d07050a80202c020640642c00b030b11507903088a5000c8008548012208040b400b076800321a541340c2c001400308081a111846942000c0c440c285aa400586904050601040b08031109000d041124410000b90302e625812500541c40d9459640c0750344420345c6c0d02c1c5410041405000f10017001c444000d014001004008152900d2503d980180d05c0c80100c40c10004900f03907440070b030101400c40c004026105a152141d4401640142c0d4181251000000003114401691080601c42801d070070114110008503c0c0d141070b00e8010f40101c03040d404641c14240040e00520a00400a109003610808030a6190265000000440b600f2034641c842d40e0351034002038007075408912280c81c040e44c00000640641f80008001d03000d20150040e82d07046948200900c02c0039400b400a00d80c25110f100000150300f03100b0780045100d2445070780d08071040e060100c02c3c10315050240c0c1001c1c454204240040c803217002c001601401c501940c01c0503884a84803140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 209082805 1250 209081555 209081557
    0x9090f0605040506071205010b0301120311060702101d030316090e0112120201200c21040305010c090303211407020604110a030c180b120106050102060f0601081b 71
    0x100081005040c0303400c110a200b030100f8620302c02c0c406600c0714900e1170a02807094041f58000d0003040300f506414801481031003410000742080364801c2c00c007240195110110149071903070464400c2c0040e40b224040c90070b24991401080303482c0c2051107800c1c5200f44420400313030312030200612940350560801c400301101c2d8880c4100d9802032400204030341141d611a4444064040603107c01d071901440b007400c1c001c080b44141f140401d02d606c10301c1d012045070f50b000c0a008003035110703d11002c034a109100d1191071052591261b1035410b224000c2da070707503500d1840c41d2013420340d00e10030b0b4035000340009240708001081c0c000d4600070702c0d400c600c04071114107421022207100170000701c15a00940d81e886402c128071942c00060190250f03020b40e400341f00c415516410000d1054080c04010040312110104000c0c11b020040000003800040002054581031400444c8440711941016501c0d603464030b0301044207580600c00250410300c410091080c03480d044002070004c0c64090207410141e0440554861540d290340 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 209084055 1250 209082805 209082833
    0x6050415060c08070204060b0706050f071e0f1206080610060906092106020309010e0c220e0708010c051c0515060a030b130f060e1b0f070804320a0909 66
    0x1045027511001d003814042c00503d02100e4800c1603a82c0309010444090083d0707490f94030310494a0740300c0c0201905480403900080031507000b0041c841745c110300e00a5440d450080c04007404108009120516106484102c91079003a03200d1030034030564a505001e00c507070142850b410b03500950030071100103c104000c40e24500c4c1002d00503003d07910100a02c1032520303064104006098142040b524060410301c100b059010740140111040601030b03400c0c07011820141c0000003504c150b00195a005569190120709644070b0f00c1c000c1d000101c0000701c501c60f40012042d4602d280c40e40754400c000c3c524142d10070111165a00c08854401c440102d22050b100748240c01115448074060b00d030348441c054080003c0040c01d056107243c25250700b04000400c0054842d20240e220750320001e0f8041000c000e0110116190f80401c0e40d02c032503680700300445004522301000420040040304109104000c0c2d4801550200b81c2208501c105640300398800503032a41d990200c541910001400055071090a10b0b105480440f12 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 209085305 1250 209084055 209084069
    0xf05070203011b0e03070f17030c07080601060206010803030c0301050f0d1703090d0212091207150c030f0302270604090f0207050c030a0302070918060e0106050415060c0807020406 79
    0x842e0030f424101035500c1000314035180d403a1050440b5104082507201d401a014540014038a450108030540c2c0072950606145002070035281340c0131841c440103041c54419009a00d2550140300100006541040f00300c0c0148129009917040d81031124114a040c80103128a5100d034021303c0200b40035954000141c80d0140e4031400c00c007681c0d9090840384c011604203c13a0a03c990103410740e81d4807814008140008280403d094452410014504005801707610802640062090200124003a0003a500d03203448061152560041d84041c1c1c42d00800707101201c1ca1805c1014014040c0030520034401704069440075281402400b03034400d00c4045201d6000341d44c4002901410303e0203502c030440c015402001e03214011000c0e252072181420901d580c80d840f1910040042e0300c080b10030000d4244542c0000146030090b601b14000c010207859000076a041c031038490520703035035408040102d80303440d1003020181e090754080e01501c5032810101420449040001900e01880000c85404558617980080050004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 209086555 1250 209085305 209085311
    0x170906060f12030a08071d1c061b05030603061e19020904090c080706020c01080c03150d140c15040b0c0a02030703080a08070306120602090f0402040617010f03050c010f0507020301 79
    0x440500100510000c0c1e4103440403540c1f91004403040c0001c400315110008020b0400c44800000141a4007448020f103419a0840d40e141d1811420400d0301211560044469803040e8032400c20f00105070900da000341825526009102c050314100909100c0b0580c0081e0401c203450500700d100400202921540300300580c0985003041300c0080011009800040d20724900c122460a5205d8105aa65180c0c00c20400d010600302c0c400144000d070014001c44d07001c142210300100b42907058022030034020800800f1668120800d02d01001c1d01010003a5224040040b620f33100185181e510846141c0300b1030180307a01c090320000d500304294008015220f1640e038040c1c12a22101d50381c2c11f010341aa00718502e5500080c2c15803011414070b078031034050b80c07080c0c50b248290780c44a964107568070b43c02540001c0e480e40d04402529100b800030340d101c3c03014100030703c41b649900c40c02c4100260040e900c0d00341600701c00d5003210b40600c10302c0440c0c00054801807a800c01e007001684100f281340d05913198020070384000d40c550700f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 209087805 1250 209086555 209086567
    0x90703090b0702160e070206042d08030109050a05010b160606030f030c05060f07021507030f0f0c02010c0507120311120c0901030c020120180d050a0201170906060f1203 74
    0x20380018070f48a400302d00342d00b0700300f1580ca0340d500c2e000c040c2d010f450200c0141c0c803000108001c140d140c90340d481c85400d80314440d401d880c42099100b071042e03c108ad042d10a0b800100040107103980c18002c1c2030740308090039000c010641c10040000441d0081d411803410501554081204002e4035500c060081d43e0060a8202e04000c1440c000344009503c0d1350803034490107403901051050307203040c20b41801a4156000f0781080e0820326281071021000800660416494a00c8850b03509660300c21a001094441008a08103e640c24040d0075281c2011404081203401c0090390081802020b141c3c204810501e404201620200305118280c01805550362400c8040c8007844401c003942402400241c1080c0c82c05e000e2040200d60503401c90728221880d01c901c11041801d18071440301e8100038030318244811020400d01d05280e0100d180f207c40b4910440d155440344092009668000d81d051084202c48540c1c0300319032406c504103646801d4013030901c0e401246a100d00c4407050b0b864804903290200403508980c1c0780c0e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 209089055 1250 209087805 209087807
    0x1101110f0306030d02160b0319050a0b01030b10050d09060204031e0507060504080d0e032a04050c040302060417030706020a020c0f040c0f050d110307180503150402090703090b07 78
    0xa0720030b846030303482446004c1d9600c4c41c650011031103100491315070007900003980c5800520b00039503100500320385903031141c42004065141e0380e20610f40a0b0610020000741001110005421a0920508a031061014a0070101126808400c84040c00f251f014086080122490010080e015541004140c020650700011300c3ca400e20f10216040d5000d4411940541d40d910380907113803031081e4002c010854210000c1e901509024041da01c1214070041d0032551500c848120207551640350304c42c092a240001c00ba5080f4030300d86406000d400030764142c001d6240918560014920344164132894000340314202d032041491400b4015902203681054040d55281102003000717440c2e010140720305100d10032186101620341400c2c8205940b60846449907908a030b50100300f640e444c0c0082c45541c00361034594035040c0e8030007403810155000d03408503164044014a11050403569912540040c0e019a008069003444907031003c040c2c540242e015502e40c0f00c251100002100a4990000b020340b1030a81d51003880212 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 209090305 1250 209089055 209089057
    0x31803030b132a080708180c06040902070507050604061b03020a0b0a05190b0f010e030c030d0906080108010b0303040b030a09020907090510021b1021051b191101110f 73
    0x2096201d6001c603c4080100e001c0c1c41ca07290584661000072803000004482402c03007201e0a1403410078904544404d40c0401c001149070744903402030f41101d07401050580400c401008268040e0408507502d5080504002d00100044004000140d65209600c00c00041c035000f0b0019545282e0051801c015a140001c042c03c0600310a80315900b1801e12010070b0801c030700852090340000c1000400d440301012109004582c2d8031352420001da4113000c1e988851210b0b907006c1085101b4421251101c21409240c5040a058040140d100900c142d0404448141c42c5d5008011101a500381041c035503101e80b02c06001c1401440c541c4070081d0080310f05010b00100c69000344c000350440314100c5003070102d054440800c0b6120701c82d00d1200300c1e51001c41d0f114409113180200e41d90100703000600d41000b0b640f0711000415210505808036201a660b0351050290300b11400a0703020803441110035641c44d143c04203846400e2400c501101e1410010020140c20a40d8000c1d0071800c46008440c521741d403241007522034a011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 209091555 1250 209090305 209090351
    0x1008030705010c08130b041b0b16060506010906080a0c1214060a090b090f1b0d050402030601091413020a15020615030c1f02010b10020606010906031803030b13 70
    0x8118008002010901d80705c5016900d80da00010b100c0850f117480d40c8400e548844d15000c600f2000038a400440c0400c0e10034094034031180c1c0040c88000d40169810620126032000d04034604201c003820080c8403094001e030f800340d0401c42d40341c400614201d1090044501a130307a00c000c900001c0c18850222182d5005001c000c6c0079040c21215038842c10340c0c1b2641c0f4011070707000c110148d0b00714220400003a5801500055180c1c4041510220110120568601011a40203e030800311540c0d659080c4801d505040103043d01601d51030404101400980500d82d40c603410041031108505a144a01000c540750a109076000f041a0001031000001d6002c0103900c44400711040c40600152041c50360103450000f420f40c61201c0058031017010415035201d414426051b404003030055649620390500c40e07842d00c44000e92243c40581c00340800341414000103114032450351011080609043c50540c952030081807900030723250b060500255003914407021a81d4118003500c0f64200328074000c121107854202031a9884 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 209092805 1250 209091555 209091557
    0x7050a0b071407080a0602090406170d081617090a020915130c09050112060807180507080108060105010c03020f0105010e04051e060402040515040c0519020714091008030705010c 78
    0x250b10030086840c0d558032681446140c0640d0701152a40c408104280d00501d510000500085112611042500651040c80d12000c0341e0b41c1c00320241904a9900c8032034250891080480c11000c611b0041004101e442e50140005482002401245024200b040000103059000c1d01c030301c40d5072402030f01d07285455407402040b600640301c00c0f48000c4000102e01c150b03c42000645c840e509114101001100c03110300160b4a0f001c2c1135600d80020902902c10000380740241814401400c55940d000a10020341320080c0110b002d01580740c005010001c004603405040d1842868030008031019802d0491514140fa400030301740b9441c0000200b20f480c080e0310aa44214061012100e00403d41c400c030700e86144550340d5014040d0002e80c082001450150442500600325200f00e000000d1280b00080454443e0072401020810010b1440003901c018503d11900d4056400500002860010b017543c42c42c1d0b629888a100b10035180004209518102120b0041c080d040200d944a440303d250840c02003000b102154 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 209094055 1250 209092805 209092823
    0xe060a06050312030a05060a030f0803040204180f020f03030d02120f070507050309090c07150b040608010e060402120f0a0305040603050a1116032a0b0105030a022107050a0b07 77
    0x45031600300020100f00c0d108015030010302c1c694030600c0b000000c242c0a0b00c805c6d881850854000042111a41081c20440c050480c8030344e0f90401b0b104000c111049428904500e902c214800b2011510700e14170814196010b13a11201d20700c0c0344000103420341c0316282c14484060320108518480070741e4029007600c00d01c3c0842d00c962898860b0b0745c1c00d82d0203011700701004000790f00030005080325003000c00d20300f030b0408541c03044d050500c28503945d5900c18210810301192495600e04c5008060714040c00b96400505140c0300800001161300c00d1a515420700034006402080912481016a141040b5130703566803011078140e41404000c1e113030040855009120391400282003c0220300310f50590701c1103084907001071601a20b402110350650306030304592201075081c008000f60306d0b883c60030540b00000001c100c0240a002d0070041e46000344a420040c0c0009000f0ba00c1104440016102c0c1031040c0c1c4140500b907040303100e0303a083d405100d1400d4001e070881500000302c05c400140c06644200034000300d0740b1500580c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 209095305 1250 209094055 209094059
    0x21f02131e0b0c1b0607060603081305010e0307140a030203011811010e01091e030c0f050a0b092805040603110103051506042c090307050d020303070519030f0e060a06 73
    0xb00c200d50007000046405a000a800034060300c0b4508a0608884006050681080042d81302d960441c1c045900c20340311600009000350f1034468402012001d400242482007403030b000703003011960307ca0141c02501c0c400e03000081581401e80d02e5003890001150300800a100d00311111341d204014652400301125081a54003001c4071940c002c0400112004060b518040c1a515107018031922480c1c030b00784080d50708070804c0080041209030b0748800c00b170003040403084003461601041c4403400180740e00012080c64107208441c181d940b0b054241c9806038124007100780703002640c5400541d080e00d640c0203950140c0340041c00030400c01c2900c034142070040c01340c90410181d66600701141d0f503c0704100d0500d0303101c00c01300030512a204408886d014000d20724903284400103035031003404000e203030299003000581c1e02c04116801000001c1080640e41d07070a52010354114140034801800380e000340c0e142950b895610302900d1403401d129070b100c0600302c51200b00c103110039106800d1a5071201030580300d031044181003c01c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 209096555 1250 209095305 209095319
    0x306050a0b03040b070e0d0b0403091401020f1507050c240c0315090a020702120a05070f0609060c03111906110408030d0213170601180501030201021f02131e 69
    0x590f44104e070482602c00403070f40c0341d02d17041b40c24030070070800107504c50341070f0444202003000b9020880c40784d8801d4440b002e02c0307414142e5600d15840d02121081c1150301c44402100303811008540ca4601c000c040d4044006c5803030780c1c1c1d01034800e0301a02d840c2c0c0e030a5200f41c000f184402814103a503140a401084480704040d06c2703030500840c06110071660300e08881c420003040c0c442410f03d450041d034443c0d4000340c01230618542d0341c0010940b2525500f22074440d4001b04030a01845024400c1400400d8080709094580d842c01e400a055a07503244206000c0c845020702d000181400350240c0c0b0846610708080e00d0403c8000c49130021b6100545031306031030007072514005500c10700411048030241e903040740085040000e04161000a58001c2c0182e4200d05100000081d400560110455905510740042e06039903041016503c0038400045888003150f0401c001080940d07008640c2800a80310710100d0089180d600303058501038415441c10402004801e070b80020707001011000070200442a4802780c80c0a581d65034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 209097805 1250 209096555 209096557
    0x1c0203100f18032102041203021c0201050105010c03050c01020403140109060b030708072108040b070308060907051b12130801050c0f030609070e0402030c090306101a280306050a0b 79
    0x21000b000b00f51081c0645480e01d03064401c3d0311302c103001148058074068449401420903641c0d00e03021400b681c080200840c12840140c440300f141125480204080e61501c1c00080900e00400d4015052000c0003480d000000c1c020b40480d00a1600b00780c8421400480026003030003041e1040041d03800c1450600e21204614020545000700d540400052980c00e0620518141c2c410300d0201c803102190300b82501c0380c0050066006000144001700782d40d6280c4030b6030b0402420580c401050f061190100b10100154a500001500c20307202c44e040912112025076281c461400310384400c2130082d41800f2500201c0014417607161021741d41c841009200d90780b10091405960b004542d0088480041840000c1e02828155509684468141350010002440d000401c040340d100380c070100040400003e403405103050800010341c0040480c1d402c220703c54945a68000586642e01250203071010015074801d03d12030244c2d0546040b20007100f51403c1403c600301c0136004200500c600340c0580c1c0e24080c00502030003030b10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 209099055 1250 209097805 209097851
    0x16060806100c0b0a180f0c050109090c020a0b1e182506030c05040e040f02040b0609011e0e031c030e06070207050105070303230709050d08091c0203100f 67
    0x40e11169003615400e00b00c00140c01e54500c0301d1a44246940d1180200302c8281b002d1040c240251880358600d1304010004011301c400b41c100110f500e0800c0400040c090380000c6000d1016040b401d10000350712001c012203440400103800311002c030609020300849951802c4030f04408000c40c0200e800e100c0b00d10010400c03442c20004c20075003c14180300d0411031580a41c021301700b440ca03103280441c6003580350040d150050900743c500340c07100d001c4e0b90f00d00700850400f0311641c011080201c400e242414610000205052001994100e42904805144140c00d0140c502c200b0b0094005060315194069401ca1029038402031012500090522000300b00540e808201c09010308080d40c003504402e401d24005645a60144030214101541c1b00343da08140011102c0c0e580725144031803e1007140b41000c01d801002500a60000c1e44a10070945251000a80c00004c40c0e040140a076498042c070103014489220314031168102a4060007014040ca14038011507014000034000703100200549060919a485c51074015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 209100305 1250 209099055 209099063
    0x20d082704052a0a210b01030b0114031f050409080d05010e1909030e0402070f0309050f180405011b08091605010906050306030a05070609180504051e16060806100c 72
    0x1440310050840c0f12402041c41010600780400008203140c0c1c1e0030b124641d402e2241210550380d1542400540c1d140c068544400c0702403a01c1c2d400c5d107441c2c001c5d03c0c3e8944000b0348000b0103a80401c16640243e140704070b2200080030001e0041201300e0840c1020a03907036000b800341021003440d00b000840e8900001040e640151440c40003185985040b0707180f81c000b4541a00305606020040141c51110f50b240e00041001500c90040c04411029501e0b01900e100450f401c100c0c0700d990840c8000d20a5102c0703044402054040e0340311141c60362a1030515900410100000b8110001b81500800b0840d40085001c0e01454080007119142c40c16100740715144192070013000c0c0094000b21003041143c0c4a400919081000201a510002d9031356640a2034441c4586c02217000c28a103020410002c03492042d002700b803607800384091125142c0365440d40e440b0803841c0c0441c40304040c24500002a28010015045004410340c070403550320ba12004090030741c1000321004cc1c80781c0c1d5544107984115114550b0b46a9040d40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 209101555 1250 209100305 209100361
    0x1140109150b070602040e01030305090112110a0309080f07030513120803060607050f060a0f0c03110d0c050d060f03120e0906010806060d021201080c011b020d08270405 74
    0x108050a102c9a1001e642500c00d41d80070f11010980329a0a40424004d510035203805031341310701e0000090080d01b82440c1011107945058109041071200d80121080000e807454009030071003140c906561907000301000003003100c8000ca510020590054000c0c0740c988e41409010700c2e80c80da00d44542e000a07200c001c00510800c41400403c050341071402c041e284840c400d8003510052070015040c03c0c90700504135961460280c4404001da940c0c00303e88501e0700101454502405446044010902c07148500c0c400080c01a50380c040ea2246244a9800d071490b15029500500c40d195880d15900f107000c0040c00103076200c22540448442440c080c1540c0c0c0c980082c040e10040840d81d42c44015140040c000b004260484010000070b00541e030b03144000c00c1c0d4840000c0594120f0f5041848440c502003034881c2c0903052003c0c0e030940b800c0d12410b0404200816a048401059843d0103203012103d9024514030500110b1841d400e4045042044140b4115000262401c00640d554040d07800b050280d8200d00d0240d940c6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 209102805 1250 209101555 209101559
    0x90e0111041505070c0302030f010c0e0f0105090d11060310050307120b0a050703060801020d09052515050403060f0e210a0c02030c03060721061518080f0114010915 72
    0x4052400713413074030b10300034100c100e44140c0e40d80210f4105210310782440c0e00769540c1c05104090980156140c3c0300014141ca41c6081244910006081c1e44a081006445519581820010003259a0783d034010b940d4003420782600c0f420701c0c10340e044182141d802001c4c440d000e4080c000c2002e046001c2090000c54111611a026031030b690f4070600200409042c0d8410191511408034040d603007400200290203031844d00007015031640c10b00b02c0c02e00b083d807449003071941e13a074004540c010000b2211040c16580039506946030305042c114281c8a07441030f50f10041110b800c0004e44450038001c2d50090141c00c0040090ba00100d0700700d441100540700c90855099080400d100640e01a0320850800d6401840a030407201109001c00000b4503200040380c5450004501004190703080e0380500030801c9040d84080180022030804403203000c0300643c502018200041c5100a2101407400c1301d011000f000c0c1c2d41d0030740319010380d940304490180c4846200075004214030030002410901c03502c0b07507040c2c1e0210388107034010440c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 209104055 1250 209102805 209102807
    0x305120f04050f030a0206030117010501050604060f08090a0c060801060f0206062d04020304060507090b03070c020108040812040503090a0f0317030402060d0608030d1a0f0f01020102040906090e01110415 89
    0x3018903241030340601c0703604174a02c01a101d420045000e00700d4648116a000301403807032142034500c141c22060081074180b10802445800041480e0300d042d80b824400380503652a0038151074000c00c1c680107000030030103200009034070b0381082504e8141c60050380c842520508039001640e40703503001c1e030350b41d5000b81c41400301a40540c5220729040c1c0f411000c07000c480303d45a05000040c1aa08141d505803861641e07102448404c603000f01c0701c44010718202900e40d06628012101400d9140101c2000e41840b00810000f0100b100d1581100c5003c1d00700000d100b5281414186642d9940044800b580210120140410b58100c421900c07800c03264000761a8103030410003d40c802c83c42d00050000c83c3c0001082c440c00e10b07110014000c08000d0406078005684800c40240b95030140c0301c0d000000c8204019132034010240b84c446052865244100340c1d58070301c03141c09650040b8020300c182c0c0e02036030500d4585540890020402e411803800b540c040c400901500502c1e110880c5603200b079209141003920140080c807445 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 209105305 1250 209104055 209104069
    0xf0c110d0f08221b060918020f16050c040605011110020f07021008070201050f04080a030507200601030c08060c0a1b06060e0a05010e0907060e04020c0d08010305120f0405 75
    0x1241000011081c03101120103041550748103003070200d55200c01c1c0300c80e0b041851241e0340403400174501898020605407400c10103850149410305100301403500020015420304800007102c40c1c000c000940031091031040e0804c01c0c0c8605916004a1146040040000746507100d40520340610806c10f028000d00c4600411260082d403200c000d0720f0303034544240001d40150350703070005d58201040b05480d07a41c21450151002821079a0090a400c2011061400e00c07010510000c02c0d00c90341502401c00045039221450b0696020030b400e40c44020400340001141440c120200300c1c40d048900c202c605001c5140c6514145e5100c0c407048a071a80205000c0c4541311590344210500121002042641c00c8003280c00d458500a4481036003011040550400c103011021220b481020b00502040540b201079050a01d035150711a00144228030402c541032196503010307074860303044a4001e42d00310704a4445400a203000350441c00709100507115030090780e5200c7c0c090042c0f10210741d400c0c1c04c1c1403003440c50141000204a60 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 209106555 1250 209105305 209105311
    0xb0f0a050c01060f06020d11030a140a0c02131e0209030604030c170d05070e041a04110c01090b040201180e040b07050d05010b04050f0f13020309100f0c110d0f08 71
    0xca0b40d2202000104086440c44150103003500354068403000c40d0090303000d8540340d13008001c0200380c1c0c01005604401c6600507103803078082d504910308030303034901007a00120342c0361174000006540300301d40c00c030120380c12812640482400e151700c07840003850350100c6209000300d00030702d502d05e0340642112002400083c41350904803503191007251406c10010364402d1a2703e06810801d4220b040da507442040c41041a00144c1004403002d085406205502092840f400c4291240e001c3c580259103845042d41804140c3d0191151034114000820808030700f400c0030105a10266426404514144076282c840301c4c802144000395240c00100780019100c981d500741201000900c0c01007045010701c20618a180c1c50b0081074000c21212000a454a080c03070100850040442401886000b400e07003a61103a4446a0f44540c0c030502000c801070b02c0e030303a0306003507281018802d450201c40b181c940302d00d4601510701030303002008401269640054100d1150f02082c1d8079542410002e01054000c105091200d1080d420168 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 209107805 1250 209106555 209106577
    0x1050304231f06060e0316061b021504030b010b1303030c0212030304030917030a021903030905030703090609050402030402010e0d05070504090c0825030f02010509061c05010b0f0a05 80
    0x203242462194404110354502e802254416107070507040041d59802628080306010440150121110843d8022a80c2c2141d218100500422303100c005502510614106400d580142149400d03848100c0804500c0d8061b020444141c10050000b050040301e503400d660000d91002c4c1103031940344c00e5440c20f490300d1503130b031108030b1b0320152946490110300302c00c4c006140203074880c1c0c0300c1c0012300d030400400743d901c0311040110201c0c0d80d01c240201601d0940c00594420084c2160000c46890626800d0480140c545070401401e50700c40051588101680040c0c0c01e0200d440540d501303d0352a8443d01001b040c0d1200382c5000e030003d40502e40d00d81840c43c01700d443c034448502c00c20446940c0d550312401700701030314440c131001d850740f035101c0c1c004200e030241c24800100c07804c0110a10504141146044461240c0d0314013000d0009001c0900c01c02c21640220101c2e2410301c00180b8840d190703580f24460201142030300841d0855a8200380001440c10284c80a032418489403403401d0b03007000c4d80480c0c1122242c00904170a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 209109055 1250 209107805 209107813
    0x8030a02130311121b0f030a05031207092111010903060c091409040308010605030415050f0103050c01030e1e03040506041203200a02010f12050718050105030423 71
    0x1500c0c0001c00d4031a0004521500c40114260700020402c504c1420408052410360040714072481004400100304080c41412903104098600c0140401d2408030440c1c401003040c40002600e0520b6044071342010310540d402d51354003c0540d1a01e041c9006641d43c3c4140307880803c04d8030048030002c1e40442e0044e16010040c58072219503541e0b500d034141558564000c91004c1081010184440d01e00303201c1030005900103803400e00090400303030740041621605120703440801c4000720116040140f001011100204004405e00003410045184800702d08284000c03556442000c3c00380d2402c1d40280600703441c40000764050301901c2d101154204410b1907007182200f190004010220b00e6569001c0070f000a4400d0908001810030f6514006c1c01031030707044d40d110700f00c0500e801c0508040300e40020f00c03815003542803034032104080343d014040c5c403c1c0701511300521341d260900040001882c0c1c05900036150040320454138500302c0e0b03994010341c3d044c40f041d6000f80042101c00198400041c0c11000d0011a1444604032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 209110305 1250 209109055 209109067
    0x6040207170301051c0206071e0606080d08011e150207050312030703140411010509040609050405060403090b0a050306120f031305180106050304020120160315050c0708030a02 77
    0x11aa05040481e8000c001002000501131405c0005807030090320043d000111044003150005400c600031240014140100802d03044041044241821407059100388103201d0907884100894841ca0201c80010000710030340000243c10301c80c42c1c4802144001022514000c1c0d040c400780c406d60b065680346001c15071190301000102610704000019124400590240e00c0381400d400c000d045e84d0415540903803100b0b908087c480032855617611041441c4007420142e640d111450046006020981e02004007e850542044140000403d41c288a0b41c4a07a0b0780e105100c1d03c840e0480e4a82c010310020400060f801d03c0000d10608008545411076110442202c848803c1220380718a1a803000070381200103a40f900b0b041149090100384c1081010099103c0042907042180092050200600107410040103c0740244520b90141382d00101018000944019151240c000003c40085100031240c295204c00d00d00c1c00207100e88602401118240011454a40d0039120789295410150400c070703131550b08100f1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 209111555 1250 209110305 209110313
    0x2d030f020316030e1213080c040905030a03090312090503030402010f020105011d0a020c1f0b0103140708100f121a0906010e0903090405070e01080a0c0e1002120c0102090a150f0806040207 82
    0x2414400480aa012400c41c7c01c20040a003002c0880582602a50601209500143c0040181e8254541c0c1303240000e51085a42011204095500848000b40380360070380742000c0c00404001544114001e80761014103801100040703089460034401c0c803081d9034841503000e15002c1d032600500e07000341c0610009400d082d4100c9129052a544c5480d8501b070585150028011156900a03400740c40002d0034200256002c0070b00c00590688010100420801d45000043e6541c200341400000b4080ca100c0c0d9200302d588410070b02c890701c00303070a03800c2d540380155000c400e0301c10381c501050038407503400360020708010303460500c0c941c2c40d001002d00501c040b0302045c4503004854a852080d107114079480d540703503d003005000340050311541f0094169001e1078280704615a40603040503031059107402c20b45280d00c261002039000c80c2002081d00768541141000241012140c03815006000142d408a07400c0c03086594545081e03174944524800500414550070510300343d03c1c00703222116403002c8068805460b10202e56a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 209112805 1250 209111555 209111557
    0x609060f0d05010f060309050607030e03071a06041103102114061611120a050f0426060910180b0f04030207050607110f012d030f020316030e12 63
    0xc0007030740300e075a580100000e2952400c800e00500403418200980c64013601c4031504c3c2d150003024041816102d4541c010784986c03c1007103030382d456001000c0480381584140424480c0c1d00545000d8800c50030018030510783d043c16411030b40259043c0d10075190311860030089400d503207910303103100080d0018100c0c00d00104003402c000041000720480640311525160030107403002450022000e04002c00544d0310150554006040c903d0906400380309501d480030a8011115846141054101100089000602d00c1c2c40000700c0704e030b00f024000e803000c6800c640c070510540da02001c8802ca00541d00440414410300c0b1107500094201c0c0741d18000140081491300d440c0c02c002f000b91001e040013005d80d0100024168103105000180101312650b03461305002d41c451100c29010003100900c2002c14900c07140041c0e014265500b19500c03180b0146420700c50704800c480b040d840c10f03034036440824105028201104614070171a44108030140400b42c19114843c1308034010080c01d440404203128100e006000080010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 209114055 1250 209112805 209112817
    0x1504060213080c150405010e010c02031c050306041b0909020d0612030806010e0306091e03040e010807060e030111040905090a140a14070317220312020610050f0609060f 74
    0x401040d6852255050000d0109005604c04000c1800d1105114a07a80b100200c0b201070024038004032460039900010342844403017600c841c03200c40c8581d050500940c021000d113208010403103041022480a85000d440c490000d184c0700d0000d87e07040d50070300028074154058040144181400180240c940c0650810403210600640202c0d210604011031580d101c454100000415005000a23042c05045990b9640380796825480361805003884080315201007054600422034182e480f0003550b99090391945030507180c05050001101148201d130282814040d07041c10358241c1c1d030a03624092400100138020f18010300403c02500541074002c0c081100c0c40c2c1d4814201d102c05010f800340010b2454851020380b1882100d10090f00414400c001140f281c0fa01240000c107240040b581d0fa0403040540c2d03060090aa401440c1584859004428000c0410005043c1141c2d1340844103551115040c0c02001c05892050355801403201076a198907007032950144c00003d00c040d06840c240500746146015540150b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 209115305 1250 209114055 209114069
    0x40b06121618050a060602030d021c1407090803030f01090902062205030d020a0b0403051e0409020a17090d0f022e0b090c03010303030917210106030b01021504060213 73
    0xd02c0002060b03500c030f4070035160001400300007080840d181a00181d228040c40109461459020400c40b0304060500c0102c007291210340020049818428920f180211080c1c079004006042e80e8400f28204900108681c0601d40702402101c3c05d81c41c18086030040d01103204104d0b0010400e0100450604512801c001001c9154450170000c81c1040103040c0707003010410110f82103620020084002c5254043c0054009406d0301e002651400105228807100d40703680008034101d00000780000b084902a4040d03c103090640c3d0301c08000076000003401d164500241c030701c18026005861595195801005260120700e0039005880240b240103c10300c640d103c0d100b041d201409540f031844080c100d1940f00c0c09030a03040866103040c690502c400c0100300707400305000050506580700700010601484442009080d0074200080e951120800d0011085c000a403104003540b107407071000070038224000d01034141500c80680c0242400106020310f1803080c14098819a010b40c0d00304441280750807003408800c050008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 209116555 1250 209115305 209115329
    0xd110c07080c040c0c17090603010e0f1312030f0e0708100c1b0b0907050904030f080f0606070b0604090f0b2e05040c201501050405040b061216 63
    0xc1d001480c0e0410b80c24000b901d100e58a402280c541141d00712000c0c40c1c80301e0700100d0700f01c800703008098401c800e48100480d0750b510850210001507903150300462180304480c061401d611030348403101d07102c1c2540740e5640001d11001c0c010312101c50440c481c0c0c6c890088052746c0c000101e864142c800019041401903007000d0f041e900035503401600e03c8858003801c2d00010061a1080f40340542e0219130310110290784008000c8405040400c0c500c010420080b009010300400ca40c5d840d04040c500641500340c449004008640c00000092406407010741251050790003070109450505c403aa10009085001010701c0c0e801540d03114840041014490414000b07407007404110590305003c41c2070b500c0a803180074404c1940e0b9025410280d00c6801c005104101c64040d0740104d01d9140e00c1e030041e030b64465010400064813803481010322589400281d0000c2401c108030180500341d0303c403000d00095400442d8007a0205902c400426550304061304221032000c9050306940c04a4210349590b070b01d00e81c061780700d0411909 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 209117805 1250 209116555 209116559
    0x5010b07051203060f1201020d060e090c0906300610031b0501090603050c07021207060e0303030c04060810180209090c0909011e050a09020d0c0c0b04080d110c07 71
    0x2410480c00102110714058a802c5240c05800141d03802d400c10031545c0594002c80842240c506c094040d14086003d0348000d0081039201c1ca000c0340c1d42141215060f44500ca1015035001a090200810b4040e40015000c01994003520042c6d20000e1400d01d06a4240360250402c030f0341504042c01454040c035190102c130740003145581454a005402036000c2004d004011408126076a08822071400302d8009007004202c1e69101c0c46a030015000e40c910194002002080d4030b440e00d1004503502081e100c0c541c56040c2c4114101d01410b64a0200f2140612002c0017000180000c5004860259105482e0701c508554261245130b10b00001c40208044003a00760045215400b61414400107548011b10302c03506070034101c25030300048072401d042c070908040c0d51180c603603c0c1c0c51300700c1c000004000d0074018259541066660003410002c0d40b0007036094803c1c5103040521901548690340e4103444541105081d4140e0700c950710340d5101c40d80486803c02e0065524040080348012902c050460751200f1409412518 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 209119055 1250 209117805 209117813
    0x24031203051806070804060204091503060e0a022407080a0206010e010e13120e1e032e0b010e100e0306070f0906030504021507150b100503011509030605010b07 70
    0x40001c1c001c0400c82c41001e500701c0c00d184001892691140c42c500d40744641d81c490b424030310001d100e0f94004180045c108420041940b034400c002d502200d1041004014001c00a400603441e8040218005c0d80000055810700c18101400742034040040c090885038540303074056a80c42c1551b403018000c40c1c0540c1013503004224030f04280000714010644048001981e24008001802c1e4491800000b412400c4d02c200d240c0b10716101d0404a850014043c0074030803031004159803100b0b10760182800901c684a80f042c804014007020342c520441c06c02410206000d900c00c2d02403800501201022181041002d0b48401c0842d507a80c28030400c14070181e2115070031900d0a4042c142030000c0280158140a03130001c1362000340c0d60002c41d14080720302c02e1070300090301c2d142c40c130000c0c489071425440b1100c4440046403002c140640022040c103882d808810402c041c103802010b110b9900e08003a00320011074420300c0100403102c0d01c81000104a503641c80d01511031501c80d1b550800303c95082c0c1022407415400304180b400c01c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 209120305 1250 209119055 209119061
    0x31210080c04020910030203071403090f0f0d0e012a0f120f020d1d0406030503030601091707150e030607050c010c03050105091611030c28051024031203 67
    0x107007000d480c00d610305074203c008100c2c00203c009044040550010008180d43d20030b440040074000d07000c80655a07070400203400c958072101c080c0100d41a0040c1b0342d0000e461440016100b155002c0c5458411240306140d00640d411601205a004140382011551004510080d011b070f10312407003186980505019070074111105d00442c200740e01403140041e1114210707500000c0542c1038050603d02116614803806850b4407010003602400c0d0403504200b4040200600800514450482aa6605002039403a0442c80309258000d030320306400e0b004484180300c0801000e0b400300810304541441140041d0840c0401d10f000012940500050008510030801205c203004d02e501e100c40b68902445254186000100180005000c40400314080c000920fa610301860010f00c4901a00060746c5d198100d1614442e26011400c1c0108241181c00007088000b0937500d00c6868603640080041c02407114074080080204020a43e01c0021450303480e000750010314008403070303002d03520030a41d0031840400d480001e425 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 209121555 1250 209120305 209120323
    0xa020a030909050f010504021b10020712050a0c03031d03070c0303031104030c0b031308040905091002040b1b011b0302130e09030a1805150306100206070c020d0503121008 75
    0x21607041005100400f0311300c0190505440c02103400603501d6048500300300300305050008210007801502251821200f02d50302074112140203062030400c2d000c202c4401c807003520840300b1850100b9011000c441c04644661300074075030b0700b220311800c89504101c2c030380c0c9502d190448130007210742c003119820600425074107008200755001680c40172030a05007565a0040c0e0b112150050112240f004000038210800d064503440e51070750414101a41d03030f07440c4c0300007a020308011180203150344207005501001003041d200300c804480d00c0900700c9042420341506600e00c00c84488645081c0d40d00c4241c0088901ca40c20032040d400ea038aa1801a581d05d121070244d060303448141d03c402850300b0003004201c8030b00400702c201e40300c0c60100d14060040f96005055052030710304039004150040c600029203480100060b00860040b88100c031083c110440d40d00d000c0341d40c0c0c0700131100b840016040420b440010700703004401100c15842a001d5a0418076440314502c00520308503140e00d010341b05500b040016140030301101c41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 209122805 1250 209121555 209121569
    0x30a0213060206190e160f06020f0a0b06010309030e1e040b06090303030105060a09030812011d010f1502030d021614011103072109050d090f0e13080f0a020a0309 71
    0x251421200810150b101d001c06131341400e844200b00300c0c1c8400c06100061903803a1110907544940e4072003150340d500c1c208034042c0300701520400a101184070000900000200c1d0301085100cac103a62440011800340c80422811010b00512485100d00307641e5100005444405414500d580740704154204820345003201c81e650b000e07070b5082103046102e8a002c0100c905544007070360710503525281d03454200c41200450748080c00303254000c00c40324001082003180c01e0495140a00c0b29074429444400c90b0b036510004c1c451420300440620341000349038205040f00c1c095089a006403030804503000d40100980e440b07601048020107109032304000300000305071031140d1020401c000304031140004038142101e120181500b4140545074480448031002140041658210700780144074080d0640b61103a5900140300b00c07100407804524011442c5800002c03000e0032190031590b60070543d112582801d0840c2070215041d00c40100030170900400300484c000900300340d034040c0c0c001d03c0042240d0400500035481030300556 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 209124055 1250 209122805 209122813
    0x8070e0a0f03060b03071203051201050105090a03020f010201020714010c170106050406030203131416090b0a09020c0307140312010e0601021e010608070303050c0114071202030615030a02130602 85
    0x44012010301000109596010b80005039624613040024944041944803c0b81c1544c03294252007003541c84000340204201c0e41600c06010b0740c81d1801950103010b442d0800f50407500428040001d440c1600000401100c1030000514000442e244d0b5035050039001c0c5c0000060b9150000314400c2c950142d030214035003d016070050140e5040900090203482544582000c0603004404603060342c50081e01d0407545603102c80700b5000c07801030b0000d80392500742d04080c4071900c4030300303800001e101c888034002c25003010001002d0f941d1140c2030903c181c00079001452880c0040c071062010074002850600038848043c1450001e54450340604100c03004554145c002942c04404002441540c0c0d070001020003200101040b00051521210652401007110794444460740c400c410002040c5504200100700004a1078003d21520b509610410300f182c4d03050f56113100107000e210350080c90f107200d030303025640144004000c1017488094108000e4184c005a590020081d0300182c01200c0c51141d0325081c00501007400030b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 209125305 1250 209124055 209124059
    0xc011e05060315040809090103050105060f1e1311040b03011703040f050105030405010e030f0706060e01051503150a06030506040e160b0f0c01020406020705130218120a0b0708070e0a 80
    0x82a180d183c1800b400d440401c414010604201514041c0d07489620064148409907940b404c003070b4060041030b0349007400b500b501c1141386140d050921102003c0d0400c00c01c07003c41e600761501880048510059070003c0789030b41e040754840d0210303020001c10040c8901d00e101e41e16541089840542c15a00d4607041d1583d5000708010403051308104424030803500d003400c04a0312641d89040ca1400340841d2040c080316130000103113442c0d0a41c07101010300f400034020641086042d864640c96800c0d04020300500381d010101e840c100516010b014002d5500031f0b10342600d40010003205010422101040d04240c002c2500c517410410365040610030001840035080003440040320150803151021224010044150b0002a100d03e196120030b04940d03c607421800210750301c0b50348000082d103458450040510a4001900b22032581e4440d0007070350701034803020110402c03050b4120708208c40101e4003854180c0a0003145602d802044130681024401c0015440760041071410540003405444030700080c40c49400e09000c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 209126555 1250 209125305 209125309
    0xa02090a0603380f011401080903040b16050f0309090c03070c06020901180b22060e060711040c030f060506071e020301090b0907081203150409060209060c011e0506 72
    0x41d0342c000c11095100c4141043d5030500588440500c142c0c04204106070f028020b501e290100322504891900c403403c00310900c13110044845050568240c2d850350f1003408140040c1c2850001030100950701180f03250680070580e1140d09100c3e010071601c003d03400200341400d250600e400102d46c0885d204068514500c1c1c0103c001d000041000f001070a04d903404602240d181c1d000310a5000340030896540f0004560b0340e20190310903640f181c000600703140d224482d1095804000110b0300c0c180c8640c1e44606942c441c0010501800d900402415200f10341020b028008035100d0b0311070802c039000c441e90701181007150b203401d00080e90515880140100410424000491512426810b1900c0d0620005201d10020300000b405010400f0300a041082c1d15814080c00740e10008003141155000320aa41d40b248d03065000944078082150294031480c14103a038580706141c6a4008810140b05540060600b80300b503000c10300c1500018450302d0560354030039224201c0b0b281c50003d400030186118050080b4544140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 209127805 1250 209126555 209126573
    0x2011d0322050316080c0105130b07230604051e03092e0507030e030a02010509040207030201110f0409050a02040303170703091a0f0f0609070e12010e0a02090a0603 72
    0x81880301c107403007011403a80008980c0d00000024100102118140d02c0a10584460030042d4800c101d424800c1d03010103243c0c1d5000d00d090700d13854112255011500c030f02d048d44010f6907a0000030101c036500982d00c460440e14500034600281e0060b41002408186080d2a0181c40d001d034800c0d90362900300c03181404202d214000400c5440285065a881c0181079414000445c680d0104401c011400d40a08140c4c0b006503015014041c9140030380d40e00420035402105054558840c402c029000070000c0190b6100c6040580051440c80d05c41c0c0300002d680f003120302401405401001200c07030002000102080001054024181c2100c400c036000c40c0b0703252950340c000c7c04128103a000c444042404900282c0610b003e07600000c100c0c0c2e048000502e880040c00e012180c510001c07107066040c04101004109203203c504940c5214503405003030400a034565031425141c0c06108100b460b4442c0c039040b403881c0f044400380500d0003070191940040c00c2c0c0784018030400210100082040b102071b454030004101044d0365a03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 209129055 1250 209127805 209127817
    0x20f100207050a020a06020a1a09060103060b060c0607020723030d0309020102030d240e04200a080a0b10170703080a050904020c060403081e0402150910080702011d03 73
    0x25800680e20790861600d1410825845406503114480c0d41c03001600039004110501038600c01e4408080b0800c1c0f4007108180028242c2d041d075110341c8035000601c00540b441e448a840000300503e602d00300184c81701c03100d1030302b44119651070040e000002c0c104400440e0394100052001c1c80802070071804a0000400c7d83e980f1000003001c00c15441e460303901c09590092003201c51441c0006801c1c404000301040c00342c1003030480d81d42201911480d00c0c00240c4208c08400080c0910703801a004102681d41017811030018050302d540c6035008138000c10004214000300061209e80d445001000703540d02d8401c180e1ba05044041e80b100049860340400c0e104070003000703d02001500d6011a22a46032140d03900101d440303001d4500d01941003880040c003080402400205540306500c640d6070001c07640e48800038103100d070013048044007444840384049001450429410042c0c00140c2401d14100303070f44a03000611021815103010007080d11801442001542801b4200756580380b4460004000305403103582c1d50f2407040c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 209130305 1250 209129055 209129083
    0x8070507032a0c060305160e03060f04020a09060806090f07050a06140d05090c0405060103060b1803010906020712080f010501080414070506040b0a030510032f0402030f0412020f 78
    0x400d00c803041c2d00000840380b46000c0c1c0019032011000d0301c40e9806001820103403074201c41c031030340800c1482c1d4031340c403400b43c400ca5544060040d01741d0f81c80c0c54444403200b00b0086e2040781e10104200003c1681c018900c0b400004054601c01400d0608100d0003076070030401c0700c01140800340c0101c001480b5a07203944c00140c088440525203620301802e82c11000849018504800d0f031654140800d0102080c000a0400d10071881100e0801c01034070342c1001501121140d03c0dc0a00400b41032000c6201c902d540c4401e5001c038034000d000814580400c5e542c000807a40810002c803201080c05114000b601ea000110b103601c03c00c055600d024a5050a002900c403000081004003421902d0b4603007031102c90144400b4006040182035151501d459158070342d0507400c030f032882c4000245460001101980e00f04502812179411202c10008001150713034a80c006580b6401200181c510b42d0418841e9840c0c920042d44941c001400c0705002e81001d16045080c03a0950209500315400340e071440c030080602180c110440c50038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 209131555 1250 209130305 209130347
    0xf040803070201090f0b04060f060e06010309020102070312110d0c02031b030109021801090e07050d03050a051c0207030e010f020709050907080703060e0111070b0a1e050a0c0807050703 81
    0x40714001c030701600b80900000c01c403412120a04080007400c2034400d020342d1040406100702c20288505104440c0d0398800c1e686411107003c082100c550180d885419940c2c018030503204200d40b05e4035900034002c4c011a400b0001400b848284070301060a100e003841c240000c2c07400c003107800e401e0380000390780c0c04144080d400c001d99107258401e80390340c003544010407943d406440464559049034a42d041801b0034411000c100d400d12602001c0c403640413440805843e0020400711240d092501c2c00c0b81c01e608451945404d0140c20040c00c42c010b01d2200c003545240d800100056561080e914000300841654130b00c0605001488251141c031640100301c81003541c8402d600002e6a960707000d10319180c041c0e2a84144d03103d000d904d502000340005904801d8090b0740f5903000f40f156010709649207029208070307080900501c0140003c1411124075812405854403100c6003113240a50035180348044400c20344221203a1580c5808101440350084a495030080e0141400c0e401c0160a440c00f07000208400148461000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 209132805 1250 209131555 209131561
    0xe030708030913090501051503010b01020708120c1204090e010609060b1207020c0613030c0b090102030703030e07030c0e09060606031605030604020f0a0809060c28210b13050f040803 80
    0x9002c2c0c1c841d1304101c0d0020300a0185007426140d0304008068601206e009500b421021811940000361040807034500d1801411001a11802a00b55402c100d4101c60750380913442100110314101c2000e0400380802c3c080004855080340e0b012800c540180d880389001500b8000104504c11031582503510303103115252001520358907001308030f040c1120001c5040c0d222901145803c142c1c0400c2c0402c1c0160381c42030056030710740b5880d4108003819000d200b1034140141d008000c4c0c1d0b00043d00c25000302107020220003c0740c0107a5129540c054820b07140d40c0010702214054010807800d20010841c550b00315405440071441c3d0f0811700419a40c010760761804001780a00040810544d403102d0b411a4040e10b01a80e41d2500c80c6442d810040a0303041c1502e0f012500c1c841e100104000844000c203c0d0440004040c14a00c004a03840c40b10701064025510001400404240341c50071100c0c1c03a50088060000510002c2c00a80f80c1d01080f00c00c04c2160310380c1c9509440c0400b0406042000f240481e00079811000b0b180d140c1e9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 209134055 1250 209132805 209132839
    0xb07080c0c04111c06080613050106031205070b0f06060d090f06020d051902091c140a080c0d03020f09010c080f0712080601050a0c0221120a0e0307080309 68
    0xc0700a950260700039262141a080400d080400740483d03401c804c81002182c400c0d02006020385540b401040a542c025202065558900e130350342d04201441340c400413904903665150510030382c4c004004600881c20001b00b0700100403003a50303003d602000c07504501969041c1030011820714002c0080b00410541e45813441c1060020490700d194640e94417070010340d95501d002c5a030310040d040030f5480316003018542884035200103181c002d80341c2c10b2202411050320386154243c0344402440030707441a51400d500d18007194601c0360602c518400203010311130603030f51040362801d8145084881d0414808141c41440040ca00195030b80031a459400c0910303004800d900300d4144070601d4444d070f44042c0f00c0c075000000c0000810a85c055121440700d00c540741c03e000c90307803144010754161040054600000d2a18101c5030010700d02000e0200315030040d00da104220200f0b240310289084218101c05a01c0c01c004a0614100c40e80302664003000314003600a403034040c4c40c1003a115941e0003803210b514410150140843e0b80c031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 209135305 1250 209134055 209134063
    0x7120e010e030301080705190e0604151e0f060f120b01090f1211010504320d0f0b0109061a0c120304081206030f0a03050904060f0608090607090b07080c 67
    0x4082041c01d403592540d4030800c00d07950703407424030466008825180c030480c0010804e0038040101d40ba5206034001d20b03a07030082040000c000306c1542e441c1500907118041007000c0000003040d003015055041d050318a092400c5171071294200d42c0100200542c443d5031440181e445049441d0100d0b07240c1020402d041c3c204010f07612410240c100c034042c41c5a0110008010024540b50031540d4041d0b40c85004040352180112850702c224003d84d0241a00740505505103085420b981c00204044082e10848119040000d2064020460141c80400e41c00b8188403c3c0010b002d502401028000f0b0304210b9246410201c2d5004640f2030864600000003107110300794200c0c18401031065210104075903540345000d1030b003146aa00103155110251a44800107052130900080b020b0b41c16407150001c00b00c3c15039075035040b2250782c0b10000140e0001d4580000090444400e01e4407001741ca8551103241d482e10b0817220052030300300000e111104002c80e035202044413403141c0d804c40b42555006140e041d82c0f0760700814900d00e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 209136555 1250 209135305 209135321
    0x40e0d020a06022109030a1704030905010f0c02041a030f0609070e101214011a280b0a020105040506090a120804020103090b010b0903010e280c120515060907120e01 72
    0x4c0007034032010000d5100b40480180000762160303c5072440081008030140620703004580003004642d000304240714560003018080c001c90700600c1c19440c6ca4426034049801d0700c070104802c204058001075030701080d280c02c1c04200000802c0c0b000400d428038100c607286a44240034410700d00000c88400110340d44c00c0102c80700601400c40c02a070b140c0104180d10300069501010107420696518001c442d00340d0032101c40f40040a6200206100450840003009040c03840c40703c840f03040f414082d1340002071401c0700c0c18003501d0f24100c0c54000007a18545402c10340d0925800800f0000f082e080b50b22000e00040380894101803000780c5140c1000c850703407075200581c000e009154014101130844000019200301c000003c1100c40411347c000e00075600070084103544d40047c1510900c14480d08000c20600740c9480c280a61458040c90a402e078003a6100110051401205400d58443c0c006102d01120b0100424800e07070054029a40342c0300071b00d40104018024014040312501c107648035808601903807000d401201e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 209137805 1250 209136555 209136607
    0x10b030c160305091f120c0c0212010608160e0705030a0905061302031002040b120c16030c1e1a090106050a1805013303091a0402040e0d020a0602 64
    0x140c881c40605001e440c0303401070003880c1e100300744e9202504500a01114803031108040b5072101804070101400d52006082c6850741c640800c021885040f0141e51501c0c0c0d074168a0304601c00024825052208c007a08105c150140155a1358104401300046451075006036440041c40c500940c490310b491140c6e4005e8503c4400141c8603100d01c00903c8510200c107038152034058402c03402ca07204a903400c114082070303000d184580c480b07103c420300003500e01e0384072040259030140c3e07692006403400f00169031280000a01c04402d60004403c1d030045410401d65030801604690100b45603100c0e100f0780c3e51032403508401361401900e05451720020400460b82500240e0240c0b030002e016100c000d40b92000444502c055180b0b00c0350741c5040000004644400003e0401c0d0030100c0c03841004c6241c2c0c2c05500600c0c4080403815541010f80d079180e824086a00d0707080900302c200c0c40d0074101c1445c0c18903004020694204401c0410309401c104c191018150b00011400f00c103035071000015880700c0944104108204600002103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 209139055 1250 209137805 209137837
    0x506071a0709091103090717100b0d02190f050301060b030406020a0e0307090905010b12060c07260406120e061906150e010f030c050403030827011e090b010b030c 71
    0x540c0150004000d1481000414100d900071941c2d03642600b00c9423500491184203800180c0120b0043d080c982108086a07400703482d102c0300d44015070200300c034418122110404940f0b40343c000c0c0a058820b017400d1000b000c040b0002d10a00f0309210090500348000740000b4a90b540c0000c0d04415203002d011158007803480101603400d499907800804001d00804072003200d05510700186003445192042041160103008801440300e6030300c54003000810382c00864241c520307600003074415102080c441d001d0703019158040703a102d03191450b240f006812454900382180c062420a11700362203500700026103640c054409c802e5002c1d0701c0c0c08154080001c0003d5040311160900c0f00c10208000c07034110020310440102a84c4078000392000e207104404076076054010400107102044100082449409116000410b0011560800c02e20103201581500402c8080900d0394680c2c03400644104000d03801220160b1909003402800440d80d00c64071034ac00140102c1180450200c045800c0540000c10303140502035007202a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 209140305 1250 209139055 209139071
    0x301090602040f050d080702041d0f01320a0b0406080102030c070c1208070201030207080c01050421050c06011205070e0f0f07050a020a020409050f0a031101060506071a070909 77
    0x4034080c1d40140215041c1d01c0d408400000c3e5818100b01d800c20b6503400c051310382d007421065405c0101070015120a66000c60851400c214004020300c407840c49501d060700006201d001c024500d0713034010200c04074a80e581418040c04031000c0d401300307000c0342d0040ca00c100010344644100c0000d4020107064002078400d40c80403040207501c44009005144060003003400c0d2000b130f903580c2d0740860101c6a8210040c4650340520103040154041e0f00030b802a140321348100fa0401103080344507070031990211010394039541c1d0400e120000340f184401108040c0704c030b0729141d440e0401440120b40d071a501072162241005e00304170244144181070040c000944501030900249042010030214500b00070344420301e514407904080740c61709009600306c0d80c0c0840a6005003d250034581c003084000e200d4802c0036200741c0a00c4200300e1040005000342010b03603200341c87c1d0300c4c1543e0a0a0710307a4215180790304602c3c01507400300300381d078042050b1029598080000c1c0c000f202e80303503441c2d110440b60040240d0204041ca400d10f100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 209141555 1250 209140305 209140313
    0xc0216030c0e06030d0507110d061a04050703151404140709090f02090a0501120608060a0c18030506041b05031b010e010905010509270709080609030f1b0a02030109 72
    0x45101216040801e02c0c08503100c40c020562191701005121700411001c1003444000341d004501d00481c0c0f0001000025189650784608042c3c40980300c000640d52220000300249142500c03a80d90003113241e24080145542000150100201602440c25500441c0040d4440e55903a50014051404845120045405c0080d000780528100d8082c12394804d0820000640c015201c0c426140d03400780003000381c26501c1c42d210055a400c14210350505401c1e8441d0b00c0130800c0e8030308200e86070140010030380001c0ea8002c00d03d001000032003900680c0c01d214400304820000f040c000648550442e0308105c002600541c9003401c030444071101d601c0590180074085100454a24220304407022110a8950301c05000d1400011a1516218010980070400034848241c1608101350301c840c4600e20340c03c850b42c600003885080050101c0494101d400118042020b00c01000d050082c1900025400000c60400d041000c074000307940260400440c05219002803000074040c1001450001d130b0f000380c020400c071401414 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 209142805 1250 209141555 209141573
    0x708160302060112120521010e100f12060b1c08030a0609140a0b060705100b03010e03030f070c020109170d0e060405060f0c0304031709030c04090b06040c021603 71
    0x20003540580612800000c00c1201040083d00c0240c1c01020741d0800d0520910544a85e00000d403494900d040002021415110742080c0c80d01802000c1800720b114540ba1003003517850354058011041081d400038081040c090350107003c0400c0380e4040300200781d001d030100114440081000031110602451541c074018041c000300250b00036101004140507842d10b80d170000341600c860280c5002c2c41034103000060240345447d4405410030400600711031801740d180e120342e86402c0100d0b00b903005041d0358049808882c41d092182e1250700322818041d606600c1d0240580845400003002442448454400001160702c02e00900000e40f00f0105284000d203103820102d0341e2080811141004118001102d01c140e24003d41070b50204d0384020078942c43d0503804180d03a201904800205942c600c0f090201100040844444503610542503c4161312031601c0001c0515001b0f1400d807840c0194585004400420f542520059012809803008518400a00400c9180442410060184290200011041100c09a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 209144055 1250 209142805 209142847
    0xa05042301030b150406060c0b09030d11031618060c05030904020a050706150f03020111010f0203041b050a051e0307030b0c070302060907051807020304030c03030305070807031a0409080708 83
    0x2c4610a42c2e130b0018414841200c06900400000c1094551020000390b400c0711050341c00029042983d00f40f000c0c010403802034482950080c000c0000120806c91504209040380c14245020b240903903414900940b8260310b0210703802007004120301140e48101703024040040313820b0444003030021580d5220040d0300403c66003100744200c40450810400c0700841c0b078160810000d80e01c2c2d0394851444186144c5c0155050040c5a401c0c22042d502c510a07114441c03458800780d8400c60192000254411014122802109207600000d00c0b8030090b0320140b1441d1108030f854464503200a40c45011540070100007480c0c071511307500040030000307210104040c200340350000d05034992003a001c59083c1e464140880391200017070700581d03410000d10015001060b230400513181d00501d4600581340350a03180e0b00d13030f20719215842d001070f030100303440384140a042d0380d0000e8a15031055041c41c0070407440801064890801c01c0061320248a00d488041050500c1404d82c110b4001581c010001552500b50000e1008607503024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 209145305 1250 209144055 209144071
    0x1e04050a03081c0911041e050f0402090f0f06060a0201150f090c090b0f0306010903080409060611010903020a3c050c03161a0408060a0e070902090a05042301030b 71
    0x10311400f0855810343d008107540203034052801010141c100d420f000003000c200e144454aa2001c0c100400020814426a40115a076880c0700d20585824014481d440700c0c0900150203030a41e5008000350703200c0c001e20164101030b00f15812665081581c0080340503041481d03440551520003203000800ba10042d901c07100f180c11a520900802c100e40c3c006451101c120b20800f500e0b01001c000c1e10b8450105176001b5135001b2014140740d44900d071a510381c40b0f11030304a90080802c270f9680d40014041603821003210340b01c0380600030081c030a01529031350094660140d080010801e841e00e00d56102000d502200340c034092143c416040101182c400344603034081c2d082910544c5c5a00604c4001d0020b4200821507a1f440c1402c3d02c07101c40d905140801c1c868880fa86c1d10181a15101e0038480410080801d02045011385030200d40407406198547d051030502d901d075845205180e03c10041d414480e01c88110200842c4d4040b10002036150031003180301c048030140026a500300384e0210002c400c1000f0300b03410502070380030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 209146555 1250 209145305 209145337
    0xf052b0501060e03010b0108040615080a240b18041103120d050903030f01030b09010209130207030806030c010f08151503091023090c030d020c030f030406051e04050a0308 75
    0x480f02850b003243c14404003540081c14510018012801d2900308103000c04021284c00440e0b65250001801c0c48281130f01101c0c61803228038483c1204100003480d43c84480724030b00030018038900d240003d07455881051015022214600000d0500c4101d0241e803500000190944000925200400e00180d000201d45071036186040b000c249160b4000068901c14500e4000b414110390030750720382c5240e045004101102664080050440603294010700091300401c000d03000d43c4542651a01922481d802441c0b0350081c0d0201407905110307a802a134401540c9254100342c13400e51510008411031103a005111500403024820f005148074880b40294800c0d108101a00c80420040e8200d02c280e90780c072508024240004000c00d0034000700148043e400460b1101290b03000c00e9128003081c102003460760700b41d0140e009681c9404960505202c0180c030355400c1e5000d5464203040c014098414000d00100740105601e00113451110103401e01114003600d8000c0c60b4420b203903503e240c40800e55208071288a15401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 209147805 1250 209146555 209146577
    0xe0115030c1401050a0c0f080708042402100f0b09040b0106140403030207050609190e09120306061b070b0705010606030c0c0507050f01050906030c12160f052b050106 73
    0x140404058000ba80140d4880d881d012003002c040700c0b500c02203203041d01c0c0303c050a8034100010340058000c004082c07090031525203840c40c0100b03100c0440c84a5880c4400034003110202824243c7c046045070080c181101d002807131207245103501d002010f102141c00e41000f0801d0900c01480b4852040a040711869a0746003c0c030040c040c003909a40c0103920000300540e1295030180500e01d4800007400c4181d0025000f902c001c043c1c005456510500350b40061021a0b44005200000800b44200032040000342e250500e182021004150b4900c03d40c0e1400c643c2110307000c9000b104002c2480b0707000041c40c041c000543c40e40840d042c000d008217640e1050b40003191401c1c045080290140e00841402d0b07800dc030140101c54130704018041d221043d644840d040040c1000160020781d180703006140030300b03001c2c05440d440300c030454034001907050043c0c889403285038848250035000c1e51284504030a030180b490000e0326011402021324440e1081c425810030310403005003090741d500310395010380d040f9a0b0030b540c0d038403883d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 209149055 1250 209147805 209147819
    0x50f0702120a0507170a031406030106030b04020f06071703090d08090a1b0f092013140103090609031110020c15090703060603300e10030e0115030c 65
    0xc41c200380344400300600c101940d440c09034002d081100e008150308041d6007a8017441c3e008982c010703c079480201c0c1c1e0791a00c66066800f11040241e1000c020b90003000705504641b00c00c07480e0003008100038403800c0e1458030f43c1600e80710710007940c4503168000503003040420b01341044901900119000107651181c440101841480380110b00d0284000b0170140c0410700e49030301c41903808000d85400d2900c8480403d0005480b1444150340002449100c230000b41c40080800080d9034030703a81038040c041e0f4080074006c84800100124405080302d883c4100348810303041000040e006400b021001070078140c81c08421754241a00403140001c1340320f000c400c1d1502803507140310401c12030003003420854550b4400e469400050000308040c1c3d0704400750008644015070307240d071210103a0f00644c00c12100e4000c45070a840035171059100c4264510020b601c0d0a0401c42c0c0e4500041c514456043c51510461240a4107500703540603034400e141084811000748441d08030144403140b070710b200388811a5030b148081400071ba20 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 209150305 1250 209149055 209149063
    0xb0a02030705180d0b010602010c080a020328060302090411040b1f03150e0411011407020117061201141504050f01050d0804150201200c0d03110c060406050f0702 71
    0x41c0056141ca82c18400404800d070721580724203440e280c2001c0f04440c0400440c002030980c50091a0542c004180074450000c02004407a01621403e5524018002c7c45680100610450303800880103000103403c0b0003200c0164044d0141e40e0000e07400c250304205000c1405851aa0f10075010000d8801b401083c403413900340803014482400341814617400342d140c5d6451300c5c429084201e80410002500c900c40f61030f00c0101d40c2c4c15600742c40c111400c4185070110400c9580044944c0e202c0c4800c04076640c01c0c440726400182840d0b548140b00c01d0800d02c2e1a0000b6a01c0e03681070703082c8480c090100c00801c410003800e0305150034410b05946c42d40984131418210001440d1078080c0314429804652036001d280d20309000e00842d107031440e1007112988014400071808624903100710044c3c05090b4008254185005464a4982c0f074211040300000d40800202c9403c5400103080e034003a5020380740000748456101c2d01a0418040c1d0222902c0a000740414001403100940250380a50008011f18a05858100c401e984e2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 209151555 1250 209150305 209150311
    0x605030303060d060b0f13020403030e01050f0a050d0e010c0e040501050a031511090315150d0506150307080d051e1903050c190f022a0607050102090301180b0a0203 72
    0x80101c810f51040d00088594010b00001c800c05007101d04002c00b240300190041c41031640e1078050545c0030a04109040d07126031100b500c4402030809924100032098400c0d410302c2403548000501c04000790f8020f1120740344e40b102817007030400c00003000400c403048002060a1100301c1a184900c0c01c02001103118640001c1d00c0c1c0403603074406003420034a26501205800b83c070a06495100c0910f050007024804e0318103005082006c9001008507445240c410000203c5024006106000d80308078410000082d800260441c2c07c150940a00c040071024040040d00d400b1254014100c030b07020b20301110185c50340000c050404000d029008103005464985c01640070300505400000c404410b52032400d00300d020358421600500b1003045249803400c21030100c440e028400d1821000500e201c064074801940c140b00f0101148401c2806c40081101d21440b5201c1505c60b81540f0b01c034400c002142e108018095040f070707000010140c0207004110304200280c0581e03442040c251b800c8418400020341540071072003160301c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 209152805 1250 209151555 209151559
    0x60504081504150501080307140607050a0e0a030c090b21280c06091d060f1003020c100e100605060301140d0204090506070906090302030a0b1b040303030906060503030306 75
    0x2184003071140c296600c80801a10903910600d4200c074150407103407140202400390018200135680e50629142c00819076088214810b1590041014401c51951010881c2d03040d40003032504601e040743c2840082c07a802015800100110000400001d0307280442e000107010a5044032002800d070610440700307044010251040b40585c01440c0c100300000e4440701540d40500100c00312031301303103403c696400c1d195440c590410b4010888000040104420540340d510758044109900e00b814108078002c590044800100c0700d200d004103801c0450310911960585000000d4181200c1ca0950190901c400801904a81010318011110701e1078620100d8041d5104441020704a10300e103078030b4400540c072800c0c004071000342e01c0b0b41101e5001d80980c2c1ea0780210f2258901500281c1b21500708040085c28003c2ca903440764007840f42c01d400030805030790045040668960029040000d56544036041c0404103841c0804803807030900800e010003416410740c805909144151020001e15407a103041680d00d020448c0c1c030b0b035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 209154055 1250 209152805 209152813
    0x7080a030c020708120d060501031b080c07290f0403050307050304020a050613050108060a061205180706180e061020120d0506040c0f0302070314070b0f0106050408 72
    0x20265109501000c0c40441501c182d44050351a0b025080c1000015400c103500c028000c102c034003400459110340001010b0900b001c10040301d90308901d00b030159002017200d090204940c0000c11002e4000c003195242c0307034000d074606188048420461406594025501250060100054091465905074500448d0103468150456450b19411501d9500041c8101c1e044150002c00050603280d083c0604000101007840d014900c0c02c01000600304a070040c00e5038403800160310200580783d0001c4a0b0295802402d4020031607139100240460700c81c0550090805074030911070005025070b803181001d028106130000700c048890366a00c08144182c41501c2c120b60103290481c10109842c002c214842d50040c1c0305100030866000c0c44850380c00c1200f4041d03000040940041c806807200060f201d400c1d03100108440c02c04c61100c0c02d1030001e2000358040001c6007070560008445007810301410b40c40300c040c04001c034119a01c0d503082c54240b100705000d0319440c4e01c10a6000000c5602da024405503815109003100030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 209155305 1250 209154055 209154067
    0x8040824040f150603050c040b1e040f02040803040602030c2a010c03090f0f030317040b180705151b010501060203030a020703090807170f010c090510031b02070501140708 75
    0xe480c03250030000b02124048801c164058590780203002c0c890007140648003400c1c41d03281403000e0100780c91040d0403452041c842000d00181300102440607903082c400544000030200c603502d01d05002889113070084c1d4440c1c4004640007030a0f0340c2c0080100b41c00600035083d15090a140e004812004544083e602ca0308018007440100e03551050080200841c000d18041501b40da40e80e26070340540400740c102d0300c00d40203000d90134014150071000c040c0480d4904001d002d0700340f400b6215405c1c9551b025101c400d039031100341c0da4600040010080503020740001480d51071041c5800c940c0490b2035100c034a40c00c10200342c040781102c04010610410b8104c6000f074000d9480d681e03840501c0c200941c480300c4210140b003a09075002c2800c240400175000502001c02c0302c1c0c500802c40c022007a1030048040780b14842a81000e5580020541c40300b580021034100341c0700001c0207001da6100360301030042d501910019190501b070540b0354542c0020000e044070310a8a45440040134403001103024802e101c40903040c0d030001c100ca = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 209156555 1250 209155305 209155313
    0x150606070201120b0406030309061418090c1b0703060b0607031416140c090912090609010306080322140d0b0603010605060309070f060e18060f06070804082404 70
    0x180c02e5000e03901c0c3c200014038003c1c1c0f00c000350440d10741d40c01c00d40001301a600140000ca800102018144001c0b61000d8180285000c0c1484c20b100b00140c00f900507920500400c07150b0704a44180e81030440c02c0d000040c141c020340c6901c541e854425200c141d030301a05012f0400011309240c0c5c111a94290540d80f18404041c011808420a0b41300c11000103640070b001a0800c080785010031861001c1e00c2500140900020b10307820410601d0009d80b070110141c016040001c0c5102d8020204c0356440700030b1302e440c1d44807030312000160b00400310744e8807500e541d0000040034503180c4c00023300b050810000040c9035075496101e01c40070300c030001d07803004084d003001d010105100807402c04900745e40e01600c001c001060075030729900881c200d07030400cad00c02d4011507100ca24103000480c03d600e12400a840c0354034000e40c02e4603540c00000c0f41d210110050324502071900f40071a6141d29120140d48000c800680b00756550034903440c10103421341c414410a0050300503071089001c3c00c0c80c08071204800540c00750b8140082d0302d680e11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 209157805 1250 209156555 209156567
    0x2103050a060e0a090c090c050c0105060303091809070315020a0f050c150a090f0f060e06040236070e040501080304060c0209180d030203010e07020f07060302090301020705120c150606070201 83
    0x80145c42c66500300c0d40000d519651070083e00705544560351003e8503124050f903102c0c251040a8400c80c481e0700244500c00441c0c69420f00042055850f4565031101d807500b20fa01803c0540072380001d0105402003980344256546a00180ba58010960b1030041481c4032000898a50158550018482d00921410301440b000b104259410084013070300051220302c9a51804051000c3c017038222a6504c1c520511420711400e80324480c034a5628102900c014a050340c002103d8000380c5402c0b00f8984004500c1c0c06146440c4140b071030b19558010101102410b2504d400b5000620480c1500e114905000010422602c084103070340442c1c1d40c0c1e0302ea42d000040c40f41e00f0001442d800425448540c03403601145800c1c0c0c0420004000641c00a07240180d03a54100398480c41c407038200524020665000c406808042c040026a0008480c41441d00580701e10b600d0780000c1c0a03118100014001c0e01c00d02600c0400c08042000804000e001c840c101d81d40400f8800750b0700340f41d10040707900b01c2c2c0c8101d09205400c00b55018031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 209159055 1250 209157805 209157821
    0xa05010303230903010905070e01090b0a060c03020a1205031006090830181e03100c090803040f060e09040f06090206040e040f2616030c2103050a060e0a 67
    0x2580b41003101583c0481e003114000e010903a801c0d030018104010240310200c20a0152042c2c200500c19900d101c030204120348130b140314001c100002581c01c001418400e101d2511110b5010460030001005210300a180741c1090760030503c4503c0c0c582002485501038040312044030f141c02e001e00317420900c0700740342c1c007191440c00341e0714076a0a003007a50000d50918071402003400c103044441c2070390108000c805000445200310269800940300c1100744866030380001d269400010020404500c4181407041202c60007036903480546135210104010a10031903610a44051300c241d661641401280c1c3d00030490228815140603059101411080c00815480d810000f84680040c2802d441c041c0c0d646da44101c100000c5030309845501402104d00c04201d894042c1042c0b4131081d5200c0e079826007088046072070a1203001c1d19544844040325004041600420b800b0111a0300a0303150350741050707200400841e00840b0301402c8002881d04000400c25081d5224002c155401800011019900c02d016200149468 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 209160305 1250 209159055 209159117
    0x10b01110604080f1b2401032003030903010207030c050c0103110412081207030f0c080613090f02061303060e0d080a0c090915030c140f010c0f08040e0f0a05010303 72
    0x401c909011161010a081092440759008100c0c1406c0c0164000314440120f90f00076021101c6001000031500301d02d9802d40d00b901013003000b025410a0317800240785200380001250107500201c0c100c0185600450076060381c0d40140c00761041240007000440450b01e01c0300004004400c00d0101b07118141c0c062051020051107190803d00c3d19034401c2c12034405000440e5504002a00d0b003c0b8084421901e00030341010a11034104038003079042c2640002c400150520403040c0070f40c0d8420103032041c840a410401c1519070068800f603954601440706080703038a0031b070005440c000d08204244d808e0050000300c1719582c0e0070907900c10126445201410015110f205198000c200701103c0c0441d00141900c02c03545800364441009019600c4d500d0f00c061003585039440380c20302e2402154540da49032640d662a0201040910b040700c07081d0400d24000703550510004000d00512000704010074040008880356000f600310030b5443c08245c4e1400100707400e03200709000090013301d2007201c08010180c44805100e00e0010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 209161555 1250 209160305 209160307
    0xe1f05011a070c030c0f03030f080105030c0111030415170f0c0702090a15060201020a1103130303030e0a0804090b04060509090714030f010f0506011e050708030601091206050405010b01110604080f 86
    0x24076180c0701404a03654006d040245042c500400c10990091251450201302d070078440c80b158074050020352079059101c07600c2d041c0006800d0030003003108144100c5001c1c20350344c18110f6114042c0200100b00c0419441e0700822080440c01182400c140100d03014455007660700c0301898440c1a60a01803a210090300014601c0e45690462611758080e080f81c102420b0164001a15008080c1300141102e81404034282c01d0f0300100b00c51440300410826203000d0381d401d82030100c2c50410481c60307d03190072040b140c0a0061030010401203a41e802c40c0d040320910040494003808947e4484040010607a015100c55681c0c0d4024a020040c0208040b10840f101c24010305076545d807880c00c0507590039076001410010b0748546d942e082080d03030340c3c0145402c02c07400048441002e07100820384000d002c62103000005404100d010001902680c4102c030540d0241141e0000010b0300c02441c6032040181105943c1202d2950802c20140c0b0103500c20741840510340c08032130017000b20340c48507124090981c0c0910444482000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 209162805 1250 209161555 209161559
    0x206010e060d081620040e06010b031e01090f060b03060603041104110f030a05010b0c06010b0d090f05030319050c04062a0b010303260705090f03010e1f05011a070c 72
    0x1900081301c0072040c0503c0c4a1031074003002540c1e0710629401c6000c1c20384111b00c1c02c2060b10041c41c00003455419104d50840030b541c0c1e601c50819410f0398a1600d000c03441e100c14540008503118845810541405020074011311019803a00c0c2a021107000480d03019411080c2407000038042807180e0302c4580f5104001c1e100190442e00c10492051948c01102c8030001e800c030000c06d01c994002940300b510300401b01401c8040c1040b030050542619030806102c0d4201701c140c04149450a1b500c158001050b00c1da10030f0a02c0840d02c1c0354504907490f60000c035002211091509180c410202c407500541f031141148075051b5240c50300b0000c0a0b515006070401884d0501d9400c000c6019a0340031646440805010740c081d904c240d8950b14000300401c400c0158002010041c00c00d04103080b00018070203802c41914104140c0300d0034183e004c540c911a042e010b150b40356003403644520140c0001315505540c0314002400070400c400c00120f103000d4413000c0c13003a051142c0341d041d8246506120300300a040024490351180030311035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 209164055 1250 209162805 209162827
    0x18080105010f05090c03040b160e060403060614030a03211508010203041712070c051908090f12030901081b030c0409052d060103020d14070905010206010e060d08 71
    0x614240c0100724840000c0e0380c180500e203001c2e0741003503020524605d01c03031441c07030b0940d189040d00101400132981042d640d1801d95003d802440140c10051000d040c1503110b50703690910b80c000d840940308020002c10803080105036820049911100380e5015124440b03c80b0005104030f10341c500101000303039029a152a04145407654401030f9006041040c00561641480e0500c05c1e43e008405141c00c0d084001000000c00b20002032401e5030384012242400340c001f10071400d041742080b00c08500c030145004d50780c0c2d08004024141c0c0c06400003c1c4150365841c4e0204509050082c0d07811b85140d40c02c04c60b40113100c01010b6601c50001182d03c0014040c50b118441e4004002003000d8205503440f00e15a00c010406100a2507944a103513846404403c3c84100005000f8101c407001000d03506074850341c60380b0300010355203034040d40445149040750b12041183c1646100301e9840303818180e03039500005101c180700080d15840001c0842c141c41d69440c140440c0c2c3c55600c100103183c0840101100c260b241800140030030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 209165305 1250 209164055 209164061
    0x1110f010615030501080a0f02400c0c030c060f02040512060a0b01050316030b0f0316080606010201051902030615070302100f0e0d1803020901030c0e071e180801 71
    0x42c5050301d107050401800000103001d51360140c110410700d5000340b0348400840d185100204007560190746419019100b501610801504280d0302c600f0700700c6a580242c041014003414400c03888035403504014101c1404001c030385500c0d00c9440900060203400800001c80c00c070f0390100507007044022006107400d580e64003080965460194141e4150000001c00400c0c00b824011880302c0e04003443d01d20320b0751804c005640b45001c6d19102031010566260b032001400d44485095013682c00e0010b040311035900d2803c15042c600411401900603a00032900840c103154014003500340a90340719080080e0061a2188180c025080105140e0b03124003484944500c11480310000c00700d01e0700960103006840c015401d448152082201144580e519103041c04c0c22005003c100300c44030071054075000c402804c40e10344c412007144450700045d5000b500200004204030f507090b03007801200d88840020000e641d80f6001a100250044001000903020320245103e07644140aa0f012001030000c4809c0150b4a98581a0071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 209166555 1250 209165305 209165309
    0x60f09030a0b011203090e060604090902040f050a022104080412170a120c0c05070501050a14040b091201020a0e090402041d0d0201060f050a0608090703050102030c0702090609070e01110f0106 84
    0x4d15100101448185640b03d03030418003500740000482c040d130402c8404100b00388111311070540c0c410703562035403041155540d0700710703241120070f0400038012402d003100305000071343c0000444001d039402c009843d01c40385a0750711613500c22034200700050f0405d8981102014440c1403148121000038084680c00800e84086002e8004044180d64a17840d09403e000c2c2c20b01158080e04240d001d215142d886070000881c000b0744601038550130b20300180c0343e120107003042d5000a8440304600c001c04010802040454961000c0c102c03580e001c9031441c1002030303543c00e040d00301d21801c80325000140c031049800d01a030a26440040c0c02501c0a031001400300040c800c8290500c9142ca184056504010180303882139070709000c2c01c40501141e1401e0f8900c5c91401001401e2403a20f440744030140013200000600b164818072181d0015074000d0000e55613032910070440c40030b0394003101040740314490000200d800d908001e68594801c4c51103490b801e079404201c400554507075154030250921480740342c403152502d08080c069140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 209167805 1250 209166555 209166569
    0x60304050a050d08180609070b0903010204050a090506101107090c0e130603330f02041211090112111509030a0c08060901051006030207020d060207030e0a14060f09030a0b01 76
    0x350342042114030540c0320200b4055a215401b640038014500d0000c245981203807110381c40036994800141c0802d0190003142d00082d80034413420b01c0014228250b4109074442c4408480513035102e41908020f0320300510f00c10a0040c01e500c0000140001117aa51090701035007842e003801d0032042c002500240c00f0f03003001c0800c504034176101c2e40c0c20820400d0b40080c00d505040010400081014404a4002c0480c07111940301055501c40c6c10610340700d94a603040354041c1c2624480030b401c1c1045803c09044200d8034a46440c091240d40c1c000141c18020f020007548080d50209200f203010031a50104071319144510241c096502d001c114400c110742e0708004401045104548d403003512884c003410a820718500420003d8164104800c201004d915100038105a40e803d050068a490582c00851440030b41e220b0010941840010200107054220701101ca40010032502502c51907190000c6020345041038141a80101c02400705107044c01343c0f6800707400442030140c22264815904d4a035040380b0f040a91080c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 209169055 1250 209167805 209167817
    0x80319020111040b4b071415010b04030819090e07020708013608040312030b040f0e0607050903120a03020c1501082d0a11040b0f0609060304050a050d 66
    0x90f0b6501d0040041700d00c202c02c4070354804c00c625105100318001d010301480342c0c21281400d084800898000043c0d0788042c0c0c0000d004a05500d1450ba483d90303402080c8007401c034010340b510002840b910382c0c0c0100d0742680e0340040b0090514071900c94502d14841031100b001d0a0290218011514403400741e2007d1258850f68020140386240186003401c443d414007024414050648001c10f22145c001c682e0320003400894021203030500c0505098400f400f4641004007a48100004108032030fa00d40c0022106103411641001f241c030811040000710740a03c12982d240307800040c0028a187d00943000742540ba40d0240c15509000c05802c20304855900241c1d110012950105504a040d01c040007044401c03822502408410b5042150a50740c0301d800c03e24040c99112049042201028202c0d00c0ea081404002e048910f00c244510b00b0441d0201400001d0b8041c502c0d24658130700d03d150070a00403601c20f0300170300034030f1504c4c1e00f0b00144121a400100300f6216032255044079000079104014070425240d0700d41e00e007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 209170305 1250 209169055 209169067
    0x20030910020304050f06090a06050f0c06040507050907110d0e0415030605010e130b060d060b040c020d2a0210110714030606090c030a050604150f030507050a080319020111040b 77
    0x300c544003207004140074100621107c502d03a22400d290000760303902410450b84030103c5030004e684078425103620072100e000350001d000400500188203801d480040358194019942c00000b1942d0781040c1d02451080d0741304c5104d44504d1401181000410310b40a4000300316030003003000121452400c1d03801117816558920040081d0008d0104540d00400300d21030900724403803180c03174203114074501400ca203210380c40e000320f0401004082e9010101c00d0300c000e002840440030110b006034480111080200108400240c41d0350500b500b8100010303504121518412060260740034084480c030341d6000e80d0140040040810800b41c0200f1425000b40071ba00e01b2003e1300c10361142414103280700074010303074010f01020081c400c00300070700c0068035440760800c0d0f00010150307290030001d0041c1c06041c03204040c001c881c0f034000c42c2417400c4242e4002928021001c941141d5552001d102403441c042c4070f40c08280c0c100788120441a044048600a0f00e4114400403495901c0000c3d5800b440e403141c1c2c009600c1c0c0d2400160 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 209171555 1250 209170305 209170309
    0xf0706260601022409010e011401031e171c020301121103030c010509060901060f1202040207110a090c030b1807050c010b03030f0d0b0306011809030207080f06090f07062003091002030405 82
    0xb8945038640f07c0f0b002882201d581c0c2101d03c0c0c80c1381041c0802803a03c18000b201c1c046016070003012140f0160410320f84d00101c0341000c41134100f607110305030403003001030780a6840d14210350a000f1130341203400c10b003180344c0c14848036110315590749010400c00d94540000c00807627890107024000c01e0702506151018240300d0601a001c0340c00c4030403379400480d0002d000c010800031f02c0d101c00d803180c00c11601901c0c0540d8646807441c3c11500403c41501e0981d115041407004661812268400504001c5035141003000d080c0700350811401107844040d00e41184080700000d03551510810162001006603800400d106e00040c00281c1180c00040c110030200350b000c100c2c1d031014130560081107100c3c4016400b8251a504140318407a107190070840e20101c0d1603d4148100c109442003000c50000c0c2025000d45424024141d0079030740380c080540f4080c509210b640d160304680f00340491418115001038888002c0100c181c0d580000101c90840740d0161400280002141c5480708081208002c01c2580030b55070b19420902 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 209172661 1106 209171555 209171561
    0x50c070b030106110f25030f0b06090708070c08090f0901120b01231003141612061404021e07050f070626060102240901 53
    0x1100144010000000c0e42c140c0300c207651140303a43c102d14405580d681400e940340710826000107140e01c0a02d0407910348800d04401140106000703035034070b0f00c9200f00403c95410039920240010100b040754544001466800032290074500c3d05030a003468000c4c4508024400242400c00015400020b9950b0860107400c500c40100b29544075a1240500d448202c0340885c101c0d07940e00c1080012039411207038480c070350441d61040d915490300001d00003008203010300343c0034907021325654541c01c85012903601585440740201c2d81c128000c1006080b0010b01a101c08800980c0c8a480c0c00c81c188030042049c0f0b0f50b407090890484e0096103c607542c42c0f22200507002e0782039031a000ca400098039401c0141c0456080e01c8180350000781c45640d6500c04c016120072000e008018862140c000498025074401311404d40c004c9418811a210150501b00040d141d04c94841900412882c6008001c901c0500740 = true := by decide +kernel

theorem cover : BRFrame.Cov 208992805 209172661 := by
  have h0 := BRFrame.cov_init 208992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 208992805 ≤ n) (h2 : n < 209172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
