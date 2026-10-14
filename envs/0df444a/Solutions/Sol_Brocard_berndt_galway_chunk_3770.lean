-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3770
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:37:34.764263+00:00
-- url     : https://prove2.me/submissions/546903fc-c88d-4879-bce6-4d56232a4f7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 677877697 ≤ n < 678057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 677878947 1250 677877697 677877701
    0x30618070f2301080c0f0705010212151503010b120901090c0801062303030909090a060f05150d1703130f050106050f220c0c02120f060a0c0e040908090904060f 70
    0xc200003d0a12112518051700c007000c0a1040078503070028840003203110343c1005025011b807140565040c0031075006127000d424649182e148000900e00c03c201990340a4070034803002c1c08480c180c40c1ea54010616200c541916205158406048444150750b40c0071a1000b15800501c0c2e0300c06000d0490002c04e66501d080190400400542800c1c40c95144002e20b8401d9998008100c07401b41c441601d165400f82d0f42c160030700c1d0030181c00c11030280455003031402c030541c0d032881030b84036500c142e8440b40c142150302c038200280034080e0b0008600074030f0142010b0581001d50300d20006154070a40d40899030f8062400e9546c1c062a454035103004480341c1c5c3d1180da00303006a28042c003a5402d220415201c43d40103d0320301c0c80706c55440012a40d09001680e4945010b03094610a05101d0203070790300a0a407026110111b0798003070740c980703846520304c0085c058580030602280807400303188036030081691440014501e170b4041100400d0031401c00c5640d000e003080800010340322200e030715125500030400014010406400002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 677880197 1250 677878947 677879009
    0x403080f150325051215060321251e21020c15070c15031116020108160c1707050d021c0201090308070309170f0c0c040902030618070f 59
    0x44501407545c1e14201415000038004801d203400c924144850316004042414900c4000c0120b02d10b0302c83c07c100d07500703101c150401060000b00b041320a106410b48408405d400641c0c0750700003085a141d0542d021035a5000e80688140c840c003500c40c00756030350707520a2801e0004012455040c0541c0100f248803205240000207c0302d00301044184034540038407907a80440001a40c040c1454107400600380805240c880d0344004145014212125500d0b0040c107607174006820380c85001ca00141d9901c00003007070401c010300710101a01017a114800380c40182c4d9100c110030043c4a0b036155406c2400d111103808184104003140820b0159000707000403100d0101448400441c8003222000c0d60305015403d0700190344040940e074411034a03e0f000441003441c1c50500500f9002403441d1f0081c180106502c46c40745c0550000f04001e010301000c651703070308000714180001c0d950b0f2424040d5040e048140050090500340306c2580c0d50502c400240d030401d540312a0b140d0311829442d001303907120820703426100130000e0115030868 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 677881447 1250 677880197 677880199
    0x705030c030705150c030c030418051b03060d020103110a1e05130509090a0b0903040603200301030227150406091404061d031b150403080f15032505 65
    0x200b402d50925011031003500c03644450384042c01000401c01a030701400d001b5214400c84c01c40c2038a035140c0e47c90b00c5400c0e900c074900c40140034492400010030001510f03c440c5960b05003804403d1419903884104102641c000074405038141600c07012a5188201c1c808004c2540358007586468241000c201c12452220a8001d014000d203e4104600309040900c840f100d0704886080707805045641d00c0d503d40d1803c04403801e40041140d506da8041c046070070380100190068231078555040051100c00000070901061503420941084010801800507091075440c0002c9402007648180c4d50804c541034a86040404a41e540160038034114520810301c0c1c1402410700428070a082031028010040d29540400000b80004203119652180780669411440f1603610805018007925214845040c1044c0703450282501740d0040c0c06518540f000118030b11013020300a64050303a0707614460785c5441c60420b070010041d08074501500e50001c149115681005038005250904002c0004681c42c4241003d0b6114a90080c1e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 677882697 1250 677881447 677881453
    0x2d0315060f12060d140c0f180a050a09050303070201020403060b0105070b190626070608040f030513030209070203070219051507060f020a0504060212030714030a0608030c0705030c03 80
    0x104a00c401007005807601c001602078079585580700d8000003010841c8101c8024110400b117803c00c000c43c8170100d00000102d000b03917240415052280104000582202d4081c01140c894101162100d00349a101641c4144103507000161840c003600c41d84c1c95500104c83c01d0340141e4000800340300300301131402400c1c6100c40c02c4c280b40b400c200302c59540180030100181206038440e00310310705801e001c49581010f801800c076402405080413034141300c5064588c07044110354461103800000035410384603804c058811600403d080300351000d15039048a241d8000c1c036900c3c10f4012080c8c80800960b80f1054024003861131074000316034680b001e1061001c8004040900c480540320b4403803c0040e500e0360b0503416141d046441ea61503071000391340b41c0351005043c904c003912003191020802c83d64451b0410000d1041c0e4002c1e80840d01d07400b02505511017a44003c560100000d00034030380141c914855a800307140c001100c030a021485079101c40c1110302c0d6802110362003440703510040e010000c80c00c01b8401a14040016009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 677883947 1250 677882697 677882707
    0x1b080307200d120507022e11033603060a020405040b1e060901030f060602070608010e0c0f0714121905040b0a0806221a0f010c03052d031506 62
    0x2e030615507000f0006603024000d0005044045584551490b020b520360480032a001000d41c0c01384c42ca084040056280c04100e10442402c0c1400000040d11008040c1c1000c0c2000006078003943c000601021303031407000e1074851103a12000b954041c070442c0e118550310100183c86a00d00340412055078001d8180390f00a1b41c0300b040e009004681d030380764100010010754000d607446031424012001818800200d5900700d11340f03400868141c0d400b10741c0e00203c807190768030700e11266200c038901010b6030340c2a1190103082a04000c0300741c2c11030f0304a01500960b0b00a0b00c4d55985002c1c1c219081c0d00388002c440c0616161000060041403440614600d0701200340c641c0b41680c00c0c80d040c80c446840611801c880d03c001d10808000103800381c3c3d2544c00c1d8545807990303030300b0381070016a0100225000e4407000e848191001a510030300c20341c0307083c940001582c00005a40f000c1204100ba1010744c0c4940c080d00403903285050300e402c082c0760b4098141c400f00540042c540300c01c0e920304e4540c0c1e1103200040241604c0f0301c03640302084 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 677885197 1250 677883947 677883953
    0x427050c270a0c0504050619020114250c14010b010906090b040306021614010e100b010543050d020316060c03020d0c18080304121b080307200d 63
    0x354142c0c880501c5400141006800c0400d0360b0314015a40600c0c0c0c046c03030024402c075400400a00307940004145400a1060074000f81c5060421a4202e41040c816103040d42002007049400308269600a61400d00d65202d00d0726403183c100300411407503003e0312691248100308180d41c0c041400302c003c1c82507207015180581031040c1102c0030b215a1102071316141e008289500200c01d032081b54416035901140340d4100002901c9581d0217403240312041903031401104126980406980140c0301c50040580d182c5180142c0000059800c0c003207005a8910fa103940030214481c0000c84091408841e02500070758006090b500d01985000600207102045410901480c070583d1002c0c000401070340e44c010004540f090384404120024022106420b80c281d0509640c0d5418940100d0380045031a559005600d801c1d031219100c580e00d00c1148114180b0484610b5490301003504101110280403020b80d45140859503810010300d99000903906590b1240c000030322002d10040720100e9440207000740e50308055000681c07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 677886447 1250 677885197 677885269
    0x2010c02210a0c05100c1701080d050a030f09050f0304031518020d2901090f14060d0f020604031217090703020904050a0b1f06030e0c0427050c 63
    0x41c10390010b0010402140f0104031052200080035401c0c25000c104103180000c00400780000c0906642049507113100110b82c42001054100a01d010750f00e5552a190520f8400c400810030320042d959800e9840845000080043c4600c00500b6542030081d51103a00314140550f001d00110030403c1034912b0a40451400200244848405501100c0000e61450f103814000d031004800d0415074106d28003001248040051114014140d034041c5000f00604201c0d50a41022104c40c02003020300b130078000000903c985010b81d50703400c131140728a1803203805004550100e09990426002183c070243d40740040940b0b03e6004142000d5141c00740c9180c0180e041103014240c54080a010103806131203036130002000e00004201110134260b00c1400c10142d840d200e801c2168003038200521a13036002c407050000802c079201c1d02030403c1c10070030000a4404030300310302e04210041040200907800442e083d405038a14030b8008142540c254001d50250007059908400c1201c0b40c0903005081d0700c50340165521000032800c2d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 677887697 1250 677886447 677886457
    0x321020408010b090f0c0f1c1e05040302060402221802040c1407030f1103030a0b0f01020309090105040c0201140412031512030e040605040608010b03060c030405031813090302010c0221 81
    0x101d5001070341d500d030b600380c1480c0c6449160301c0c2008c2c881161042130b241c040b0551102c00c2c4c10100b524803003111103025100500340c079800d980c00303030042c0c1c040700100d030140c900950811841e64001c220a00300e040000405000d036091030409040b5201141e180e281941024041c2040b00c503500d182c40203e455614401c1081c070f01500e0b030040d01300028803e034100b0b102c1c0140000704c0d502225008983e01c0349024407240c4003910108541d207005081e020141c10310b035400002500d1007072400501005c07041c1e00317003800d200003460403000080440d0b4950703200e00c0b4413061044440380214040c00c1c800103000140c0d080a0140e8808054030034004203441c5082000410b041136070201e817949032078805806000300000802400c502d40090f070340725291030000159444154000d04a480096040e80c03415928020940e03028002114013611940041200c1091a00056100d4450560080c031003618020128070040c2214030040c02200941c0d552001806101d404026004184020400c1926803400c820340620842c020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 677888947 1250 677887697 677887711
    0x1050d08030601302a0513120308040b06061c0b19180605120c060f041a03071209051e070902070c0e0a020909130321020408010b090f 59
    0x101c04a80940c3c07003074500700d00e10700740c40106241040c00040d086190300030a8000d480180c0c54004980040d200405800486045004500c045140200000c0d582c0c4c2d0311403041a2510440000041041003550403050f40280c066540c48600c1c4c038052425070f10240004d00020b1082c036052203000c09003882c52103a0402c0c03294040001c20303040001c40110f111502e0f141c10383d180414410a01003480000c20b01701860300e10a01400b40006a074410510803c40340798006456160004104040c0b503092810042415000ca003440a2030941d40d80c5100548628000d4035101da01800010f00212683c8804c2540d0b454043c1e2104201002e010340d25507644161814000240c03229403000704190510a0007140011b0242040640d501c04040c60407841c064064014100401555000300d50b494132a48240c4001d40800380c103d8440d074072030b010a001d508800034000c03001c204070640d01d010014200554011441c8011402685a84c28018190700b903c01590207540500544001c0001e9485501003940d00300c00313 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 677890197 1250 677888947 677888963
    0x70501051b07180c0c050303010302060705070b0d090c09140622020f0a110601420306031112070311031c210204080312100801090308040c050901050d 66
    0x80100798103800c1d015500c21903409008a120010307220948040320b01103071180c00003c0061040039030003601ea10403003000141150f40184014401800c0071002005047e000718111040c1c940d480c1d901d50364550022201207410364842c03214804010010140b640a002124070a1111007084000e00c1c540c03c100400040c400c1000a907110941c105944111983c2890b04000b59070f2402c43c1d00146003164407032810348002425840c1e000c424000d01107001c0d8142c5410943d01101c030100801045002c1086281a0403074405481022080221840c03000404036501c3e180400d00b00e00e1810004071200340103442601580700480001160000402c045054960000014611290703400100e442d0a07a00400d920480007c070012807409500240c01003545003100011070700503060951040b090380a07511a40c0d150350300510585080d907203000500c2d60310242d01100c1010541d070355828123095541928040c0d01081c103490a0105001d41003010704003411054400b0a070319407401d80801c00c0c40c10340b020041d02d195 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 677891447 1250 677890197 677890207
    0x60f04090204240314070e0705180901030b09010506242d030a1a01050d1a0303130e1e01030831050102060a06050a1505070c080106050114070507050105 67
    0x240d80c650254024403d600300c01006400c401e0100c041141d8035000a031110000c22101c0c0c000607800107200c4050701c04102a0b00880e44400000340c88a410a0302e4240d0349820f402020380c00340c1c031000320030790080d806280e0b402c82d1820940b101a085480141026001d08208072803641d6014152030b03211080000215295034941c0741c07211a00103440164620440904040c41d0000f500d030540000d14040c98001c2c8041095191740542a4400c05034002000c0c0861000e205540380079480d44d00698409130250280c0c060a911a8006400c550001050714898001c40301c0034050103200060960703120300840c280c80080300000740005482c0a051000510307100d4001140d20b208045049014903107400180901904180043d0f4416146003070700405005124001c00078200b00c00a01034901140c0020300f030307101058100019190f01e0910400e41005118042208100241048600c240205944c0c00000340d5182424001000a40d45950801e880c01c400c2c000c1d0000b245000c9006801c490090801903510 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 677892697 1250 677891447 677891449
    0x3050a170628180219090609153b0306040b0c0a0504091103010e0c03280902360403020d0309031106090114060d030804060b010504050910030203011103060f040902 72
    0x4090b25030000c022002c032900b000c03c00000705401811000d04003800e2400039007403170142101c401c040c40c4900e80015031240c2003003010f10031854210505d040940352100c84a01c02e6540602c0b4223810f0311110603024002c8072085041c07082c4069103000038104034044d0115081a854040c96888041c1451a44050002e0b5650107140207200304d5005104400e8244480d0b8a40e141c030030081d8009100e50300e50b9814136800140088101e000700ca00c2982d5183c00e43c42990061481d442e802c050462070030301025a242743d210003603940c41e04205118110910070103032643d21a0700c2400d840c41085c80349041e803103d000500000a0f00840d1902000d5000e103000507141055040c101c03440020401d51011502510044c03101c11a419000f8496080c40c00c0303404682c0341c41c0d940500200185c490070180c00540a840031a00040403a08140681078051400f1400e0070784034000603e4607401541d14000c0d0009403e01081182000e006026481d1416503040307085242010200c2c603128003103000d081c0718a58400f004021 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 677893947 1250 677892697 677892769
    0x50702010b0a060305010f060903031d01050d0e0c03010b270912070501020904060b0a1d0a0f0e041506030f0b060d051e1e0a0b180a03050a1706 63
    0x1000a0051004803083d0791070038050000c08080c01845091082c050000c652107028285184c112030745075540000d600d003800490700e01989495503050420400308801d00700302840e40030740c82c1201516400b411034180002c3c02c0608454120b40d034203001c0c040320f4014049190b04d02e40800e251003800b111247c45943c615a1550504014000081d0203103000318080092040541c080c1240b1041a079003080095100c14080203a809405d00c198002194030031901e1403d481c0008118101c6005002e04800e40d403a0914070184800760741020120802400400c000e0181211040d80603003084501046854215100c40411118408010305030800344400700302031b81c80b90f4100c600c0917504181902c2c1c4103004107084817015005007032002c0c810300c119906000c0021180c211058602d8040004000801895a48038100d580080c011005828000e03914000d40340d0912520082e58441d540341e581d50f120707014015060040c050251244000d503101081001c0d1500e407112410030006602c0018038100e00c81395411 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 677895197 1250 677893947 677893961
    0x8040308070b040605060d151d0f16140904060203090a0b0103051c080f0f0903040305010606030b1f0914030c0d0b06041407020715030207081204020306010506160605070201 76
    0x4080080000c1e180103000c4140c05182c082e601c640c6082c000c0380c590300c042007002e06031183c01400c40c54003039910340072461256001d040302d0055242e070345290b1541d0908244c10121090754208098019400418170444a00100405040f1003000141d9140c41c241c04110300d842c0003000201850b03400000309141460400141a150307500c0098031085603100d1804035128517043c1c0080300959800c45003807100c0e900402c8a00d10414000034028101d40c1d48200c01140058040c1038209603020400011001c18403e00604002c1e02c0b0035100404c10702c0360b501c03d009801e9901031a1442c00ca00702d081411440c0d0380505c002c0d0444d0f082c0d804000080342400006801c0c02c0e07048550716440501c2c0c580c41c034204924021128425142101d04021800d003000c281e12000747d04445d1a40141c0049809020501da041811500302c41c41d4130b0014246000ca641d02200c82c1e2000b40c1c01220300b0701d541e00708011460204001405031005031070b468100150540740c0640c0c43d500503002006030341c556000815051003503020003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 677896447 1250 677895197 677895203
    0xa1404021c0e150a14060f120f030309190f020904021207181128020325230c060c031e070309060807050f0a170748080403 54
    0x710b5024000340741d907243c1d116040d00c0d4051401c50300080d128007462062403100c81015501c0151950340b181000208540300020300d03031141c40168801d4108070204085104601080c000319600e0030501611840c1003031880c0f040e86840070301d42810002800000103481c010354141c820401503180c901c0081c084d40030303628420b856449000c40001d0151412702c040c00740074a06203810002a04140b0f01040503106841c7d2080484080104243d0700c00d556091045c01e1348a02e1040e00d041114000030311003000003103064622800c404241010912600722400030755564030f072100629840c2ca00b1005615004030300040c5100c0c040104409104020071700407100c0c1c582010b00350450300e40c5403483c015030381e401c03241d07050f400503041d04c0c008100303203008021303550142c21547c450f0303420031150307908040140d0300c164220740412049a42c0e2000003a0002c0a031805014a41c83e1400d40c90781c000c1c441014860421920412134588864821440134820854030305015880248000c0f803080d814183c85130710643e0300003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 677897697 1250 677896447 677896451
    0x60806030619050603010912030f05061e150705070914060301090512090f03160e0a0b010206010509090a1703011509050a26060703091103010b010815010201090206070507080c0a1404021c 82
    0x88040392741075100c1e003402e2030819000c02a0340c071544140b101d44045001ea48984e450011410005840d080a4190404080d1000c00d03247c084655200c6050440720792040411a854030415a001d250754800e82da40114250300800114550ba00d60070364400302c0c071180e42c0c03603e03200280c000c2d1151180c003010348440303401804803440d0481484809104046900c00c80c400c103c0c1400126000e09603501828101c3c0700143d00a1450383d082404100751035602070f0400c8128804ca0040c84001100b00074101291407100300015140e61400404c5c1d880f01403841c105c2010008000018001c56a4040034a400d440642003600f100d0551b1214410001421a0400c40244076a00030800e6041d41904580c0300c242c41802258480d40c0741e241450b09981100410324007003448000011a0031840002601c031206e0144008034031200b031500442c01c1a40b01c000d0030780e425086404280100340c010000d8080c0001c2c05ea4040c00801c0c50900e05540c1945458001d600c210b80009112010814031601190b8860b409401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 677898947 1250 677897697 677897723
    0x80711030c070b2508120c07120804021c1e141f0c08061320040608040b01150c03080c120c07060c0207180905030d05100608060306190506030109 64
    0x925244c203c200d07820341c007402550b1402c040904840c60a010641d1007500709003806001c824200100b41c00521240c03940030203204810110f80e00c581c00c45500b6603281c880f150281007500501108020400c46800740381d140340328a10004110300d100e10340c2d041440081c4807403007800d45030601d404403908444c01d02d08d21032011fa40c40e20b424166051003040c41d030303018100807203034541c0e00503243c184085413040d500a40d10030201d0000b20207504645030b501c0c8414626280d1041c92800a0f4854202d600400b0001d0080c03000c010410182d811501e014028101c00240305005108009140c0c0844603801010402d03100702140810622006603081c0d041250230080680c5044800719070540c0240c42301f503401c01c4c180040000701c2400458000151a004480080381184800c04240a0000400d0495080c407080000700d865000b9803044a010314030460100c4002403514400800b010b00150445101e90000801c1c80001c0c00e1b00d42c1000e5141c1d4503800c01041ca03a4500002a0040941c000c024003920301280b6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 677900197 1250 677898947 677898959
    0x60b031611100218040c11070e040c05010c15050106050a030e010612031d030105010b120a330506030a021b010e15040f0b10080706020613140709020409050103061b080711030c07 78
    0x4624038590702d40d03c0840708d280d41d961020309000307902950003514038080340e10180503951040c4203418106000c0d5004051841500a420084a900340d102ca0b002480100b21451011340c11b0040001e161110002408000e0400910000b154944c900060900404da000d804a1054201701c0c100c02803001002000a5a50341c03035424400da01c1400b070389081084400004114a145120314182c12040d03a40315800360080c03c081d01040000801210181d00500c2d01c00207080d0b0ba91401540704001c10400503803140d15203e1038078000380d10b04865010907410026442d003640c1e000250506203542c000d03c10110703600c443c01d040d4404840c1d480003410004400c81004032420070308003040308868210003220492669604100d07124002a40e50581c03007200102e1600c00700b0b01c0c410a2147c10000c00d801e5841503640e64450204980c025070020348180e032520010030901046214110740003403482e0804c0003205203410010310300c03c4001c00a4080c00310000c000400c4180c10026a0801c40c02ca0702141d621641b951 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 677901447 1250 677900197 677900207
    0x2e0f140c0604110909071802070506090c040b09010b091e030f01050f1006020a06051e090109062d151505030405210a0509040906060b031611100218040c 67
    0x11020f48200000d20f4070b64507035040c08a1074610868203a03000d80301c0c2604010040e09150107950030410b00540234041d08020a00510030640101d948100410342e4501c0a400d00041c3c5603100d80e0b080c8038500c8100100b0041c4244000ca80500305c08071001500f214000c8a00c5031005030004400360075100d5110740824004056020b2400b8000c845a40f011a0381c8143c0d010b4010700c503502400300160440c8804800048041e001180c0004284011a041041311300254851100468040c002c0760344501c452000d00caa41e210701c2014002007100225141e81c8011070100e1141e810f1612890181c0e1910441400300800540c03901a00180f64410090394840d10001e050f0741041d82e042e540390184000c14041291406003d80310803841040c018189249444107840c90f4200401d002c0e0001c1c0c03140f94550000b4818410100900120fa042c507499007000c0701060701c80c407080318840c800d01203075007107040428400181e802c0301041c07501805655184043d0403441d0000081c071282d60828108a440d1031955008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 677902697 1250 677901447 677901451
    0x12040602120a141008121b010525020312130501090204050a0209090c1204290a09050d02060907090c020747030411031501030b062e0f140c06 62
    0xf40d03c19a545813505201a48104514410030b010360303000300c00e014845034280c005020107001c400b009004081c812420907081d503030101d130741d0b0100a9944040030400c980221071103403111a2880207500300a003000495014603000f400d02540700c003510f00240b0800a00f50840011582d0240041c40203061a6418030040d4100040d500e119000c01000100300e8400001900c41d8a50704c448650b4468540d51516280c0e400035401a0312043c001d5007240c1c513203850f1400041d000b0740c0e03032410014811040c0e08003a0f082c516018a503e0442d08a0006c1c440d4501000540e4026541c90a200142d0720003c1001a45030600b0340e40001240001d0350945a0300704003080d0704000002c40280075164051500c10040c844010000d00306020b5181403001c034011504000c414000c482c80a01191807640240303000c6480b0481c26441200c085032100204807041c02c15031079035000c403525009004151103000010000000302e6801c018104580d894601c0461441000d090b00f0720780909000390768a4442898075900d070113003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 677903947 1250 677902697 677902721
    0x607050723121002070f0b0705090f0d11040c0e0d05101107080f0d0603050f0c030d02030403021e060405060d0f0b0105040819050c04240f0b12040602120a 68
    0x1840e15800100c1c00d0840c0e140203801c1c98103002d031849601100e2088005d42044030142c4000351206030200004480c0e1900a000e00302c075480740794803100410208545001444540703802032180440c01400142c9a9841c87d820480448002c2031218040341c007114519450b081c102d9100d4486090002401008140c103000881d40b0315013480410518204148140700d4031400402c100005c021580b0201c04242c0500b011418100010500c41d07900c4d191249000090100e01c010754200000b4200305107400c0160940301c840070f0006c1d604062464002842844031403006041ca840c090a040e94607649010486000c1c2100400703094603518580e860030001c180c0c94602c14042c2d031406904810075030040381650f0456500c5c0c0000c21205a82903601d690340000020119000d07c03903005241026603413030040b844614110004504850041c0d40b024280b2042d0350300c0346040a03802c40301400303c02d880e5411079240c900c0170918840242c64074580080248203003008080d5244590040c0f1041c1881504100103031a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 677905197 1250 677903947 677903999
    0x30f050111040503100e0c091801050601111b0d12020607090506131503110d020c070e1e0705071a0f070f020303011208070204022b06060207031106070507 68
    0x54401d00c40c50307218a01405038160300064038003440e00c026400404103025008180c40281080e00081080488190b5820101048103070300900988d80c24800c0350380c040710900e840d07005d101c0c04098494952820040340c0000350f92004d200005030301c600b1218024198848a103030241141040002d4840006070b407590000344041c140000c4501c1e0034400d0300c1c08048800303031200c1c843d494a076500b030b418819820908103041d110100d4035120f4080c1c4014140403902e8060148ea03502d01c03800910308010b1960868144485034800f80039a8102e140311558074482c42c0403002545403038070078080e0b40a0192640050598142842c100d032a10f00d850f2100307000780406102110141c54060301619410780300544140141e0040c001001030000c80340380c5100050090f5a1549449680c0c0c02140681c1d000942c3c1024545a800c1c0d038010203002448292040610948100001d50812000944507d00c520019000b10701024458403035a98000c200e480301507126040b070b1032072607507440786061880c90603400c0c800e140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 677906447 1250 677905197 677905211
    0xc0b01060206090c010804060b0409111302030f1305070305030a0c030e0105090d03031e1107030206181005041509050109050d05040f1206020408030301030b061e0d17090a030f0501 79
    0x1d0001800740c2c040e05044015003d4440d009004651364a0b00600c191101d0b0703161003140d4559101c81c400c411034640030f40a820700300d02c9004140451031042041031000030348104208045540200000b0b90440d242146400000c803103414001d150003400d40001d0801d0000081c0e065110360003400c00c00301c083c429260141c082000700c1c01580e260140c08100f87d0000aa003548000003480f0380d1025204081d204000311b2200b0006142d42e01f201c41c080b60304202c040d000034041c811305804214040d17108880384001c00403074446561903a122900d40403020106a110400f04d403c1040c0000d00c01c0c4001ca00e00c00c1040701009500701580070f0400032034103850b031703004149109114601ca03104440640750003080042485e4500400240d0300842d0520648503250b081c0001300d0522000d00055000798041d07000c0c403419040c50010021001542850b40c031541003101102850b5440300010544010b42040380c904412411010303020707813481030303204aa0f0700416521b030110800c0313600e00d4492402d60003100200000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 677907697 1250 677906447 677906459
    0x11415040b0d0b01110f0109051c0c060510090e1005010905130b0402030a0804030507180b0a05010e1f050c010e06060a1a19050703020c011806140c0d0c0b01 69
    0x148564040d807241c10204000d040d5101c10342d90071103501d90f4010b24144520403030800035503085c181c01aa448501382d44403013541080c000100006400f60074810019032401c442000050141b0702c802e13070300504064541d00040c1c802c00b258441e040c01042950828016a0110807040362655000305210706503526010012034050383c1d40c4502d03807188080010039003801031245c86101c030a820085c802c030303030600c18034504030001444003015000551242d0001c080190030800300c200c40304001200580702031328241102e01c1e60799a0b2100315040303901c01e003004a0100b80703020209080748200c44856070628682c102c0742c02043d034030500401c01010b1981c0200130341141c0e2092503440b802c1c1600c03079075070043d980101444048014410560700c0b50604c01070074909600b481d540d8071480300d80031072040428000f01e4000189a0180002c105c0700800f40f90014408401c6502020b10070305034000c0100b0000b00440081200f00c01030122902940b0b034808859013401010700003000c04140480480c1d001b02600d00004403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 677908947 1250 677907697 677907739
    0xc0706090e130305040b0c030d0f09020a08190b27030901030b0a0302030a061d150f0c070b0f06010306050607050d03150e040803060a0e04030801051f090308090d0b0114 74
    0x1c260b4503075207036842c5c5890030040d0300b581d410044650b81240801c01580014400c20310901066059032400454440002c0c01004900385480e482481c0c1504480080c841240c3c004540c00b08850f03014040d03c041ea1501c05105ca8001111080c0741c00460030083c040c0e00c0060000007030030284e1403d0743e0a01800c00203005102d0750000f9840f009400d54441c41718034000031442d4115107480740404c0c00000c0d20340402e41406240600100065048405440a00044504401480ba8400050307a4407030718205040d41d801d00c4602c00284000390005141c80803031201d03071181d04010002d04e4010601a01c51001d4101540c450460041c6400031a1234079000d13154002c4805200780841e168003064003620394039a11182869403008000b1588840f0f88680440d545c00b25401903801940242d94902ca158140340c2409200e95016407850003001c040c5200d01c140380d5100110b002900c0c0e218a003a52504a644007288903940e001a0090031806200004a141c89003969242401c4400300c54207081081c25903d000300d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 677910197 1250 677908947 677908981
    0x180a0b030a1104020a05091e211903021f020d0510080a030e0d0213020a27031104060801020a020303190b0f012303131b080307170c0706090e 62
    0x88240b0b0b160305045140d161a5000e00f40d80708540c14520324240b19000080c000e41d09408101d011007074110318810b440d0605070300c0741941d02c40c448600c00c01c00850580c4070740d803400d00d585880754500804004070f00701071003480041107000d220240840396030b00c41c1c0c8c00000070350454080926101c0c41c1800086000915401c1007084a03004005403040c0e00f5940ca007103c07410180e100040d0407a01a0400100580710211514451007440c3d1005840710903405004000b1082500b4078079025602d0034030b1841c4000909110700489074000302842d841413003c40400c016104940c443d10301544040307039111040c4c3c0c000c40294400c00c108500040c42c02100501103044a00f10400c03141c0162911013414000e501444c4c1d401844460066810000e0034000d40403a25580115140b01744411006940000c0200240300d50000425010101d0240c904190303c2554901070b041c400307020650f0280f07011007005540800c840b01d281119007622015600e40c0f0020707218525078490000c0c0f00440f07500040f249840c244e4144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 677911447 1250 677910197 677910203
    0x3030e06162a0f091d030307050901110f070807080a0b0604020306030f010c1d09151908070e060114131707090204121a0702101a180a0b030a 62
    0x180c00349070241c458403010b0782d02045030b0070003101c09903252030800d568031142401480d400c44036202c00c600700303d1500f003600c100700f0364821490903076100d0600f582e1000c019039902681a150041e2140b40c400c0040b10f4000b41c44802220301c3c02241900c0821140110b00603050f0b500c240100c2c0c2c1c000b5610813520f5500c034803204000d4104428000455124a01900150b40004c1c000f0125121020624500d508403000c2d11407410120b0220f000c03d01d0100006c40d40d41c0c01380f500c100d85140c0c2c245800664280e480341ca050b4418802c10310035840e03801040d0004506005044180121501c0d1a00c0d14100c3c1c8004106072059804609010501c41880a8200032158000d44c640481c80c0e0b094580105662125420340011004e4082c1c040040f07400796540c4080c00080c0100300c0c138035880c500f250401001c1d80d81e02001a642c9207070101e080100c243e800007010303103c44143d0346001400a06c0b03d42189016170207541d8035a8014100307102d14444a141b412845e010314490310040000c000b903031007099070364950a0001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 677912697 1250 677911447 677911477
    0x906090804141813020f031f05180709050a090506040c0501021b1e150a02010213061e110a060204090207151b0309140102130f0f03030c0f11040e0703030e06 69
    0x505070b0f0f81e002d004180d00c0d5202400004400302143c00090408c121400c44290034010456030000021150240d142c0056401c0c4001810141c07451840d51203450f180102c2c40310545580c045040760900d503109109980d08030b03003560200e080c82d28103074640a2a81c851503005218400306006249006c52101f10300c41c5008110145107881001c210311103940d080410744d03118210041c40140c80c0801e80003071000484503800140c1c0c440020425201d42e0503250480010002880c2c103035110898058109a07501c40b03541041640381d06000c25062408103c014002e10301400030500045800080d000f4240b100d2040e5202c104608607081d00c03004445040c05040d819241000003050818042e50044006074000c0060466410700c0611031801d90f440581000c0603010110410010b042140700000e0180001c0004140000c0c5162002403010700d10490151411510040100c10410325400910407600054014410344104428a0751910068032040c0d002c11510101911545404421600840c18900c80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 677913947 1250 677912697 677912701
    0xa11010605220c11010c180f06020d1b0f03050a110a1101050903010e0105092514062809170102120f0414030d060303031812080a09060908041418 64
    0x250301c0030300a200941414041c4d01d900082180030280100c02d4074070304949a5404684580e4000d0510783c41036808207031901381e000400e001807a0b002c10f03003802a005030314085810719600b0090596541318414020090b002110071581019044006031225070750300e481d0b090151012001b82622001c800e0001016410b504610500c90340c00350020b405c2240c070207000024680d030b41503c8030382102c4044d034024142d030707100d000d642e80c11144c0d00d444030b2090310110401840441c940416803080d01c2860b84c083c1e02c07404000c904070449640c2d604036070041c00a070804080d900e440b0420054070100890250f03460b05003501c3c40390362040505000711001c0d4900d90145500658900595a51903c0b02906c21a080d050906014030702c107004201074030125104110000c0c0b4280f5510b0042d04641049034403400035200405040045202c40c804d0b0141c01d640d07403c5c07100d0151b880381c070058010f1188a03c02400c442c642040749061141d900c01410a44802e0400840c0d5580b2240c00c00c01c00d03d03c04a2199145221200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 677915197 1250 677913947 677914009
    0x1505070507150c020d140c0307061b0f0b072102090604170f060f100e010501050a03051005060a0c050105060a050904120c06050403030219081b0c120a11010605 70
    0x2c1c0300c0d501c0d084a15007030b80e41c042c00390300090801c0002d0606481081d03400e440002c48180c1848500d61406040b0300418006103099805484643c41c150802c4150710183c69183c20f00c600310141010283c0d001c03020710940c3c034211740040d081c4000c0c49030085079250501003484a40300c07184215102c42c100281050b0600745801d04c52005810020319444c205d004e500e002d842050020480b081c007480e620780c4075402a1074541603001807883d80b54003c21000780020010440c1d641c010003140c07508070261a001ca010340d0b4402940045240705c0d4000c513001440050204000382d03014454615007480707031000344015202c4000b000030800b01405130580c02150200401c4c000764101440111035945400d0161200c02b40c0c2d12510215a01100c040e40880c1d0009620601a1151080c580741d6940c6030904031001c4c18152414020604500807182011000040040b040c0000300406451103038504401691460b5415004001c16001d61120620b50708000020a6074a0514000400f5102c5840313401c0c4503500c1d0300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 677916447 1250 677915197 677915219
    0xb1b0909041b0602030403060b24310603050a1a0616020d03050903060603010908221502210712050f21090c22050c0d0e06011505070507 60
    0x50021070b290300c5540082003207201c1c001d426000511840d0095071700d86140d42024020b507a480440b05214620000030004000c9028143c04200c44400b007290740c803105600c00104022900e030f0500300410464907002555141000d020000391960359070300f07101c207842c4d11007108140d4050441c10300c03814140c00c040680d2400d011010b01401e0300007510103003242d20b0342c0d0003042c07110030031002c00d400042c030024044403036040030031000d070700410154002c00800d07000f0f4441c2ca0301030040380d140c00b070854429140319010040c0d214080300a40007040b4030701280c3e00745c5400607565000f01104082012012006460040f0140007600c00c0140c206020050401c2c250a04503041c0e40300313421540c0b1403c000d1003040150210020000c0741c0302226590301c3d0740341c100b403500c680c81c2008000c030340343c4108070260341c00348140e01252058004899030300c80860075880d440c03415400c074080e18001900603454140c02c0322000d14001030440c1205d00c3c124140001c48103c0e103044032144908003014005600040003009012021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 677917697 1250 677916447 677916451
    0x41101020a20011b0c0b030a020705030d02091804030509150408011503171e070f050f07061403010e0423030409060f0e06090f09010b0405130b1b0909 66
    0x5105448420080341c1d681c1e00050040c6400c44002040700d54041010b5130440d59079500051494100101031480e0395507060130f18414014141024000700c081200d00d1441d0b015181503c2d8050300f5681c032002403041c620020b41007615003521540151381c80801d8031101072045d602941c5c05a6a4514080184040c40810502c4241c2080e00c401e08210006200e6020311403044040c01c52008510420720b10b06001c4151084d0810b4840c0c032400c01c00007000f990254041780081042c5403000c0b103440e0489810840821082040082c1140c00381e85c0082083d0080414520240c864984540c1600403144400c00a035010034000d0108401500000c038002c40c40080c405425001c520b00c0b00034203148040101d40c1140c2003035002c0030000d03881f040103116440c3c8030300c0c514000e0060708042402620300307078000500d001000b4010015150100c004900342c140c00703401150070154050400c5c0700d20305110700303041c8000b00304101c26269000343d0008100b0104190701a003245050491500b17083c40d8039001000711000c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 677918947 1250 677917697 677917699
    0x901091104030f050a030f031506030e07051005190507110d0528060f0c020c010807050706090807030807020c101107030f2f061903020702090903032202090411 70
    0x24400040050a9504841c20162281001c5d0030035000c0e034a805030401c0300200e6410285810440c0c6248882e40d0030300a4411181d1910300800e030b038981c092865081220642000360046402d0701e010222540200080280b448054424510700340720400803a818003c906004254a0216462060900c0d042c4002c0b02c03014011003e448201502e681e01031200444039008058281c1c4458408040c0205403040341d00302c0310b1070340701070007000c0403c00000e4030350609032041814440100e01080c4411b22840a5812030340e48038204212041c66400d204640b42c01c811400ca00280500d0005580702e031000c102c400c0c107128003402c003942c01300d4114020385909092082032f05452140c0500000418803070160030716000c1c0240c104005541302004a000241451010241030b4010005d4510080d141c403412030702907485280c4455078482400f501100644619075000e0342c4680e50f0010710020150103c000c5001d0390381200029440d0308810390344d000d112042c0b01c0195010084034001030110399144c03000c060440d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 677920197 1250 677918947 677918981
    0x2120f100f0503060609090c3714190e07050702041a0901090c0e03030d05060913050307080d0b0d06060f120c18110406020a0b0f090d120b060c01090204050114090109 73
    0x368a5010074506100c0b02d01d1201c00605c0700303075500e641e0840302c0013101141030b441c030011101a082003400a182207448a1182c02031036a600b17444014131529045e071015290400c000c4cc141e0070301c0000140b10390000d95069110b54075004840d40c0b00b01913640001c2c50a48090651a01c582c0380c12920070052120381e00c04014003070504080742440d07800340300400c91080800c03c0001d10741050070034001e2a00300103040c201e1804130070b920500410000802e5481055009035a01e036900155540c1c000508480082550010742000303440f402c002941d0400300c150b41881c1c44061409940310400041889506d030003600400c1030344070501041d8240c0c1c0151400824071207000c00c440703102201101060780181c0c85080180c01c1501c4c0d01d0b0400c1100215160070400a00401d803407400d02010305074603032801040d03900501034540600d070190440e07604414503960000b000544c03910003240c0420301a000c1c2060072031203640740c0000400c1103040681d0100281a0242280d200b86c1c0c2800c0d0354a00510004a020f84000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 677921447 1250 677920197 677920213
    0x2030106091e0608010b0102031c1508100c09050d020904020f15030405012306090709031410111e03071704060f05060f030c060a0302120f100f050306060909 69
    0x228450080341000b4201c100460a400d003501d29000454245070003c8004e81d0400074a084c20381c0c0e000040d80d030610300c0060b08032006c8840d0320b01071000b09036151041107445499000010321140202c1d00e0100a00c0b420014044102d0442c0c04494003c454024154000c0d21400780ca009800c0c6084016881440900150ba0500c075820003d03040455803001307144440300c00810001049020f004148442c1e00100204240c0ca41046c0c4940c986840280720034018008803000036000352007085018002c0da040902c1814485c0301d01300d19502c59100c03500303141440741401e030302c42c81184d107500484108102d81c1c41d070b07035003641d00d05580ca0240c7c0c4d00144c5140100005c1c44100c480240d0396901c00c0c0c0c0070307030722a000010701e118407400c54000b9140b00421051241200ca0b190708500e46012864100e00c1c4000c558165a40c0c1801c0b8007500280228540700c020018400200009500610142c0c0d00030700410340c1d82d0b140c013961034103442c101003a079014446c0c140e00060049907042c1008841c0c1c40e0014510029650f03c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 677922697 1250 677921447 677921459
    0x80a0207033e01091a0a020d0c030c020705120d1b0c081c0c05060c160b0109090318150807110d091e06020a0803040503070c1811040602061302030106 66
    0x4080d040c0c0840d801286140d03041a1500c500b191000300042142000348451011511000c0396005400040c01a02c0140c200090510380e241d81160700210804004220f84602c4040c024001c000e10070085000d807182c9400852140761107481020307619082401095018101c2c101110103180c84440c2e00b00b007280c1c800e18032001880e054a840c0190840c04007c2c041451140150f0281c06620483c0e10180500f10700c040c8081040401e07000d0740041010302040d90340001c0e0400044010f4149405044800d169001080c0c850407504001c02690107907543c424408561000c5e001369401d00e00c0ba810401074026034448505020380d011940c4a0340e1414144414801b500106080c18454a40c0c1c43c0001d01c2c0e041c0510404c075803049250308400900a03100b8503a818214040c4d65900e80381d02c068520040880000c0030048100300701d40e00c40e644038401c2451103942d40300d142100c05001010300c20b103030f00707100f401100c1490381c80580d0202c650507402010035442c4c80c0d062490340d2541500698155403141d03008500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 677923947 1250 677922697 677922737
    0x50a0203100507120e150601050d09060902030705041b0e01051308030c0f01020a0c0b06210616081005060c0a080415030e030406050a05030907050d03080403020d0f080a020703 77
    0x103403041204042081c0c544030f01c00a044084440071049010719151185081041c0000c2050700c1d0800f00c902414252290801a41e645c0603180710100f149050031340700b0b030030040c1076084400600c1c426000c4801c565110700030041900d940600012401000744012070f9518410402107003e141c06040c03442ca03242c0110041013410b01e0747e4000846a034000550743e02500d8003040990741101d0000021401c051015400800d540c0e01c02001501c00ca4200d00420450742e540e040318002d000003520340e0328240d0f41c00c40344a5102e40003110881700084030004203001d0786006010483c8181d03120b0903080081170a1400300705c02074005400120080c4a0b4110141c0050180ca0080c80603140c0c1105040000e40564002400e503904c07140094156002440704001d0150070000352203403101341c1d041543c1c81c0d60f60010786500d024255440654003480440e03304007071540105800b4011400b950030344404a50078842640d004441b400703111b0014502800041146030aa400307800441e100e49803055062b034100440c440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 677925197 1250 677923947 677923963
    0x504030c17070503070308150907020d030b04110409290603271510060302040e0a1d06070503011d041203020a1106090d030c08010b030c1819051302090d0f050a0203 72
    0x490340e15004d002c2c0300748842c1c0c403001c11200304689d0401c8618002c04025150413010500d88149a101c0007030140035980c2d6004010451071140110351950340d2a465080580b1401c80c18a0003480910403104000311a01520000e005c4040c10700c500c0c54031820000d01001d0f0324040402c4a2040c2040320b000a03d40c14400c01c1e0302c0b41c84074440002d280c24110007205850005070f00c032400b414410003040010305078400001c0d03030241a090b0005042000180190b0080b203a4140c3c0400c0c1c0d01408003080641900880654169505c024103462040030108590b003400320183c07009481018410700d0228910300c01e400038800e03a103480c0307014208582c4500c0003914150054030394048540041081c030049640c540718504d401001441c00c0600341d490038042120b00d00c000b4101c01e00e85040042e10141880410b00c20b5403034540c015114110046d0024070360701c400c10031401558441d81445c12020300c0f0f0703401070003500c0c01d480d00109071031920710040d69840007048203071208994a003c2c035003004025a4081c032403d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 677926447 1250 677925197 677925203
    0x3030a0e011206120501323c010e0a020405090f100b070804030b0702031317150f16111917040602030304050708241b0a1709010504030c1707050307 65
    0x811451101c491107400b03800d031091f0003046e00350005030801d524248046a2500801840135903008003150b003951080c0c0207410b100c9070f42c40c210041520b00c083c4031580303c140e048070182072640500c0d4642d040030106920803846810380c0400341c800031610027000300d911150030042c0c0d508603201d040e58400905106030041082500c040d08081020002d02480c0b64003a64030010a00c05540740c907141c00344803188000c45018544108400d0900501c21180420105c445031940350316a484c507240041c92500195812180c007112220140705d48441f0b82d0240b440e241058819801034503458407405462454200701441c1034543d0001184145800068a00144050035166010b0346d9240b078103040061030401c0d01d5000c091660301100040c81c03040741480700c030031130701044030407a4016485800204802058807010313024a000b000135030300c0c4544e8000c0b106201c1c0b51940c4070b1100c0ca23a62440c420a0032a041102d000d008508100114400222902c10789010404204409814481140c545601c0c45d00504000c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 677927697 1250 677926447 677926451
    0x5030c03130c1401140f04121106030f070e01020a0305030a09210305040311070b0703050901030902150901090f050a15050c06070305100b0933121503030a0e011206120501 75
    0x4001c2941d2160003080210090b5000c10301d403404124032203246c4e100d544648002101000602c0d010000341510710041410b00078485900c90808900d81a68008240c8070240482e00680c00e01040c0d5001059a524040c2c1507240c007411a5100304040001d071080d800111102c2c00040e140c1a14003000700540340d03c02006680c002030300d103424600509103d070301c1e24082c5500d50007004104400c0c041c8004072003c0961514042e500d810b5045c0040e00a40900a0000d62140340d0703220711413980c08400040c5c400c0c10000d0740c45014541d5100294802210b4900415820105c1110140002041c41802031070031019480c015141c10329005a090801e00103a9000d4000fa807110140314051400d04400303805010b451202c98941511000000c5d25800c542079409200240c9850144c00c0451844400e49500c080310002c60342d031030020500d80c09403001101c4803030400848145030740150600000391081120503490740214650700e0801500c1d039012024602181584404d400308900350004080303141c003481a000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 677928947 1250 677927697 677927729
    0xc120e012105090f120405010309030516060f0b011b0209070212030a0609062322111902010605150f090409030509030d021f1505060f03040309050d0305030c03130c 72
    0x40504050f1344004c1081958004a4001e405003000303030803a01120801d08000a13000c19910301070f20319014541103101d20008040304a81400b4440c3c0000c8003090807030200300000d900c50001503038804601400c80450b4140301c0700c8403005040141c2c50784d8205042d801101d06940380060303000d540b070b40112040c18003180ca450041110080f20300038003018011042c0410b01c155824140d0303c2d007400b02002c00c240b24001e58400e84869248000d04e20903003e080a0051012641c1408817000075403081a100303103442c440c00c0411303c8441c410711441003500c6004140c50070007030705865100032030b0f00200c407901c103074038400c20000107150b5482c03180030f40740ca20940320107407511141401c06007400c0c1382649007829904a03104200040502e030a0014a107400020001000000078114807101c40303c03904225007061002407118144080c4070b0281d8841c0344640c0d5012822070322171041c40110910700c1001000302d10240b012032000078101000d143e0002000b01c00e110400881d403a014849643e40d44510b001841e01d0f00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 677930197 1250 677928947 677928961
    0xf030311010501061b0309051203071b1203080a0e060720060601050a0f02030f16020a091a010c2901140102011a01050309031b0d0806010c120e012105 66
    0x550200c410312010001c220540c1350000182524152504040301d5020050040c000c150056117080c0140102030015000d4611290000c1e58903800003800b80d94085000500700d41100d0484ca641c0103403003114640c0c1c04001074a41d010382e40b902002d003280b18580c1c1c6a030040d0401c060b081001c64800c0c2c51598500203881d1401540c04540d070f008070b503011031941040c804c021251740c000d0112100d0b02b4045c0f811180070aa20241241140109203644229000000316a011402c0302c241c4081418000c5549508031075860400ac000c41d040c0820f0680390f010320040941080d8001d851502c9454041c4d190350400c0d901c041c0030742e0118510225091065888640144440901407002c07107050f440a00080021400c0700080070408610506114100f000000005031103076400e00503034114100c00c00c1c01ea981450f15641054039182c21080d007100252504001816941c8150605100c0c641c2003c80b01000c0c0080b0f4004541100c08400814184108541e43c0340c402800c62191342007240801500143c1410441 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 677931447 1250 677930197 677930207
    0xa2601030b130302060c0d060b1612090f050d0c030501050f040302060106020d050d0e0c0d050a020f010903110f010e03161a0307050f0c07050d060903031d07030311010207020a0f0303 80
    0x2e00032406a03106040064000398000a119420158540c07a250b110565508424050011500700507070440c400710381044200c103003020740d01120303200d80030995515000c0c500c204d81552440c4030350940b114207424104200e08104540040e91401149180c22203030720b945801d800d44600b903402170032585007607040000b41581440102c1c0581050710180241621040d4000c01c540103c00c5540d42141da81d117112040790758100b02e0038080c03200250000a081805060040d100d0325a82402d03400740c401c88141d241d466128204000941780d10080800440114405201a2028448021b4113100380703440b203451196020060849491581d00b81100c00e02c0c01d000b80040d134288800d511003071940040c418131803859041015a810100450030094640b04103058161405030107a00c0990070802c40c1051000b030140c250081d0009501a8400717101c220201e0440c1e01c0200b20418603004940c100520900000f0311072100106041e42d0000003500b060f0f001c0d0002607852181d0352002404c2004080c0410415400c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 677932697 1250 677931447 677931451
    0x5100e01020406051209010e010507020d02061608040311150c04080705060a0e091308040b0d0c091a07030903021c1703070210050601050705060a050109061e0603020a2601030b 77
    0x12100940c00e00f440c281e0050490f0082c90300d1a60b165105400003601d0301001d501c000691241400240102c1c245040040c0d1102e41c44403440c40103010300d10002c4c01030031210910307259110443e80e0707080155907280ca04803207214044c0052400c6001e02d48003200c040c403054056501031103840d406240e6603498440110301c1e01c0140e0b030103d8000c0c1300502486110340d400180560340240c007038420203d140d4604124458582e0820030007402c885021801042d0207509401400d11440c20b00320400808181c07100541340780c8441e101d00014044690641c2c64030102c06805010760600c24145034900948030390005114012a4180e0415a82e088010b141400440601d01d42284491050140303182042040252036007984050070b511a600c1c0d0f4081101070b442481258440e94000b03098411a003001d0340300801401b002c0c454003d000381001d80101d034821312006090110008010414000da00d003100540c065081200100140264941d03412031903441110080905c03d003516885e0129811483d04204240300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 677933947 1250 677932697 677932721
    0x170112082110060e0306060a17070e0106051c2d111804140106080c07020609040c02060609010b040b1b070f0303080405060a091a04051606090305241f0504090510 71
    0x1140e02400030503142c0c18941415200709096100a6242d1003e902d440c0ac07025500c4141032040b140700000d403a5030b225002d491030094207920801c18141c80f03c94042a9003c107640c1c0c10060a60301c558401c181d40040c200050210003060110700300980310024181c1c0d17000650220a40c03000a80070a110380303060310800000070401040a00b8039410070030024201e00009201d03c0c00c103a030016a0406554032102034541c145030052084c481c6400030308009494401c01c0d13500303900030301520002140407070268059905a0301e0161100342002c1c140700c0050107030702c0d113000c02c40e020703020b154000700d007880006041c01e0280d4000d03110340c003003410146840d61400318010704c6c20b842c49107013064490004403210111180b240011010200035100d50405900304000b8030141c40303da4903907920014a064102100703408582c0100c00351040310b0150a100d000e040034000681d2200c0150700c0c00200540a03001c48801c00481c1003003110309403619640494201c80f412007040d0303542c1e4412110209484250f00804451b091 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 677935197 1250 677933947 677933953
    0x6051e0c0607050d150b0702090105010f1b020d05121c05150103020904110301080a03080f070e120a0203030a050c010c090e13030c050607050703170112082110060e03 73
    0x60030390552500e072107028000c103003040070020b034100340c00b01c0381d0b04110000400b414204107001c1d03032140807455aa01c5030608a001700003803000003403958021542040b208160781c0f21008030380401407000c44400d2454800300d0340080404041404100708000c000c2c03000c1340e0b21061a54603607614268800d07880070703511240354090524017000f02c00040d1049040c1042800c2c00c015840d03c620380e000501420748180c640120301008000090220000180c1071841c82c0241c8880210b0f885042401322407240072101c0034081044004145a2070902c250452240b450800070703540200c0d95980020b056900c02010480020000724081750f80c103400384103c0c3c07514515810084406450b11b00c01051004004042c00c00b102500c8103540107060040701d000d0b000070350102c107681040c90068006880740c0c01c17041c02600060087c10561503134440c2e5103082816100b03c50002091004240d40315030319507000050449000c08149090640700945c030040d14000c0d082ca003d46040030b41040802400c50f44540e017500c1c8254 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 677936447 1250 677935197 677935207
    0x20c15040503040302090c1e191b141e070609172d0330190902010e061812030703270b0a020c01090905040302060a1a040606051e 57
    0x1c100008960803aa4140c928901075a550800a4064000d66410035a0280485503080c401614807005040340406482a00981c010381d900480d40499a506103150385d4020785c0646012910078501c2d022140c045c0c200b101e450030714614a102800f4610003108005900106083c0700084e0481c0c00ea0b00038115085400407407a042c004180e1ba9030141a10510301800980f01341c00104298944200c00c4000301d2003100d0b035641c1c80da000c14000342d802c0e554064201032041d50030000c01041100c554000d14190500c009c0783c2e203142c4e4040006100c1030008032305008600080d58444c1d01c548015207201c040904a2003e40b02c0c41c40c05011442c0c0c415000d241d842c1e0820014100003a41090350050401243d2141c10000c00708064080c006030305076001110050380118400038800c1d4001201254180d080e230350713104076070758070311044050314029140200940c01c82d0300005e81e400d0b101d501594128503003540e04d18040c0403901c04201215481d8008000041000910031a000d5402401c43d0958030340341e50047c0b400f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 677937697 1250 677936447 677936453
    0xb0a1e0801050a0e1b0a120318120503180301020904060b0c0f01021c050603030f04181803080a180c080a1b050901060c03030e0d08060f01090b041224020c1504 70
    0xd2440807400310f14544032617800b4081c0c0e0b200c500f1110007414a040b1071800758582d80c14040c00f91001d042501c900c0032002000030414441518200c1a441c0d0300c1002141490070310030303d6640c66070035520181c0d0199400c2c4200766a0b03a0b210b01589004000e61a0a1a82c80146006450402c0458200c02030260700411812198000c004840c216a008500300005c0310707150f200009041d4401c0180a80741000b000c10040340205182101d066580b08040042140c2100507100c1020220ad412001d00803d9a1400007a2800d8594010240c4d0320b03101e40c1e912002200319920094012425000b1003510390108001400700061140342c0550200a90708401956143c5400036a00f25014040d1404201300e84c2800410940207030000403645030b0700d0050f030740c0401050b5401000124100c4246d44984800009140309500601c102c0d010b0301c00501c09585800d0400020706c2840852403402c460841c2d211095501a0910180548404403c2840960344002c0203522a01c3d000742072205004941408040c4800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 677938947 1250 677937697 677937703
    0xe03070b220317090f0d0602090a060906050a082d0106020709090213020f070818010807050325200a0b090d0801060c0309150e040509030408100b0a1e0801050a0e 71
    0x1654610389141e035641c52134004a14107031404160240c008003041c00c10410006150040c0148000c00c0d688a850259a0705088813a03040300d1207481c01041d001c100410440d44584000b41d4491051981e0020401e424240c17034141c4c45021481d00011003800005101007941405000700412514800744049030460f0001040ac40c3c190100c40d1942d540021010b5100b001c12050b158400e400202c83e90721940c2181c0c2100c00d000c80703050724a0010f082203000610150192068074019401c0718440d551a031010f0001545002d03140604e0380501a01040071000052010181034603184614083c0c0314459041c5090241c80c000508140e1103034018140a90841e9803140400f4111225443c007030001a0302c0d420240c45039650340c2c009150701402c0b880d25a040a40140e0030800e0010169010001ca40c2c400e03110b41d84900903402070f0709258002070144e80800c85a900110b80d0001d004042004c403d9440d0305064008406e82103030010f1008039541000420300030b10031203901004024090040d21000203446803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 677940197 1250 677938947 677938973
    0x10801110418051302180a052206050405070b180405060a060804031803060e061503160522020c210910050d060315140a0603020a0302100e03070b2203 66
    0x2c8a96490380000c01055145a08012198010305001c0700b4450b4845868404107003100d0302c2c0080c5040001064901003603804807840b40002c3c40840e581c03407107107503034800203401c01034410f842c01d104240c8049041c1074800014200102c0550b40044081400024401600c40082c04940704840e006410840160042d20285e4003070340c9031604001150300b40305040b4054219400140c1550f01c1c208800c04000d0000071120700a5115802d00c0b80c40340302c080c0401d644c50960303070006223560840c008100300e507080030043d1820000c030b04c0454610350141c110505080741c010703609298865010030940e452131100000c0000001101e00b154034a4880540007088c030042811005508000d80002c0c3c40c000d18150341d020360040c582c018040a41d80d0300f40440b80d00500313203c0a01c8091904050080b4000e500e891003124200c0e42d0191040003080e141d602003140704519500804140107150310004441e513018408807020304400c808140d244d88042d558110904101000f19401046062050000c0b54405188079 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 677941447 1250 677940197 677940239
    0x405040e1204031b031709030115051e01110f0139212c1c05030601091707030c080615041a030a06060e130b0604320108011104 56
    0x40382108030001030382440c03030550001d461b490040502e10700d00000c000051855280460091100c3c50a00a014903020158828164403003203840e001a50407504695401082c41d05061855010f076489103081c3c246821310070244090707555110048414030f000b4400040f560392a505d0781d40100c8013076007100305188501060703a00b80f1401603984d603446030314000c1013100448034010500005c0c40e1448821001c0034000b030610443d04d011200c101c1d01c1a4001146c3c082c600f00921512800034035144282c60960010300300034100b142564002c50151400c0c0518000240b0b640d000300750345031450400180040480e0801800350f00700744180400d40319030000710844200225400515800c4039901101c003801d0700c12400d030f098020040c0c08014420071b070744400c00f110416680cbc040741c0e50310362810411704150204001c0009a00902180032400c180d480118104520001d214143c009451040c20007000c801c3d01072121102030300107000080307081c080ca14804030000245400d150034035001213450300c0c01802c0d071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 677942697 1250 677941447 677941463
    0xc060f0f010e1005060705060f010504180803270309010e010305040201020606131d0a170703120f09150914010b0f010c05100e0703062007020405100b030c0405040e120403 75
    0x10402003c42c803080c00c0020000101340c565140da075403600300d40b220001ca0f0b40150111350340000240301c2c1014010040340110007813081440600560f100b010940000c0d000783c1003582c208010144030400001c041800c218480011500d407042c0800045c054540803080e14109030a1009100040c2d800084603900001c04440407018140c1c40340040005200100b1a020b903a54014203002000d28081182c0000b40c0c05030020442d06040840c0e00c0b50b041c80349200c0140092046100c03010303100c46592151042c09503125010420701445d841c0c6541c01c000bd60400700d10142e07100c1c801e20400004100c80f5a540390324100921660040d040000c400041d5620000e050083c10340545080080c2440f200070403640d56401003040b956480349250303449185000445103503241c00307594084440000300301f100d060340c160700c8145492900c0d8240406444e01601640301c4200e401408a034810000c00694490114036056a49880ca014100015038040f01c1c9a0b91240d00940505c0020008990031a403e898000031a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 677943947 1250 677942697 677942701
    0x41e020705011b030603050f010501033f030203071706130902030102190c02010f0201020f041a070b04060b130b030303070e030a050a060609050c0a0207050108100302090405030c060f0f010e 83
    0x12050240c28103081041d0030741041030342c82c0840b0703800d030b40080240c074000c5048500700001281503278202c40c005e0102828040040070600c801d00100d480240c124050708042d5000c020050100c2d8085e04070304004540400d80110400034620b6015030751058141c044000002682018404034510042507507000b0052901d84503104203546003501152201c0c00c108030700340c402c00411040105941c80d100720480c00903410401c2100d80038414001d0b10141049034034650f1400d4609021000b0544045110101c814400c1c44290003003076400c0707413082c0b10701c1c09900045000c50207038040210a130101c2c038a160b103043c5014401c0005450000a0300d03400308080c01c0c0488045540301c00a85800b02e04880203019200b01004c0d0b60070403165402c8030013210021001480315840c2d03c41040024064070003614016030000c001041250310900009803c2140c03507820520150b26500800c00341e203800c4609440d1940001680000c40b0f400b00100740d4001803024921226041010078108145810b100741c0803244003000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 677945197 1250 677943947 677943953
    0x51603120209120606030c0607050705190b1c0b010f0c0b130c060e030127260714070509011a0715091505010806070921080703021b041e0207 62
    0x20495420b084000d003d41d40d1101291025903480b40c003100c5031406401001c1c60f142c46410300000352099031b580000900b048606003002d10050709007580f020401c0d1b114140340007811085207001000c298558408450b66400e400d003019066070070005800b810090401e40560300b042d0b025944e4003102e5400905001304d40ca07100d03c1c403001440c04107409400032081460015411f40c0204011a00030130036030090086203030030700c4042c1d81100b6036440700310001640301c00c0c5000210380d494544007014408114800280c4000710107a441d40060000b211114254803082c01c042104001042c000c05c0c04840e1004158100a40210401c0449081c4880041c004c42c0040411266000c41f103050321f12a8810404440da0b0308101c0111144410300349e0645203004004a800c110101e02d940c0b00d603100d501c079454100e10b4210130841a180e11000c91460300c8034030b101304001440040041041314041d6005001c0e04680c45148000b070903259000500c164a4028000c154043c00d00110a80e0b00c0300c0c640058a845540c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 677946447 1250 677945197 677945201
    0xf0b1f120b03030d05100f080105040305070b04020103150b130f0b070f140d0305011502010b030d11010b031204150201091101030e010212091c0305040f0233180105160312 75
    0x2441d4200c1c41d00740300801210446c00607018088510f507030340c04400143d0f25445c01d400c0369011349019000032005c201d40390124090350311040c3c002c0c0c4107241c00100c24881c2c2d52200340150281d0810014a080000c12400109001581350302400c860414841c40520b0440e081c041c1c2d00c030382080201040c03000c0017490709002080040d040345060040640e1080c0c0c01c1840700600901c000d0250300c040b0140e00c407030070050600c140b080c4202a00082c004090014034440181d584e4181d10700c45103040c0d921030042210640702801000c49012075100c500f51100d0911069440b00740b00a25540b045a140c0b403105400725a4083c0700d169004000c1c240040d0208005c0a07260180c410242c11103846c20124051103c18000000c0714110403450740b400c201c1d80f01c5244411000ea850945000c1c08036030090400402600d0003020084041424002c120400511150091140c0d2140040b00641c64808102520409548400d0496940092a00c2440c2c444a854a040c02d104010b0018080140c180c0520051080503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 677947697 1250 677946447 677946457
    0x25120219240206090a0f15020409020a03110a0c02040f06050628020d090e040c08010e0d020d020a032019051c2d09180506030c0a15140702040f0b1f120b0303 69
    0x5031f000d5545035101c02c1d07024065400803400c840040d203004039017482d2605801c00d076040c0e810281d440582c034001071303000c00000d00078192000d0401c1c2d03958140000c0310341d541e900508810015981c1c0c0c082c0080940c0b4500340010103002c50b071055411141c071420a09038000d52110540303e0424121049865034208170208050740e030880243e0b90318001e060030481100040414051020b542101e85d66842240d00b00d03110f4225100042c0490b000400384807501c01449000070041580c1c404840080005400140304036044a9041c0c031310350880d0058449403580819031207100c40361410f0855922650b4042851800303880040b58212001501190407114420b80014006141c2402d254503050695070b02440203001c15240c65100b07229041c1c0d01034550400038892400c43d0700c0507420180209020f1810380c1c03a0501d011221480d41400c0000e1030042e0340c6c511500601e44003000700040d48603101014090400317080544090000204003032000a558401c8170300340c4404c1114804160b85984101191440c060 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 677948947 1250 677947697 677947733
    0xa050405062e062c0a090b04240911040e070513031203020d14010501021203091501030c1508060a090c0e04020a080925120219240206090a0f 62
    0xc004800180316620100d400c129091021207546005401d600320034019401940c813a0b0002c4414000700150314140c0d00101c101400a0004580c01c0e407000c1602c41a40e001d032840103850304125034140000505e61040c5032103521344245161401d4184103181c60710709402400481003200c0000c12000a40100108078001d40d88055031169024400d40050301a401070a0300e617040c185460118041d4040c1c800045040f40c0068004c3c1503811390b40c24900460b940000e2500c2d51038810040c00c83c485403e06031002d402540107400c0641400e05141c81c110481d9650030300c08003002412401d110981d61699020802c8900e000c0300004c1d00355041400f518488028107882d54824030204001503903a41203e409486001c10206651080c0b50449000c2d02c00d000020031190105411541409a10f0607d000c0242c0b0900040c034810b1000e6011a41c2c0c004401c0387d40041e00c0c1240e49124000700d00d225850340719142251070020340090300c2c14149540d5504000040642003000c80690300c0b051203842c0c0c00307030110303011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 677950197 1250 677948947 677949031
    0x6090718140c031f050d020621101d060a05060d0e1f0506220b04060306090f03030f020c03090904031103030f0105030c090702032704021c050a05040506 67
    0x9085503060301d50f03410841d0b0065141c02851240080c040861000e44240c030b44c000c208442c1c400c984c1c0c09002168003e5901c1000b4050301e1600340b0144105060507503c203030313000310310306a40c3d13803d16000302042d80003041416105100c01c0d0602021366194a00c1c00107590b02982c403552a85082a5408040c1148490200c00e50040c40c10401041a03100000311082d51100401d00441c0c46030828131080409050800c07800d20030715050300d40300e00303440e8210310040b800080c00861115129140c01c0c04640070218210388501c1500403081c02c15402d070280040c90b03070030740d8411810607000f01d243e80d4980c851241440e00c00c680f01d800260400d40100c8080104c50703035031408c0302d0303d82c42d061300c484030022401c1c0500ea00c24070589120f200c50346040741806108901a601442c10882d070410616100f80c04c034601811420584000d202417078403244054034418994624010000d5015404441140e4000c2d0001340b10b03500b0f146c01c01c4046607001643d180c00100020310000d8841a400c1e50b4150f0900707940c440440d0107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 677951447 1250 677950197 677950201
    0x3c03190203031e0c010e0f0d0c06110f120f0c09060306031e030c0c1e04150e15010e030703030f080c070204020f030609090d0914040905030310030c080609071814 71
    0x203c00c4070050002ea81580008100e001ca41d58905569503849030161034455000003000203d00780b003000130480c014440e40340441d617504807101e566200c0d00441030b81144100c005c5020200410048159900030302d0220818016003440c2e03903910036a110b489012805070030000007145654030100003030030346240ca2802100c4010f03010881d05880358401c0040300400e100e115100c071102c0c1b0348080c540e200d0703141d030303414450301c0010368814007029000043e0044011380702c41000050360498510803511034148070b00c0c2004000000320014008000c1c0d1500340d4007990060030140b0000390014200100d0692030305107049030b641e400c900144107201d81d0350001d40150001c103400b01034100b984040c5000c1d83d001c941c455025941e064443e82d032900400008400101c00e800100004504200f01c040d42c07860182009c034150400752202ca25552056405035802140480101305000e000f43c0840054151701c0c000c2c143c241004e030070441c0e4810042c06610000501180710500080c0d00d0f901c59003824100416145280c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 677952697 1250 677951447 677951497
    0xc0a021009120f020601061d03010e061006030c0e060a0e0604080a0c030303060e060d0809040e01150515030907060e040b1c0312150b0f093c0319020303 67
    0x4550602e9a44089000340c1d461600580c00070480d58183d65060740d4290001a910102c201201d60f2450341c1605956101103100d0210024003c240c840c440f010b5282050500d08000141100c0c074034000715003000b5a401400c0a180e450108440c10071000349001030141180c200061618442c1c3e41c80124903100da40000000c00840100d294212070094408101c0d09070388401c00c22650408071003031688409014692400075921002801012070043d00c0000d0900041010f90b003101c505112842202c800729408010b40d00d021200d20800d2000f4000e594110b0400042c140e44da81c10b540104010301c075484100c2d4840b80c40301d501c1882c80c0e100041c20b04090309440b240c040e4205040c401d00340c00165188460b1846075215000380007442e01040d06d0481514075100c034248207500101418407076040c0070040420b0540e54091500c01c0c0d4141c0141e104406035a690448003102c0c8815862847c0c080020301401e00741c1e4020603c2404502904030030741001c0c40600c0001e05501c40c0c110000741220302180c800c400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 677953947 1250 677952697 677952713
    0x924030a0912080915040606170106150f170405030702060d050708071d09130501020a121404111306181e201305060301171b0303030c0a021009 63
    0x41c0d1030050000c02d100d0210040222070060044a940038281d000e0713000d50a03011207414006601600541000642903280c61440e41582c421a410120b540e46441040c8114081b0340d101c40000501407d011441801e810805000820701c1c80b00f049144420100003414041c0c2801111040c517401032002e687d41000b07101c071000812054403c0c2d800540074000080b409401038850f1003901094190640d5012220700801ca030044005141c580020040d901d604d0005000740081c280713908407500da00d8500390701c20f1202e1b0708465000d4808402c851149061002088030318aa80c107100c0400c0e00c0e451803c1010500d8140502186d0344401584c01d41d0b01c2d240100000c40e644449040090980003a140c0401d038140340301071354202494140e161040110400fa03000b2040d00608816060410350005155500d000801c0ba0304268000c0d442e41c0ca088400d036410220901400c1301c01c03050340f038843d442c243c88080801e07524040200810b840810000b0030824040c02080104c0e03900d09c0e034a01c28058070b5414036010311 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 677955197 1250 677953947 677953961
    0xf030302031f03210908010e0a03080c0405090a020c010b0a060807091d06040b12010204090204030b160c02040e0f011109240307031e020a0c0b090309060924030a 71
    0x2e01c09000704101e079000c80203904290440e9040031183c207200d18055011200903d6450f40312043c000c0507940007480c0d55080c0240c42000c2c80000181485003038904000e4901007006007024068403042000344850f03551840c032a030300120300140050f100c201001c0740600400101c10325950003085540001000b5900c10210f900c91b01207a036400085a5480d0180c0561050f22414401d04111003000106981816484030901c1d140060407103140f654414005422a03110343c1200c284160000f90520602055050481c0c020703600c141807800f0400f0341e1100a01c0841110070081c401c2d9228020840b6a040400010240084804c020402d80742c0c5424880301661151020368003c1010403020f802c4000e01245802a03c513614040d40d24590f02c8031004c030001c1041c80c610a613850101018005c4e60320349403025100c00e507095203412400b0b950703605112406410080482c582a0b1041110795000c0d10783c0c3c016600e5441f03043d00d400f201202d14984160702440d840c0801c074407220011042100c080c0191b00a08 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 677956447 1250 677955197 677955211
    0xc06010302010f0f0206061c08041404110a0516150f050f0a0b030d0e01050403201201060807060804170304080a12050105060f0a090e09070e0c03040327030f03030203 73
    0x3210f00384001015158103140c0001400035170400ca0015205007402032014044211030f0b942e0282d280560b945419054004e9000410210742c082503581190030b0a00c00c400c071380403d08007000c0c104001c10700f0040c00f40c460b600442c04000500000c1c40b0130000c80c00d01c201802e0040c0c800500241c0082080100102800c4682d03c1c0d80c200f0034000b00700d81e0103061181004003030025001d4624484488000c0c2c0c4c0c900d10220105040007810080000816000500d00c0e141900c11518000b0240d00b4004002225450255070103d603450034604001c3c0e41c07c0001c01c18125031a6050141617a035460800182401c0b0510101303141840000c01c01081281c0340f0000e0198002c10b8849041c0d481102c004401103560034050150843c2040006040e2059110b01070088403110f850541c2d041e540361850710489410070b91f608261030307204000600540c10364080c40c507406840b0398030b02411440d0944005041d41c1c041080342c14903001c040310f030b401003901c1603064802640e001403032003003151014a4002d000754800c032450 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 677957697 1250 677956447 677956457
    0x9020a080a0c0911031602190b041a0f06100e03070308030402150301060c0204110c0703030e011101290d0503030f0a0b06070b060f010c0209010b03010303021e121c020c0601030201 79
    0x200c1c2d00c107284e105076541d07140e41030001030541d45c400394868007552196a031041544213116484805040504040207823900c200070f52842400c1515091509903020805040814100e03000c005c442e034026400c1d00da00120880320280c1c6507204100954618180704541030701401400030100032f000b451402540580d10036a0713000401c00106c0c006c00b000e170000b13000300c3d000140c46a00030000b520345a002036040725641500c1503d00101103248500d0060954800c40210f100d103542d0724025038018168284030301075000203010204555200c0a1350514002401e000d00d102e607081d00816440b280307902068140c0c4441240c0c1c0d41e00b030010008000300ea04a80e08803440d0b05100c2d070300303189082c000140d1750400d07030003e0301d80c0c007548a5070108001c4d9413490500303034104099000c4107000341e81d54480c600d00074148052090366070750440c10b000b81428038420010070100111000540c0d0f03041c0000756a80b502003002d8503d5110079a0324003802d0861480041e1842c3d90380040b5441808030000300307006040300d100344c0387c07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 677958947 1250 677957697 677957699
    0x601090501020a030206061e031903081003020a050d050717010203060a0f061704170d0b0f0409030c14191b060219060218030a03020f120f0f0c0109020a080a0c 70
    0x4a83e605400500103005800c03000100d00a410f0442d15004034200c42c0c1e404105458070800070a207030000450354507102d4a003a56224081c1074100d0b480c01d41080244089507491811358010035040c8440313200390f6009542c101c40c1082403150a01000700903001c4480c00c2a1070941c0701b8842c034081d400940705948180c059910000e080442100c0340c02c11250740e6220045495070b4440c402c01c1c0107500500590300c00803c00513441c1d56008410050400703080607440082d4040080d01409441e041034030815008510340741c0d10101103a044800011515170040401e40049140003d0b00d080c0050408017801d069840803848003040682c50070850300310b0760048099611599032800301e03942c24080081000030b06100058034049419070700140101e01900070035000e4401c241d000300c3d14040c1004030a9005800809c40020f2440b024440810341400810003a41015120f10030540b440c031800c0c95070486400c0000e0201c03000c000c00e402004d0a80d8000f400c103600540d9482c640e40e240d00d1401003c5940c4001510 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 677960197 1250 677958947 677958949
    0xd02070618030c050d050703051c08160c08030705040509010b0301060f030c050307050a020f1e060f0f060f240406020f0a08040b09130603050a140f0d032d0506010905 73
    0x41080807243c000300907840113803900c403e01503496002d0005980500070280044041002000142c902a07501c15440e550f009101000a01015001d00001d40305541c07401071003c50f55008007104c01790b640000d1402c1d6a0703141e55600355007501ca151701040d0400311080000400e0b09410025504072100c0343c54880794003042c031804404803102c0324a4a0042101400858003040c030500c043e20340f8000d240110760100f52240c5200340f41c41e00240072034080740c81c1c41d035042c3c51400040c0611a0007029101850303419003031060280c1e01c403000c01481140100c04802c0c000200f5543c46404020107001c451034502d401544405200c1250302c603014060240c403171003801d902e100d540000c206017110340100701603080c10704040c03101a269110741841540880c190000480c501840d02c0303843c00a5208100402c6100b003585044000d2118400c070390400e5070000071111402e18400300c0e27907010480c5e45240010b459900e02c43c00c060308110f02031011400041118510780000c5043e8441c43c00381074242c0710200015940c01c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 677961447 1250 677960197 677960237
    0xc0a080c0a230f0d02040807451a031c020a06020a0e0306011706100608190e011e061a0712090b0f090f041112060d050d020706 56
    0x4010036002824010541c1d01d180314100440e81044480c0d516545001090b200c140a41c0d0400c3c104c54466550005d020070140204019600c020302240102c105021311501e9089030200c400d030344c41e040c0030800c0084000b51303000409a403001c00082a10401c004080d030441880d0240d0400115400707842036407424030700c00f41174040b1b00001c80d1850340180403a006039520540030390003aa0b2803106000c904070003010700742d070140305503800382000c00341180c8034840d04011f0900d0310708041c0072200c920100c09414081131b80e00110155004804082111000d4180c2c80d00b20010403d1803000318055103014100b22024090100c6004194401c1030140815034503030145c0402c1c5048500c00d8025106c0c00c002900000b405000003400b0450f4500301100b64554030402c58201c0d90001c02c03103620700f0a00040c0c01e90741d898842c41c00001840c0582d41040305400f005581c5000c4d00c07038003000660018144000600f240c0e0752030911071020354030106a803a0207540e4039001e5560074440c0503039408618412040b014507100c80c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 677962697 1250 677961447 677961457
    0x4120303201c150305070608070f08151207320604060c0f1e0c0303082a0d020f04080d11010513030309020f0a0b030907091b030b0112050c0a080c 64
    0x1000c2c807001d1424984101100900c00d0500114080e149a03000001051050041400415190301d41e1312803440c120038018034407100001c42c0c40070303c0009020312468840c0b20308201c910040a850221540030202c404030310b0030110341c0c0000e024000107464510b1900c1500ca0311000134000103140c561407a103420405c2481d01441c0607080c0001c004c000d0300c40207c5d11104020345454082c000c403254403034424201403506c0c441c0c2c03902503801e03841030a010410158415201a44803c2041c2000600c01004501e075002c460400450110007401181d2103005007816412190900c0c00b0958440c1d817607550351419a200d8601d020703080701007110340c0f0700e0f07140008041c09014800c000301c42c18540f440429680540040003203a0080c1e8000c281048003132600d44440e000700307010303215204803503442e4548551140d2030406980c11011400d41450641c82c620110540485443c0d0381e90705000c81c40700e203d440106c400380000071000281ca41001c00303010407280f0100c010b25100c02642d541e1003040d0303200388401106100d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 677963947 1250 677962697 677962717
    0x302120714100e0106080a02091b0721121418070b04030c030201030b0303031b2b0902040e15041205091c032006040b0403200c27010e0c0412030320 65
    0x8000c00148901e07190101402b051030300b0b601201e0a02500d0340340c40083c400100e004032881c0200b000d4010050b41c108a04800c1c0c915811010f000381c003a00340380341140e464040d000d1100c1c40e0361a140450707440c10500180e0b020300180c3d11007503119980c0c2c0c201a415940c4034030050740800c0c54840350b91020b04000c0f0489101c0c8902c12040c1004010014039802c042e80000101c2d04100c03501c070319560041500c820a09085884841e000c1000507017401008103c070202c20301c21a069203c400e040c115201e064071000c3d40203400080002c15051400c00666640c03041c002d915611805586811918034a45280c0c070f00c8540c007940d41c94005240038600808041819282c2600701e6104400141c0010101201103500c54802e142c900706281c90300f603510506241081c115682500150007041c240e0500708014003080207085202c00c030713038441240ca03080c501c04103009500c48400c0c0040000d000d242003100711401400ea107071b20100540b540e410001c0003001e280c004406a21500c00301e2540300903100042c0c50050364 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 677965197 1250 677963947 677963959
    0xc0a0b060a0608091b010905090f04020f010801120f1a0c070b060a0506180103090c0906062a0308041403070c0e060f06030a090213020a090e090a0302120714100e0106080a02 76
    0x2c00c3c060303480c00c20b0017103400c0b01d0304201d0041808960b0b030711030b140d03410702070310040b103101e032842c01c291040000610303034040309038104841d62004014108000f034130084a10b80200d40c6501003215828000c89440112520500d149402028054001c403224003c010050144006030f80944840c4200595800d0745d00ca0030364410014407918503c92000045452030300c105040014240c2013540d218890824280d003c244100d0743c0c0c410403c003054000f080003541100500680840071441440b1003140e0720b51020140c02c01c0f0444002500300045601400012440d034001c0b6074449849192441000c0a18000d60040e44182004580241040c0b254004a030600400c043d045d641d5050600c0010322640c901a0381c000d0542649a078aa40103200034903819903a81e6800561500b030100d201d8840f040903040c0d401545c4030b84480320100350f010912400b032941c0080c0080c2e6071060750074000ca19011746d01c0d8240460045020039400d80445500a0a103200008003e000c5c859030b800016031030303000d0b803a0b010390458 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 677966447 1250 677965197 677965213
    0x20a0302131b030605030c0604050d1106071505270d180b0409050f010b0301080d0806010e180907050d1505061c030504030b010b180d020102030c0a0b060a060809 71
    0x220785115180c030079200310780700081d440700781042a468460b82c009802000c20358841d001e10050030705101c64050745006440441c9494075010204050000c0340601425240d20301311402065502c10003142c480365040b100301d0000300030300068000200000c0e00e00d65507044451640109408a101140c02000b02e804060709948081c03800a8600802d04070115107086904070380401c00e041040050000703084144c80000e041c2c600801e07450790f07042068010002d0240240010007105000050903203a04030a407400481e030b511607000581e401d40310b6009141e4070228403801c250380034466807042d91180007000100c0365459074841c203100d1414000280030303288500440b075480ca001215002542c1060b030152210629104040c1c02c0c4082c240368610403000500002000c2042c001e00302c03450f9000d00005400c170303483c000081a8402c4100001c07d020340c021401d566190066a000707005032000f00c108113040d90000c0c041860a00010842226100d114418111020031020b1140c1b01c0349110700152401001c0c62 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 677967697 1250 677966447 677966449
    0x9011802092a07030302031b1e0702061b030c0111031009051009090b07030c050a050706410a020909073c11010b01051602030a0609030206070f0804020a0302 69
    0x8070310240c05640b030982e003148818940c400c400007040510301942c0e0058481c00c005000c0c00c0001c0c0130744e101c844e1504040c004298480324100542c1e1881030107070711a50b541c402d6840032503807e004e00d40300c4001c90113042441502004c00440100392085844000704156948640001294041565200c0c0c000410140510034400b00ea40a1900f20703140026000d4120b6940020710706855642800302c40048144050085c0350350103020f02681213045007440390a016404100500c11f009808016004640710404181684024101503c1010b0700994440341185600700c1b61241200301003007585520759103000110782d200c443c030aa0301903020080c4191040c1d295440c08455002d4050952548040148200041c044840071040c0781058941d081c2c0e100c10f802c15038040c210f244240301c5002d040c0d051840040300c50f07901101b00c0b6080103d8140c3c0380c5500c6c0442c00032a00e4400d252000a0120303140009000a040d00014094400d00b25030b40c8040d2048c01c044c40440304080c00742c50094112240700c20034401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 677968947 1250 677967697 677967721
    0x306051f090915090c0f080f100507120603080a0f05040b090f03120705070e06060c2d011107110d08070803071b15060f050108010b0d020910080901180209 68
    0x1a000d080000307403ea81018980049071008601182c0010b0038020802094030080001001480020054050703182000c10742e070345548819120340340d030503034075400500c0f2279004100303c240b0081c4002040105c144c6924000074180c0c0090340341800308200b60200c8620503c501c0444007950112400103042880d5001031000c5000a03c41180d8103009400340000210300c0c00002c0d0aa40b8000c8000b4070b0300a141032903d640c070180242c80b55024080411461900c141e00007072089010400130480b024590704c8000000c0345041c4901c030b8401550030880402050351204002d4040503004804511560b26208104051f05a0000c801020b115042c488580801c9040024660140c41810100224803c144401821281c1c0c480704032400c0b41c2104a15607048c3c112320683e0042c0c891420b00300c4045060000203810580c05201d24801e860300003444c01c445d50403a0301516601203003c1e0203403182e00324484000d003517103000711001841d40d1b203401006008100e0381c080f403840a5401800400365901e40b0407001c81 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 677970197 1250 677968947 677968961
    0x5010509040f090f0f06140c07031419020705090a150e0604090b09060a0c110c1915080406110403030f0e03161d13050c130f02040603060306051f09 65
    0x12010f90354050340010450300b40d501c0141a208905410040e81c0c1c500e000c5086840840c400c000124504042003624010034040f19240354060070312100d40209104051910b11812903040b070000e010a5200c0319094001680c04156141143d040e00c682da10500c41000b165544200044880d25050040011805126545801580240c00030800343c0c003645032450070300340984540e1036a0340280100310613140c051151590000441c40c00d0b00d589014851065038a103a0700800601c075501c010748003040d02140f0890304006113545c1301c0c41f640c590342d000710203050060200c8054a1043c01d0400340c41e110510b40c81100c00762540b544610300f00b180b190208030341c046480c403020368151003070040410a1343d518008090003401c0c40041c642007900081950013000754041e000d580b00e104201060f0001450104030b00c408880300395100300382c0380c501c1d00b280c2020700304015030030360114800580852801d42c0340d0044400d580c06554140041c0d01d074800e10a0203d515504904d050401c40341041c4501d15951300880 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 677971447 1250 677970197 677970221
    0x141209040b1f051c02040f0504050711030a0f030e10230103031b0303020c0105090c1c080d020a0c0b010303050307030c0503061e0406090513020a0b0c06041b170f0c0a0501050904 78
    0x900300345140107401c805c0380e0042e00141941c2da840182003107a4030705400f503985d00160b18980015441d84d25641c1581d00d0140041c80300034058001841030304c00303120364480307800001d1010898403900902440c58000308010322a00e4a012008101c030651403100004003812a681603072040650861401140c40c02d51980c00200e08164080210105040c003d0040e2070003406004090108501d600c0100980034140201c400a00c0300752810110211340c07214180c0d00644007031540940c2c4c4a481110440e07070040c1d140d5001f00001c14050010052580c004042e46c41210035440403c01c01c20070040644007800215841980300e0103189814010000014210b200210090000703e82144c480994000751402140d00c15020140c0d12807000941ca0420f400c58014200068410b2a0824032110980c4815000300041c0a540d45000c121f040005103c4410006000042d041d290782c4a9400c54152135100c0d122400b401d42c81030b943c6002c103915149503100210381d8140c56451030012480705000150109003520 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 677972697 1250 677971447 677971477
    0x50d0305130f050d18050108040b0403110a060506031002040e070e03032502030d03020c12070c1508060102010b01030b0f13021603050406020601080a1e141209040b1f05 74
    0x11000150304000b00c0b082c81c1e845500540b40c00c0c2024200206030400c21081d64480c0d040116081280d41d803c61b0300b00e5042900301800e035015984904058035000b00407400914107225584803201030200f40c1d4040713401a80102c1c26503c0300511134000000368081c5000d0a0349011005020030501170141403441a00c2c0c00c06000d8030708044042807945d003014110141441d5000001000d50301310f1a040c0301107a007448440c107045080c1101184402d540b000d0800700844a248001412001e010051f5040001441071440c1e580d60b021a49030004c1c108081039885501541c2000d12034440c0f07600900031280c0740740c070180000519241c80d000708a4212040c2d81c100c4d0542d50b007006000d4a4034801551000254081d4a1320355680d46010000ac2c9401c00c140e000c0e50643d0003c2c00b082d00010046104002582403000511080031040d05081018132900309070300d035442c455548540c1e101512034000e005200c604075000c00507844810240f00c0268004030400207691045207001c60720b04d00a4006d0b00c6161105004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 677973947 1250 677972697 677972731
    0x7050f06070903050c04060305070e090304051c110d1e0809150a110303160507060b18160e0f09130506100e0601030b0d080d0b040204090e0c0d050d0305 67
    0x50a021090750349800103140000c0a0061000c10009101d4011040e9000c2000c240365071a031940707c2034180a00e00900805a0120760188400c1007541e01400005042c03203100101c07070000c50208100b0f07001c100c90006124242a07a14900365864402c3e003504010420110313507440c2c0d0382d20a01210610220741d043c0e41444010700a84031903030011090000815196a1440c40130405406401040c804542da07501c1001048044101c07d5810389400d2618100070707442c1d13000d0380340c000054006c9040141d00302d42406d1120000251114a0074000c00d15801d0740c410b000d020f02421101201e82c0c1c01400d07004041c1c0c0a0802d1a0300780140050b6000da240f1210340c04c11840c1d07954481c1880000d42e8241200c0404070001d006003507180610580114003400d00300f10307070303840310000ca5500d0b20b02120282c010351004c41c1c000015906900b00b01404200240119940c070744521481c001003123403442400451003580d04069850030286204d8142c590484000c000d81e05000c2c008134003815008004698092081c41 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 677975197 1250 677973947 677973973
    0x204050a0e010f09171321080d061502030c0c0904020a0f0303081006031a040c050c01020403050a17030105011b050703060e0f0c300102220e010f0308030109020705 72
    0x2140c1002c000c0c403040c010803080400d013440c54002e00380401085d54040d0801605101ea0050755070141203807244111801c4140c1c03249126000601700c11006044031100040d1405420700b51391041c42a5406101543d007040098070007242d81c3d0260507042c02c00c943c0110ba5528440c9400071a940e80948001c243c904000d842d401c903d204807140b62b004402203a00e580900c484c10010b540d0600c06880070b0310301000349910300c203010000001c003050341c43e0081e645c600100385818882c0307044440c20410340b0001c0d9600c42e50303494801d549030145441a1229480080c0c00c10109140104807812070358140e5600d0009001c100a803100308812083c00c036000d00c0f0303e00300040041da06019900c169920640506030002c900c000d0142403c26540346c861142d108243c0d10b610f01c81c00c14880586c2a6026041880c00c8114094032500a100301ca0030b0503035900254040c80d100744209401e0741c09580c426002000640d03641e2402d10324151040c0402880c042c0c00380300500c000c030869030141030103d0082040b00d1401045107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 677976447 1250 677975197 677975201
    0x5030a0f0e030a030b06160605270c040e0d09030206220f05040f05160e1c0605040516030206040b0c10060306020301050319080a030c110304090203061e0a030204050a0e01 75
    0x1d42900c5403500081016402c40f9054840e04104a02c02d486240c0341c0030400d1030200ca4000244c3d4010044d554410108604d681d14400d071030716403031203d41800038081070400026039803100302c03105074400c50400d220595903601c0800c1c036a030407065076202c00d0000c2c0d056601f0003940d90044030513014030030003989026110360a882001030080c810030541c40a25810701d0180070940b1140d900041e84c8504000a10001414016161408841d580b0740700c03240110320400148181c4880040291000d00f40d10024140406540210b010350301c2107080b50040c4030b400c6540c168882c46440040d6110300706000c00c020034003800000308280b00c900c1b170582d21905c030f08ca04018101d980941080c2d40c526030201c0107010301d0404000e044c01a042803035410300711482a40d5405000d01c52404401e08154540300205181c1c6c0c0036030095480c122060b41965121500e92002100a4101700c0e4031620031683c10010408118107000c240501410141000c0d0780305045400380405000003030910144140d46141d5988101003c4c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 677977697 1250 677976447 677976461
    0x10e1503062d040b010c02090403050c0c040509030c0106080a0f0f080904051302100201110d0b030118050a060b0a0605031b0c070e0f0f090303150f0604150915050a05030a0f 76
    0x2100030b5a115488201c00d201c21a90750f011000e06004007900010050390b10745018561150745403400d540d603586208456400c00c501d03200500d0700681017209010318200048094a6088440700c000c01c20035a640030800d40e1400c0380e11020b022603580203507030000704960f0746e0204080782c0142c1e480c0d443c0580c07000101c0c04a4504840d1100314121001000c421490481488942c00b016031000388503015080c103612400e03200320f080c1c00360001d47d20890a2030a4400b034011744900f54501807440016281c50030700d0394844a000a0403228180381402c0d04002d4030307192070b0440685e51b2503600d80c0e003183e030b40540c1500c4a90040c00206d896076010b01000c007441400b0401034024024100064482e414440454800040082c00c00d22102482000f0810310740000800e40342d0044009000604406803100810500095050011f40045001501099240c0da4034000c0d042410300741c0d205c0101c559510b13a03d000e06090100c0074030001307004000c4490101c1c41000034503084200780c031002a6100c024444002141c40c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 677978947 1250 677977697 677977759
    0x8072d0b0a09170a031e0e041a0d08031902040b07060b0d021002030418020901050f1c0513231b060c0304030303060f060201060e0601050318070303050c0c010e150306 73
    0xc44c40c100c08069000480f501800c0f0054603945540d00c00500c0038140e0704458006501440e0340d910030801d00b803100486007210041c0900380b4000e9407005c0c140701c3c03400d61045900c905904c40e5090b2081c0000c82a10855044400503140d01c3c1c280000ca50390f101c09465015061079210134002d01400c050307518109440d1440710250000e560304c903e49501440e8040b0880314545006206101038866640c22008481a00301d10020b1141e88006940c06000b10141405174031000c1850081045080d1000109414401d401003011000c06545909000450b9450585040d110380011071601200d1290040446519900410280c100301c101c80c44039145030842d0340141d00080d1915402c20808140148440140400c0d02c002c1c04450b050a004d8141141d02901c424104040000080e008844d0803241c0d030142d00b00281903070380455490a00512031342008066100c640100369181e0340703540c0034001d07400c01e1080140401038481c4601c100300400d03400c0148042d4200c984e682244100c040d40c890b0788100c1380a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 677980197 1250 677978947 677978953
    0x103200307143c031f0e070b13240909050c070204050a0f050603030a0c030f0c05010e0609160e04082101080714090702060f0a020d0608072d0b0a0917 66
    0x12031100241000c440603d09000f60001c0f40c10104441e00c0c02e0022021003400350f8080b801d00c040b07950240c40e103103050348081e8040b6030110b42c44201941e485424400c64680c20400b6008054429802d2094988410340e040820540c0408102c00035240c0c0119034007040d13201590b0308209054022809660b8100d03807800b40e035a40d9045007104121203201d0241c10a00a50046080074441c01010700f10100d620405000c0c0001400b0304441284941c00d072812455001d00240b20203100c07c08440e50310002601c058102d805001c00f1541013401c0e860407035044420540b070902070794a0f5a00c0b0341d4815480350141040d03960f81010200d84005400300740f140240210310040240074540140c4500c011307502d008291103005c28070180083ca560010310590006400d03078940104d5103580c10014024400c000c0c1c41c0010030304024001420f00000f14107501240c50107941c040205010203440c11410702005005455a05126018044009450041c040d100d1641c20480d0710780f40c035504c1c86542030607143d842d081c00e94 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 677981447 1250 677980197 677980279
    0xb07140709021603080901060b0d090c080c2b0c0f0303110312060f0d150606080c13150e040f06090e06010501090b0d23010320030714 59
    0x118080090340020300c80c11100714102002c851003081e282c01c0401c00a0200301c0a0004140042420340c0120001d0600490740c541d2000e00c0c004d60005405c00400a490b52040c3c240e00040e10b61004c02d40a0110340c000b03140f030542c42010111150440c800f0304d0900083c4581d8581d80002a003100a8440601030041c21a40410f00d1841c00510b40f00e10364107602e000c0d400901038542c042c12701c5c2200740c0e0011021642c0036141034510003c541900a4003001410240080c1d688d500480714950024040e0303401580c13824415501ca204500e0303144641c1940408403e181403081084450038071501c80c03840103502d0194140040700001070180c0b4000241c03400b402c2e54450003002507145600c0740b60401d410000c080c265541c5401d001034050207862044412040c070000308a0318041040c2c0c0710341c0c4000100c3d882c0c0c0010301c00a11181e003000c58240422927030003100320707140c0f6601d452030487c84003450001001000c0032400e00d007007080060325176600d190b040906000401501303203042030402ea0607506002e880c1505 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 677982697 1250 677981447 677981483
    0x1060c150b060d0c020a060f0b010f080405032b240e130210020a0c080c0108070c170703090b0a03050a050a0b280509090a1b140d0c0b07 60
    0x44100380c0140c9a803400159403900e449890503141c1005100d00b002411080540302079003040880300300180030910301901d40009508940c040310696600380e071018102d42800d081600c5000e800c1d640a0182e80c0240424543c40c0040c044000c013800b4940c42890200001c05201425211f072a6502c480d0441d91442d0040650340a1090728001d180451015440d0b0516030303d40403d6502441c006800b620700c162443c018603000300107502c00f80e544403200500c410350b10100541c6950110382800d0010b0802d501040d010351040344074514964000454010070001442c41064a5010300070440510200c0d4400185200104c1d010f0449011151008142c40c1307800d04440088620081c401c0c3c5580b0b14242d17140107a5142c08903001c244140d822501107039140010a44c140015017903015580c032a40350800c1044900001c55040b1402d4881c03000750a00441c02d0043e443d920340d003801821880500034450842e00e2400691404060740180d4a23041e8050326240300500b1307030b80181820741d8419008080c0c1016 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 677983947 1250 677982697 677982713
    0x109060206163b0f010f0806011809050103050c0d0218072303060307080d02070501140c01020c0312060d0f0f06150603060302150a05090d150504060e010e011406042301060c 76
    0x81c003c822240b098400b0070010000c3e00000410160000b04428800025020f0f40038480c1d00c1640209000c182803aaa03444200c4006040d09000c2103d041c0220080740255040c2341c071683e00c03980e40c01414800023035014506100c00ca41d00805c08410400c011015000303c9074015030800c0700c2e010382a0b02d182d0b42d19252060601d44911a404290b066101e00c0c00040140c0d80401c496003616400d10700040145001c40e8441c02c14020500356110b40c0d4400030311089502400401000080d92000c401e45035a138a52040144580c41c0000107081c0c5041407000a0000d140c0030000b0481c0c84c480c89000070103070540c3d138881c03002c188203410180110f90b40d01010700540c600b143e0000c00514070402103d04d01080068003c015014081c842405110200020020096650080040c950010004212916260030201d02511301401d2031007a1f94031307101400c2120981030007025056200301066906076118502400000d000e0b0610f541c03081f801702024079510840b00c00c0c025000b81200d0740c501d88595210300b00411 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 677985197 1250 677983947 677984057
    0x80a030b043b0d11120c0c0312040302030613081605211c09020619050703110d080411030a06050c07060c08100303050904060801021c0506010906020616 67
    0x204104007285a2211000040d8603c0c03000024a0311001440c0c11128513403800c440d008280810840115400300c45000005100207460012011602c04105a020403d403510541c007010750580c01c8000040e0440c100d00c400f001d000f0344100d140510f80020a41c40c88c50400c1c1051003100e26800c404d540318940703901c200505948890706c40780103107800c1130000040010645c003190006201d458100300d805564a071070070744401e54000030f1007005e8520403000040190348000001c0700440ca00c11030120400364000b819100302003c940b641410b603100e075210942c1914a41606e95854801d040100001a0507805124041d2000c202125251081d0f0300d4082c0540e0350400264041008050401c01081d112104800031243c26080c540d5a510020b0085800380040b60814035983d0b0000400c6402c40c0c510800001403290090f004000c5612280c00445181c5803d1158100590103140858200c010b04031986903515000d00748041c0b4184030784030310b45075032181d5a082e5000e0f008008114202d0780003000120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 677986447 1250 677985197 677985281
    0xd15060e12061503070e0a0b01030f0212040204270602041d070206010e041a090a0c051509040e010605030706080a05100e0f04111f0e061303080a030b04 67
    0x4510410000c07552991410001d0007030248081601445207261018483c2d400604124058694a031800c584040050001c1e02550b0780042d00e82103001c00d10610f140300395649111411450455900c1d02d03020080039012011404d401900311480c4034520021421400400501c80e007c0562074500d0b00601100c194404d802c000c00c1324000004002070644c0c0400c1f820305680782102040a29225820300c074140c0e1610488150745114030130305010303825200080c104a182d01c030300d40b00c410803502da0f01032001140d0302c112101c030030b150140050350091134250412103c1e403251000005030141c0d5000000e281c06034562049002c900480309010301048203021752944020140c034291600362a050070200480c100500a641c1c81460401117400c00418588000444c600102085a00a8088910402c4521150b040d2022a4203400c03400d100d400e007501980d1511040b440c2c1e40c0362180ca940c45140003503100c082203100701a510440c2540c80d9449204411000100381a02107a60341c0032810104240f025110f90 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 677987697 1250 677986447 677986459
    0x4060315140a030818060d052707090902042703080a0207050c060304020f0406060905120601050904080901020a060501030b04021e0f210a060509010506090408070b04080d15060e 78
    0x110340380c0d107550b05994126640203030034951380e0840725440a00321784408003da41c045000210b1120a10083d00b00600600401081303c2c603680341828095107850079600b40701c226400c0440e04102205060f802130440d1400030b080410040103080c2c1d921040c8030048110100669461104400c0c103900c10440e591207080b0050852411800f92507281d6642c8540e110280300302c400000040454440c0c010b42425014050028480f49454840103020441c850084600540314500e02d180c0c0703c00e00160b01e5048070b40180400c403054440ea00e9040700c9510031010503065100b80040d04001513030034803c00e0f0003980200b81c20062804c1620410060030101220a08650032054065150707a4a000144110305411070301300101441b900203005040980c1c101142d0075020f40e21505d02409004c2d0025489170350390ec0d00800c526901c050421000038000d1b41c0292501400340841000030b40d18541494106010b00745075030034800307040341c1c00094610319071005c010980344203020050345400142060140340e0032944 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 677988947 1250 677987697 677987729
    0x5070e03030f07020d06020906120405010b06120f0405120a05031b0f0307031e0e101416050c2e0506040501140f0a03080703021c051204060e1204060315 67
    0x340d0390702d074000d4039006440b4104100c04c0008000041e81128880840907200c3d0b900c480001101400226080f5410b803029402e00c100c050840c58081c0071111200910014200c6035298811400c5556500170012651032098100d100b07070050488020701f0340c031041540c07611740d40c1c0380c03403c20040c880000f80c0c104c00b000d480900090201ca04c07940152548419070f49000502c2e04011040305050702841003403030604074a00151014100004070b814200148050401d110001e0f401c585841484012190910510485039110142038811802001640318003811200c4500c8000d42e039581285502444860a0300d050700400c203071003443e010b0305901035000c0f03c04006c15890300110700080760062405920603c0810310702c00039580c90101c0c3d640919001100d660315880f0703034a00a591080d00c0c41c101d241210040c12080300e01c52158007241c0ca00040400146c00c0e41c0c98a41c2c0c0c00002d02841d5040c2141402400900c1c40541c42a07000391001300640e0b60042110035041c01c842d42c11486607045210101031482d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 677990197 1250 677988947 677988967
    0x409050d0f141b1e150603030301060c020105280908011a0609121c0801081612151b1e0305010f05010e181009050a02212805070e0303 59
    0x1503601420900324094507160f40e801c001828107860130344d01c0a0f00d203000d00c0035192005001840b0344680c454041440c40a03140c030301c1056a01d0009115500001d2844015a00154442c0000e0103080700c0d0051800c15643d904800200c21a1540440000161034018200060724007400355104a90441300722503420101c200210b8198454044a18000c80d00701c3d2010440280c10070464500e11650708441c0302c0c1c07803401c10000380068002c0c070807602e0600c80c1d80c3c00b8150700d106403a0b1803021929140c6a441b010f0b81182e68244c1c565000120b07034259982c0c0d80c001d181449041c01c0d84404840c0c699902ca5410b4001481d40080c0f00050440303140401d031405006002510180c6000c0d000d68001342003095400340c0150006c0e02c0e81b2002100314150070425070511408080c0340c8000000d690071102c01780200d554000c6c40108a01907071120500c02041c16040c90300c2c4c101c02c08900c0b5041034000c6803c00380b245070040e41c81030034076401c07502c01d081503038400030420083da2108408401c5041100518035094840c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 677991447 1250 677990197 677990237
    0x80403031d120a0909110408010b010f050403060b060912102012040c05030709090c050103111e0c0a03020307051209091522020720100305060f0409050d0f 68
    0xc088106007150000c3d248102ca4020305140000b030248100034844100950301c04070071508031f842103400c20f42c07c10342e080704e9942c0200010502460140d5a040c106407668032500082d02804441c1600601c0c20000348005844100540c3c41500003035005200071250207103004101c401d402c1944c03121048111030a0341c52a40c4104403085440005558145504d990030007545c152500d60000750b06124422001a0b1085940c0240c0566800740110301d43d841c0d82c42c80103400b5076240a000600b200c004001d0a00302e075190034030660b40340c0c14405a940c01d0420103501e252401c142203c09501580c80071501e41d04000b0304000805210656020440c20f04d8542d2007c0b0300d140070040c08000b0949601000002a902c07000d4861201c951002c1c1c4011071035601e4282c0e44002e60007004240c440034040c01d0081001c1164055032114000098103182c0c0d100c20300d140440080a000e450b05500600d4140c10740c0250760350b400780c3c034211405a030152032800300000b0003030500000c3c1510740c028800500910303100d50000b9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 677992697 1250 677991447 677991463
    0x306020304082d1605150906090d090b0301031e1212060f080303061201110319152108040302063402010804020f2215090e0a030c0201090306020a080403031d 69
    0xa0740d44c121580c2c00500e03044e07040100e01c3c1340449a403080481000b80c05000090001d0044040c40d0a130340b4404081d03103048030403207414020051799400400c010000690141d880c4003001e654548081c640080b269900b0840507002611100000e0640a0b6160389910511401c0d00a289180640010700c0c50400c03096140d01009290b148100c5000c0c410200c010000e400c80c1c0341c890325440349240c0d646841088031480c02602da114600070b03803074407410303d900744a000d29071703000d40d00580582554000303903215034141a04809411641960180b10020068640902030240c0c5030360041440d40007900240c1000c0d031800d4070301d04c0c80e80c8111449510800750b41c120911070740040d015100800c1c0da040c1d01c004140c2689800c070756101007001a40b6504a2900c540d8040c1d0b000500340b89007030762031640d5010300200341e402c0e0009025581d04284000000a4060032400e4022441810035107102540d80e20388008a0b00070002c204041440b0728100410507516128203d68560070b94020114442c4804a2aa442c1d0f02c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 677993947 1250 677992697 677992717
    0x60e0910050613080a0302100c170a05190f0207020108090714040f021605010f0b010c0804170708030f030f1321121a030c04020a14070206040306020304082d 69
    0x51120040b04603c10300f02c0504000e6044404050700c03843c00940e665049042d544489141690101d40e80f44200b120000c040741c04031041c0c0a03a00d4603110722000740b0000e4044041034000214030510141d4500501480b41c3c8114401616004103000141c00c40c400208040c03e643c010342814403424138400c0405a2a0030240e900142e465042003600009205045080c203090301c1481c080e000300481504044052021b001c2d0031f1108480920040d03c04440384c0000615443d401d201c2403010041200a80b004200c03108111025150f07240082d600b1944080d50303a4524035400400c010152501b2018150009008494a01000c0c5c080d2503024108100c441c101910140284800202e68402c82181c0001c102150f0208100281e01e0741c0101c410f0089500c860181c0035142000d04a0300c0e03c0e2003511010380140d241c440c0003020889400e8116401070340c0499025070b081c0004004941f0500c0518410b0303105231240f0f5507035113504030002d03402000086c1c004076102407040d0741012456000103031511908 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 677995197 1250 677993947 677993959
    0x181716030c030306210203120306130213050a15020708030405100f030b130b04060b0f0702010807020a1a0711160603020906041701090b07091203121e06060e091005 72
    0xd646000c402410701980920040301e16500c40c05d200c0d81116206640b0030f4402ca04861281e25a5144640b10380801c56003207a10035000c02034181c010505030014121040c9142422031007035100c3c00002c21140c0207030082c920300c03c0c0402c2d8142c0c001ea0100254000342031594015420240341200140d00c1c03400a200302d00412a00001e245646070194200d01c44400004084059807600081040c0003040c0c00c000b940c2c443ca00740f01d8000b0340407039900121b032100c0c07803440c0d021843c0403840d0b0015100003902626580451040d0403440c4007040040340c60700001c40c440c54034055182850b074030040840e00341e8020204950050310a018107a002c40b50440c00708c3e01c090502585031102e210008046010f1503002600052a8a01c6548601d0301035200764083e61081c0111000c0340c035581411211400c0502030341c500c1000c0812010301082c003a1900c20142c400300d1303101140c00400708000303140505016000b540020380780d001c00e20529801885083c50301c0c0007920340704103a103400d030b0001121482501c501e41c010340e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 677996447 1250 677995197 677995217
    0x306130506090a020d0f1b021908161e051614031c0e0303040e0714071a151801150f050d020304030c05070f03020109090e0c130f18171603 61
    0x76030020300c50010090030030844040124100c80d40056032411f030b4401400343c0342207110b01000b21808400b4464010511a040200004510030303c0c1d024198142c950513400c5110f50300581000041c094000e10606c06001444032680c011108064280c00034000012020440c903c1d0751000607114242e0803121952503d00901d4140540f895040010050342502000030041101040918441c0c014411643c4241c1d40484aa400001c0350145100090200c0034100d8070f00340d102d000d20300c490380020300e00c1071420b100c10120000030340300c3e030950342405601d0814000402001185480040c4034021a003860b80d004104204000c14034070030900ea42d64429804004a8181445800441c00117603000045072011900e0398a00c02440061348012030000b07480c400d000c500900c890040c00d0300301450a000340000c4440200300003004000c1242540b020b61340d004d015103d6242d50140b01400700d0305250000904c8210300b40707040c251100b02d4643c0019070003001070081c1800c100c14010181d981500d0820082 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 677997697 1250 677996447 677996467
    0x50f031b0c0a03020d0f1115071e150f02040f080a0b18070e0c1b030c0f0106140f181006030b180103170d02120717101208070f080306130506090a02 65
    0x20120303000450742100440c0c14402030404823000800e03800d405074001c0503004556000740030b0f8201141c0c10080120700403e0744121080038170303044280030100c401000344c01c05842c1c080c902102c1506600c120310b03c0d40040568002d03c0f050105a0382c10444441011002442a0403000e544556a00c07603800c0d0a54402c0014a070607003101300781d44001640f01102c100180b00c1d403088503070300e4124041c1140f440c01000d4110101042c140316080c100d03041100100012515801084041d40c18141b0f0382c3d4000b480d488000b03603000010b4166034400c01c401302656403e02c0c2805801000c81d1054030010740200804135004108010561005044941c45000f00a241040354450ba100f4000d038020031034214000318421110343c00100d0003134415216561352102080700351240c0d000c621000d5801e103000751002101480300a003103415040101e4050f032112032910f80325a85129240101e100280e4012a002c002c0c0703e02c81c41d14000d0500b4241c0c000c402800345052050024195510150400d121560700098004034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 677998947 1250 677997697 677997713
    0x60a020c060309010c1e020d120b041103240f04020309030f0a030b0f031507030e03040506030103061d060c04093207030f0e070909050f031b0c0a03020d0f 68
    0x30600c0060525522420010200344c0600b100c4034541d008075011500000c46e80d800507078001c240da602d95000304a01c050755401035404440c038661410f50503441d014002c1c141c2d210f0340603805200c0c44151b03245549281c01800d603030201240e281200511640507641305016500e040e01c00300441d508072001aa44d84440784858a1449000e50000b07061202068108285401d6480b00c070130b40380c040e5600c2003010380307880c10140c036101140081d04501801b038001c84d6080d4440d9000c000c1802c66507084a00e413035101c0001500e41d0704241c1c400c42d82c1e0f07030316030007005001441101098407441028005003e2800c1160310459180100d005503c141030340c0c0d0f07100100300200003025804400d403a4201c07135401030103441080040a8201c0300c0e00e020a042400b103014071441c030310440c002540010054030750781e410081700c0f4003d1306030a00207030780d03501c1244026003480c9018801017645031150281c041201c3c41c45801103051502004106211300d42d01c20f0304002503150455000d540c03d6102a82d501c170140c5514000750 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 678000197 1250 677998947 677998963
    0x311071226040b0c03060d0b0c0405040626070e010b07020109210b0c04050319140102030106080a11090907050c1005011206052d072c04050a06060e060a02 68
    0x41520480004460070001d005995016900408240000da9a14061400f0504c0300340d81c06500700100140342404140707201c010542051005032050b181c559a6000641500d01942211040c0311b1038142c24400c8bc0c0002502d440e10918100103010301ca4608090481d044005110380503600030009007940c00c40e803242108802a0000c00c1200c4124199a0300d45440c4c0003403200704890700500040459030000e000e03000c2d10102c0b04c00130028455442402000f180340c41d0600c1040783d030144110740c68050300c2d02c203001a50103011991780304c2800c1e02d417440c1d00c80251240d07605120300d00c2000700041d07a03090321049141c5602000070f003059552341c07000081c80c80c60404d50b52460a000b030b1400b2300120b4885648003002c904540280000c2c4143d49902e00309003007506000c1280907203c00901e410940102d4007245165000e9614140038000351016101e44034032010302000c501000403a882c4160007440c1c00e12401e5007140702c401e0100422810641e010b80691400245103121380300c0032400060841c400c000960b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 678001447 1250 678000197 678000227
    0x50906040f15021c0204050f0a080c2701120209010e07050a0f0c02030f0c011101050f041707140d1e020d110304030602160512120f071403070207030302060703110712 73
    0x5204e16410000400250802d0140600c21040c10302080f0035840c1c0394402009980001e00509101e00144080003501100140e40a130b6401c80f40201001e086d0416203c4d40c000c00010240349170450451041007905a01600030300c45109001d070921065941c480255070400c0528100429100d4604030166014500410029414482c4003024031800c0c0003c035250440748804e0301c0386640b03515154405400e803681100c114045049150008011611909100901c860560599032501c1c00e2521078030700000e02c3ca840c540c2c80d03074880ba5000c1e81850b0b0103280d10b0908000030784500c91320480b07000007c0d150490000c00000f00002101e1441c103118051044400035588400c0c115035842c00003821030a500540202a074550080c171030110604021202200da8001c0d1280e00d04c20300e91b540c0c0f00150300300700000d4229020030249902e040780d0162800300440c0038001035001031621500e5403030002d03d000002000700c4201400c100301600c424008100382e44003a64003075284da803150444034084980400c40c0401c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 678002697 1250 678001447 678001477
    0x80306040c0e1f12090807080d0b0907110c06191107180e07080601182003010303051305010219230303040f0c090212010e090a0203160603050906040f1502 68
    0xc001c88005041030205844503540f01c0d1500b504d10011900119401d041c40589002001c20801c000140f08000a200c40e4402900c00164821040e0104031512021200712020030b007800100701d200d0904000009200d0f2040f10700ea80f88c6182520310b01c5001c20380440e8403007440036001c40c107880814144170400c003803e40d04550300320190201c45050054011500d1186160041400c00302c0c0c2040d0220311b00f816a401407541d803d040000210110040c912990b141d01003082c5408500311030721401c80294025806503440c6922100c40007101e02d0340b260030b640300505540c454410304501010603e400322030503401c442c046142c0c803104c11011022900d01c1d2044901c0340400810042044140d2440c0550f0b580104c82209413141c0b11034644080348078840c2c10b0a03142202000401c00c034001501c01c20741c00314601040e5055444d49034042803500156030050100f900703060405021040e410320482d03610008040c02018503080c103496403c2c3d0740015000203008602c044000380e0f0b26411304c0d0100c4025034034440032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 678003947 1250 678002697 678002719
    0x921010f0c0e04090314070501020c0106182a0315030b04030207080708030c0304050f0118170c0d150b18040305190815130f060e040302060105030a080306040c0e 71
    0xc00e00c0101010154103000c1807580480720b8550400340f08000c40d207039054440e1904102c214078145120b070480303241154259000c1042c14410340081c00b40070010018840d20341c0100d1070310f01c4030009a5450700c0000e5180b40035620090b101c2c0c01c06900d1461440c105050015504080042d4102e20750030b241c0025103e0400070044c00b0825900050036000c80320301c41c0594103050b441300240364680c402c0101c0305401d984140802e0001e4907208140d403e420505060640e000c46a01c0825540410594000085610b400c0106c0404020501070b02098203000c135003400b410b40031aa2459078001000d5100006165500000c0c03440791a020084441122620000306840c03501d4070b4010055440042d04006409013100c80810140c003500002d0f00481440d08084480390944050010f44400c06000711441911000b203034118290b0383c4201c9010341b0b1001c3d401f0b8840d00d031171300300079203403c2042c1e01050103a44200081c20100c1e515400382ca070451800c0341d0100f1411111001211558070000c00161303c00c0140310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 678005197 1250 678003947 678003971
    0xe1c03090c0308280e01120e06090a020111030406020a3c03090f0e070315120c09060509013213020a02060c030603030406080a1803020304080120092101 67
    0x7000d000e09400c050381c0454854242810001050518004d213004680d66820030f98a0f0b601400004180480c400c50004030300c083c440c81c0301e14200d016140d500e030300c0d0011103a42d429568042040030ba9804110000c500e41380c50b10f0030080d55081c140304081c041d503100640c0a80c60b003901c6880d9400c11007005000d0403d020009031604070003910000201c001c03a10701e1000080c20303000c1c040300b9402c903000102141e403d0358401c182a07002d0004401040c6060b900340ca00821341300e4188400701909070241d00001c1e01a801c00001000300c400c0e40e00103900c03c000e00001000b090382640071111814101994031245026440380498541d41c81c0c0780340e16841021040c091024042c1a4090b040050040c0c0c21500162600003e0402c648410350703116401d41c104210500c03034103018690710b6410070707528040007a440b0409030582c42040c00c1448200e00603040000c0030002100240030f40d82c0c10780e09800d000090601c0d2940a03038814480c8a0b4041d004426440c00041d0100c0c04428890900118200074441211290 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 678006447 1250 678005197 678005213
    0x40501050705030c1c08010503010c0c080309210d06090204050901030f0f020907051c0902090703180203060a29100305040f0213020c150606070308091f0506010f030e1c03090c03 78
    0x1603440c4001007004000168501c9c05000e04401840d0070341f1100200440d49d00d40102c00c1d800102010014030910010304414050103240400310f40f1451017043d103415481001a0507511a64084c42915005020a10480e5500d0014504503540844801e00c082403e140000c82210420800b039804a821020448030a40040007006042100c141041c07040c86242c0960044620f0102c010b50801d4a1800041916000b54080f580703c0e05107024240ca0002940e00207454054103d596520346a240d10000da034039060f9000302500f101d400034140c8481121031012801d86030040a020041640380c402080030b114111543d65402900608460040425160180041e6000c0600346e250f03840b0b8601002082c44c0704601950103004010b02082c540003003900c3c01c44071054058101031040c010180ca0303010114101c481c505d400c010501002c02c1e180350880c005400e40001039503000c14142802004004110003258000682001b000f1704540030b50700d920101e0090801d900020101c4103070130f07000700c20b1141174 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 678007697 1250 678006447 678006493
    0x1d010e06011809063005060c0313050a1101170108060403030f0605030607020c0f010c020a05101e032004080d08070e180a0510050603010e1e040f030906090b040501050705030c 77
    0x51600c403a8014004095220307082d06418050507e8101901044a4050f101c0040d0b07003050f0003c48200c4181815264103081c0703082d00204850602103100d440c1e21958010b4101c1205e4441200c1a501e030350301d4030300c140303440d1500148000c041580c0c455030088c031000c5c55032028001d40710140854000d0b141035100a952100004101440ba250f643d40d0b07681c00d988180d0662501c50350182c001c0761086d103898180422507003009986001d11051894183c804030f08002010b042d0309240e500842d82c034480d901101c1c111501d504a00b014404100300a201008000400340c0d9203404503e45990b05903a040c0381141c0210560400341d9110f0202820700241a184008050240b40603070400c1015171100c801d4111100341501c00c060f044401400100306c1c1e011134184940d40f0592861011508541005001840ca4400c9600f280c1c000382c000a040c0500d94402c401001800260038180c014038202855007a0078012449254100320001030400200302c0203005413544420040102d8400484071501c25114000c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 678008947 1250 678007697 678007739
    0x180106020c1302031006110712080d06150c02060702010e0303030a060f1e1710021207080609040b13020109080d050405090907122a060503011d010e0601180906 70
    0x560400b5018000c554800c036400f132804292205685072800030191a650280700240c0d0050080c031400050754110741d9161004113126008190780c420302d050500e8200c82c443e4018044050f10449514001a00b10f021103001301e4040340c10381d0300c410300740c801214020360441c3c01a40601010082c030280703040d5070b0482d40c25901074085c4900c980d52100705090b401c105404c40c0500181c10b02d40c080001c801e214009014030304a40003507803c08156000c401c402d0b0f0b03004e518a010758503085010000c8060340290b9541c1c00c40c01c12201c2c007090341020344508211081c054a2004818003910092085a01036122000209022010f40b03404000306a0b02810b1074010744101405400e00d10005540100041150030a0780c092003002c5a0300146038640048465250300c1c2c0d80070945c0c0c50b200c40010f580c0c5c2d1100d680700916840e40d41c503650b9818503404480c40b02d0840d6071028000942070060044002c403103005a441034084c6421200c01c80b01c9200d03070b1208009503100c00065440c1035404540d030f041c204510300143c41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 678010197 1250 678008947 678008959
    0xa0b0a060e01020c01170a0c0513060c0605070c0209040b0a02090909060103020103230403051b0316050d1106040b06011b050a050601060c12080603120d090b0a05060604090b180106020c 81
    0x3c43d8001076803801b1116401a000a4400d80050650050350b4030040c2903000a10340107040c400c032541c0c035052016180d0010408240408440c1c0d0400600340945035000d070350f030324040e00401d0766540424040302c001f8000500a040250000c0c10044030b56040da080c408000305046114181503000c903490340c00a00082e40041d0420203104500710300c600200d0240540401080e0265a8030340302100c094200b03661450708282511501d072600f41301000504048110700e603040380000c00c81e15006140102e1049460b0602c64105410f0f00c8024012511560081e00300302d91501d9070795504012100c80400c80c648110120085000c2010b00c80009200344c2c0141c420011030f43c059890710016070b641d5440a60080c00c8460390301011010038482c42801d900048050200c41000b20840c6100d081c40d004003110a40300c81da1007000105200c142141e06400681071001004581410310210710644224002c40b0300440d01c5d00b00c82d50072900c4803400c9800304484102d5010403541c40b008002d444400808030305105035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 678011447 1250 678010197 678010213
    0x1212060303040b2d0406020f07090e03040324060b030f070e06090f130e1b0d05060105010507080c1b1305070801050d0c030b070e150406020c090a0b0a060e0102 70
    0x1003000801c44050341d011120031410040c6041c00518000c5400c80040c44012142c09004e86028075907020b40041e0006070007810100c4007000f03007585444995031003c104241005041d140241000c01200d05480c6c006040035000d8003045040300581416100080085107841c10000d080003d0303030051405056080c01c07900060700d8000003150044200c00c40039038464810042101e40346007150551000340000340c1070015284545e04c803241141c0520031110b00c240c100c0d040381d820b1a0010b144417500c0401c1111208107500041d00c9e115524a0305028060601c40001210400e22510509562602425208580016001c030f0f4181404568020100f03003e01c0c9402c0e01440783e20341b0b6002da68801c60240c1d407243c050383e00e000100712802410400503202d501c1d0540011011410104403d4440d01c50f40d16408148140032003400746c00c074002051045000000d00c8241300455000c1205c41025004480004503501ca040e0703450002d007800c4100740d91103503081740c002841d160450343c2142301360700036020788051b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 678012697 1250 678011447 678011449
    0x702010c0f022e091212060e240307090906020910050913020f22051c03080c1b010207060b010e06091f032418021603140c121206 57
    0x4418621030507100241d20b10b280491011000c9100400c41c052180100c0c130f100a41d29240400880300a0b0140024420311a6140c82078050140c840202064000341525140c201d41d403140e00380c8009070a40092209040104c07a59408011001c00741c10f0b00b00042014800503d8600700a500050145024000c41c0400080450203441520b10008020741112188401d090003100254002d082c00b83d008141400b0304207001d000540595903080a0702c010001366401e1000700080a86580550032003249100003000019034403a01c03080e0004058070b1040c0c0c50b22000c6080b01514401d0b10311140c801c1d8170104900040c089190803200f00d021080c2c9410507078020910074001e4510034142c174907405c4004002505051f81100d080c05101a03140d180025800b00c0e40d8000c058160300c00d01d080d1400c202c83c0705080c098140e49214101c02c55600c44000c500d0019400380c8a05035100d0a8009018420030100d01020034004504807400c214920703080e944080340c2c1c00304095564008158150032035900200003881 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 678013947 1250 678012697 678012703
    0x603020c0a0b0a061e0f05030307080a0311070204021c0606030c020c0f040f06080d0e0405010e041209030b0a061412070e1306090614130b01060c14060702010c0f02 72
    0x51580c14029010100c03954940d03241c000300141980e600103035035000004101c5405203204400c9007154071281142464895010307507200050304528425001000b0401c0080e10340e6044803485521414045004040c180404145004841000c4d401900014072241c0e4440e55a02c07810230301103880782c00c00103552580303411000c0311032038201180540e0101041c0d9a144c540801c40d0280803000400100d5800c0c0d00345405c105503201640b092450741d10001c281154140c00c40144500351005880c100300543c50480c10092012000c0c0002d009030031026400d62469100c0c2801c0c201954004440b5002814690b2035140104224030415540310003940800c0001d00e0320074a90a41c12030044001d2942da0f00340000620300d0700b00580301000c4c0909040e000000a1160701540240c00d0003074500103080000e0900303901005000410100340035509282650010341c1d4050b4860554501e80780c400c01a0b032282c601615001c070309003803c891a00c10402004405581500701d0008041e003030766140340d800d203013090a0307035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 678015197 1250 678013947 678013957
    0x160f0308090f030d150503010c0309020907030203040b011406310617010506280512090c09070e040b0a080610060906050a05070c0e180d020d0206040f0f050303091006060302 76
    0x2002c3c3c004000d081581c1e09550003018200c01801028440c455a50000a00311000c9140c50f002007038640b007420055162443c11142c1c032070441d0405500e1032405584078401210b050181c0710200b191107031a82d0254403084261019001c0c040e1031040340d9507010f00c49000c0c00702c4031300c0801d40103542d110011601910420300d4011a83c00340600e806980d09000411050b83c0020003504000c0c000c82144904d03108030020044109041a251a0303038658001d1040420040c0041c24140d19a00c40c1d030040516440b64001d446d0300850614040c034040303008000040c09480026180340e4805102c0d9000300d0b502d00041030007805009240b69080c18240d5075081590842800c2c441d40021800038065000c505000c0d50003801041d1080c848107400644903200030106840c00d0356803107002c009211204101d20f400700441d5010a038140000c01201641c1c0b50000d40d12600108020080e15010000c1c50820800701580c005541d07001c01074a45918080c0d030384655494000d40d00d608403504200c4006800c03800780c4200ea0f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 678016447 1250 678015197 678015223
    0xe0109020f1509040506030c0907030b090106030c0c1203060b2802060603070b0702010c23010b060408071403010209090f07020601120c09020c15010f0302130506010503041205160f030809 82
    0xe800d05103c201044024031004044030f070140116040c002c01540c52080ea00d10030f400300d4400044858801040c4030f10308105811000900d0710703002c03d078101e05411603240030000f0340c0144441c004542c1d80300b00310301800060f4002c2c0e003a00700214162a030240217410701c401e100f1914114081d50707008480101d0b0398001c1926603d0300341d08111000e001c82417030030740100380300340c01070400807600500c5540b8404e00c0a46000c02c00300820200b48184980c0c0f50a00491418400459005040504006002c0d8070b6154910510020304100d4208440c191001c1d0191203031003000800108583c0b401d100d1141e44a082143c46800600810001149544c07610b41302440554105010031425400c114061009600001c9100c60b184911003c086025804240d002d01070700518005240f6a03295106000022030440308070541142000104845642e000068076070090f08940480c1d00464061000d5416201d00c10007a500c410300a0404028000b5000098101354483e50b6401616078440181c035446410401000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 678017697 1250 678016447 678016489
    0x30e061b030c0c24040209100e1f1701050612070e0f090309040504081c051902160827010c021f091e0f080f03040303080c0d0e0109020f 60
    0x10908441c1e0110150000441c614222010458564909902ca5984e0040f0180c10b2821408202c11400c0680781c56070030941500c1d040c02220f0500740162110b1038010550240040c614001c04916140104440010a072004c00301040c03000c600660740c041c110841d85d5038080d114040d5142640c071000030b0b00d8000c82c0c8080c030304003520781c95103407400202803805480007000d0300c824030403a511a0b66900c19030340100c1c4941c50459030395605103e640c07154606c0c1ca10488116242008004103922a401070200340c0f0003812006a071584582044452903029540c09400c2d45008101407241d10101c1c0031440403400856040c4680302440c400440b01450581d400035081008080e411807100e41032800503202d001c0d2801c0c0100b40b02c0d01c03036850380c005141020b030344000c110840c141080b0030b800281a11019000e840041c00d2100c100c031007551345e6489684001810440030303400040c0407100860550340300c1554684140024904e01c6406406440128016031141d8240d448911152502d0b4071039146403c0f60b2100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 678018947 1250 678017697 678017701
    0xa0806100f0b071509021207050f040917070f1a1923040204020904090503030414011103040803100906060e01121806201204060501050a050105070813030c06030e061b03 74
    0x1001013901c0c0c003c600c603144036102c04038200143ea03642c060240b004021001000c2d99171402e810400c00c96544907005000300c0c80c1c00050740228010b01217450f1841c0032014003582c3d540c600c0c50300c8003240c0c152101c0640b00d0f800071401c01c0c4c407001c4600c5e50320380540c00c616030818805904821417800c40705003d0780400d26402d00c0c0114000b0300081d064403540315000400040c01e0a4211000c40e041d107900010031505504004100300402ca0840c4061341d20f001c8440007000441c00a0195070302c0d5100152015240c1c0700c0120000300400300b0052a0401b4000552051200e955121005011400400c0615012580404100c00031100c6032060714845000c092031405d1020741d41d203a0740014503400fa444405818a0311540b001107094800601003a00048201c01d080d20301810003070300b1200181c10207072003200e00650801c1641c3e8400190364469070080d800d160364400c0c0011403d000704413584010b100790002030000524580550001c080b00c2001002d4a0550703030b803400b54201c00231841030703940300804003800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 678020197 1250 678018947 678018953
    0x5041401030915020c0a0b0a05010b03060d080705120a030e011b0309030201091b0807061e11190b190203010308042c01030503030a0e030a0207230a0806100f0b07 71
    0x1200302c03110f0080440102540c039034402c0c101070740e020101c458111b52040f00d003101000440c40181d42d006039645000c00403541014140c44880c44081c189500c0780161aa0010030302c031412080b02e11140c0d0203001c541d01d035025001503824940000d510302002c02d181c24841c607041e001c18012502c01896800002c8541800b1610990081c00303250000d070215942e849800340018080c0342c54040f42c0e5820f03c03800074960324200000e4070f444165002242000722101d030703481e48011000d0024508150318208180260f450003500743c60010a1001b80c141314400390b885001f40031020f1804c2e40034050102d00300546000700c1c0d150400364030080c0310040001008010400102c82c5088a0182244000d40f054040c035840c000780751300c06c440030380007591070750000000e2140d01d00440c89203896608150b005141442c61101c0701a46800443c803400c0d03040400310100c0208200071480303184980d10018002d84000d5181d072429565464101c800340c00d01c681e0140e02040051910954008031510701094130b1500c0c0d0265 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 678021447 1250 678020197 678020201
    0x5070206070f03060314070503010c0f080f040609021017100b091905090405070501021908221a0c0105011a07060b0a0f0e04020f1e1c080310080705010504140103 71
    0x1d50b541081642c0c0b40d0010001800d103000748000005884001c10695041004141c215800040c92070180540101e000343e4031074004080d10344c080341d50324078100300b03990f10b06006024094200e0025030103502c20403803603e082c2d000403050700300258903803d85886d42d0350742c0d10000c50003015004600e06400140b01e00c209070f2904002c61801c1d03443c03400d0820348050f03a41c8007080001c00160380403122500701c900284890f583c100459200c80300c000b0074400145545442e680130900c518001e2990b05c24143c2400261a6182581c0100410032500300010b6844c49c4007005010381c01c800b0b101c83c2c8075401c10f0000102d0b035071b00c0700b482543e404031000900e16000c0203550340c3c0c000b4500b09040d250002186500043c80c06421102c4500038402d1207181e14840c9054410450060158607095110300c0000d290941c0701d02c00c845801f10859400d44860f503120b0841e04000c000080c000030300070130161000041154414900c181681281d055a0071524403031f03101c03401503816024a0141502c00361404494140641c866 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 678022697 1250 678021447 678021467
    0x20a05041d25171305070e240609040b0a030c0605070213111b0f06190c0c031d03010b040203010321030b101b052d0a080708030c12010e190507020607 66
    0x4000310030524019035100d03070a2600c1075025100101e0000104480306403050401e6001881040c0307614407150301d010001300d46005000010340200d0b3350300d0910040c2c0d1100510000034640045000184a80e10640100940d008010480c0180e1941e4520f030340750f03003030341c010045003410540403d07080c1801c00d0910143d000d0b00c1511440244180507112800060910a00d0302411903240354200004107480078906075481c04841c82c040000190621010950206205034460703d20b80c2c90124641c00b20b000a03000d402040b0030582d0041c030000001081003803502c40c0e0b940303c01c1540c01011501601020a60840c0c1d4100e0340d50303401541260240032468031a0180014009540000000b0890701e500c0d403d14110300e040d141e0000c1d080c03c102951400302c03018540100070788180700900c404c0035207075030321401070241100c002c002e2000400420300e41c001c400181c82005500141d410b4040da590003103054000b100f0b032480742010502c1c4200e1410070540c2e000b140d01c030b001650011b0039a6141c4d0181201d811030b907 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 678023947 1250 678022697 678022711
    0xf0705030d14071710060809070b1902010608190f21020a1110021c030605030312070e010e0d0f0602191e020604030210020a05041d2517 60
    0x801000680c01c0407403151402d440c0c08203000d80e806107010040038000024000704084400c02100402c042030800c3e07900e18050b11814640101681c80e02c0038840e10f000029001000007001c040760503a42d061031401050383d079100703550003400010b64400d0031540b14198071890034803d200256024011941c2c800401151764466401d15505620b00d0340d4030a0036141c0500d4080050700582c50400501c20f40301c1404074440b40c1151507000340341c52581c010b56038446d41440c030241c822004543c0711100e402640010010840030702034a560b00c0b2422441c909461b0300700c4102000c42d0141c0340d0348038194850585841480b4010700b840e000401c594807039820050805904480084c4c007008800038606040a0b81c860075030740303038407121070000390703a401400f0b880c1d411440c3d407045500280030003002c60b40c00500d0300141300d0804070040e580e1410303202c1240d143c825500f1090410991065207804207e11400c41440346d05500c55103c150660104054001e002e821781c140001040d1310fa410120341c0d402c14a407900056 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 678025197 1250 678023947 678023953
    0x1e060d060308130f121202160e09010b0111031b2407140304030c1b05300d08011e0b0403030f0e0a08070618030209070203041d060d03050304020d05011a01140403080f0705 75
    0x701c074034510440a10560800d00042721800107100b00340740e0900520169040034240a2085502c02d1100c1c1d03524000e5080b0189080b203401e090b100740751414015241d1400f0745061605202d841100c46003000c0005a039890001902a0750050f060002103040d0380c02507502d41d54151a03102e441e120345440040d501c41c0e454240b003944600142070381c2c4007a5100300b02d800b0b1000340c0340003010b19403030908034020030496040543c1060541d41840e6502c81e5440781501d1009600900b11203060801041c4904990400700c0c28010008021060580000c2d440361008c815a0b5075038521010281031042d45800b602c9140860b80c0010014844940641d050443d4031800c5102c400b9a00d940b81c00091500b0000d80c0d03020050f8200103018844039161180781100c908495030035583d20308164000c42d440c2c820a400203800c000c00030010504540c0c4501c182e40c101a080002440000e418280400c0851242002d25001c544c40150300c0e401425410700b0346085076000751803503040014917941d400c400e5005442c104c800f40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 678026447 1250 678025197 678025213
    0xe04031806020f0c09040b0103060207170706060f0506070f0b0601210203060906061804050c0c06043206060d020d02130204050405060a03021e060d060308130f121202 73
    0x1003405000d61008001c02d90080c0811440303840c0003814424040c5010f4004c035041801c020201e4040b055950440e13610003030044c1d4450707080c14600c0700d040500c000c600c000d01d00011948140045a0848010f40c2d490021404070280d8540810606100c1c0c44001007210541c240c01c00c02045c1e0b80b01c5955400a4181030807546c00050b50002c000401e980d001102c451640030003030148a003000c04030203138001c0080c0c40041c82c02d806401d00c4c0703075010361450020340710302d07100e50000f49036840c05000e44401c1c042d44022140b00d41040e2a0003141c0101400c2480c2008082e00f804800b4441840021104d22130440701801d41521608103012401402010980e041121030b9440c2006845c0d000300160104003c21005071100c0c1054108810b0b180050a124070410002c0424005039030782d443c119580d0340e00411503c1c0741070044000302e1040d010b030100718000c452808500205010b1454020500000310b4616054525282d81c8401c2d042200d034000d10040d1100110f800f000542607001c1500010900d00460f4504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 678027697 1250 678026447 678026477
    0x2010e03040b030f0705031b0a05041d0f090c010905040e0705060f04081014010905040309081002070203010509150106080702120315030c0d080f220303030b031b0a0e0403 75
    0x2540c06580508401c14000003008684c40c0b007076400940145180c5421480e41c180058550300ea100d10000903850b0860024424851034050000c8800601d12100c55141180202403a40b413185021503540503415050000100b204c0d00100700085e4408050711400301c1e440c1000144001040441c640c40c01074850510701255039902e59014200c01078100704a140d6135410b10b400c17142001e000551940441d41052041c0000580303144500c0d040da400c000000480b5078403424122032455695014880c1e60062403000e00c00c0c81d9440c1c006000c541d000b50024004d50f124680801d0b901d900c0d141d08600801e031000014007141c6c1c868131b01c0e84d0308016544101c40f682d001c1403020428a510a0300c0100c07804075003249201c80d500301030004492191080f110402840d84948811210b1310032000c103103812500000d902d885686650700325044007000107080c0c981240d1a85070250092400c06e407135900c01c1c03107010350122401c0410710702205103501c003030944254280751030081e10341202c001c2c01c101c060020841c405064 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 678028947 1250 678027697 678027703
    0x911010906230705060f011d090604031209060c05130b07110906060f0d2c0d051b0109110103050f01060207120f050109050d1814060717270402030910050702010e 71
    0x34408001041507d5140035181b1070080d00b81744400c5502003410301001100340c0e000ca2259441601420f001001c2894515000f0080c02d0b02c1000a12841c64841d03c1e5031640d0340030001e4482c64004640c0c10f501e00f6214895a40240541c280080403074403441021001e905060003050340203000900070750b06106030440030317514a421084056040d5075403400c0840749200d0300c2c42440f00c94541c15210800400d0019452511844014a4041403020000b40002c105440c080106e2601449130000c0041c56014a400c1d8040c80d0b450000a0000e41010042880c083c040000103040f6805900100301243c6404420701e007540141a0a039050002080c6040204601f8042d20084a00c02c0000d8414503081d24005004801987d10212000304540000d0001d41c540e00c9100300b075141c01300da06589404151410750500300d40c0804002c1c0c441c0c0e02240d903c004512840f1101e00d035030b8071940c3d03075080580d984003404100c0c002200c0c031441c0c950140d10403134070003005580082d40168261002180d560780d0a1707035081c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 678030197 1250 678028947 678028951
    0xa060e0114040f030e1030150905070e03060412051612021218190306110a170c0703030510030606120b101505030a06090f091101090623070506 63
    0x54483c100c00d04200425034801c0c606262a1411550106840b10079040201300d40480c4900c0c100111104a4491000070b800c0a150030301c500050b03052003611240700880d41c0e82d9905201d000021410600800c01d91030007a401c14080c1e000140041c091541c070b40c1c495091700107082c0000c10601c1410400703a841c1500c2c514040c84071601411001c05010b18000d002494840024244460042c0030b02c004400000c6200607144c0d41c4e502285c01c640561079450f1180c45c1442543d0004142615180d0300303800070650040034180e0310309103440d00b811124403688008d010320750481c0d41c03007030203401084070400285c080d03408641c0020f1030000440106850b59a90011101160040d041e240341c0501d0090410140c0007000354480790f10300c0c0c0680038520300320b40d540c00300006140c40da05000340440000d41c40728456101000a1011078000c0c03102c2c2d2040201d600090501440640303440b411401e11f110254080c1c041182282c030b0b0395540032051541e58036040315011000d000d4800c1008100100008543c08000c0310b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 678031447 1250 678030197 678030203
    0x2060714040b120601170f1303022407080106020609030306060a120c051b010603050d0c1a04120801080f0d1d041d010c08010e0c1e1b120c0a060e011404 67
    0x40e8506001e400900b40d681c044861b00c60b48501c1c0e1007040800041203030300f45d810003400000b140e0180128a002d0381400d10080207450030004841c16403048036101e203c003902405040d01d50315816600d40000300c0e291f500482c0c00340682c0d8410808a1460b040c068000d00d0600c91314988006040306400540090b0761091003c03000142c00850040f404400c004071002c5020010002000042c0c619983d0b96103c816004080e001e010324510000e00b408040006260a4801c1d80c0c4210303200c0ca03091a0444207a1b40c440e0030000080e0000b03002044500340000d00c264986541001001c8190f000d1004403211807017a242d078084503607425003620039a1210b0007103404d15020120502c0c2603d401c0710100307007128003841d40d070020403228000410090003034124032034204484800003580c07500c030840c3c64480c144080d402c006d0001000100303d100012a40380d1100c1c88400d000a41d061860b11001c4035040340581c01c10b0790940d0700700021140005407907511664400a40c030001040e001503c04500c2e500b040115025 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 678032697 1250 678031447 678031477
    0x6020d050f090703030905091f0806070f1106060906120d0e040b0604060507260c1e0d210f0c02100b01021f05070905090c0c0f06040302060714040b 65
    0x40070744010181d0100c0d502ca15000300428503180746490042290056208660003200c04a012441c01c0d491136030b102208010b40d03000628642e9803003482c0c5940750411200a00010506161110300030312071001d4407030307404a000043c40e00740c07030b0081081220381c0051f01e0254000d08031040764070000b07801e12940c8004541600d80001c07601d648030a00007030350010030b1454404d1030308200c14040070b6080400c0d194201c0d0480c1c0c070807081b4501e030030704025048a84510250041e0340468540403a00c0002241d1448044401e0700c50090344080034400e035941540342c200c0700814000c6107140c21220b26080c5840365074003000008903c00c1e03d01d040760000c40e0b03100d02d144c00060b0030500d03070b0036000fa025014104a40c41d0030301c01050041c0440c0107150014400c10010b442240d203400101d000144142e55403405040c0050030710b401c50030528213030840d07540104511562402000a0007041c1d5a01040c060310540d091380150002e039a80ca401280d521180c00381e0540c5c0da0806000210b4010018005420324001803011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 678033947 1250 678032697 678032701
    0x16080916080d0e090408041505040806190f0603080906072901050a0e010602060610021f06080c1e06030403090f09060905010909050c011103041206050103060e0a0b060d0f06020d05 79
    0x300800320f002d2260098010400e541c00d01c000640721000f15012610085145880340b000322034216498030507507004890520812052007400716490340c0c480d1000d65204820460070038680a00c6c81910514800070b00220410700c980300140c1480402011310500c00c04403600b545e003c031140c164065140ca1206980200a00e006003c141080355405000d0450500035500c55850300c0c400035030320000102058080c0304c0c204c814180e018000c12260300c10300784080c842c43c0c0c2c89024510003c0100068410341545110354220003034641003140500b0282208507041c0341c0648401002d1026030380c809442101008100b07640021041780440460000d0b25200c480483c7c01c03468090b00600780e980c1a0050f499031031400502c440042c400242160344880300382801001000074184080c1140078039071180046005813450601007240c668401e5050b41d2040d041040300e011003075150b139640d90544600501c12405200883d00703e20700001200300d058400d00040d0a0301da05540e401c0240c0e048401c501003440d1329103003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 678035197 1250 678033947 678033973
    0x1a120c09030c012d111c12060501050f03090a05070308220819060b12030d050705030609040f050a1a041a101802070204020f0715051608091608 63
    0x16402c00c1ca1824030781641c2503180321020800c9034280241c4102d45000e40d0003250752090180407840506040300094450580c86841040d42c400c929105030b030005001d100e01001d9420303180c822002522810380d2418200000562100d101e41d1000d4049449841801001400503104101100140d44548a240e0700c41103140203c0030816004008440201e000101c180b0038050001030007904603419811080a051041c18048000e1a0011555800c0b00b01a620404d54160000041c07041400d216000c00007966130200131203080c0000d40c1c4440d03002001c080481c2c08580704500401ca4a030046007503911020b01942c40008049080e20101c0d54004500f0410080c0140b91042503140700c604050b000841c41c3c201a100b0040c80309008080000034400c601d4510264143d041d01d90050307000e0300c210740d1201d1000c50090b4075000348800f200c029412080c004501c0380740740180e9020340a43da108035828076208405407490540200030b41e101c8d01c1070f030448010903c84407854000900b202c8019040c0c00d25082 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 678036447 1250 678035197 678035203
    0x3050d030f0606050a08060d12020a020a09020a0203040b0c01020f03240103050403080a1d0d050415050705100b0105120a05010807060e090708040212070612051303091a120c0903 78
    0x1c110030320980b40290070050340760040119092207a8610744841e103035840c10300040b42c0d50031950b0050090007200c2100000c3d00d070001940013038a8000c8640e50420f580c3d4074101d2003039100c0e0040321b00040c2c000340003c114071000600641500443d280025003803016002e019000398004481081c0400701c2448042c4100482500c0d050012070286010b000a2402d62400740c0b02c404082c00414412786d8845603210b566284200c5c040c900e021240035580302c0440200c00070982d0b009406401c030740e1400c6140c51480140910122012140e0040141c6200100d500107140200707509108141403101c1085103400e0050301d0340d070b218422524008001895410409014640140741c1c1000050144084101140d644c03403404999005107031307241074101c690751031000c10000a0861019287c40c815150302080940c1c03c1312880e4500360b4518000c121a40e1030196840010b50300300c4002d004282d45035018019480b0444000224080c10078260b440d0030311f0100d6251880504a60640b1400408601e85035645424 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 678037697 1250 678036447 678036461
    0x33070201030b0105090a03150605030601141206190c03140a0606180f0b0703140a02030304170901120f1b0e19050a06050c1002040305060f0601140f0c150103050d03 72
    0x2844c005060580716008254158071a020140078841c0c20861b402d030144580d0084c0340a44805001e46440356521800c0341e010303103000c1c40e21622a81842c50507600c03d080015103988214800341d81c1582c0141844807104c014811400b080081548074140400300f002c41401080c06510a1500090010b01d021001450071440c100c1004040f101c040e0204460421080300000f0780304c29801c0656510305501c1c0070303140709202a005103c02d143c045044031800fa0080040e611541c028443c56800d042c070710348003003207502c070340801036000c26840466503215000e1a441400340381640a00000d880c14030030440000c07511052110710004852110514190401c14102d0001c00900c4039140701f09402d20001a0100c0703242c1c001e0504014011829440c04a0104001081110911000c40d500e40c4c50381080c82c3c03603d03821070340140c880d070181c07000c58400d500ca04403c0018028400c800d03800c00d03007840c444881d150301c01c200007400ba1098443c11880b08000321038240c02948684010500f61503104030260a507484 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 678038947 1250 678037697 678037699
    0x303070c2d02130b13180501181202010b060d020307030b150a0905090103030c0b0408090406030c170604080d09020a030c0603021306020106081b0402070501091101030f05041133070201030b 83
    0x1071514984d1542c895031080b589843d1914008200340410b0541d07104140d81c0100c003d8859030030086031808a511401401c42c0c003d0052403010010a00754030141e090300c1032140042e400002c1080540d00054442d4051a0072000d01e00d00410742d070040d00c00258503204427110f440c0b92440d000925581c4581c010b0004002000281d411904039851070701c0181405060650140014409000180811640404031200c0050050040195170348030f040c90040265580500100c04407803a9090901c10b200288052184c0ea1000b6050f2421f1030b044402c0c4041c01441c00220381241002901100080c81c0e001c8042c09440e05a400503101c81e629586802003400540c040300a6901d043c1060001c1903002c9603401400c005442a405c0c0c0494940200340240704842c03010300503503c0c00c2924420040340b030041c1c01e21040700340e07030501001a400710f11104980041d00c0040c940c0f40c0032082001c40b82024042d410b55582e40f00e00403007429075820381515100c0c18092107029460400192281103603010b00c01e0b0b1400341d030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 678040197 1250 678038947 678038951
    0x41a0315060f150a0f02070f0803041a0909010915090905010b030105010b04060f03020f0708120106020c01032702010212070501140112080d0e0c0303070606090e0c030303070c2d0213 80
    0x1100e4210308191081030700c10820051044107456505d4001c0148034010852545580052659840040e071240c00038006c401103c40846800685c1098403000e03107420700d40040c4016096407034000c000006000c040c105204500d00c42000040c001210b11400740700741d00400006c00d51606c5c6008140c212901604042407010062100340a2a5402103500c04204c115040042e07417010030400c6201240036000000704041c200241d1542c5180740104014100c0f0116003c444110341d03040b00642c152101031104d0803c010025158031a04c8100419402a460042c010340d10100e11043c0329210942c0030b00000c2d00c00d40c2d1070380500c0d0944112460054018080e0341c000d19141000c1d0b40d2048414403c2ea101c5070f261342d072600d05480046609000c04054100000e0840e9600d950358a40075010340003e01c110000585400042120030902080c0c040312035400501643c44c5981703a90041d1506981c0e40030544500c1030060810b614010b03c50880305a10b41c4051003000b20440c1841002070490750a01d11030740d414 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 678041447 1250 678040197 678040219
    0x1409100903030e031201032d0b061908010c02060a11120c0432010206060609040510050a0603061a07030e06071506090204080c031b0d05100609150807060806041a0315060f 75
    0x8c88502031001c40754404419082da032211000a01d188c4221040c91168401c42c150000d441310f130542c040325200041350241c03880703a039034007036803100312500500e02c00c2001d041044006103005030b20580c2c0390f0001c450643c0070700302922442c48103848054100e00c6054003070845c0c440384041595411a40c030700042440104010314050000c50b82da40102c15103a030246855501042c4030090000c284009804084d000c11046503032640c00501900c2103110304406c02d028465602608510b68085443e030342e8141c0c85a0101410700c4040c030036940e019610a54030544e030010030140041d03103801803500404130b50a000d0317225820311304d001c3d0401c1b40507080f0300c1c400d500000c449034507051a40c0c0c6020940ca0102d0310240518443d046c020b040c9a201003268486619000010605800c03a611540c1030100d000361001401d1349940c5802e944d82d000c0c0c05288003040c02c1c2c50000c0c0c0703146419004007030f41c44180a00b0b02c250290401c0820300d812001c482c02c24200340090204425410320241c4d0b1000c07003d08485900404d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 678042697 1250 678041447 678041513
    0xb0309070602100b0a120609060e011b02030909040b061c0303021e090a0504180501061d13200609180a0b040b01081f170d031409100903030e03120103 66
    0x1000c2a403054083c6c0552501e00f0805020251b0f0004401540000d01881180d80b5030342024000d0200391005060780c40c184080d0300c02e0520000503a0113151014040d0240e5485540740c1142da404000c0c4000e41c050a8084510400c0402e4120100040c0c4203445c056210703400280392020b40600d40e1074028a19009000c8044a83d5031040800d0440c0c1c015680003071351076400c0700b081c446a04940005050344d03082800005810103c910403510b140448851640d5586035807156480131056079a002d402401038407803071046101640340c2d80040260040103140b0748400c02000c0360149109800318401c898071681004002501d5004058610200322003c2002c0d03804100043c1110700007408072810305901c03001e40c400c0b140700d640702440940007901d00300c02d0302c20400c40d00340d41e1038216911010000c1e00f860b04d070780708a0341c1d50206180140c2c8450050714440b40ba03000e9400052000d05020380406849241c1407a40b400140b0007028106240b00300e0144c4c640c1542410b8a917012402075018802c81198261484 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 678043947 1250 678042697 678042709
    0x2010501150c0204051005190e010504020310031b03020411030a110408100915021201090f0b0906060c070b0d0c091e060c06090203030a08040b1501020c01180b0309070602100b 77
    0xb046504890000d09521850120715a035030858020903041704001ca06100504207905034101103271561802e980c0c03a40e80701c005103c20390009448205d0040403942042c40000d1100008607070300642c9813011030007207907a600001c01350b802206409065503000824450001303018010040c1e105010b1103500d00c1c20f85044500c1c0c0d0785803c0750341081c0840d9500c49150003001480e004082000c01441010754865102450740c100c100c03401e00c510000d00e481c200840f00035000c01e009070744c0e0703030700c002014482e40360350b400280202603010301c412901d02d004005010400b03400c0d10000d440310041c0c41e00009800c0304c8074000500a01c609030000325208030f0041600801000700700200d025503c0501e400d5600107107501c0c05202514031144002d42c10700001c10308084545c0d00505241c0b08a009a021101a031121004807150b001000c2c041401a0026000c411555002d0805c400400303c141c0c542002c410b40d03030004a206500192409095900300303420411000380e0400082030b40c503080720801c0003140112800115 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 678045197 1250 678043947 678043967
    0xf23040c180204090c170f011d0c090a2603131509031509062904020f0409090809030d0906020d200d0e1504050102060613110c0307030201050115 64
    0x440d0700074080c1c8900c89200c0d9901070310020310300030f0307418080151040c0380074010f44014401c46000c045e002002400200381814540c0c1210203032403845003241038843c0d03401e5a400c00141000e40e082d60410100415032114801c1c0801407003601c00e0480303400554010000c40d94a05900d0300401c1e40700780a540000708001c01400704441c6d40030507180800691039010348a2501650000d40901803103880710900c951a6001054424400c48003040204588001c940369001c81400c0d8801000003400c1a80d00740c10654002e1030207400f441c3c95141010b40c3d45103020141c8120040c21111400f01181c0c200310760404128404c00084242402c1050a0904000a5550011030b01c10410051020750720640d02082d00e00320424685070800b5038200e4106444007070301d196001640039015050a519080f10807562009035801d40d24164003a0065850390400c1002c904030081c40490215076070320204061245410087c800080c0590107103840e0b5225060190850303030140c1c4000842c07440400f48915003a8810001c2c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 678046447 1250 678045197 678045209
    0x4051b010531050d0b0702060c0406080403120b0a08030c010b100815180c0a0905040608030d020c070806011203030b010c1e030e09131b1a070f060f23040c 68
    0x28811400b032290003680003400c0d404030390803503108810541404074580500b44905003c1d000c441c15600da1180000e0780b445207114130400140101b001c0390000e0300c220103e0540c84803d14010070808a100c4c001000000983d0000003158800201144070810a01444080c80c004440d211201c0c000c1020203000c40100074640341c242c5402d50380c5c0c3c2c2c000383e0350027400141804196110003928034224070040051313802610f40c0000318800100c0050180780601404058410880107103085c00c046415100181d0071021001c4c200303002d111000f1a41c214208400c338000d0a00110100c4801010f08003d400c07203a03050180e904212078194010080b0303802c4031031071041403c010901d00f810203090500f207900402e91112550b0023034040003407001036220041a03080c00303030047c007250031110300d8462501072070b0080b442145142c0810380311480182282001074600b290042d100743d41c2c68007095403884100d82d80d140a0480309580c4908452051880d01c003c041554108000c802c5c0c181440e44400d203620300207110f48 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 678047697 1250 678046447 678046507
    0x90f0b030f011a070b0a0501060e1009060c110d030905090a06080304151806051e032e15081006030903080a0c0c0b011203081605040b090604050904051b0105 69
    0x44843c2c0d000501142e6040e44c100041c04080d0a00c4016000500401c0c4500c40014503036000e1201036180141c80b440c0201c0343c41c0c48400c541450031106640301c0318210310a03150301008600d44400350301c68010003404c06100e40c0d90f41c0c0c400d500b0700703042140703802004d412049214135202c0280b090110002c02c03581903a5441c040000b020800366003c0b10406e03c4c102d6100c64103602c10f00c5c0024826045005840c240e4018101d011070141c445030821007501003210340c2502c0e8408044c205500031200c40c240348108003543c0e402803007551154103a1110000b07851541c0c00040100d0b08005120b5886c10240313005e0486858140041181d580700180014809001080b41307981d200800c02c0e14030300a900306030b14554008000c4000c0e603514504400300002960050300440e0141000904070410442a14080b8000351070303071800c0c603041400c2c400d100d0708200f800540100d020440824035a03a0081d48130300c200d00c514002e003070b50b10054444070f44c5444502e10f005d051180510600348403801802100380142159042 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 678048947 1250 678047697 678047729
    0x2030a021209061c050108011a090f070903080f030a061205030d11090a080f010605030f061303200d0f050f040902031e101509050a03150e010606090f0b030f01 70
    0x603928891324110400454040c85400745903c410b410550403207800000812094070392040f5840d66003420f40042d40d001c5030210019000d2498070000a070840d802d0315120030042e03200d03540c13000643e0010030030150300b1401100301b003040c00300307030142c0c41c040c01844c101c04810002d2681c40a6030307805600707940d1440a44442c2034003c841c0c2242d0a4403030281c0b00071b040c01180707652115840c0d140c0000c2c072040c90195003002c002103181d0400103420b54118600318020310385560303030380d140c00d4440d14101c008508002071900c405e001c0301c441c00340c1c0e600e143c03102e07501801c44810986406404c50400300c2c0306100707003c010b00c525809a00150183c0701207400000000d60781c0d503190003001840e5005041c1c07010a0303006810a205a40b03e100111100b0341d00c03010500480b010210341c0556091007d07125960307000700000c805100040c07031020407044ea685882004610300c1c040c1c800c61425188260810000039030052010850078a484070000c00814000003910f04e1400c001070780c613440d0310050140d807030111200c80b1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 678050197 1250 678048947 678048949
    0x906150305060f060310090b0d050309101e080f0f150105280c051002040819140d0807021b030c010507260403020f010203030717070e03011509050702030a021209 71
    0x401c0f103054040040910340d90785890185030510100c20700441201c540303003401c508401d0030304a810b8450325800c040250b042010302d0040116540b01040f50b0000c004044540760340030b006a0001c4894107a40380c0740c4480da45031048000b1035051000b404031702011828800d01c070329150491403081c6404d100f86131040d6600c0361070075040b1030b080301d10300d583e8819002200b490210a510440046101d88640c0944080c142c4282541e816401140603c2c40c40e42c00c038032180d4035a00c02e4040c81521039031098000da034182052545848c00c1180700005400420304120400644640c148040c2c445007501e41c440441400c6208040f1742d0b110143d0005134180940081c142e001e001040c42c1c4006c09485264085000314070910410b102c9802c540700c102d008040c80b0611001d950f001000f5684600590358408802094018100201c248041c000e4420302042a0805003280c400f03008180704108a03400c024a070a103000080421202c004002d1821500203200f21409260301203900c01045032040406904d491242d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 678051447 1250 678050197 678050209
    0x1020a14130b030a020403020102010e070f05010c0213050f070813030806130204050d0501020c070e07171005040e0a0b0603030405130f06094203020105030901020706020a18090615030506 82
    0x14002c858020720100c1008594415034004000b981d00c00e9009004000c040e54003d65104440e000340000065080005d0200b07501c19031200c424680002c0c00d013a80c4001c2c903c9940304640040e101001650040d804000b01140c00c08d282c29041100120000c2034100c0d42d44004210f00c002420441c840d20860310780c103220101c950144c0340984070007048082101c01c5031410900035484402c009401e4001d80b100060020340c1d07014000e100f402140c132030080001e002a48000c9462001b004031205510512000c141520780748966507c0d1150340c4014401c05600c0e0500304d82c2c4007002407140703120390f2041000303003c19110b420070203011020055001c2401c500088049000d4403003600305501c10741c81c00b5030300300c074046444028050fa07408150310340e0a0800760000c82403c10808441305050283e560504100552160700210f43c40f9441e18001804d1030715641d41d40c01640d112a07804000203021b000054010490015220001c11003d401001002d00e0320f02c01704801802c03c0919000d0541d40c00010741c55407900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 678052697 1250 678051447 678051449
    0xc0c10020903240a1401050906040e070308030106050d0f060b19020c030d050414010c020f0609010314150102070b0a0c110105070c03050d030605030f101d1009021201020a1413 77
    0xf26040f00a2a042c25820112103a011110758a0b10707800c103c4900806000503042e181600c001400100b01c90f900d200500004e13003840101d04c0341300d11a1090000c080751101e0003540c043c083e940d4403556551681d4224a05031170f0501a00e21986e850990100080250385040700c641111130300740c0a031200641e0f4030590034a188103040c00d40500884810495281c0e20400401c2912103d03c0514214880c800c01140d861004d902d0003034102d4401d01544145152440141140100514001c6840802c101c48220248400c0d54001c6100b0070310000035100d90f03014030420b00501a23074101c8038103015528400a04110a07200d0190010100011442c4607900c038504a0b1800d40d0856500485555689041540d403c144040a0000b80ca003200100d03140c40d0204000302c500d003600c0000e10040785c2042d02c05e07009040d65070119600340d441000380d144000c018041c4200560480340005090404c5c2c0c01030103001d20440d880d407521648108000707000c0c66040780c2007402100307030081041d84481440341c0403d201a42 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 678053947 1250 678052697 678052723
    0x1201170313030302060402120c032d07030c08011107080d090204060e0702150106110a330c030506010c260903030d0501140102011e0507020304050a03030e04050c0c10020903 76
    0x1080341c02000349500000c1090040340709540d4403003c850f5544802d922406c02e0048180e141c0c110084410212a1810007100c40c000705c2c480c49601003018450003481e051040c7c1c41284c91207951001000010004e200d54510307040f4100d2114a403801903507511440e81b1440e02d413100607550760a2083d042d91103560109014100d03c540e80d0006080000010750b4400642c2c54034034640340c0520011981620485100080e0041c1030014411180c3c0340ea10308035105403418900c13004210b1051a5020321002000d40c1b10b8500c10014000743c0025441001415584024207240c140f014003c0400002040c022140030b1400700b550b2150622541c8900704017070f038030401d1400c50b0f0520001c00d2082c016003c1d58009070480b4500e4105084945045c00164261828041100e032080c81c0c0700d01c00c071a41c40c003d80117a03070b00403018810349140c5505d890015850b01c000d50000d600042406090701c5050915129250300080c2c10403000e800d00c1e002e14074059450383c3d07403500b648913035802007a410129141000400a8404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 678055197 1250 678053947 678053977
    0x50d0c0311160c140d030e150a08180316031110020309100501091b0f0507120e012c0618090108030702330702221a030312011703 57
    0x60b00d810004900d040c02c040c1c0c0d800c10403090000b003548020310003c010900203800c3c0e60401116407000d071000380d1201e8040d50012840d054022810300c03103200400c0d1104260700d601c0c01c41d0500440c544030031a12401460001d900070065040307248003441c0c5449100b5410f1072300c940307066101000103047c10b0001e401c103101107001000b40a080940031544000010400404000036070380ca0000809444c0d006900700c00140810100b07820480c440c0058154142c00d81c10326614004895a425003060702c8090350000081c0480f000c100300c0e41c2d0100414840194017401c1201c1182079000405100807010b102034850f110014990301c1004100c14032a60781e441c004c2c034140c119030f5600c154541726808036800f03d20400000f008005030b2a48804100d54002c8403000460290501c4040c40c0324950100c0d8081e68400030061a26840d05ca03081c1203a14914800300001c6219080d02c5101c542c0c402d082d007902807281d04280412a86180c0b901c2c5168119010065003c2d40e000c118400c0f107085110708080590035803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 678056447 1250 678055197 678055207
    0x150f061b05012a0314132654042003010602120c0a0b0c0c010207050d08100e24030a06020405010909050705030403030506030f150402030709020901050d0c0311 70
    0x4420054104085a2a450900403001d174400d03007080c00b2000706d420740c030042c0c031484031000801c002c4404400c0c803c0141251052107003035402c007130380907400c00c10490b020002a590749004030010440002d040208030000c000d08401c2c0c0360010400c180d103104110301851010704081401e40d5868020310308032020910005511303a102c950707040301c0c2e43c000d016010140c4141688201c443c0c0010045820301070050000d000000c009a0b00c551407500301800111024005006c41d6241c00030a10091421501c114005d0548044420014094807401000300c035009401d4041048804041603e00343e001448951007000c04002100d20b50255046043c0c55400d481503402d00c80c1008040d42c002c10513544240c81d510a11541c0b480401d056800461707255001990510200300068001d130866900900c000f0b043c0c0d00c4030010a07800614109500d0340d1280c4e66003480c0144400e40c1000d200341070241c21000c20a524000d030b6a40064190b214110034007980c1e66644c0c8e0211080c42c0300e98081141c580100038116691 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 678057553 1106 678056447 678056501
    0x503070903060612021008090c0f06040f06110c060a050901051b030c0c04050c030105010f210c0c12020708120d0906020d150f061b0501 60
    0x40102010040700160440c003a05000c1c0c0120030715203043e02802d004004480d10340b04103400a10405800b0f01010420100b400c0110311410f9808040c4810550b000c10204d12a075403000f501401204400704545074065510b984003454034084405005440c400c0102d00c0c8107075655100420404c110782400c95001e00d01030315502c40308006d15040207400655003802e551107290229110b4201c1020082c25150034440c4603000401224002e0442d8108400a00f04641114945c028000b0400800c003a003500540300008030078080206200f1f05005620140052005400464480c41420041c42086100042d250101d07440003005150501101c144811198017001c1042c404c0782e12081406c0c0815060f00080c4a40f01ca201c80000d00241c1c3c009407a8681b009503080300030395400402082211690000c00b0206684841544d00080000c515082c0e00518603c100c005841c1e00712002c0440c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 677877697 678057553 := by
  have h0 := BRFrame.cov_init 677877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 677877697 ≤ n) (h2 : n < 678057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
