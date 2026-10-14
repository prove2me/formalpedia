-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0609
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:43:07.541081+00:00
-- url     : https://prove2.me/submissions/58ec234e-653f-41e5-a4b6-13ba54767f45

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 109352517 ≤ n < 109532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 109353767 1250 109352517 109352521
    0x3060f0e010e0a03091e031b031506060305100b030127060303080103060b191205120c01050f07170c03070302160809010e0a030b0f27060f0a0b0102061f0b03 69
    0x240128043c08098005d0b580d00b80a40d40b10000b400c4800180c0510f18070107a620402080000c0748075410120b400c0080482c03547d071f1556900e904450450704104541e5036aa2600244a61034240c4140c2c3d42018820501d0904075003000c10001040c4010301071850425268808400001c0070324880c00007040c2c0214061040d9946c0c0d240160001c81d003800100e0b030030760505403040d100c1c0c04c01a04001c6003500b01c4440840c454500080f242030440520000c0d1918007076105080070341002e0000400003480007a00010340b526001c0c0d140700e0100c401503c0142001440c2c2200619940c1022201d0340000000c0b8201e903890701c0b07400040d4024483c258070114410034204498040c8007092015004440d000e0321901454213880e0100450b290483c00010000406d0700c011403211604501129070103522034074002c0701007003d2200707a40c0300604039031414207950021040200c545110524540c1105080f001403210b80d01c00c40c0040d449400c010a48401d0380216005815442d480103040340051115410595881c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 109355017 1250 109353767 109353791
    0x12030905071e0f06030e100c02010b0612010801060617040204050621010b09012c040303091e06110c0a02090c0f0a030603050d0c03090e0408091002010c020c1903060f0e01 75
    0x25030b11441500204510401c00094041c0030f402092144d58015002d0b0800b81c41e80000040209850140b04085658482c00d0304003948401d0024204100100c2c10368a4562415641313500750360745900004200000500c084c512030811600c00c0350450380c100d901044503612000862151700c1e42c201c644440000d006010300c01c3c0341041d0700c01190f0810030b503820015680c07203417a28102d07410040c04140ba40034104900350411080041610380040c03107440c0128101d0078540b504818203d02c1d00301e05500e90f5031079180600b00803142c820300d5150450384495504000c11a49165281c010300740c80603001d885508001342e501900c00741103070304900405625945030210300d24028000c040d10302086995100b4110006103850041e0785205115605588072854a41000c0c20b511040001800407200c800c818021035405603542010080c4a44455000107680048504020b251000f07880c0081d004820700b47e481004441810741880940360820008118550004034120050484d410700c4102546001808046c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 109356267 1250 109355017 109355069
    0xc060f0b1018060e0102100b041d070801050123060912010507200a0c051003020f040608150907020c060c0c10020a0b0a0608030304030c0807020904080918041203090507 74
    0x500b00020502070402034807a40f00b03441003200c41c0302042c05030744803203803e00036440550051641001d01a20202e65206060343c8003200401512103102c1a420a00050040810900c91580180700c0800741090074030b03c148082c45000410110349008400002d800c6004e503d80d811803100300704040e4000c002510746043c0081c010902d40170100000300c407500c03021140580000c0c190011a030040034106116280c41c04100c1141501d00307460f030602d80c00f4840345212410503806040107255680703500c800b520f08848801e0340318414001041c42103045005006805a0006c1d0760080c006003910290791314541d03440f4443c40c05100914031544040c01c410210716440d404603401310300510804001c3c0395502c079121148c0944d9280d0040c1c080503401440000c1c086031040c004101d200740181d44075490b100480d00804c210f0402100c0c107803800c000028043d545403c0240111985020b200d00f01d0b83c207814a07a030b4100107500d44200c0441016101d001250070b0180904c0b90100070000c04041003003076201c4c01040c0c0d00b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 109357517 1250 109356267 109356287
    0x31d010b152a07050f0111060106030914030f03010501030e011509021308031c150e060607020d051903110a020303030a0509072706091a042007050115150c060f0b10 72
    0x3000e001c1c1516840c4036540114400504841207e0160840341e00b0080f00324002d00749103205642c004811110300d4050b200620040001600b00303072100e592503040800140c10360f001c8840600707041c0e16003010744002146941c00d03072054500014006d60381e03d510115081041c1d0a9410044150200044208105110920242400304e03038905c01d110340da81c002c5032240c500c80030703115034589400820b00062a83c17801100030300003288000d0102d001c001103a12041d14107a4002541019001c00c4140601816000b040010700714501800401c650b81c40e030344c007003616030001821509100f170300c031400b0900d0104240805805408600b0406030a240a5140d02c01d180d15103400070030b2601e140890105421030103024440a420968a02e81841183d0f10240402003000ba000080c400300c0f510280c000e0380d09040e005121150080d8008210040c00280560b6a415180d102c40c07040c65800d54030f480a90f4005100850700340d0414400922040c2e000d01c80d0303015245041446132300201e0030a2182030f090b00155001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 109358767 1250 109357517 109357519
    0x1b0c040b01030e06181002221e0614040302031203010f0905100501050d0608010501120201140405030601061808060703051501080714091c03031d010b152a0705 70
    0xc04040810001502140d0402004801e0340d04030760001001d1403407031807004d082507000004480141585c116080c0498009501c450761920381075242d1603801d04130015100182c04040301c04211404a000c010b4a4a501845400c09021151101d0511103002e2415a4000d49d0003030203503400464004800b80d016802402600c625080340321010070104814451240301d00c0340b018280c0a400d06050064940c0d030000d10903c0c58403900c6040c0403801102c00c3c0151402011140f2400040908074400902480b568500803008003405200810040c0d4000641c54110368003030030324000b10300450b040c0281c6600160040c0380f040c8107a2050140305030385580103902c1a0008081050180083e03001126045c00c1521031000107403000054024168040d401484080c07002801d110350143d404000090011401e0300507030200340c0d14480381c80702960450130050882000d000812000303501100003440008410750003503943c1c0c408210348401d111008005001c511071191103810030444c4400c1a9510680340c020b40e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 109360017 1250 109358767 109358771
    0x80c0c090a060303052502030d031a0d0c05010507080408070e010515030708071b0b0a021809010308030a050712020d0c110a0b010504050c04051503010602070b091e061b0c04 76
    0x351801d039203481414192903256036220b00d003a50780030111108802101800a01c0e210b840c00c0140183d60800c840401880c3c2601c022400000705001702c100c40c000480c03414014861040c03604001021030400d241034031804d0a00a032070700c88a0030f001c07101d80a039800601080c4171b116008070390704040e0310b038641c12a03100701e40e080644c0e13195104507102e84c0400c2c1c6000022500d00804520064002e0809a1014450b140c0d20081c04001b9184d01800705001d44400704455400242070380758044440074840ea100c0250340c4076200c4d52640d6070f42c1071030f8800200800b0785142d8500c0455110341c400c00403a000503221314000e54840f080c0094120091815040010100381e000c1c884118072003010451400443c0c2180c06000c2e981e190005000c082c00e40241202c030040020480451943d41c2d8010208182042e11121070300c96040c035038043c1c91303c0c842c3d03041004406001c0c000071015544000c90420402d01c2c00c208081c110003030741c2c04200b1a02484080c4400318a22000b0803049a4000840840c010011241 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 109361267 1250 109360017 109360021
    0x1a06090601092102130204090213080a15020a030b0a15020114060a03170c0109080705060c030c07021018080d1419050f0d05040803061f02101503080c0c09 68
    0x642e00b030b08051180c40d00140d40005900784148003200a080307042e0028151700040e82c80254520203c1c2d0040d005880a6a07000c511201741c800700032500405442088010090000c5a8540d1141340740702c64500c0100c03036000240d0000d4140301c0d40120b070b810100600701280e900d840b604c988035044120140e800066203009141e244039000345500d00d01820020f012156410700b183c0710100e01038900c400e00c402c035010800c41021403510034829900918043c1390201d4461034070b072800c0c1d400c001d809000706050400038418801e172100901c08442c04154116000f034010000007000303458020880000c41c2940c91803440019a800300407400300703046c80341c581d907182c403c503c143c01d28000e9004280c0c00c1c0303086505000c50031001c107000744020841e80781c13010006828000d80200719405c2c1c1e40121012141008044140704860401d0320b402c50070001c0b050100350710382802942c0259910710114500381d075152a03240600d4004042603a0340059904840410790b940601d0712141d903503440c6c0c401031901411040c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 109362517 1250 109361267 109361269
    0x403080a0e0129030102040803030f0610030b0f041d0f0609010c110c12031b030d061211100c0503030a09140706080f0a0b06070302010c020601061b06090305071a060906 74
    0x12801c680402042161030a00320240b0300c3c8980c2c039201e5081c1c0d6070159801c01c03000c140070b40100041d52003030860041e24070701860050240001c1140b0b101d41c110605003030105542d040e643c1d9900c00e00c1d19000c182e50025440b40440f078014140645190b5a40075400b491680701290400810740c507114042007030081c00f4511043d00c045800302c000524180c82c40c0c012102c201824a06004010341b00c440c400e04803410020070f04443c4240c7c0031401d550311541da01c00509089030780307018080c60340105003001c01c1d07598030502d54441c20300c104211a22503104034884800c2d0001b282c0101e208108807034018044944078138001c0c01900090980345810348032030004010480c446c4030002040d07410b6414540e50400304c1d80714007020210109024090551103521500320711400d4440b00040d100079402507001142101c488031010703040040c1070b04000704121061182d1103904021400c0c25603803c1c0c0c0207100258581d03960a0880e030500a07540006d021210302c109118001988080180c00340b102103400c804507881d060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 109363767 1250 109362517 109362521
    0x3050c070804090b010207030b090304030302070e01051003090206040b04060e04110403051b030c0d12030e0111090603040f140307140a0c03110f041b0e0307060e0904060f050403080a0e01 82
    0xd40104800800c100901025010b80c1014034265410b004607108035403039590300c0780c14600840301c3c4d01131036202003002c00a0590410014008004c010003401540d41051702260b40b200403113014138149030700c84144004640302c200c1250010038107585c0e4551110707161000145244080c640369446035040c1080341c24000700c40412141140d502c600145403501452620080300410340d4a441c1d40b501520358401c0c150b45500b485012442d02c81e6040c240114001d000190031900104405030040c1e14022265040000344000c5032004c9004482c055107075603a502d41054030f4001c521004101000c44003895000050000c0640300c0d43e84110640303c240481200c070f440e03640c1000706010b07105200740340041010a103108421582c050010700082d01c0c1590340000f060550350380701d011340380e0802802450400b03a0743c020f000980d24a8100d010300400c518092000789401c98075043c6520541560011030308002d91540401c2221200b11030500441c6014140a0080801214401d03062030030700e01028500d01043c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 109365017 1250 109363767 109363777
    0x312270f0506090906010c060605030d12050a0b03071a040b0d0903080c0721050903060f09070e040819120603050307020901060c050a0602030c09040e0106080d0f050a03090c150e0103050c 82
    0x1e4610001356491034011900003400190554002e5920000803d994800740030301422103000e0785540544041100d084001c481c002080304c941c080c07400201c0c1c2d060703540200301e080071100d18241294000e19200a210028440c6900c603260f181d0380011900004511034000e0980d1078020b40b20302d540750766450540030440c400e100b0003e10000c541d400105e04d8500040503c2114240c41c90250304004400d00407a103410401c0d10b980c5070000e008400c0201044003000802d0281405440c008642d060942d5111014003c9880c540c9190f6402e030580000680b00c2c0742052401c08200600380720b00c558a041041c2c82e43d1180009a0080300884000b003542c9008066010401d640140100a0303140c1d55180c03c4001e40019180f000e00c5002000910025a2036003d1845907181403000040d10358984501a0300d00541c400d4284184042d003468455603d820a0583d0552120b0b8180071403148180d02c0c1a40010356250001102e00030080c0641d2100f950005c2046507240c02a203007049030342c494555803403840c050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 109366267 1250 109365017 109365019
    0x21021b0103020a050706151505090102060f0403020c030307080a1805030307140102130e0114010807050403060b01140c03030603070b0c120f0f0714010c03150312270f050609 76
    0x8901245495510a6004203040360481c500b85061a034155203c0003540c204907945206a80c44c02024070060034142a203c1c198061420b2407442e05a42d8070010392907500061a00d400c020f610780000b810b0500a111917005010000c1c10f880e41e40c442441d01c51126081070302c1a50020b10f03003001100075503140441c43d00031b03914018000d500340003440e92600e43c0008a50341c2050155024815850310b0007850f1040005019209000d00c850b60501c800000240c810041d0241001501c10910100d56004401c84c0d095030b40110000c141421a20016244802ca01544805804000a4006c011800880030754000d400440586805a50301c5007495540c2c0580189201a9001642c1c200b842c4a0500010900c10556a0301d03a4103003000550005841d07088a4001d41d60300c4a4040000f010200078803a25460460a040422101c56092504055001c0b2400024030100d6084480d8544038080d54030f02c4481003900340c4a0211030705800c500c4003a0350580c80344c04484401140c01007400d15003003040c0c4542000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 109367517 1250 109366267 109366303
    0x5060f010b0702090a140106020706110304030c1502030715091218151112070c0b07050a0303020c0109062a1409091b07030e01082d060103021201032102 67
    0x20f408000d581280074110003100740c0d58000000e070f403202901c2c40728000d0010390050030046207000c4000c1c11141d1204040c00301600104400c3c000281c4d00d00c0014242c80344858803019500c51094103a146100b0083d0141040c890000c8034014010b40ba003041c41514450034200302c0b484d81c006407c2e18840c529509075145640300c20360034086000170414203003550207546003044615450145090030b09080780001500035500040c40820310081c44c071402c2c0140050a4040d140038161346442c0d40301d10400100a007015000600c15500c103030309401520103503410210411044202c103c17400d492000c9090b00000380380c0c0c24075107807031000d00071031140e0b0072091003558003807400404004200b078961008001c4500d9040c139800840e003450030702b000b03043e060340709845440d404024480050a8041c0041010004c0e00d404461040800c541944030705251480403d1b22925864000060703000c1e019040c10450108040e1000006000d2499995842201c0030440b12545000b44601242ca8082d56143c16248213 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 109368767 1250 109367517 109367527
    0xc0711121213050904120816022e0f1407030b011b1a0903091c0201020a0b062404030b0a020901090e19060801051006020106120303020f04030b0c0705060f010b 70
    0xc9101c0000d2000e2070803030034a0214940c480001400140041d241a5000c006650783e11901507000401141c002e520344040340350340011018003c2d80c6104442c2420000440007280340740600c08404001111508040c3c2488801d20003010800142880c3c441c10110785c1820020031801402845000054803040c1c0d50070418400d03108030f5915411082000310340d5910003201122108501151042c06040460042c41ea15800c0788102300030349040d2204244201a015101d000507030300007a441e0b50340e030303448009442169696000910480701240381c040c540c0c080b01465541141c000c0006000f628841e9000b140907407a40c801410032402071404081c041414004280068510030301c03000d51204031071440701010440c0c00a4242543c3d00d030f0341300c121280e46660610004021b030880c803801810b07403403008000d041c0c94070802c500380b100210005810f0660001e41c1d00200b0f869801201d01454100030995187d0404015a060b1070784041c1040c1c809018042c085010102e0081d407450484140c0c0035414180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 109370017 1250 109368767 109368793
    0xc0f0806010e06070c0801020a0c03030b01090e0f0a110c032109190501320f190e10050c0301030308090106050105030103022b05070f060201051b0f0d02030c071112 72
    0x2e9118540550f05d811083c2000100b01400740014000601640e0703591200101c10b24028041d1401d8410807818020614014880c4c0303041e1138451540728069004143c0c080d180d82040d1002050101c03800802100c2c0081c411036920000001448507010254907030b0048441e8142d0102c2c071900c140c0e0548200d405c10f0300d0030328000d40d440c0700041442e800f4500000701c5500c0503030a40b001e0780d40406514508140600c0e85103010401c0780d0444e0f4083c8564100c0d1206107050001901d0b50307103220103089080f0390788207814a002001007203040980c00c2060420019030900094551043d0000d2104500044170034002503107426040c01003604407441a19142e0450742560308012042184140b203200f2000c0100695215641c00140071901d107000344050182141415012900c10602c0c2d01f1030819a070610080c064600031300c0d604da011480a0fa1174481d01c0700c103000c980803003501c40c180c06400d8060012044c40111503021000b4250103108011201c3c6d0510050180020488400b0b4000c02c682c100c01090103003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 109371267 1250 109370017 109370029
    0x9050915040b0303160b0103140a03020a02010324181d0c13110307170a06030b130302030415110705040e03070b0402030304090e010516021606230705010c0f0806010e 73
    0xc10b2402810342c1d0034004420102414452115001c0e40c6542c1214010414016850066072010b8090300c090540071445840182d0b942c0500300d0024101580d45d190810544158444004c08114100307c018121303960f521341888800000c04001c9006103480b210720306d4a0001d00024030554068000b810102580d403080200c01c0d000313900c800c00d079561950451038401d0703640c80c01141325106580740c0c5030309048800413029007a84024003c1c180b0503d04a0280003050180780041c2c3c0c894010b181c550440b4480d07180c102d085004551008654004d4007500c03106507500980000c03220002c02c2c08803000150b0b618204420f641200d02a440e40d6002040000003203042061710b594014000b8084a240c103549205050072604051400074659654000340701821000c8d0798088900d44251000788007800590300406901c3d0503902c41c240070b00c0080b01103481d0601d0b00d5150700441a80c0040140c0d00c8540030308000d800390401000c0c10000916403200c03408054041d82d28980113140c103940f4820281070600038404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 109372517 1250 109371267 109371281
    0x90c09010308090a0b1b100203090a06090f020619081b091002120412030e0307030519060f181217071b0203060703060503070807060f05091c0c060905091504 69
    0x9003001c44d0040c0403494a206400030044444040007840980000200803402d1143d00c40581e000315004000380981400e0018545031315540120000502459601d072018901c480303070100a400000110700e9020410060446203401021a01e482c1041c0e03948405001c2604d4030080b0448602d64140b04141040c14010180c80017140300d801162603184503000b8007000303600507900034814650196000780030154005004000000e041d801882c12508550314152103040d8018412900080070b1a10400d001040e000b207014604210f20030081c081409500c02a01c81d500308082e2000c0d07210740303100340540703224003404240c210140c44124419140c004003120000c01c11040c0d6020400e81a1202025950600415000300c0c2103450018045180105250801c00030b0360100c406074002e5142000b5068000128089190b13107890040d55407806040003602d4409904912a90360900491000802004000301010703118107440d00c0d00010350395810400b0f02c1400701c410713600d082100c204480315800e06030030a003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 109373767 1250 109372517 109372519
    0x90303040305181801030506060f0402090319020112050c07021503060a0513060911070201030e03070b0a0b04020c010905060601110d020c0d03020c06130609050d2001090506070803010302030105090c0901030809 92
    0x75042d80080404d91080c9030f000e810644e00c80e08038a05210704c0349400301c041c41010509440030b504200080c4002138a520038820f490f1503031607000380b1070b004580c0b14003080d50100c02c038481c042005007065250300e01c590b040381004034000d032105c1110b401c804400303e050780c3c481d8a0040a0203519803c0c02d092040c11101040c0c4010707600d4540d100850041243d0003000741540407242d5541e1109607900004054500700d80040740e0740d800400641000c51f00582c8002e5202540300400318030121500081030091040b400501c0305940381c09000c8003003040200d8800c1c0a52002d136555980900034144090303c2c0e80c60600e55001590000c00c4992150404480f0350f10101e000b0f005031450400d491003c20829407141e031001107200840340301031040d00d8200650b03c0140005031985a06e80d00c545c0d96007100b070750175604298490ba080c444002c2450b8403440b8250080d01d0045c02c051b03103c900c607242c03607016030304280800c031300ca5401c2c1030003e24100c00001e40c1189c01c1c000142081a40d0b46962a405041e0780b00154103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 109375017 1250 109373767 109373779
    0x406030b1306180b06090601030e06010e0405030405100c020108060f01020c040f020909100305072108090d0c0b070209010e0903090108100f0e010806060108011a090105090a030503040e09030304030518 88
    0x50f000c3c40b0814410781c518010154454039250100400060002c0101013a041c10302e00402d40d04003080004003141034a0b031418a42c0c2c01c40d191400d0161a6020ba81d1000b03521038a0900c40000b0117900203000301196100ba22450825158141000240002010803070f0059109005009031881c040c3c00c20000c5000106005141103080b4011822050086038061441da0310701404000b000000c110920080203076100034100a03401c0c240c1011000c440c00c03005400f415011030701c5580c558502c4003401c0320903407040400c46042e03961a01c42041d43c100360b00c01d0b40300f507240600000c0c00d905035691651207031b0740c5040907500c0d0460000065800f108082c150306079448901a010031185407644400000d44086540000f0075172414008a141440c0140f44c5810811502c00400044a20b5640c4c501c102c08040092522859242c004841c9030081d41e02142c0d1100325490000180440071009000360f503641d1111105981c1d40303940d110350f1303880162001000075004000030500300c001381c11407a10a00c030051503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 109376267 1250 109375017 109375031
    0x101d040905011a18090607081e15030705060c06010b0304050a140610051008190e0a0f0b0705130311041b0e04060f030b0412050c03070803010e01050406030b1306 71
    0x8690854600f00c40741c14020303c0101c0c140d411032a1281140d042806103850203581403901c6012252140009068842031140340c40204181c0c1d440141600c00034040c0c03070301c00f030140e03c1e10110740c00301c0a108844050090207840004105c5081010441c0c10b40028040180003903480c0ca250000305903c01070003500d2600a4150017000100f44980038600d13480e404005000500389000c5040c04411554007042c4540e88200704410f2654208043c194400416070390192500c1e41440040b020740743c000009002c0c1c2c010081503008100100080c030420f58001c40071001641e0341c8585c1569203100d40b41036805c00381c44220080001500a00320196084d01c00303400814800030b81c407240d600c0d5502ca40020001b03d03050030205c0c401802c0c10711440006000450041d40c065245890b505d004100141c000b411490035041a0360b4100c0c050811990001000e10031242d6035243c90604490b00e8100303000302d85000c401e40000040038942400394806403a04542100180e4407140c4c40d920381468451030032100c3e1500c801d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 109377517 1250 109376267 109376273
    0xb0a031404110a0e0105010804020f131d0d020105060105040b130302061206030c030102090117090a020a15110a0218070c020a09020d05090a0c15090b0a030c0e101d0409 74
    0x1009010302e01c105a076501404668040140c00c40c01a040180c1c100c90740d00040003181c2c0e0040a4a82041e01580c0031407110358801d001c1003000802c000d0003403800c0d04050340c1c0c00758000f0400607032020070340c4442039031141e80041d40f04909030380b4150b030694000344007840280303ca2031052000f00350740f102040500500959907070102e2100c2c0c20022410300e1a0803d9020070500341010301070395039a80000c40c000c40c6010740040010308030190030ba4640c10300c0c29002d00040c00b0100100300d10014a030f001401c480700b281c2d0344c00f0040c0300c4000f46443c060009000781c070907101c0f59400150002e04a07034005c1c6008890801e0113110780200c040102004c2c100011400418003507140c0c186040c019000703120707000d665010030f409900140c40020700300040c15800f100a2402280b101e103581000e9503400744005000320600401268114a01d801c28081100000350504405070550310020400d01e90751a01204a464101001420f0f100038115102183c000c0400210a2310300400802004000810000349034075a62 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 109378767 1250 109377517 109377551
    0xd030f11010f09060b0922020d08120402031c09030305070305120108010e0c010e0a0b09181501200d030509010204030507090501141203070305030a0b09040b0103020a1502070b0a03 79
    0x90b006105280c0c1e03807810081444018000c03500900301c15104808a42492503104201c1516050116204031901214030211741c0c4e41c028049003160401d1141da00ca90300a551031081e5031091303400720f12078843c01c1c00c904112441618103110040050725509541ca1654406031600d600c00c2c0f000302c003000020410a180c1ca840200c4040c080c0100100000d0700a03070384034069240c070400d0074000b410301c12a20464030899640400090943c0c002d00d002c21f40380d01c00080420f0800c0340821080d046500c0100030040451031a04080711105000d0340c4095509401c0c2c44041544100c0500d000c0d00c0750402401790340200d009810058000c0018000145000e680352100c07410103c40390803050380241c45100400039042042030141e400074089035450200e400080300c3c0d541c1c902c95600700400740300c0044000f80b00340c00345034400e0b0700d40d9001401d000224a442d01d48072004942c240004c9103d8000c0803008903c480c080340940780304244070707001052900e0402e01c00c14034a410098900003016180d0045034003210b002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 109380017 1250 109378767 109378781
    0x7020306100303020123190b030a140d0503010b120405191b05030d050d050411060408010e060702010203060d0f150603030504140301020703090915052106090703020d030f1101 77
    0x540c1c0c0c030704665085107402401d42c0e00401e90800c08039060400302125464248069402c100f52451541501704544001d201624034080d035613a050060200e041c00f40211201001c4030040090b0607510000b82d140425982c0b80428044d0b06000401809000d030035008a860351908203003c0c0e01203550042c8103082d00b1a01c000300800440d000c3c1e0b101402c8500300c1d072988001e28090311044000e818444902c420040090140d040d0401e0300f16190408036040c009649640d440d892005031520b5174468950a00c0b0b4080c080036028414948140000992928070600c00d480c0a0f0500030300b00d440000103519005c6503820040c00546003002d13100e0170b1048080091040c03100440c03007034803296155031820f000c2c041d0454842164600a13401000f8060009602200c0714050300c4550000044e03118500380110500210f9822007900000c8200124801c1480864251083c8842c5c1c0212100e6a840c09481600c1e04110f01c8006c1d0072905441d95400000e01440c0d00302005c1c3c15900c0d25010403142c4140c81c1c0c6c03e40d021 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 109381267 1250 109380017 109380031
    0x30601110f03041d060a03021804080903010908120703140114030c03100504020108010b0307050d020a051306030b0301060906050a06051e0403030e010806040509060a0b0a030c090609180c06030c0507020306 90
    0x6610401600050304d50022a4000c800711912095540b840d0003040c102c00c06110702a02d1030030400006000c000001060303d81c1620f000d002044446c0d4180340c921155484003217080a10344001c00051203041c444c1c0030701017925030031510014450b4a001492081c1c041c0080e034403a8140200e01520403039880400a810b006411060082024203141c0009005100e040c0c00c5807000410402c104141242c11808854010b50940c0006030f480569410460709406400505840c4008140700010f1041c3c1c150454000100c08400800c0301603506da104c00200c0e10280700b855048060440c007002020b00540192082290703060303030481a12503001c001b02240d480b13900218041003101100b10b0301560710000d0f465201105a404020b18208048600c1d941c40e401480304101d20b8031042901030549841440c1801158028403980e405038980404a0242c030f868060014000d00d0b0800c000004c401500d40c40d1a01d03034200035000301743c0d0f0805508902416182814406002007040400d0058408021003445499 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 109382517 1250 109381267 109381289
    0x4091a040506180402010e1512010e0a09150c02071809150509060a0b120a06020c010510120f080f030a0b031e12030a0609020a05031006030501030305030601110f0304 73
    0x1252003084101d52000c0c1020b401210000c5940402c00f142c2c040b0780781c0290302420310a034819040c0c4000351040c1042c02c0050301010300824001c41040e481541d1030705a61039a40e03480d20a60f1210010b02c21502c010300007614102d848140300d0110581c991100c01c02e016503105941c0b1a54035200e12050140e820f40c2415016541c1c0c44084d028450015201c04014030000340a0100d410600080760742c440004d0516280300d680c80c00600c00c291360f180101d0740144011003d81d6841c50181c10400d000b50044a42d0b0000d6508110010780c0f00c08044c088c500135151600c801c5408050641c44040c04100031032400c941c5001c0c1045401c401c408540d02035841000c0743d583c00b284a94401d0281400c02c5201034680c10190841d10901c1813140020031000204103003050010f44a0340e444084402811a81d0303c1f45e4031780c41c400030303501038540e034081d00461080c103001d01c0c0928000d95820742141210b500348001744c0001c1d41400841c0d070641c070403070a043c1c0000b000001c54200d2400a4615800c5a00135400605528 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 109383767 1250 109382517 109382561
    0x60503190b010f050a0311030109020907020d140301120b1306020d0b100e060901110c09040f1a0106020312040602070b0108010605040608030c030f130e01060507030809010c020d030b03030409 84
    0x8401414028058040191409403142c13900001c1140d00e086804010710042d041c4109158984096100d010100c0d0014103000c41400c000001940f03460070b0b04001000698030103580000b00207040c048a040b141042c0700d138003000c40c1944403020603480181003d40140c0010000c2c0000c59141d001800700d04860a0001400c5203181c800c2100b0350042c240c2c02414400020f503078160680d00c0000341d8071024001e080c980d002180880303009041c0780700e1003c0342c3d900c0071448052009108200051a03032691065034098980c0140010000c03004200b446403400582c81000907542c054085000d954100c0d2096101500f049400d60380e08004042c260429149a959020100071620b231034041c500050034010055031400034219901d90302ca01c11010044080f08000a64111040600d900d900042c042c81e0300d007d4055855000040c4550300825058001030201c10100d0142c000610401c1d401030400c0d00100110f804100064025044454045a00d400b00740070004200c3c3d041e010b8040c0901c4c0e90a5000002c2d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 109385017 1250 109383767 109383773
    0x16030b0f06030c010e10020709060e0411060f16021f11010f020703050306060714070e09010c1d090a0f020f09120606010f0c0606050409110102011d0312040606050319 73
    0x4000500242c400e0384035403240515030341c004100c1c1e6502c08044e54004c8441311040010380c40c294459204242c1d42380340030b100180803003141042c103010301d1040500d0f02041c0484404c00c00b10f03014500081081c5541084805001d604c520ba101450600c054503010b4485219103500251030102c440c40d030080340c18684018031026007803080603003c802030074045042100344d480c001c00c2130000030540c6029a9000804400b40450141e02035107541d0820101c0750040d032207550450700c1e243c00f6102c21400b9820500c2004d462805404012181d1000c054800300002045040000300e040141104500725a5649200c00003403050008007140780c18001190380d90981042848041050070041134081e8000d40d091003181d0781d11100300ca0f061459482d19410b84845402c1c942d00078402a0700c016405880d10391802c0410454000b2000716480c2600204900075006803540d903600070b0200c104005410400c01c40c5581c6840101560700607024080c00140c2a480e4004246405021840c000c2ca003c10565401c0070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 109386267 1250 109385017 109385041
    0x50a0e0708030a050d0509030c030a0906030b0609090a050403030e1e0c150301060f09050402120117010c0e01031d060c0306130b010503040f1e081c18060e16030b 71
    0x20041c0384010341c40c2500c40c80c00146140200403810310701c40d49620118024450810a407102c4110440a50341c1d40c0c03500510245c90030100e4850000400d05011144507185000230070346600d00d9001c4c1c01c00545a60b5052000000c143c000c00c00c40902d551100900042801008250103481b50120360720305007034408260b14502817500004d10701c511000c8003c3d0402c900d00c2d0041e24110f90f01414502202039120300c042e140d100d260f41006804c103101180700080c0e0751507160424100d80040c01c0d400013070381c0e1a10000d4280c402000f2410040703207103041c1e080310700d52090b440380d100200003030781e00d1003442c010203071041c00c112040d074141c02a50004001e02085141c008078510003100c1414082210861600028103e400000d0015160241c03150700d190030b12801094000c0b01c011040c60207969a0b060b0300c1c20803015001410341c1c100550b80c6001e4007290030842d01c1210115031582001c60503040700c1e59600c402410b041d4400c0e25150003034010b05203128000d803407030300c01551080d800c1c0e0405142a03100682 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 109387517 1250 109386267 109386269
    0xb010b130909150e0307240506120615040e0f03280905090403090305060907080706030e0705040b0301020708040909030f0816030e030f0c1006090504081206040f050a0e07 75
    0x400500d0910503100141040c043d0b01680d045452012840e10b80490300e26046000304000a445900780000342d136051254030001c2004018800c00420540e2100300074400e0b00059164194810380c4040040780e0141e184e141400e005640060000c142068100c030501d040144000007549a0340c0081000500417050020725001f86844d40500050041d1906008001c04240d2160a01a040240100e0305141c850310010010390781210466003c0d0811220190383c03003002d4800d9000b20b01503410080f5004c0d129000d80c1b41003000e5031000b01403032820a41080002c189001c0c0d07040e4199401c001420000301983c01500080004510024102000e42000f4019060f141481d004021894003009207900ca00300140e200b41d9500d00c0d00050300c001078105035166205a6080c0e04e070100010811420f10140083c06030300290381181c051002c1d5a0380c40803203081d10020395008150980c1407000c41c125581c4440b060740d108070b00520104603411008070311001c4035003c3d07e1000e00107131600c44903420700d001040948 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 109388767 1250 109387517 109387529
    0xa050702091308030f090a080309161a0d020d0204080115030b060f0a0303180503060c0d0e190f05120d020909060f420a11030702010e010311070b010b13 67
    0x8400074000b662141d0303441c40b0040c0300c6400042d0318401300321580c604001d03011840380d1210744265241801c0d09020f07030318240c2f08511050041c0d20080440e2200d940c4851500e818051803ca506080380c0d04082c002a41110300702c0e4020320341c2484001a80c0c442400340c0608003800024580c030b03183c150300701900410402403800d40103554284040ba4281c841c61489000c0300c1d0540341c41d80620880240700c140104003640901e0f814490681031091184010b402001c0d007255540c42040131800841c0307070f1a120584034030340300d8403130f50b5074407104011815441403103040d2485402901d0010804d1120320110350030050080c511a54007049201d441d0515803002c0341c020318110303030314074580b111300c000105135046900e0042c0c01c1181c40615034141080c0160b044211081d4100061603044030314081c500c040d00600214000155080c80303242c80007802108903000c0355010703036603520545c40c00001900904483c032000d9440d61000c200e140041005003c5003070290000403c929920f0460406207103010442d034004c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 109390017 1250 109388767 109388791
    0x316051002030a0203070305030606070204050106030204060e03191103070f060203190e0904020112090609060903090f0b03060108220f110117041e020d0605010504050c03130b09030f0a05070209 85
    0x82c03603d03600013003074905540d4503180c4140e99544110205846000b0890000d40050904002042454042e005042903541c02d03075500b010001403404165550310740e0a44160f08807911003241b00896142c4c443e803495440060121011156034211a0400d400c80f0380c0708400580011541c814008140c00503100700c100c051a01c03aa00c68913070400515004c2c00601300905100306150842c0220b415500205c60158100c8400c000501c01c07410301a0140500e8102180010310030381c0b0200b165088403c43d501035847c145407060841d40c61340015200f00030050300703081d11250294001880141685403003000c1e81e00c01d150320310790a03020340f815120703800d48030070558184900104225060342945130582d0380503800a00c031110740f607d0010a419144002040650880015100002484841d400050485100b40d40030041c030360300d0034820000390000f901c41070010281002c103840030900501000ba0403010385004d07070340351a40303045901c10300740e03c02c044c030f40017080000c960b03c401d601d41411000c3c0d11500c49850 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 109391267 1250 109390017 109390027
    0x7140607120f110109050a06110c0607030f0b09040503130b0408030f071b17210304020f010915020f07080304080c060c010f05041a0601020c01020706030b030a02031605100203 77
    0x603200054402580351000c002d030766040c0b005410311814016070281d985078003c020a1134a804c001340c503281c0d40700041e00c8032420080350440540d88001201e40ca0440c0340e018160649441c101240a061a1410804a95110700d001481d9a0320408001d0146100e00002c55441c101050900c1c06c84034940d00c40403000d48248400c0242140c00300c01c40781c04c501306105081e911002c61900d1800c0031000a441e4021800740c2401141c06080c40002c603412003e144100da2006100b0943d0742c42d40c2c07042040c1502d01c2d01c070501c0420014101148104c0440805061181c0f046440b100c50300d5880c202e0302e50000040e4010390200c07918903800c0c0000c5010301528400f6618250900300b010b039075504d409070014040c00e8005400711000b00d003035100c1100c18812035030078440b50420381441004000421044011250000081390b070b19030002030b104140090680140c1140c0d0704e4001c0035002403400c1180150107024200b8600b005070340c00d02c80e524400d0140c90b40c02c60600d041506000c007810300c40c0c080c035003503510408c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 109392517 1250 109391267 109391273
    0x71803020906121507030c111603020103050a02070f120f0207050d0219080718050a090b0a051008010905061008030a08041e021215072307080909070207140607 70
    0x3911503000b5400e441c1c58810700b80d00d02c442d0303241c8400c240d51103a0000e04001403050195041d0000c0b518181c1c60741e20074600a00407943c541d1180040418950034601d007040070030041d4041c0d0403041d0b010541c881e0040c01c0201c0740e121400e1600f07c0342c0003110006a00b0000208903908501c491b07481072a1072005005031410280483c900c28441b40d0b0186c4283c915911848864100341003980142503200300355128603941c1d088200040030004202c9246c0341c03c090028034005840d00c2a09840d42d003084000c0c1c0152202024030b801800040c18199012500c620081004042401242c10380c0f0310034030090416203448050704840c8038494000c600c0f641c00400011031802d0b8805041500540c02030515a1b030556814940728045c0c001c5017009400140120034200380c041c0100d40102c0c0920702d0850100c10b55160181114461080d50080d101d200085038014003180000b4050800a44160715140c03500070500001030071043c0c11180383c40160320005090002d1203d139640e20780c802005841c0305013003801c070341c1d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 109393767 1250 109392517 109392529
    0x703061508150c04030f0b090106060e01050307120b100503010504050106030207021026010803030a0605060a1209330f0212061c06060617010f03030c0821010b0307180302 75
    0x16000320540b0300d6100114030001c05203011280195032104c074a0b00301c0b18440c40c2c03807100c10000b25540300c015407901c000003030b50798003600e412104510141d58191440d66030703200599843c0082e040209055030fa81104207802d80758088159003110340c540740e1a0b10b0750314210821041d501e05800c15810540140300e480c0c01a200d0818251500200381020140d0040d009803548404010104c24074141c4076842c00040c0b0480040021401548165003c0c802141c88000380400740c130a4095000008031449074184420f8a1030340300313100451082d0350b8180c001840c3c40e18500c104240c02c8000260b040d10121241c003a040903c41c0e10490780c0c1c01c404c01d40c2050301485020711100c40041070b860090340841016504c248841d0000540ea0754001da040183c2a144d00c0b008041c0105810015079180c0300b03000200e26420300c2070030b84084941c55502c0c00e210785003030b50341d10b600c03604040c00401c18003030310100c51100703a40722071500da02a004003400f480d00c03441c001d0001407800c0000702c007221561080d0201440036031600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 109395017 1250 109393767 109393783
    0x6080309030601030816080304061a0108091002070c05060309030a080112030c060902060d09050304060e0109030b0c09012102031b0705280b040c030b09030c070e0408090904050703061508 82
    0xb40640d21100c5641b01d114111a50407001004d0b20000130411080100a070b0202c2075a60410fa40725140c81030b41d000650b95404299280d21807076110207074030f4946051940062900620400c010300c0c002c1e641e10081550b640080e50001c40c580c00c00300d6519101c40e070000a04d07006041070f0304071681c02d0f8010b441c00382000741d031150b0191600b91544010800d6485001c112042140038840800c81030b8028280191039030130500580c800220800c50b86929980300d0401481900d8002d07190721655180d01d070205500342d110351651414000c811031704d4818081810111090118044000f69032442e10f108240c98092980c00c0c12480510140011400b0400001f031000d04c48006220200b0711071490b240300302111602c0200200043c1d04041000100078110340300000700c9119003180002d645070941d07569224002c40d1030425040c0d0020070104024004506030390742050180e0300300c0340f906072000c011540e003000469060720207a02120701001002680c3c803501c0d004800105012844c24244001c040c0c645100b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 109396267 1250 109395017 109395023
    0x702061003020f0604030b0a0e0f0705030c0d0228030303150315050c041a090a0503010b010c1b09050405030306130b030705040f0b1f0f02010b0a060804030c0818040608030903060103 80
    0x40100c83d41241e103c000842e0003035030700708035604040c1c03901c203a40c0307405807814209101003400f07141061384000c2c5c000520710040e900c2c01006000000d0024003805404140701a0699000700001c6006160008d50041c149a0a96001c441000b0303900b5801c000c1c0a0b500d9810350b440c1544c60a52080001c41c103520058080041558404252921a42481d600d0350099811140401c010841c071400c0410300343e0018150807000ba50b010b01c50658a404160889061003101070100b00483c00880c00221000b4410a007100c41d98100c80d00d0075105c100003c12980129001c0350b02d81d0001090003400d14061005a490480d9040300707012412200000ca41c945505205040c0603d44501c2d000c0d01d00c1086820401135028050103a07803011805818002c4d0740810710480d200810800308544c0c4800344180075404000101401107071070700d840c0890454603480d00410030303410415818070800c00199404020415404a8100a44520044410481201d01c2030780030901b268802c016090680d2070100d050760441e50 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 109397517 1250 109396267 109396279
    0x8151f090f18020703030618020a03053709050a0c05040b03060601050d0b0301320c0301050a030f0201020c1003051b030f010e0601021203010b030403030b1009090b04020c0f070302010305070206100302 88
    0x558174041c0c000c4c1100303030040c080c3d040c8110079a0044030581d902070400c08003155410300c95615100790b102840080c040441c161000c07a01d1040642208400d004400183ca40b1000207030003226407545402c01c40c0e0440f0131101001180010042d038036240c0184202d0361411005084203042c03820020f0314922408400000303854a40141d050349940c290b20071504160f81618010301d4002c0400700038492a4030004003000c1020200224428070f981d1001e40e4144c441c05044401c646003103458858241d082464103d0440c4a0000b9090382034580c004294540308940e100400d01c1c1c140f00c541400c8030b00d00d02441c0c511001e030034010000240d40108103113045800c503221a5005403a0000101c2c10410061a900b400d154008000105a01454001c5120b980640c3d02008601d208004010100ea6060882000500b40080a11030500740341d1003540340c1900200700614059034145414244070b03000c40c103105030b030b00442010020f6582500565034040aa0b00c05071155182890b03c891503c112800040e000d05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 109398767 1250 109397517 109397527
    0xa0e0d080711030f03040516060c0204050a02040909060519020c07150903050601080313150f03050703180f1a04050d0c050102070804170d050f0403020108151f090f1802 74
    0x240101d030000c00301c03a4a0020f4a50780d480c40d0014103c65403081e070301241d50b031040000c0303000c2165007004504190380c1c0a54600e41c146050f030b0200030207082c0c0a4174403031b03030140d00b04030000d5510b4041c841c29500c41e126140c00304003450a00c48410b215804520901d001c0d60042004003034800300410b00d00e0942d0490001103031442c1d08441d007202d400007650001010761240c0000841c017004000007400070080d940070305d916080d80714101d128052604040c5813000c039941c04800c07d00c07580690002580040315140004207142460141038128545600c180c1b0413010200c08032051202101e40c2d2602030b12a00d41c0140c0504059a40360303620310a1416103800c00c103407155104100302082d011a000c41da004045e40340c880d501e48001892910f010725982502d44680142d0004050051041c1e880c000a4004418101480d5400640b42c40d540200350003011070340001030290b0703940e40c0b500040c2e5a4003c0780e240b05900c414a000580190b400c4e810520801002c00810801040040c89510301480c507014056115 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 109400017 1250 109398767 109398781
    0xf0e2e0b03030c0604110a03031e210e011401030c0b070f0c230a06120b040204080105070e0118030b15030a02030109050c0a0b130b0f040b1c050a0e0d08 67
    0x140500300c0599418000010041c2a403840003902c580103d000c0d00e40754000450180401c9001c000d1407100401064000360795080054810300310340361151450800510ba41140b6070700c090395401c4001c05040a82e0307503504a0701070640034424050f00c1d050030303a52103030194115140d1215565442c03090030240900081c046040003800c860100b40c5179400b4020100c03030b07500d85481e100360380d01c0010710840d108210054401c4624040c41c0d01e104a640747c0e102c40c0310255480e003245010b08860990325400076020040004d6000c424824588191125a641440050390321700040c80751122004501c50540510014404628021a201d4200c11f084440c0180300381201c020a040c0400c081c0041c1d8154640301d5107c00740302d80891030170ba07945821103d0102c501d807a1060041e90740181010307200b080a650909021100f184d10045c041418424120381c02d04d80c1e5070701020059809840d1013400103030800c03260b100d08416400b501c4e030020382e403a0041c002c5a003070b10742c2a591110303135601c614104480e002c0402d0761 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 109401267 1250 109400017 109400021
    0x3010b0417100203040804060305070518090c09030304030510060b1201140109050d03030902010f0219080a110d030b040b0f01050a141606020702030705030d0c12210f0e2e 75
    0x200342c2d42e011080d0345911701410080307040d80040c4998000320b400d00c000684858030500c122809200c0782130001c141340d5000030034030110350001050040700d80c1040240c81980e9134200701900045200e2401060040c0500400350103541042c0d0000185072418482400700c0440e8480301070550b0540f0990400020b503543c0100c54488507544040c3d0000010620842131640c5a040a000d0364001e0f200e40089002030340b0b00303c3c1d0321002086402800d002100010000410600c0141450000c40c540114081035071103085007005408005000825030700d0740ca001050a180c050151240b0044840044600c00c810010f0300f10700c281c030301943c10402e1255003c0c665010140546a00d080c290380c024100c6071051514400079846443c0c164400c3c170940d80002020310b000203501c84050680d5603101040032082e540c6680200c00040c0c10410f2042500740c000462402042d150020f41140102003011401c600d60f01007107a141c012113821980140800048402d0903241440700d1400c00c21036000c0b005015070440c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 109402517 1250 109401267 109401283
    0x302031e011b020c01020d080c0a080619080619150902030709030606090b010e030f1207080904091a15010806060703020106080102280201021903180b07081b03010b0417 74
    0x596800e00b80d00d1108159002400714411882a0215450745d0084001905e043d001220503043e00f0b0003c0094200d200d108a140d1500605c002d00311029401e00c40c400203000c0240d61b00075610b19403056080120900090303140d00c00206403c03c040000c40c480c0606220710f09000d01500300c4403500000414040c07803191116000558100100300502900c0d81c441a0140000e02c107154002192031011030b5003032401182030003046047c1c0006010040c9248400b074890703044828160b40350340e410f2003c0031080c0c4450250624140c840d0031805483d503440c181440b0030a50123084161400144140051140d030001100c41c2c001d1800c4030034070745903c01860200e01429031a04050300550004c50103050b00e03040406a00c5904c0c1c0380b003da41c4031040c28400200d00701d0284c4455030300e401442100b200c3e03160780245c1c05901300748001c6058040440540c0c80f50103104c1d00030366015000541820400609118140d800310820803100001072955140c981549280e00030303401922500608403460f803021100401c4411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 109403767 1250 109402517 109402541
    0x4120e090615090301050a020901181d060109170105060108070c0506040311031c09060c0804030f390309060908060a0e070e01061110090822091103150a0302031e01 72
    0x4080f07854001c5000010350020070509d408520080601440d9861070500030050312900000000d148c400c04458005040002c1e281c0f60621404050200e800c62142c2c0301e07211428013074400810b65080c488001008080020058801c01604035521f00004801156807a0003940524003014110143c007071090540c460740401080740b0800041c2c040d060191074125070f03982d6000c1d103010418402020f40560302031404403801130003c0c0c0c002402507105400749019520704a5402c042040300f8111100c03019484031007030007800840b180074000e83c041540c0505404040d0015141c00000f05103841d845507542c0c00064032982081e074070351403882d02c80041044110001c2421806610355942e591138058285800c003030038000301d40541d4600301c0b5050700078054101040d034041049454200076402e14141d074059403494011124071450300082e428064047d8090142d8103490302a41d07810300002c0012480400c40f0040e0150f00c0c010390400140c2da001c00c04d1030000c0d091140346058010b40103c800c0c01024070903040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 109405017 1250 109403767 109403771
    0x11011206090e06061206071404050d081305040605060403030804140a03050c0114070801090b04061503140105030c0102060c0d1104060507060c03050108030a030f060b070b04120e090615090301 84
    0x1190031081d0042e9445150840503951980c407550f041c002801d400042d10b40c9281d006401040c442031042108820788030103100c2590400d5100c1001407026000c0f844140e5074901c0110701700c04040039502c4110000c000440b420007405180002003021405184805020700c48900009070500038114070b1440300060b00e0050b100700b8051845d002c1c240f60859811030802c3c1d071901141241c01c2c000c4010b440e011780c3c80307629001c5542c0c1c0f0b082402c0c009030140c10b11140c0c22030344491740050702c0710a01801d40301c07802c003540300440d613800c1710145040c040c50160702883c0b00360301040c580c0d501c59070007040041e000038121140340e079a00b100c081ca40300502544800c09101c160700280004105034000b02900416201c1d0f5024001544240e1003241a14001c0c010120107070420040c912040d40a03600080245d6440074000c10300b141d44034002c8225820500042d00d5818151007040100001d544100f513014000b0f042c001c1071141d580010401c80c41c8014030080c010344640120084007104581170b900e0349a002002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 109406267 1250 109405017 109405019
    0x21020c0706080f0c03090c131401090507170402060406200a0503130618090518061015080f13140a050a03090512030d0b0103020c071215090203030711011206 69
    0x80c0314507400c55800e403c1c142d800003c600703203031008011203010b0307000c450007007480920203130030001b0b0050800d4814104170350300c8a03030f62411000020389500810203210001028540f00b64068010000801840e5605c510241040010b0351540180e40603141d8038600703262102d4813882e07450505a12010080c40038402c0710848000c1000000c001c24030b0031300c041181d144207555407006503403080b1b00d1070b0300b4003081d00c10142c148801150b03030b40001c2d80603015420707000f508140d0252a0303042400c261550784400c96480401d000080400c06000714000552a090503149400d040c140300c2e000b4003805480f165801c95074a034003801140c0c2e8281d140b540d0b0100a4407490741d801d140455036481c110104902041d04800002030f689022140d441ea0507584201540c41e20303004a28400007803111910840c1030507428491140c07800c20800540300030b490711700003510402c200c6043c000f8023010310ba000a14001e08002e0f03000d0068038040160380601c0d510000800c5141e004100517101c07002c440c401c0030750301c5141c000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 109407517 1250 109406267 109406279
    0x60301030b060a050d020904030c05010b0a080a0b100f031205070c0b120105030f0a03031d0604080307030e160603090c171b04091101081306110c0d0f21020c07 70
    0xd00714054030044419001040d610300600841d1412040c010750302c610843c0008010900a200c0141080e00c07503c0001369002880c40004c1c40c0c40380d60b400002ca50b901000d800f070300308441a000c65400c5050024032244591814070340c1007170700d200c83c000101000b82030740d11100d0441c020010707202d13103c0d03010b0500b83c40e03c7c0d110403240d14213070030101041000641ea1800090241004201c500c100c0781d40034040c1007014803d4606030050416295121101c40c160070a0102d0700e44144010f50103644241580b40c3e50341080f0000500303940e001340c004070660f04010703c941454400020740008840c01ca050203d80e072007103410440d107142d10650110b500252009141c00f0300220100e01c500400d11805808045540c0900034001210141e020040625908401c2c002d034641c00340e80d040707a01c55040030041002c040b540e6952020341d00602c13a40c07175060402017103c9184031400c0c0052481c01c2054906000b6902801e84010548001e1842450417003482c01c03003204460015404413140304034050100c0744200e80c2c1392 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 109408767 1250 109407517 109407533
    0x201061805070e0406081018050609010e0f07050619050912071503090803010b09120111070b0f0f04060b060903160806010605070b060f01051c0e07050105040f0e0406020906030103 79
    0x251802c0002d01d09094140321403030188500d03400d46161704000c111608803a03a503040240022104d40032181c040348078200c0010010082584140035640010982c01110940e440c42c0500400c800e00c0150440c290074031943e1a070b1410398042117148002413510141850066503948500d400c1180c010350700c114800361741d4000140081c00c07104030340d04151002c20380120850845800031001491400200010002e010000d0040c0c0070152000307014801c9124005c0c22a421030310440200c003082c40c00450301400707020420700d540794403c1d4000380b45122454040308010303242310000c0000b08031a03660481d4605030b440b604241c0f030001c00d0213012035400700710301c041011191806109000b100d1160700c0000c40c2251081043d9611a03500034001d51160b02c842040010034120300c456541001020f10501c0a1481744101301040c8452100c0002820314125251504241058010905000c02004200845078107981c0003821140102505402a00c440c94440041e200c0c071000c0540c801404000801440082 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 109410017 1250 109408767 109408771
    0x5070915170103060c03020c03041706010e13020108040507080f01060f06050a090e0405010902040f05040302060c0a09030f0c090507021018080405041a060c031c020304120f0201061805 81
    0x800005055000400711041514091035181100c840c100400004070184c000400034462410b0240c02c011040f6182403031508a5440b40301b0000d044000fa60941c0c03814012140500340741c11844015150112441c0d0700c08000420003410003ca0358002000d0007000d015880280408406a8282d056103400e542c0c00713022280034206034420000c000250f4640070b102151692846c07500c409000f00d01e0074160542074400140251010f54a8100900043c0d131203200700c1d0894419040005200c0c1803900b4000d00d04000113041f8950040104100180c654100b0b2080301140d074040c01000d441e504500d0540c02c170344007a034856440541820140012103801240c03401001301c807c181000031403074900144000130f100c000040d100760000c00c010710450400ea003102d10101201c0d00ca1111040045000c05c12a5000f1603400d02d4507040440e0a00b1555000c00320150b024010b014158150b04041d02c40000149122041500f8400d0048100c10304600030f42102000b44075109510310000c1d102400c0200be4081 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 109411267 1250 109410017 109410029
    0x90a0b04050906070e010c03020f060c0403120206060a0b0a020a0803090f0622030f031b030203010906090501080303070f1701030c142d0604050a0f0311030a0f02090613050709 77
    0x340000038400340c2c0000307032081c0b10351003030742e03650080e0481e0b01d0042d140f41860303200030360031405030381c0f0042e034450410413900740140f0070341280e50754031032440c2080000c0d400304410b1a4110340102c000c0c442980d94039070042c0305039a01882c0490ba9a04405400e03460540b02e048001c00c0034a01000300444904c000c03458800040f40c0c801a5450f507a2614080b1490b0540c45400d20002d500e00002c1d43e0100744100b000550301e01480c100000d605c405504041103d0084401290009070004014401c0c558203020f0107004101052080c4429418118081e40301e0200920150404c04980d515005040c41100c03072603845d1a20070b030755003500d503105c0c01c000c1d460541d21300640181d03504640c80306003117007040e4030410011002051240350759141c0c0d05e100d542200c0c0580d85140d20200034080403034140c1d41e102e0504010b00840d0000c1e01e001d442c43c900306c41030003844400c440c4650442450301000c28440d801210340720740d045075403040607655000000d141e0413000c810300c19050701d00030401a1464000c10080150b40c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 109412517 1250 109411267 109411271
    0x110403050610030b0408090a08030d0510060e010507080906070b010801050a18080d1a03010f050f06010908100b010c0f03030902040506040c321201150203070309060c060902090a0b04 80
    0xa14014040b06001e2a40b00042c04034041c0c9002402107a9808050200040b0007040b081084d40c0c0ca00b025851500715464400d1800e03039440c02d01c03c540d032800d94040010801401d041c0703041d800d0f55001801c1c030b020780e00b4050a4010300060b107020a90307640e4100c524072070340f0040d2031202e56101d100c0b2600925085410f0b42d58545001004105070031070a000458090b800800701c1e15060701c4c1c0400134040c01608580c0e0420481c00c00d071134802544c0a0180d04003002d140c040000707403468119440404040701278030907414000300400501041c400407400c0140c18108403004a018228040102c901c0d0048401c05090b0f62960f5004004050703240c3c001c00003480c02210113100580341c500422007125070101d441000b20700c0e00e0040e41c1307884401a14211244000840701c0917040c2c100203201d01a54080707089606190700500051002001c000190503084089100442c2420309540e005000c030500784c0202d0082c007103d0010301d0104240d54102c2091117a000d0410382c0c882c1800ba20540c050411180340a02c07480c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 109413767 1250 109412517 109412521
    0x41d070807050607060b030a080a0c20100503070e041409061e0a0c050f0c07080d08090303060607020d02040c08150f0901030204090c090c0c02010906020d090b0c101104030506 77
    0xc00001c41105607580101054a09520390741d49000405081c4130b410b13010300a455559020030380c0603018000e800465140d080903c86145031428a120a05100002d1404200c00408d117079110181441c41d0b0b07412a003005a600d482d4508190703019005404200c3c0c1c004e0801c2c102500e0001241d0485024000301c3d81142c00c0e58840e1010745105030b0300b80c0c0308400038000702d200207819901ca40c0c200008842103403c00c41d113014412040b0f0700d482c0d4080c0400c00b910b80d020003820030940b1000c000340202210145042c2c0701500786040304540b00c0c8809807920f4071603440400c0710307401c0d55038070482c00254540c010310070050000c50b200051710401045444041000941d0001074443c1005000d8000c000300080000c61035a095508100040250f050306440144d803044000c1550740052099a800700d00584036402400920700c0010711035071054026104640021211350943c603085401482a100f10624050300d92a403d43d0031440d2901c110306803040b49082c010080c101c00c000354018810b680c090b005560302e03a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 109415017 1250 109413767 109413779
    0x30c030614090d03200409020301030311030c0c0108060f0613170703031b081603080901180f02130e010606090302040b041806110d0504030806040c030c0507020d050705041d07 77
    0x80341d022500c00d9100c0c0c1018441405040c0300b5401820564800910301104034007440d08006079801c2170300200e801c940d0020042c018190084030040103406a1001940703445e50f0300d2103203500c640e0007908043c103100c44040420325a41d94032801c60303440c0320090070641d21038401c1e10100e8040d14551184101c0001c04142e42011458041340400c2075039090740340e1004003084000703511500c004211381524081001c0c021304a00040d0804000c407501d009a030f40070198200100744600b143c0c030b10100603980c0c2040404080005500982d84408250121501d41c1110120801d00740600312440c0d04a4441d441e1031008140c40d40c1211010040d28001d660812560b0000024803044441744075689052411400381381d00055002d8128170a42caa1102c0442d08105481d150502994010340703084011610000810034a402c00d481682144607851605200ca0510520054814402c200d0041e01640c84914220240300c404c100c4100201000f03032080047d0b0b507400741d50078807179100711030390036990f0148110008003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 109416267 1250 109415017 109415051
    0x20109060509060a080a09080c0601080610180506010201090b010807060816050316020705040c081504050402090105010e01020f0d020d09170d0c020301090c0308090f031f09031107030c0306 83
    0x46001402013882c002002c0300075a0040350040c08001c00c0340c2c454425100003040f10020700a203000d9140200742e694100310080b81807420091510300c000e25400d00401c18840781c0e6003600800540704a0005458817a040102e002d000350760400740c00d1015080000036115000150a0100d64059843c05a41c1d20b070052440e40d0801c05603002c1002810a002103807500c1010603005000c540306004681c603da40d03c101107000e4841c541e0203400400c807242d00b000205098000c1c07101005108990800c0f0720b241c60342c0066040034040c0261410040155500e480700e0b4003c1004494034150601204c0c44002d001600a42e5035480480e05400200803041c00208d03842130042200103d004407028101141c0317000421582100000c200307030307815929280c0f50400300791055480005180561801e07030740d606106040c071811766469980180a070b880b40072428500d213191011206500b910b02004103e010f19800c040700c4041000d0480f91040c043d0b0350000017001400060082160310610041c00f0411030b003000a14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 109417517 1250 109416267 109416277
    0x2062a010f0b090708090709050a140105040b10030b150304050c030c0102061b030a060b1201080c1804060513080301090f05011a0703080702070f090b0a0b03011212090b0a0302070201090605 83
    0xf41000701030011840e09401004043d074402d45002c11540c207580d950140d10255003007030f6803013850280d603800d10700000141594010701500c01590140800030203000030800754802c585102c810180c4c1d407088400255070300c60030020811007000800e0340368140303424019241d500c0860518444c0c400e8400c10010b950000c500e4a11a54100d400c410380a444020a40800d41c4010001503c1c140c0e40c500100d40240004007070204010901c00c551202c1d0f040c100102d15110031040c2d658440c102e0040141c10007019000391a81c4079512410100b91510b640008445500d00c0207001082c280b4080008100c03030307131258800450221510700c00e000e070340d030380342404880c950b003040c0250303203210b03041140300c000c80d0044c00c00a400c021248106c0f59607550701c860102200c800341c0c01c02d07400703181c54009c1c982ca80c0c035141641c10007810860482500d194980507103003011558200b4001e000e0f802000c01150f245004001002c002c000002000e03507203e644035401002588010012408900c0080b00410150300c40c0742620 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 109418767 1250 109417517 109417519
    0x608010507030b090c0f071a040b010503010e190503070602030412031103011202010503070207051017250f0512010609051903170c1207050a140a080406080402062a010f0b 75
    0x8000340d01e80e02840001e031b0b840480c030b007100840c04008000c002407c00487c095095048000a03a01e401c0515200c2d54605040c0d0055210341c0c10140c54120304000410240c1220703040c0080440310401d80d14003542580506036024140d40e1001c010002440b44048001041d584c5540e410422403402505507141800b003801480360a50b01440000300650040c0d00a50304098940110b803001e40e600d40c0041c8880c07002d01202c0b0001540b0401c000c03843d506030040e070350300200340201202d000d842c1c2800c0c0b02030070140d00591104000c0100c84c9006414010700890b80401d204e2103c0b000c031581c5845001e018102d1a10980b400740c0070306050258001031191980c01541c0d808410705d000100712001203412600308194030415030045804806100400400a10700c151166020344074840071802c041c40070240c07100794800b59070040c1078203134006074402d800c03074055603414100048152603030b0000c1b40031800340705030070440d003070300781d030b4405035200c100806c040d40c1ca80040020f01480444940300b030240c3e58100351113 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 109420017 1250 109418767 109418779
    0x20f0708030414010e0f010b030318150712020604021503040308041b090e0a020108060a030c03020d15051f050d020109030204110705030d020909060f1f030b03100608010507030b 78
    0x14000288003100215040307809425011603140760750000c5030854000c81c050b85038030350015400c1d40c5202000e0041020046085001e941844421442150f072400920f9801d44190003501548094103080010b848440340c11403c0c20303144002d03e44010b95540310a50301170b48a070f9140800c1418000000303040301c1c41182d042d5215852a01e40d69220f102c195030a450100480074000400f00f0742c1074a07032040254002040c00186820740803400054221301000c1e14090013112041028000f043d424602c950403680d06480000c0901d400b070a01000105401c1401d40c1e1440c01c140500c44403c407a4181715607882d450807004285195980704004c2c10707a221600007400304200c220304002520303103a0b0025a60080042403980b03040b0080d941c441c29a032105008860195000ca0768203501d05124003050f511100940c1d210022075007900c0001d13001322403141070050680d14001c0c0030a09510070f4100c2084d954000c0c0c1114940402d02d148440646582d0040810769803920000900e03030340c440c2c00f901800700c4001e003007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 109421267 1250 109420017 109420027
    0x15020c0103091e0804051516080705010207021002030a0f05090a140310020406321b070509070504090f09021c0804050904060b012601061b060207030203090112020f 72
    0x1503020300054031007620400f9403120803040a40f03159030803c080d24480d1000660300d81c00c0800b00680401c858192000c0c1d11802d0102408051604036010322498200b8007158640100d4a0000c0c0a8810044000d4202107000030000130380d500000941400002c5882c0e0009480380340d035044070075004c0c041240da8004249182040b40703a01060400c0085180075003914240044c2880303800990340580e10640c00100d82605108006010300098803949128101d0300041c50950b9880c1030540c0200500000e582c0d001b062500040e060800100d0024003014115505c10b01d004003018240d500188106440e00b401d240060034801c0c9640300d5035000b16030040090009140000d100c5455500902045a44800c2044007060742c0e0344041d04c0c2440b0f9441600007060409a901c0010420310200740102001b07000408030074405484c104185043d40c0d11440c010240e170440c41504119821070703803000f42c500c1d440010203000340340c0c2c0031004180002d820b8880740c1310348a0b00b01c1544100c2c401d00520049822051007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 109422517 1250 109421267 109421269
    0x14060907050a02100608070501120203360f01052a0a08071b0609120c030c021012020f030103030915090b09010309050d0e0312091c0204090807050a0c15020c 69
    0x2402400842d40304072486103030781d40d5070042240c150f034010f400e90780d100400c10095982e1004030301241c42013485055055061003001e290b02903602d501d41880c406480786d48403c101e150340d0b03113560f8001d055004544c5404130611503140200b0040e502d6207000156607808131480f050180b41d401079800c151a000c1c1c9010205041192000c030058417080400609108030b02d840d64107801c007000301a001e48000101d041c280d1804110508440a400b010303c8000985900443d40008031040e010f9016034000311011208281100c2c0d203a07002a178140854800300c0c0d002c45c1c2102ca04007071410f032071203925944150303a11550f000441c0c09802149400040221000f171042c01c4118014018926040c10003144503445a910036042201461910001030054940c00205242c1042a018048422200c0740d00e40500c02c17003c200082c000308500c00c60040404003910441d2aa5406a40c0241d0009205600d6181904d0916202e54070884159400e805010010420f0080d01441d110302143e01d8000380a0009241c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 109423767 1250 109422517 109422527
    0x111306060e09060301060302100f09060806010509040902060d020409150605030408031305011103010b07061a10030b06070c0803030106032a03090f0506011710091119090f0203090114060907 83
    0x90000d41c045d525842c0000058407100c070600001c89681d110044020342c0c0b038000803c2041c0e2940500b040028050a001041c2d0b040000c80e40201025500481c1010190012980c240f244050707400c14944002000a2607581c0d95204420001409102000d000d030740c1c82048a1a000903500074150020800118080c90180480c040e4064815400031859040d082c98908176900268828000030a00050405c1006018410411100d56120103a100c0700c1070840030a244a2969400009141d40ea03820601a41d41e10016111241d0b40324614071082078a4120035900c0e90020b07c5540046402c286800010b0f04203007011020403110010103038414064044210090301030100191003241e08008250003144090100c00c0c043c0c10340070004421034014216003072030300c1c04000c2e001d40310340c2c6080424000150308014240009508030b40b0800c2c422a140c00e60042e601d400e0784040c4010b449d0580300303a505003654000e5845801140c0c02040040040c5040148208003120504e621040b4240010300050140d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 109425017 1250 109423767 109423771
    0x509090109021e01020f0106060e010c080d0606031d0102070b13020d1b05190b0f0a050d0204081f05090c0405070e0316080631020f030a111306060e09 66
    0x45001003600c40d007a4011a03a18084960745050a580070403503000c1c2960100641c6400d10a07a030001c026103031521300014043c0d20790155143c100000286440c040c00302c00001d46812940300c15041010036038584019004000e150014070b100329000c0042c4000b050b061003941d02c1d5680016000d07416039500240e500514009000890340000801004000f2802e500004038511500004e07800000c0c0c2800c042000c4036503c20301c10044804d0200003444480e0204017624410131105100a848081924007580d21b4021512408207051010900041c2c0410001d44200c404044048410000200070101c0080d90300488000083c3d034440d14814a4078105035101c0355000f415880e1103118081d0000009040c00c58a01740c0030040c448540d0107001c00201440745070303002501d46094820300c00880e00c03090300803001c00703800ca0354805105101c0c0b4150349401c0a4245061402002d84101c0091403910b00140120300000a0140102a40c1140d6683d07162040d03200381c5081e030300d42c0403200c48850100b081c92500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 109426267 1250 109425017 109425031
    0x6020604032307030e0307141302131e061404080312070201020912070305121303030c080d050f09010c050405030307061e0207080307080c03010302010c12031413020a12020a0509 78
    0x42000300707400303800307481003d0880c3c14460750303c024080083c41e007018035007000d42e0408a440e40090600980c00c0e0b82d0342c200201d044110080140c0c580d044905995100300342a441040c03c2da03400c286226201c01c10f60584016141e540d100c0d260080540c2c0c80c280c009000e140a0258554402c10161190900341149542e115281344001b5161610400100d0000c2010050403580b0750f0088605004010b000d00c81200002c01c2200b10504103140d0941c40c01c860b4451340f101509001884507280d09000440f021a501d00c0002c0906108504081e0b00303061002d403084940e450070394600411044103502c26001c82d005c60380c0081c015805c185050f100c4000810358203615003200e01050300e01441c409024005410500c0c0941e043d184c032403500e900c0180c07003007500402c400c2e6942400c200520060781c001401c2030b010f582100c071480d040c041d0f4100540c020540c121454002d08800400c01042e1040120840e81c405c1c420780720992440d50f03500380c00070300c0400304400a5104407074003400c0c803690800c4e00990703500c210 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 109427517 1250 109426267 109426307
    0x201050d0f020d14010812071506080d1205060a0303020601090f0b0307060503010501090f0f060c03030212010314071703090d02010207090e010c09170a06151d0103060509070602060403 81
    0x80031126520881e0720807000c1109980e01d4201130300c10040502002401850448090000a658400301c0b854038828100c0c0181030400905492501604d10b51220001d003001004440e0070007401c10029120001c2680284a020700704000a001810500282006ca940c580c000b0070040e420100144003034159041d42d0040f0681e80c0c1003000103035408004182c0241059200c45035a135043c00300040c4844440d41100d01c00805030b400c20410032520350810802c0381c41600d80101445108d140c00c030b010340b00b200594444400d01000120a1001690140001201810455043c242c0c1c440060060b01840041c0110a8100b405071807401c1c244440d28100c580e2051042c0d41c00d5948400010049808000392404269510038944100940250454000d44400e04a01c50111180c00d10740b40d4030a5007078402048140c035401d82082074408425003e018022144124045641105560760801424403007030720800d0030800803442e8980c000c41c500e0140c88699003c0d146a03039554600b036595440814400940324 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 109428767 1250 109427517 109427531
    0xd0f0f0e0a03080c070f03120e060405120105090f01090819170103080405090c09130b061b010203090105180a1b0f0b07020a14010e090402040f061707060c020109030201050d 76
    0x39441c0020800514818101c035074a4203610000f4500e4103d40380c01c048401d100c081420700101390100c02c0134240c603401d481c20441d007198040118056001725840190000e0310340b10625005030041d0082446900203000b100c0103107510048441c2681d44010300030305007940c10403030580d09520340c62484c01c40ba8020705241e86804aa07060074244c40409034400e94040102043c103201601c0d0001a0603003004150703500c1c60508542d03000180c3d1003501600004000c56544103400d010303031150700580d03504d5000440501070981d100c01c5414084d5104441400055103080002500d074100c1240301000303000340d1001800032010a07a10381c15900200c84410201c8111103100040310075811007000b02402e400d600c829290a81c0d803050140c0c03041d03d034228108030754050b521b6042e01e9a2025015842e481300301c43d4103800e41c03110300200d401044902c0c0807041c0141017900100d06528000d000e00d2081d5a03040449004c00c0e0b13078000840f004010500d00a000800c1c0070400c0000d58031a40c0580181e00410034002046 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 109430017 1250 109428767 109428769
    0x607020303160314040506040612090203120408010605150406050a031e09051507140a0309020d060c09120506060603070215191401120f05120a09090e0d0f0f0e 70
    0x503001000140381e03070949480b5882c00c16130b1021540900f2010078015908080c00c0c540000c2c4180a00d0081e030b410040c800407060301a2905030081c0e4002a00a41036510108480070300342c0c100c0c0e01c80e02032003001d50f00b01000000c1a0822449000030100781b860803a04280c10004100d40311b600240d000f01c2050781341c00411161954041758841102e2000000141200417458000e0801c025000e80542c3c00c0340d2001080150b54011a850381c070398101e001001d03514800444150002c0082c8907020350448807030a820300c10402d095205144024080d00c907a28090b07a550621125100c65040c003c25503040300001c1441c40c1400e1000d540c1005450040d200881100042e25214600450b845804000b03042800d40803440203109105407007000010705081c660410201c1400140c8540c4001c001d6995500d0001c184a81800103071180e840b41201e8940d10341d04d80e0f50080056000b0b024107600c06190100040c044800050409107409158032219030044c1d40003400c0d80e1030030120900c0401d025003200c0344205 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 109431267 1250 109430017 109430023
    0x4140a09020d020706051e010501030b060f070506010f080703051507170a0f0b01030917030601110601080105100e010608070c08040510051c0606050f030901061a0909060307051e06070203 82
    0x190801080b00180c40c1c81d5541440c80c107546001e0011201074058000000e02004d126102c64152030082c2004240c0a5000000c903e103413050402d007032500b40010901c1004c100d80490840d048562260441c040940c458000035210041880000c045034130901041e100200201d1100b580400c0034200034407150b440210296610004031508941540d6418003248944911301c280200c5403028a0200300494003680c440b6809604034410024030701000c000900140e11a0f100400300c0f0700444165212561340b48190303400703884151032802e010f2034402d00104450740b50b10705c03c504a8000f55225905603c56240542c3e8035001818141d4800d8800c200c040380300c2d15010507680c000030319a036800d95501b010030a410b4000000e02c41c1d00d10b8a81c1014810014280d0100c04d40e00345180403e009907898441e16800c0d401401d050303001561000c03045a0303084282e485500605402c540a0b611804255650010592545032030301400d41d101034071b0500006010502203000c4203020000e05050b280105a4000074a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 109432517 1250 109431267 109431277
    0x13021204030201060b0c1b030309060a02160503031804050a0905030c0c04060e040b01051e03070e0103050f071a091c081b010b06030c03091504031d031204140a0902 72
    0x46005210018002003660911410008000c0f55100a042440c41404580c803046444404000140310010748881d580c0c00b40104d5080310300c010f0649684070001d540c080e48554124818489010301c0c841c1c006050b04012044455105e8101c10110640f0313000d100304001000c02622011507107075242070f09070009808100410b0300c0c07080c1d00c1c010203001c0450350801003640c01d039401c00c55050080005000014901ca0501415541c086a400780c1c909604407484c11690074120106526100705080013680043c6041c160341a24040d40aa0300b07059544045030340c1d00d01151141729148004030406400749100000038003e02c040043c8a59001026481d200180f80341e00300d030913103c0200001d880e5030040400405d508000c54000002e12401d00e078100002c089000040032004601c0000000500900040c0070a0f01030102c2c200855640382840e04000301007403000c01d049450505441d03801c140d14600000c0100440c0020849146040c2c18084002c500e64002441c0982041a55001140c8011a2f0003d0a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 109433767 1250 109432517 109432537
    0x1005071209080301320120030a030903170f040b060117090303150a0b0d0b040623010305010515030406091704030614011202090f0c0409090308090105010803090102030403111302 78
    0x164a0713504100304109840c1540780701000030000700224098003800180743c0c980249007402e20184040d0340545080040313694881c4d18090740070004034008025015880b600d90300c0d001c0e0f40c2d86028490701c40b1006d0040c0c0d2054070026000b140900c0024006800b204900341e201e40c044c5440140d440c0710b10202008840c040d0f64a007555040401044030354214800d01e4422160212091150b151900e00b020250740301e020700f1460b00a0300d0f420342c08000c1d100c6030000d1008085180526022031001c5180c000407508010f80e503800a4100000000c80e0714260001103891826410414515180c0d0b0b518040101115401252030b550001c0d80d100d450000d00000e800114000d820205541c0300030700098000c1c1c03205802ca030681c0481a00307440007503102c450540798051080141c007406500c44c4c8005601d1400346501c4035250a0821002104060b4030042c0c01d802007520100900c240d9032201c0c80f551700d82c003491a0050050b80b040c4000c00110303040c9034400c000c81601400e400f11100d50700050300140d80c041c0c5c1031a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 109435017 1250 109433767 109433783
    0x315080109110109060807080703140901020702040f051b09030a0b0f0a06080106150c020307032012010504030804081b060c190305061003020a030b0d050601030510090201021005071209 81
    0x59007803005800c040381c0c21080134039000d2601401c100c005084404098807004c03c0003200e400148149000c3e40c010030b01e10b0748014148600b440c0228801780070394071441c0c049003d00d0a12100d820304415038000d490003158017148074040e000c1f100c01202d06940102603172036814454420404d0200300307408800390190b03074480384500141c900400e4a00c10342c1c980d54007000050f031500c3c1041203401001d0507440c0c02700b181807810482061460002a2034a52907400180c004030700f103940b241c40064500d00100550000743c40440100e01c0c282d00d054200c0e0411103010707010411660000700001c00120040210703020b43c5050792602540c00600d503140003022501c01944850000b0241d000c040c0d02d0030050171004031450240140d1426202061900881404c0201415004104000910b0194112120180003e080c4118203166820402e03a030300303001c0c44203940c103002e00004080302c0055801095041d82c0c060700103124500540c05010000c05004240400b085084000c040b004a06030044079881c41c010541303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 109436267 1250 109435017 109435031
    0x1e03010303050c0d020d0c170c0706050318030405030606010e060f0705060414011a01051305120102070204110a050313080403060c02010912020a0b040809060403020a031b090e061603150801 83
    0x42c807841d04408800c81c00543d881041140846d0754442402185680d000309000b20100d543e000701d455501804202c44604c0c080c146000ca403803540038001e584106002e07000303040005800300c0706644a00c101d0003906c9d01a04080c0014101c2c0d40100040d2118207400b5240c9482c01403a20386002d4203401c00403085400d9003110b011b000900c60a60a000200700c822070003001070800c8000f01c0c0d2076485c1300e0710480c0c1c140180411455090030100c052200200b101a01e00c41f4140c8010b05038034000d51082074120320462030101c15403400d01c90301082c0e8014141c10784410f841c6807551010f0300d10b69410100c00f2540d80c001040003000050752801030341d00310708135a00041420040d0303291040f485014014140e04541c0b00390001c1c0c0100303281d801f8094020350001c011039603414403c0041345181c403450308080d410881a07100002000040303040d082c041000107441d20442525400c007c019107000c9144030310345030321100110700080a84c026100d01100503050000300e03402400c180b4038403203000f03621558569654000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 109437517 1250 109436267 109436287
    0x7050303150925020f1b0a090b010207093606050c03070c061805160e0105030a0c03061e05011401020c03030f031b04080727091101051e0301030305 65
    0x101105504000b212000d20501e44001c1064000000104101800b01c8102090210034024042a014030f500202600c2da601c807603030341540a10011140103070007988002d50000d1015400c3c0700d8072040843c141c1c05000c03440d14100c4400701815145c181207003c20350541034000710b50070032954241d201080e40790b9484085c0c0d00d41088401c80300001e10342d031031070714081040100407640b00c0100c0c00460b5000b14005002e03524540403560152a000d00184140700320103140f0382650f419640c4004850307a010900f040c980e203030414552a03441040d0300600c2d00440c641e091001600d290000c10100c00c1d00f10342112503030202c0d8109001d6450a0740508144030f0400600031031542d05000b00408010140e005614101300c4d405c5514072484010708400d881c000300c41f4811100301c080e40c11100107110100c1140c00698450031032007120703003030241c01281c01961502000401e44940c0200b0390400d401c002d01c02c00d005c0190005540c2c542c01780c24403290301d03d072900b141d0160038031000185020798043d0392915210b0032030032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 109438767 1250 109437517 109437541
    0x312010e07020124091814060f09150714090405010b04051005040b090904170a050306040e0604020307060e030a0206070b0702010c11070315090204020c21070b06150c0307050303 78
    0x1801c4005100768240e40134104c00c1c03002041100b2122000720000306036000d80d155100803401d0501c02881056000c105100025001410314000c0c0d1419072006c5080d20f60801d456600d9210180e9020206115800109a103010f01071005d100c48120380b005103000410f400080031a6400d030060104000c2c00700d410700140c1846100300c514103840e421f02520b401d0420b0a40241d900030008164420102140014100b0030a5890070640c020080d0a81d070f107c091110000e02182c0003290070070701591500207440c5c0c0700d0a00085030782c0903e0f00a0007401d65142800340c100e6a00401040c020703003500c10300d500400161580070003802a0341c001c140e60502c40c200b03110000d00f96281c03011410204888101803101c04038011a82b50100c3e6032040c611742c60503180422110142070b114101961003880403da9403040342d404602c0c02e096404000b42122403070100c403101903190081d0301003d06040104000101c0b94102070600c41d181c420068500741c02c0000d211812443d5900504084035160004000d11100d80211 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 109440017 1250 109438767 109438781
    0x4180b0106031a0603041214070804050f010504180509010e0706110111210601030b06030901020705070503010c090303030513060c05130510050d0c0e100c0308060402030f0106110312010e070201 85
    0x95607140400010307000031300c10340405800901aa40c10802d024500760044514088001907000c409884080f1400e041070150000d226503402a02c00c0900f141c0c2d25886038046905a410b600c10703003d042194249408000e0100510300e100350341d6100070055450f4000c00486e0000c048540d60780303200c11340305a1690300b036400000d65658004424005015203a1240d440202d90142c01d034010b10260b0b940000484c060440d00090903008030000050118002c410f4004001d4907010f903040b94141c0d40c1d500141400c80e000c0440290004189003000d2000030300c207030400350700074000700d902c1412400140c8515084a101108070301c045080029a6500287d980c0c4049008040444800c02c0e519140c0c80080c007184180b042d070450355035468022221803030041c3c0708202a0a40681208134000c104140a803410202180540c00b00380704400003030381440c190003100d21810700a01c000254dc0d280040c1510005a0340389040040c3c0801d104010b50040e030050094006c1c040c403e600041c43c200703454081d007101c0030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 109441267 1250 109440017 109440041
    0xe19020a0e07020c090a0609050112030305060d0305090f0307090e030310140d1e050114010807090209100f020f06091e01021206120106080105130201090806100308070204180b010603 80
    0x182034100a01c1d60f80114003021409415121002141c0c1e55001407001060181c00000050345014004070f481c0c040368036042a0203220b518104000c1d16030300d040000c4003c00c4400100003c004012050441c2405c00304004d030394002500725801d0070344407a504801d4419105049407150310100400c68070b60740e411140802480d030325540c011800303170440114a08187c0c1420203402d041400710b0f075054618146480c9800075030880020401040c065002040500c801c2c45420241d204007030021031402c60f1031080b1402c96000800c0c80c96922507001003070702c3d03844d0304200f2001036000fa0031400803101c2044c004a482403910b80b01818400e10000240c000f031035035040b07840c0802e07031040c0224954403006260680c1c102004640210b441d09429041742c1c00341070319420107a50ba50a0105100c004c0d075010074943c48043c401d8071034a6409d504d40c20f22999a90049070201b200c0c0c004100104042880e060007020340d20b00244c004204098899103021503c08000e00c1290f008240e680100040c42d0325220303104032812 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 109442517 1250 109441267 109441289
    0x2909010305030703051317100606090807050910170307020901060807020a061a03030d0516030b0109120305070b071205070f0c080c0703050105070503151c0809040e19020a 75
    0x104603241d10b0355a008200c4000e00b4403030001090b00340844910302140080500c201c800500f03030a00504143c40d680d070b03250090150743c1440c0300401d60501840c070711380641c0c2c0c030307540200007003890034041150b640c2c0054140c0243c0f0800c0e070004076220400c9041c2007640190075000f0b41c0e461130b0030302c1482080c1d44141e1008041103d8801230252255012686e202c15a402050104820700c1d4041c1d1400020040b111607039241c0300c00038580c80b0090458000034490452071048038540501b9202c182c0903a0100c454490018044140c280b240b410240300c9102c802c5d002c0d2074410b0409007950b072460302d13201c400d4400c4000b0030603010041e00c1250050040941c030107220704d420304500218910240c075205290100514141000c0341c180840300c400c0208000440d0010020322143c00c1242c0d0250046c3e00a4800452207a003a1110201c181003502400a0802c50955440806c00030754903240440d070004c404050380680c8130000042c3c2084108030302444009001360118001d0154410406030302101e07800055940703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 109443767 1250 109442517 109442519
    0x50102032110081e0f0a0b010e090118060203041e0203030405011224061e08180f0709021b0105010e0109050c1303080909071d010f0909290901 63
    0x1002a500d81298041d050038011282c84220380c5202e800e002e60054202d03445001d414002c0b0201c1d60b40514a4495070fa4152850109044e480c06d854180c6450054517180071000104514080c02c10a01e511400c44000001c0904001c203414502c03009051040c0c90790354002c000d120038030110329400300c0340b42c03040d01c0401c0004000f94046920780c05144601414008008001c01e1011080e801c070142c0344002c0d540140320880c4483d40207059441a000d8000050b462844612a6445100300e0300603028440e180e110081e038846001e52060040d40308841c0d400d006582c2c0004200204010171000707820026000760701c1e80980c50340b200c000100320030440956810a801000000c3c42a00400d0550303200c0d0001141681d84c08132501d2080c440d41131442034106884400000348803201d4058000382400315808491911440703000c43e000800d0251010300d045140b65100907a41c020744664098007801d0070001c9600d41c0c2c40c41920101e40c0e20a944242a8542c2030302c11141e05d410660464a03c0c204071488180e075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 109445017 1250 109443767 109443787
    0x20d030c260d06090b240913050a140f0a1107060c090501081308030a110c0604110f101d03120a020307060b060c0712060207080a020d08010e06030c060d0204090608030a020705010203 80
    0x806c4441292003511151040070f112800903608a5908000160921035100c00740c042d0f22004180444601c0f070041c0c036207190102e807420a8000e05016803022842d1000e16168880b10200610384002800e40c03081003080701d40005001d90041c4038080c070b12525a83c807118503050000d000301000a042c0300ca034150b41c4d1035031800150848256508a80c80103030004507035200c00c0e00c8804510515038516428810881000f00f045004141c260400c50244d4201c80c80804106c148041c5444038400c0c0f10105626040c0c0d000c22141c108141d00c0c1c1d00c400141102c0502041182074111a4020b081c01001030300000381003010711800c1c0c0149156284240c6480313180454a14540f030f16143c060044920038007506941c981803041940503922010b130803e49040d5904400d0402950360055102120007060410000140e48500504028840c1001130058580c2400c0107040108540c08113024620141c1d09000114552004d44a020080d01d2114011a41e49480c0a0003901e010103580c00703e411980100000d00b02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 109446267 1250 109445017 109445029
    0x2070309080f070e1009110d140408120a0b04020a02010c0e03030c0706050c01090c121406010308030c090103020409050c0319020f0405040903170a0b040c0c020d030c260d06090b 78
    0x221100b02504d202c084e141c01242122520203548111b2849041c20012145c8024840042049600b02c0900b08482d1000c241803070070742034003202c015020071818000c0d45095004810301d01e500c071f01c02140c009014401c80c03000504070703080b03e1503200050799103a081e01c82c3d20f5004005180d26040c00c6000310304280d204100155185828005d6004122021a81c80307014502500000390184d80a00500003058851412200301080364000362204401c05940c55050200407455505994001035118a582d941210f103103415400100e5160415608100c0001d030280d40d032103002c0c010100195199a01d0900340c0c1ca0000c11409002c06100c194030410000519880c10811641100c0050b500840c07041d1050405481c031601c3c1c081004041c41d000c80401040703400980c0440410b00046404001c5111a10001c41d00f01e201800000c0d0850a21201100464064205c0301c80c0d940c492401004105400100c0c40c2100f220340020a112460100b00c0341c5810090303001e03030005011020000c0211646907000144 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 109447517 1250 109446267 109446269
    0xc040f090209150607171c020903060103032609011a01080907061b05030307030606140c100207050f030a05070317162102041205060f01061e02100f02070309080f07 72
    0x98802c481e40030f03200540340d0005462000e40c0100d403507215500c4a900d044038907404040701a4034007806101c2c2100c0014103100b5960f84600180c0200010fa08655042c0c413a00c2066010303402600814201e11032007207500305118800e0f5209070001c20048151b482041903600e00650980c1403011250400c080c00c540003941c002240c0300c80ca0b2440000942003010501c0480400000d440d5000c0081044003042d0560000350031940144d460a0004c40c1c2c008807041b260103403050010940d000400003076454500e903009004540c0c001c100ba10340410050400516540c00389041c00302098000c04d402082c90b401c8071101728014145a48100d142c60708211102951502035154401d102141400c0e0400e020701c018200015070503e50110340e5192a038003400d000e5542d4820840b05d51041e81d00103108840200d503128121041500c84020303a810b0740c000d000e2114248a240f404501c1030682d10b1010440d14014444d041e1507010740140d9a0019041c02801106550407001555210383d841c5000c00c440094080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 109448767 1250 109447517 109447531
    0x705150a050112120e0a06080411121009080909041203060801050709050103150e011d150306130f0503040b0301170703200a03020a0803040f060e06090103180f050c040f090209 77
    0xc40c001d8079a080589214200c1d403501c03600006c1207100429800c0c1c110020320300550140400030300902c0d0602c20000d004044129052064000d880d84070314400c00c58104203190391195402d00c1c204000700b00800c1004030219030580341350110703941c0d2424590701889204003404800b00207000500c0e00c1e1602520803415480381c54101591461202812581002c40c030b8060034916400e08440d50350b030020351205e000a030b42c20349120300bd146d020400c04078070898000040b00300038002d00a25540c69017540e032446458001501d011200120900018070280300a2015102d168011a00c03541824080120050082083d500c50383c05060b0500119240009560600e134281c0c82d0610704e030686402080c080d100950009400072070b0600003050080c400f00c0540107942010080304c0605a0702c007411070303c01d141d031240c00340c100008001801c440d500c05d401c46100c5d02449032811000000d5550b401091241080056030b8540103500c54103000c4c81c180c041d166280ca901030081c000c2c49007640014031000d4001d4415 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 109450017 1250 109448767 109448783
    0x6050306040f0f0f0b03031801260a020406030b06090102061f0b040306020703020d1701030206450a0b03010509040f050a0305030103021008040b1603110705150a050112 74
    0xd503580e03a56044400c0720259000107025140c400300c0118007034101004442c401ca424004240820308001040e54030190b2515501d80803043d02c4070040d0b41c0680d04045210b00104244064100c88441e034442c40d01a80d95000c3c0140d0300d900d80b0a00038100c074180d0448501c80d00d02000301400303c1c4c0e400176415421403410008031170700400009451160f919187d0201e05090404039001040c408030341d003c3c0040901a401b510301926a101c0c1c2203454030b21002610f40d51141060050004d0f0800320041d10082183c4403070081d003120014200c0c4040600d201031100f000040003001c00046003060a8441c4895094400401c0039042400e5840f2901050085d540a80316941c006414060106280c044840d048000d40e445000c05060003000350b4824002030780915110f210140b0200d10a00341c1e688940c1d08110540b030592035000202c00040c005101c824201900c0d248010900b00c10348008003881c51255006181d600802503400120b030340f0042410580c1803a210040104045a0b40b4601c00d5507801000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 109451267 1250 109450017 109450021
    0x6020312060f03010c090302040b090108060f040816121404050a0618050a0f0305060c03040f06020304030207030b0109020c07080105061503070201022a0c030d1b03020c0303030a060e0a0603020a060503 88
    0x455003484800b81015411340c200652412002e4004030040c0030349001b42c80910891804005000801d0b80c284180314031a484140000e070300952501010340c004d4400e08030346242919035075800c60400703070001e0700341c60b10110031010040c455040080d5100582910340e000d400d00e40781c8030028060540311720504040c4100603010000d601d040710b8160000e000001c1500d0b0301a601c800e0900000e148600044625100380d2000c200c442500c1c4082e648200d0348010b000c546a100c5642d603001a400141c01241584502200030001400950790503001e004a104010303121781e20462103c0c5030901035440426140d03d480184200354403072510f00d216946502070b10981c1c0e034558420803030080c03098a128004a01442c0e40404001c020040d04121440120048484059903101010744469400341003001244c0800c4078410b5190040c410604c000d40a0b00541d01c0000c01100402d00319031040ba03002c55115139410003800a500d80c407641381d070041c09450081110600303541c08a411041c440c090708051000102c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 109452517 1250 109451267 109451269
    0x80f18030409020301080102091503010302031e01151724011208040b0403031214060f190b0705030d0c020703050d030b040207050f010911220e0109020303041508070503010602031206 80
    0x80710024444040210360b80d40e0b444e54114001e4000c020f484d8401c0d01c0e4001619034a502c100709403410b0340d8004001d00343c1074150046868514038450000b0b9042c0d5214090441210a100d900b04010400b0b11001c019802690300710b141025078802c0305402c1d0704182d48e00484200855482e081c19601d44131f49001c9045054104000701b405142e000300d41114001502204056000d1801c419040c0c1600c01803017142c08403100c8a146c0c071001c849840e002010302e442d00450345021503200c032385024040d01c2035102a4440108030342c0c0d544007070000e580caa800001c5450384055148614448a40c052006d00051400c5689154441d80c1002480c0b04044c3c494a0700c0040d83c0c1c4540c1101c13002644103080f5204585440c0c0d41c1d90107011015800d584100030a4006112801c1201600c410750076542031600c8203504003100540123007200c065140143d96a40700010058600b00000c0015040c55000c41c40c441c90742c12402800c880307000307020f941000802d0004001d06a000015104081650804034007145e403454 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 109453767 1250 109452517 109452523
    0x314070f060903020f071502060c16030309020111010207140d0311192114060103020a020703061808030c03010305070518180a0501020a0e0307051206040b040c08010609020405030c01080f18 83
    0x1000c940d446c052602d0020b00c8842d100c0d000c101c580210b400b61407150390340020300146e50240d01807600500074046c00c071000003442540481e00b03291050601e076020340c0550400e10f089801160b42203e844a40c81001c03000c5036410444800c001003203107024005001c1202c00f2500d54090740e811200c04180030300078051002c1c002c5101c115026601500c104500c503503103045001519004004890490304280441ea49512034001c482201f903039034000304489440c43e0307540d100400034042c51610540503642c1200008418000640c06103c0005520b912941142003283c10f01c40d03070340e00080c840c3d000d60f030850b0034803440d20008030b5210302d0380c0040010703100405076240e04000201d81c004140c0d501c005400b01e0096048408503200400a408a401542c1c581c0c050040c048280c50044015a1008002078002000700b019654081c1c800c02c03d100c00c144d9900140d500390b0361300b5000340d05c5164001c80c05000030f080402a0141c540004d280502450070040980040c004016091001d21034450a540c1a040d200b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 109455017 1250 109453767 109453783
    0xb040f0e0105010c240c03020a0f14030117030405060a030207120c0c0e07021e070603150b0d020a02190f06050f1003030509040207081201050a1a190909090501090314070f06090302 79
    0x1171041800300420640d4010000d60044001700e01040c0500c640c001d03618410150a04c1015005181514590030b00185101c181e11140c01d10342c440c03008000216590303d0340409002054050b840c09078503602c44c0d14010b80240c0072008600f04200030411603801080e486601e481c00c82c0c03055900c400c596200c07860704034108080c041ca000c04a00700d040c9126207244000880b8021101d103590204818120f0381e01c4101d030030400344508001c9141c181701d036007510803082d401080b025640e4011104a06240401c0b5044400100410b59800c0341c1d03038400e40180940c1c5d0192640c018006401c480040c03901040c80085445140809001c001000c110b01001d40c1b604d504407070400b81c0200503251030701003411901007011003d0203920b0080520701b00009141c0000b14582001c903640485050401e2114092514040001000001001012500014003440a200b004450340c094030000c1015800360802814400e505814092407810400440c00858407a26100c2c402542c4100c000c1402d213041d0030308034541504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 109456267 1250 109455017 109455083
    0x17060402060d180b060f0103090b0c03060f10030c0206010609150807020c0d1103070614030a0c05090a090203060a060207140103020d0605060a0c14010903080c03060a0801060b040f0e0105010c 84
    0x2d8200e03c014000589000e0784a160100e4021a00e1130490700110141c40c3d070841d0081041051801003001000d82c440070715848031020b0b008882d800308500c0003c5d0340e44540510b940101e0f5483c00950500c5a041c060180504004c4c10030a58252801a4041d400220041c130602009680004901701920900980501c16401001c1140c1c1c03000c9801e240b000320000046452191141010000700a4080c882e00b504035507440d442c40d07080d03948100c0b0300c001904400800d0304c00c02004208000c0c66a6580429070050000c503400142c41c2d203401d400307101100c04160410707000c0d5400b10034100045c0340300710070081d40050b0a2034050b80700c0a4520261002d86000d0b00415400340002c100c4035402076001d4201e1103024011b449c004d00a00800b01407908841003a200580050042030001307250100d0f8500079504400050209502d041c0d91b0340c001c034211f0b0340541046030721160028041080011101d0414040c141600440c0820f514141c0040c00b00802c00500400d041242c504401000310301c00d03a10501805 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 109457517 1250 109456267 109456301
    0x50301020c0c04150e01050603090f1204050906150417011503051c0503011404021813200418150e0a0c110d02120f0c01090804080717060402060d 64
    0x141c10001901c600396000c20354001c0d032070851504030580c062542d0008a64511181c007001c0c0c4d080109011456000800000807032103402a031548004040010180218009071010740f02c0e4203160801607842c8001c1d0880c0e204040e00010880c0c101611004c48040f0b40a07500303568400035803034071400d01411000440e044900e601c4680017040c0003000c9551803c031416501d2100c110742c4003c0055485000030f000301240d0300c00130f504018031414298000e200c0740884542c10803101c660304c0001040340350390440700001c0341e44074201a50841d070040d402e003980d06080503000781414180022100e440e41540c5140e501c440c3c681e559035a10500c2210484083c00941c1407050980c54011030701e03405400c1c0403510350001000d01300d10244030310b07010424026404241e8098000925130702c80c9001550841041c1c3d00750f442c0c0821a02e80f440c8006d10810200500c5140016202c0303207410000c42c2401110340c40404101d280e2000d42c841d400780403403880e60241e81120700e0b035207816214099100400d1a149a14a490 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 109458767 1250 109457517 109457527
    0x1803050f030301031101020703080403110f060c0d022a040504031403040c0e0709290d0905010603021005090a0b0d110a080402100203090f060d020705030a080a05090613021905030102 80
    0x8030110045050701d009007140c0c404a0060390049035a00301d648006400c101d0180005d0000034400d840c003400d02500100b4901400a0300c90000d100c1f40c2c04034022864a0b030040660101e0031b40c041c403011001499190410320401c2d9040c5120a0581c1d9030104140b04984e10700000c1c2c01c06002c1e9400c50408011041455202d203060300d41050b0302c0e5420300881c140744000400241219108091041c180d41c00109001045101981480c00c1c1c4184000d0401c3d190302c0501401c0e1a5905920855401c14021000030030030510314010f01218141008500b010402c040002d1007040e104c0b40e07c3c010880b52094060303030390745c00f00ba002080100898810060405800503000c00040e92000c1124000c600803594083d285c5248002131fa501c0c894081c5081e00040102c019814501d4034002404000d142c250b005481d1030610365546041d40c2c07103004103c021903c3c0400380820441329204440d4800341c24002408503040c07070520075030501d0340c00800034401c2c48044031010013122805203950007088003500a545031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 109460017 1250 109458767 109458793
    0x140105060a230c160611193909050105180601050d02120103031e08040b01051201090204020307020a03120b0603060402031801050106050406021212180a081201030b011d0601180305 79
    0x644c40d9202d81400200e001d0090350808034046000b900078407001110400107041540c4000c081f605629240b221f901007643c11004006800031002e0180060078654090107091680080488006800850040000281514105041c0c0c400c3c10341005003400d22640360205ca01000002c0d2003035640c603016a03c0500c000104060b00051102400500640c0c40c01c00208103800445203620304580180c2902e2504004000c141411400c40d100000d44000110300f890032a0042000e07640191090b80040e0b104c410013609140e44286c0d42c900f0300c00603040901080c40c001c000981d1600002d00b0451180764008007013468100040341219000d041040248400c0d030756200050302a801c28412840540140020301090704400c40458403218441c0136600030340e0b2a103143c500070740c060300040308100384104c91561010a900201500310401040c510000c258190b141c00d9803850b1042e03210700300d520380c0054541040840281300d950b010b0800c0c81c11a024405441c101c10842645510262090040310700c101c41e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 109461267 1250 109460017 109460053
    0x9151d371b06080105010c02030c10091a030a06080304060c06020a0309060c08060405060402040f0b0702030f0312091507080f150d0602090910050a030f11060d140105060a230c 77
    0x112a181d0703ca4502036a80d0343c005440c94090b00c00000e5164001310302c030000e2454401041c00c00d081c040c2c0303000070301c1c26103910030300a02c10042c28454040650101c204101e050081c05400080c0120002850925140c0440581420311904005203200d8001c04c030000001d210394810b0100d960802d030180000b901d110304c050080c10056409900032401d080000d0710300d052600890b02110414a0000992031501c007106900c0c0d00100c40c2203900d800b900314101000f180c100041c0a502d031400129118074185005020f1500f810b50108400100444d41040109034106e109540d1118074607908484030b944202108180284640d100c035403004c0c00b401d40805224990307002d0410944203460403a516160078000a0328900c852040540c003069951341030002039244560080110b10414100d92800000f0002403107d80000400d80200d560710f429005010071044070740c070300510b0180c8410380307800c00d5040010400c0050140d0b0300c0154030744841407402c54141c0800c03160701340d200d030042e600c10001c540c842c2d0700 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 109462517 1250 109461267 109461269
    0xf050a0503100c020a2406050406080a020105030c1303120905010c0b130501141905060301090c06110f1b0108100503030a03110702060d0e061e04030309050109151d371b 74
    0x81461f141c1000070803507041c144102001e49400e1b00040000441d02e900441b019480100301c000d01d0302c1d0a00c642d4a0384041d0030400c4010398810078000c0c0e0088560030009141104503400103040104011a0401280e108030704a604040d859a1104511510307017003c60262040001c0485d00c05010030030040d03604041496085810300d041c00600690316158101402c0e91010b0401a207540c2c440c0c0d1003004624041d44030302041070120025507400700c841900da1401d04440d01c501c1400c1e0b41c038800f105425503a000110541c02554074103100721850410020950300e016600c082024150748070407038500f400c0d029040d683e03000d40c010306080e6a0100007081001910110030460114482c503008030f500b45820483d404c40e417107000c200c002115500c94508802512417080b080d07c007035590b60107080100c1e8800303d0f02102c010f00710002180c1c001000c0c0d04240c6080c0011180c00703654200d088600d1a02c101150101c1950f0302d804c140240050350003541c0000d000e00d00e50001c082006110120200041070100b40c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 109463767 1250 109462517 109462583
    0x40f0f11040b0117060108060a081506010e010305130210030e03030a150f08030703030911030d0e030706090501020a0b0a1e240302180703061502010203010f050a0503100c020a 77
    0x48142c2161400550340e180406055031041e03040c03180010615481414030f01d521620091082da60300c0d644040d441d080c002080d8107100070018002c108200c80d40c0022a2103c400710030b10382042180382900040e103a0360380106d0024440c8070382c03902100d044c030700c2a082207400c043c2200030740b40c4d02e0802d84045001800000c0541c0075403104180b000510000742a61841141c040c0b0010b10310f0150b160fa0308800400c90f603030342190410380403090a00c41da201044451044d902c80d0b283c5d03042c2c0300143d204151400c03200794854010045051020300640c0d03800700d44045500c2e0700400094150320b0760b12a16003e0000c107481d421114030f1807040520352a2481c0c05c00034521110070020140402500700c640c1250100d40000303034005001c400302008900d0081420355204142d860006285910342d000398403ca00c0003044040141e4000c4018440a1150424000101000c5400712861440c0401003612015000000c2c0d100360b60702c04402c15800c0c0203201c205110362340300307100c03500c1807042d40c40165038920303020080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 109465017 1250 109463767 109463771
    0x3180608100803030915070210021809160c03050d270b0106052701020c10090e0901020301030b0402130b0303161e08090402090d230d05030402010c020108040f0f1104 73
    0x941c0304000c0103e034000c1917100040c1c45105040d00121801038000f40c4150110b1048007403000d040380c000d20107041070781e2249810303083d02f02c084401c000300200060304100101201d141040340b1150000002420664035041ca192107010042a800003400201c101c00980d01e1060000ca41549171400b500350820f21841c0c20280c0c0380d885100c00c640d1801420509505102450b201e0803a04607070303015508a00c01c052048854158898010030700c4520030f10041008904149401d10800c170420006c298024001c00c000c500f150f01d5515104800c1001034800f03800345260f40d46a07805c80c034454100300240440034044a9440c55908402d01c50111000410b5480460002440d003071070b141c40c903507655401c0c0c00400d020304104091007080000d6121500c816070000500b84403900007114044140480c04040741c2840001f14000903450601c510041000c080100400030000184e82082d0000402602807030200c401e607484c1c1c030b091911412910f030050601c00880401d82c1c10002015850401d040e415101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 109466267 1250 109465017 109465019
    0x180c19050c0601061209050d0908010b06190e0604090911040506010c020a06261806010608070c0f0609020303030910060602030408070b09040603150e010b0901050d06090318060810 79
    0xc44190007030680449081c1c001000420504d44198000e400720803c8040c001501d25199844030314107100d4881a0000c82c0300014200100c1100f0300c0b406000717107010f590462502e407461180000603900518068107219942020030710310b40300c0070180c40c05040700f13110030000d0074424100b0750b1801c505548038900c900e0502c40010701d039501c11140803011583c0a01810002401c040d4241c81c14076518400b600c0840b82c10011000c80c640c1c600025001342440a00d2450700c0500c11405070500f10160401001d1011600c28030585680c810b1a00c144642c00024007a803006251a0001c00b8243c41c0700041d44c035100c08401d10645440100d042c4000c00c103052001c000c4e840d51600c050361a4000c0d8031443c0b0450300720080410000d450389005144421004000003034058680e60380000c9001642010240ba9984800382050754900b44a0400003900407500f103500c1d07614080000e900d0100c0c080c2d005251540f110710502c1010701540d030003100b25a404411004064940794001c00101c1d080b150b100c0c151100c008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 109467517 1250 109466267 109466317
    0x1a030a081e0f0d05041104061e21060f0204090c0e0f031c0309050a0209010f0e071d060c0115080c01080a0b2d1806090601020129180c 59
    0x82110120030300b4850003801c100d0300d140c008004100041050390b0740c00740381c039840c00b40e5aa184550000b401452072105001005956515070582c0203400c030108181c13062115003001c1684021361410203070301c4180071680c9101e442500c3e0290050b6800603615a013007a0524000390340110f40b100309104140c913406121300081c0b003059940d410390100301818010741d4000f4204644a07420240d10726004100300c2c0c550442c0f03503000c02c111345002d030300941c42c409100c070060120f40b00c0d003540c0b42c1e0802c0d5030b85012a1160504c4000c4100c00481207001c0e88135090024841c00c01080c20342005540c0f00002d8906900aa40c408c01e107500c8021040b0454002040140060303500125403040b400400000b078000d0341102c5c0392540d0308805407540c194440c0003d50030050f41c00c0c55641e6045c0c1e140035011100d03507603945c0d05144090011012019040703074150790501c2074681c60142c1c1e500c0e541c0d150500410480065040340b00c0401e02500c4c11848603298001103404101c44813042d01c0003003192440300b01c060703240305004034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 109468767 1250 109467517 109467577
    0x10e010810210f0f050d02010b0a0905250320030112110310050903070209130b0408180312070203061e0402010e011101090b0613140a1a030a08 63
    0x312000012a803995060082c00c00750000520240c40e8403000c1d885100241c0c5607941c48403c480d03021641030304100703c0d210402805001034002068140000d100c1c1303215500025141301c0560203000a0150b48070000b81c04288000c040c45085030070b08003a030310013a611040040203081074403a000c0c0d0040d80c480e0704000112240301164101c8490302910b141c0c81c80c05540d106017850a82c0d4040f5810300c034403c107100f40c210403445140d0041101740015541c1e203a052050140f04c0c0001484646603526420b0b9840110300508074066016501042480e500c680491107008440c244d56032040d01031040c80000c207811844032009142c80c0b4001c90465503240c2d60300c0524802d039070400201030462007c1c00d01140042d4090406403801c184141000c00080c3d480e0781c4102d0845920b5002514a81c10a405100082c00c010f5075400b4204488403041c0000b21480164100e031500281c6550400380e40c800c03031180c2ca01d003c2c4082d2070b0301040040a031780d0a4455800c24410769005030101d050950600a07404600407958 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 109470017 1250 109468767 109468771
    0x9060106050f1e07081305030d0302030405031b01110a12060503030406020d030c050d02180a14010903020f0f120d030b010e130b010c0605180c0301020403050a0f0303020708040b09010e0108 83
    0x140815030f00e80007a941140d030800f0807400f105030b601d480910000000a100c580034110140502c2103007494607203030030105440d16802c000000203141c410001c0c400815000f00440700c41200c80380d8040c030b030084030749405401003c0c1c00801c0c8420340400f00701c00356420780c07001a05514940c0300b60b00f444450340303c004164030ba100d00e02c1218003690007400c5810313885019402c03040c40644075088c1142801c80d4140154240d0307000005c0001401404110040f040ca8049031004c0a0b2000c5125451081c6402c00040c0030031120340030182c40340500c03c15407566992140c09429004001421400c0320050300701005030354401c1005008003080c18005004005e503c2800c0e41c01c03010300028280401d0410070082280140504034010303040100a02d82d060204105000b064080e040c4240442c480400000d11182400d10460600d4440c0e401003200308042180001c0109a00b40c011100071104219850203400a104800300101a01408240000c00c3c101050142c65070490a0300c400540304025001100d0381082 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 109471267 1250 109470017 109470037
    0x31e1e060c0a0c14061e0f240301020f22080307020603010314030c070f050118030b06010503060310050a0501031101030c1205090109170417070e0601050a090512060906010605 77
    0x6000b4400b150344110070710342c40b660082640c8911120031341022401c0180031a070003e00c0c40745040c0d03218102c0e40c00103145a40b0447c1d401c0200d695040c1101c031450304605082c100d0000108031020b80109a40030760440d400c1c02c1c281400a50f4030300441441c4203e1001408803c0c0440e100c2180c0000c03905030200c115020f05500901070351450382944d640e0a0f8812034829000300030b1006011100980008204c26005042848008031031540303002d00040c1038983c180c17400050894031540800c0010480b850302900003c0900b802d82c2c5940d22240801e01e4051156000400b0350700381824812800d58076030181c0d051b240a00c000001c442e9100e8010750540c0d00c00c0d40b0300400503030340c2540b07030303448041030790001c1e400200d11000800c0c040510345807840c24a07641c0c8002c040d00c10001508000310100c1d40300100c8a000e03404064503000c0d28084454501d04401415181804000949000020311525000001e8080100800c1220305640700311556104102d804a1051085100114520780610300341c0f000040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 109472517 1250 109471267 109471291
    0xc0f05010c08070f1e0c030b15013204030614060103110a0e01140a0513080a260d0908180a081b0607141006050a05060414031e1e06 58
    0x24680d03a0b14440d40481c00010317102e14048081c1040c0008110b10044050340c01840580b001e80d0650901302d03c459400f51180204952103540d5003060b03604604088800154a80e0040c01c05039202005051580000c82c800e044590003c0c01004001c11030b481056800d0521000d5003042d62050015030803141e65805800b0341002c14001010405c0c800c801c803420703402c0180343c810b4405035120b03050441c1d5002002c41101088006c50021042d070605102c21b4014402c0500030000c0c40240e0b292103a5840f9800c68500d17040c040003400710440880c2a0442d101141300120411502c0d00c1410862503a40085d6821560f040c050b111348a89480c0c0800345409a5940714090482440122210708059140c80d01e0580c000303000f40010303c0032902d041110481c00c101e66015140001d10415010100d84240c0c00a85c814401d10105100a80340d01d42545c0070380c0c0c4681c095814280040001a25081c1454642c4903105804580b41e000c0c143c002c03801981030480310b050548032404550300d180d1182d40c00c0b40d0600b0a00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 109473767 1250 109472517 109472527
    0x4060c02060a0e03060c12090a2604030218040515010806011203030f0507021c03060e0c0a17040c060e04020f090d0c09060b19020f061807050d0c0f05010c08 69
    0x1c60038000a026000c1c0905201e1004502e49001c28200401200d1041c69100f010034003810030740c02d1041c20345c0d2046148020700714041c1c2641e142d0300d031098000914141105000c200f20459500213040f10065a001859200d5018026901d14005501120100c13003600a20005403000c8000f8458903045e110028050840c5a0030000501100034481e2003d074100364070742a0184111f0510300c0fa0600510555001e03240510301071340400d8000d14441840002c00d480d0800400c4141942022140c04c102c0580b0380d80e0391440c01400840d405010103010a00c000c401c202400100195020361008851191f2112480441c1050812089000d98452405040003c001140492800c03030107034414240f00d148400390300c0d03072205182001c58002d60090705c01260001116010107c07003499808104442d4401452605c501141c42c2ea201c910140c400400311142550b0542c0c0b4420600001001d440080d114809030490703030a01180d40e04403441017103030714411808041415441100d035501c92039000b400c100d14003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 109475017 1250 109473767 109473769
    0x40213061202090a030b0601030c0c050309090408040e0702060702010e0304030c0308030a1e050402040513212001051503070b1b0c060301080c130c020a080f09040204062304060c02 79
    0x140001d800d10060899003000240c071a0f0360780759114400b40d030162007022400d1900400141c1200e41c022001030500c070103d1100c40001d5000422540c01d900142d0703224002d03403901d182c414581d000e16042408801c41c5081040b405c150300088641c0f00384002da00901c00c034445d48041d03a44a2195002c0941314070719568082c40410b815000035500180100c5000035008428116052210310042a072840c890700c80d03040c40b042d03103014060381e500960224170140100e41c0650740d81a400d4454010020200a500c080c0922103004600b40645008444954183c510092203004d0090104451502c204607075180c1ca5101c9c1c3c240000c3d9074043da54104181c909d007800001d0a403040c06001c1120b55824801d40410840c15141e401c0a58020400900117180d551401e000f0450070041d010a44a180e070301c0c003009480704650010b0448200c5401ca50303640d0750743c500352004115510a0400701504280000b80008038158001c1c0c0e000c0d03070034400700307071194815039040048951441103100344000101442c03050805 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 109476267 1250 109475017 109475027
    0x31502121609140a170303090d050313030806010c0b0711070b0a0f0c05030906130e1302030304061b0f0f0507090b0a06030e0c04090c05030c091308090d15150504021306 74
    0x81000082400310819600d01301c092002c101c17000d004078190400b0003407001c5034204200d0f2552200140c2466400e62810503000c5081c0c120176600601004030203000308800341d0042ca05c03d1030054201002c04c09500d0200005050503c11098018103403081640004440c49070100f60744041ea841d40d585001600001000c41d5480b062450544441c00104a00c103e140c1d0385030002d201103080e014107000110318001c1070282004004044603017142c40396119500607507000c4122010740e0114203111000c69901d4003c0d01342c590103010020082d10340c2c44483c0c0b007400036804640b020a4422030443d8203e549030795115040e50404554207030450249401448014065048221060307400780480304000200380004040e0b916207181910305a2200700288464181800040e800400c1607940710110304101049055400d00c0010181180c02c020640580070f0b501c3d0a55045082e03003000e491182038003000466002060011000030040d044084005041d061a00940f1130916890000da006903162a4090390 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 109477517 1250 109476267 109476299
    0xf0c120d0f0909050403022a0102250308071110051204150207050105100501020d050a080c070804030f0b06030105070f02102403060b0f0102010b09011a04031502121609 74
    0x705000c400344011491001e10312481e40700318042d60081c40c11300c8008211441d400f17085440206085030072450740309140d0700021544880e40e062102043d601c0d440c04000740380e021950300b000740944ca000a4035018001d070101341030740c8680c0407105400d02c62032014040d035040c801c500e074030319440811000007400b0510981e5285540c00c0f05550140c90a625540d50350308488084804620341c2c1c407070640900c4296070420504c0c0c101c5405090551400e007040b40090582400140030400074180090744804020840083d14002d40d401401c1c001e40e0301082c0f4202c100c1503011200d0702d01071743c6000c0c006400b0070b102c2c0c0a07819128071550058250265405032040240c8203020600d1213084070035000d80c03820201107012500440c0036040010700c180304902041207941e40e01034080d04680c140540c2841c00c0d075071580c001c3d044551b10300840c1c400070f134040a4003109000d25030000e4900804103581c40800d83ea00c0c1c0051a500203411030140507a5a4443c0d14018500744101e11030000c0c44844060050042c4c0403480c00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 109478767 1250 109477517 109477547
    0x3090a120f0b07020c13230c04052e050403030314010303050d020702010c12020a0203010e16051c0b040b04060b030a3c140d140a0305040204090c03050f0c120d 70
    0xd21116019000710318100c1e00040002405547d0700e002161100d1507201142c5048000300310540035080554104a00340501e0240600c129000c0b007500504010201d04111000c042000e42e0003140c00004d80070f0450b801512003600482d082c4080450500c4400205078181d036810b07203030740c0d00f00056509034a0003034001240032030501100e0300c95007000c1841040a6580c400301c5500a00100c01644107250130f480d0103441d400c0c4140d10240031082c203c040c2a040e802680d41c2a1400741c00c51403030302c801031044e50310050080c240c00c04072000e0106000034081c10900c0741c0d00984040c8580f826813400e05039180c44615000d4920040611040c41c109815901071540c00c00354401c000d250203c1940c407229400c24014212070612005c142d1440e114414482e07032002070860b0405407130031000b40071100014442e206100017003580d42c2000900710358aa9121011703043d004040c1c19899900c2c2c1c5000c030303681e009070710340ca80080c4a2288060000c1c9030048000b0886600070300075040e02d58540344155140070500c0e083c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 109480017 1250 109478767 109478773
    0xc03030902130c0f0201060806070f020a06110a0306080307020906040209030309041107060e12040b07170703110705100e090606121006031506170a02090a0803090a120f0b0702 77
    0x205001d40d40d41034410b4a00c1030219400583c4075026400900880005007a120943e4103100c0100310030240402c1d26640050790b1300f440b909000c2e8400301203041881140005201c289170061503900b903039801d07000c1e016151064034208045070f203c0645c3c0c0ea0300c0c020400000d40c460f1850b03000504c0c41c106900a8407170b50b50080e0841e070400c0240c00c00101500c400c440e5031011200040365840902100d8000e15980d4072035500079200810007503882e180148114091410380480c00100801080031408400130991200210143c07a20b540c0c2c81d009000307401c02e200450f01ea03c1595030104072403a114010400606043d119100303411408814060a4107008240640c0140148079241c4195094103025100d5480821511a01418040c0180880e203c109401901d0885204144801c80d00f00103455000d2030f0035070184400d984c80c81c2c02003001e48510030304141c2112040000188070100000138041d81c40040711103183c51503d0345540517010000406c05004120151901004610f030852842e802013024415 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 109481267 1250 109480017 109480031
    0x908100b0a08030a0c02040b180c0306030a06090b070201050109180f14032a010603020114030a090210090810090203030a0c050a170405041a100f02070503070e010608090d0503070c0303 81
    0x90b0303030458001003000e5021810684038403045203403d1080580b400d1046842c5503140c078201d00b4031800c050b070052005d03050910000c01b0400315a410800c10381805e50001080c4603914140ca030030b4444960980d00c2101540c05d101c0080307003828442c01611151850460160042c40c9203440e288030010074140c069401c002000c284003650308091000708100c250360030308203058036040c000504400390b45240080709a45001c01c00d20040c7e030b200b040042078040d140503298880e02e50740ca04070b008108001000b54002070f1031008614580c2c1160320300d42103c9841d0141c80c0d240341103204002c2a11107805000354140c0040002402141c00342d220780041c240550201c50380380c46195910086450b04669488404101007400c0000c2d240500410100c0001c40340680c60b444201c40201d41890048210385084c420000c5012040610800c42c1000600d8002d0445400c1561102024030215003809140c002600381000a03e44010000c4c05e000414001d90b01c251840c3d0303030a90202c030b0745a003050b012400c050f12030070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 109482517 1250 109481267 109481279
    0x2040e010e030301030309080f0604110f09010e0915010b0301060503070210060605070605010501031806020f09180405011107031d0f10170105120c0f060c060112120908100b0a 77
    0x45500d0011080c54000c41c3e40b5415810090604c6004c1ea01002c80e40d0b01c8408040400c01d4040b42440d001a13110000c0b103501024440020660309200f280036800510703607000003d40723190600905014111800503074901c072140004104241c0c009008480e4000020001000b10901ca080110b6000e85a0301c103444604407d1148a02500c169501c20700005a000c190340f0107000c0d0a120711801441c090904014110040092007040c054099000d000c00764042610156407008008440e0303041c00081024642492140c94a013038240256020366640d860841000c4407241c0c1d1000300d810264250f200c061035449200c11f9000000d042d0001550840c07202c401800044d2124010b845a800c6139031509100301e120101b04680000050340210f2140c40c05003c1c80d01c0d5020b0204880380d51400603101d0b00840320980012030030701e01ca20011fa00c118401c0720f00000700902c00c0450b000032503110361400364200000e6881103c901c0041c6c000e1031090303003004007900000d0707045501040b6440c138080c1c4419907a542c0c40c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 109483767 1250 109482517 109482521
    0x30c0306010806040c14031e0f19060c0e01050d0c020a020607030804030f02030f09010804020406120c1503020909160c020306010f06080108030a02030405010f09080703080904050901050105030c0d02040e01 90
    0xc0d000020b1a409041804104921512040090441c2c0fa240036040c0000340002581c443c845201111800780310072503102511001e11150900680500445001901d00741e00020750440400c0f05403022071801d880c4140c600e10907004125002c0317050759680d0070840d00c0c401c0303840100740400c00352040d4840c825044006850302c4010345005802621181494541030401424507030340750310340d503003150410404488214107020603030b0006402864481d80d00d0b500c40c4082402812680c22440e208030807208400d0400c80c40b5411101a60314107402900d00400b5000c094003640140d000041e4031842200000304081c41c500c093750308101d910304c1c10300581c1c009900480d0410744c2c02e0b044214007600380b00703060082e00d4011191038018000c450045141400b6103c000317440380585d0040e00d041152031a50356a801b8883d99941c4041c00900b400d940d420f6030342e46007640b100d07400504c041d03008a0408002403640071040c42014102d9a001e009842160401d41c10062600d810410032030388507580d02480d480f20b140c24 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 109485017 1250 109483767 109483769
    0x521040b150103060302011e2304050a060302040e0c07020420130608010b1812010f0203040201090e100b0a201b121002030a020c0312010303140903060f06030c030601 73
    0x81442031400c1c2000340000c01100700ea400d003281450304041c81000141da100a28041c5400070522840d601090b41d6401c550f400280c000401c02030740d410001e00c1d1408030a400900032241c0032a00300c0f8045030b40700b000f9005e0b03008174411840014181400142c581c50a18010260b091004000082010382042030240040c0e00b115403000c007070004612407505000301a002000b0b0030841c00c0141c895032420301aa201882401112425040d1140b07080105c0d8603840361406403841032400034010301864180e114001d400807101230740010008180014242404901c11b80240c0c401c0c4401c0104505140102401d913102134080c40c1088041c14644019030340b070f540500180800381000d083d4603040c4401130b00c0307400345014145100d0ba03030714103904091440010300400c0c1c13040d50710307070168032a0f40e072a2115000303026401c9025054040010210602c4841c4420903061328807a899000c600203e510b0448480d0140f040041d405034003031800f244c041503030155072030742c0500c00134221103111403898007080c100b2000f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 109486267 1250 109485017 109485023
    0x40620070b041e08070809120d02011b0905010c12022406040b030d080718030204090b0702070f290c07030f030e10090303180306020318011d030703052104 68
    0x20300041007030040c01c243c0503040c00510301c007141450382c450010500c02c180c001000340c0c00c0003070760b00502e0f110b0500c403105c02051311003559007184000b10064081e040608100c0c400b1600300100d80d1a00b402020800282c03601a9181038406041c2d594405400201840f5003040d486014090100403050600c10715a01c1d1018003401414140a010310096070740114041e80300350450104150044d030b1204503180e0001c01460071a0b40810000ca20302d000301d1503600040d4010303041c03050801c1840040e500d0075004601c981d00f19036a00d503644040c2c00c00c440d001d00803200080361031002959844085160603007224049000d00d86402a02c031605440d0581543c4120b88a500740702c0800d003856041024250305160544104011842c0c61100406818180c0401400c0c04070541c00c405240389071038004009913902c06000c55a0b41002270091030300044001526109600f000780781c07007280f050910440c5001400c03000035418946255010f4500b0380009200700300d0360005503204070107030100c004100e0040340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 109487517 1250 109486267 109486283
    0x605150909090705060f03070507020405101d0403050301090f0209030d0216060318060e030909040c050f0102010e03040905090307050d0c020103060806061806030304170705240304062007 82
    0x504000780801414001d040080036004a07004025948480d41114010400c0c02169a903a940340070307056415000700c081c0a900a8a400100019000c40c03840d0102034802e101000300044104030140c04041710116801800107800f44010040404180c0101d03400300702c1c030000941880f40c884042481c2002280441380141c0c03040c00c1c4411070b1000c94452101900940c9010310070a0065003044083d031506030030040509646103962500e00c0c10500a65078100300090881c070701c40c10a410b1601d0001224000e9501c00c811800d01a81035600511440203054051006507040c80c1ca41012074008141c01880c0102d640020002c0d4000110140b2080000c0d50711501c510a004090740001021a40c854025640ca6800801031151583e00d000096503d4038604070302d20382d680d55000100e4114001c60740041ca16207142022002c84070004508202540d43c10b441c0000d164094282e00d402c00303542100c1e60700340d880041020901040380c1d41c000c6a00050102084a8600c0035524407206540c4041000c0d074000d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 109488767 1250 109487517 109487527
    0xc0c130c0306050303130b0d09061b0f021615020f031225020619060513020309010e0d08010623040801050610030614040513080c0a0312060b030c0a03060515 69
    0x181c01d80301e0316025010a50080d82428144008440030202034000d01107a10004240b03035980902c9504601c0707046a010074280540c0070090001c001040c411481c81010803180c100c41d403081d51000480301035100c1007000d02c80100f85800d015803a0003115804901c00c501401000b50307480d48c802c100401c0c0c082c03c0514401060b24004518014070341503480c2580c034040414204804156001032130940100c003c200b00b01140071040f24100080c0060b50144e0b40083c1d480ea0800c14258003940a94464940940280549401c04082503224402c0d40d88000c0421a0b00303005000207442401500e4600292800f1204060502c00c5080304582181d803144403941e460382c0030825941080307410000241007900b014000355043c210b80840f281c8101411074000d0b80d0b00c0000541c0078055200d10b640d0340d034204091507030b0341031402c000689440307507a40c040d804102e00f1806031503c03884922444c4c1c225442c10a220b800d41d11194500f55455000d003800200f010307124400820540c3c1c1e04d10381d2814121122003895503a03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 109490017 1250 109488767 109488791
    0x307080a060b0f180102010b03102c0307080f121006020d090303080703020705030f0c01020403020a08070609060c0201030b120708070f0e0a02090102030c0a08091c0201020c04020c0c13 81
    0x9229207400070051a101801800480f500102c152401d03030203a008012002581c84004030f00500b415804940c0c0f6101d0440650303040e807030991000800030f040503d00e1b42c2c15000c1003140c00403401500e643c0324056004102c0640411582c81c0a083c01440380f11900d8a81404044414041041600c82054202e91604104007582d0104105040c40d44e47e41091480e661139a24060300c8403030010040400d00d80c0026041f0108541442180d520200c5072070380c55100e01001a0490003504180003c03800780080c202c02041036100003c0032130880c0d81c80e03907419007a10300b40301003110300f44070300c01049050640303950300e5500d6595040e02d100c00301c40521005000c001c2c545140740d071400c0380d15404542c1031200900b041c8a140316840031260310903520440941c0d9010620b004034514864280d60b00750714001c0004446c1000320a0000b8a000c5800300ca400440c00020300340b22103800c00340f000c000d000d82c0c0503d1041c0400d080c103402500040403030605032003020490a0100b001103590b4441d0808a5590360032450032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 109491267 1250 109490017 109490021
    0x12041a0c04170a02131802090103140c12030a0e0607050307120e010c0f0f1b060305070201200a030b1f0c050d21020c0102040f03030e01030609051012050703080307080a 74
    0x98810450043c00b150002d500814a0800305403c2e85c040c00342c03202c03075200f90a400c0441140410354091f121800359a900c5c28240107600ca110344500c0140254500c180d4140740822900500d070306404065481d0164010041c0c4400302440b84003030f040042031044102080090020b071a0440c003502a0742d50b68928008000c00191543d045641445020103041000c9a1200c0031400699844003003a2082201803c3c5240400d101031503400040d03c800c840455413647c036401c00d9015101c0364000788100d007030801d04420b06003514402c6111200091001c0082c0d203209410964800001410f1000966018000e9180307103840b440420780842c08401c80942003010401042c4001050740c0f400c80c0c140d0341000c3d4428054400180e52110154000c20210b9111400794101d4005001040444400940d28600a007030320142202850101e450120001111606400341c54440c10b00009150301c035508007074110b0110310320400705035114070610001000045040740158001c0050b61100d2180340b0b0b01ea031032401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 109492517 1250 109491267 109491299
    0x160207051e01020c061e0715060305070602060604020f09060d060b030106030c080a0902010503060112020d050103031101140f010b13030507030c080f0d1d03010e0a080309010609050c12041a0c04 85
    0x20041000300310352032500d5020041400c440c0c20650020756142003030f05007020825011032441c040c8503c9c04800004000d0b00140c944101c800580940382d481c0d5403c1c0800c4120f010328000d240440000300038410591410320000d040e255042c03000001c80c00d1700c5100034621900248c000701c2c0482c2e5a2a025410785d42c101080729400aa00031040c40030000a074002409400041c5c01c0300d0500005103042c17181443d00c3c1d019114101c00c119410800c5682d2402d0040000402d035160000c154a0042da080e00220350088562259642914260590f4a01000d26074182e10441c40406020003900c40800000e0081c042000214010702149940e6801c12024500b8420071075a405c07196400700c080d0001a60b00010540ca40009610f20185000045030201e030151103c42120040c0b4060044070b84200440300004c0c50244515000070090b00740c0700c5001c0d508032101940c0160034004140480d00701d0400c030704007041e4064840c185009603041e03400c28050340c260081e00c1911a8200102d824080711943e0788180e4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 109493767 1250 109492517 109492519
    0x30f07050303040e060d0b07031a030c030607142101060905100c0605040204111c0501050a0503071517100810020702011e0201061206050f01080601030506160207051e01020c 76
    0x448500c0c60080001d949209500c11012080d61900000b1816522440030b944c510340c20148208242c94100001001000c10700410240c81d040c03032004150304d04001464402c2190080c004100d030f611101400d94130307000f80c50702a10401b4020041c1c03044101a03090004003901002051080c0741d410104064000802c5400c01d600442d00e00b001185c03e154410080409143c001100240c03030349483c004580a007154400b03802d04402c0014411140510321003c621140c240c00104003d40c2c0d880700700708a5001e005120f07083c0c0c5a48840c505101401e1030400031000840d50341071183d40500b469102200c000c0c0122400025002610810040b13580d083c03154400a100c2035008520740451903001030601045103808031803d80e0703242081035005000b540440090302040403948400401c61610301c01a10003143c03041d80140a12000040340080011894140c030352000142c50180d45042284922003d4134401204510418a001803141c03680f82d01240e80f41c2c0c040d24010b0150f541039001a2400300380c10841 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 109495017 1250 109493767 109493773
    0x1e060405030301090903051611010e030607050405132408070e0c0703030209040608060a020d060515160c030b010e01080c0d1e03021f050417161106070f030e030f 71
    0x100000c0c80200c21641034440b55100000d80c3d00701400c007100c1c240071b940c6100e1110b1507221640014020703040220442c0901c02d0341c581131982a13240505840348401e0f944100800c0042c403003403040745800f01e110078410a528600086441c40711102451040908540c40c0403d6a2004144070b070701d00c18800d520240144004c07400e1039041c024400920351080030030140c00c03d540800c0d0b038a8140e4a907040b02005000300011141281450040203000b94000500e0101c10303807800f2400549420304012400400c039a007540a0705240c0510300e1800702c404244411150210050404030018440303603c000d01820503d415084190b0420410b0342c500080c4a1051307100300d4004070f4200003d000034010801071f0032035000c00307251403989141c103078601954011200c00d450480446c0c4400d22110340d00091049000e56030310612000c45448800c036620031102b8844460325403003041c402142815110807008440a8080c0340b9203a000d4581d190542d40b441c1c0c0860004624582c00b105903c0d0821030018a44003030780103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 109496267 1250 109495017 109495021
    0x12030408070b0703120c0e030d081603090c092a020c0310020f0f072a180504081b011b05040b040e06030304050a0303030509060109020304110d050c03030c1e06 70
    0x1400d80c1d40c0d5001c0c400c150b901d60340011500c0405200d80c1583d03200f0702009400788a90345c400c400103000840d04c03141c542c0c082d200e118071a041e5107218440d070074028403050030388103600010b00200314050106541c05803051007466200203a040328502c100c0c1c20b200e200640403c150003081c1411640c40944040c00c0c030443d440303886070307201c5a9030110703540070304105280340140d680c501c018000440c0c3c00389102e61030481e1008a07000061201c607400c98a04614030450901d503010700f0380c0344c07104040201e000c0c103034004040d503071029080341f82d552045070414002c0000710300302840040c02d03d0a0500403510294141d46914101c0d541c00790301c02c070ba1000e0119505200d8182803c109504566000c0ca2080300c0c4007148500110726652000d000b1900036100250440c50001e4a070708010f000b802d019500715000344508000011030b40b00900c02d03039001d40d5203c2c0e8481034005d12402080b041c0c540c02c510994450040d101d1010a641c1c080004140619550001e040c02000c1e49010f000394001482c00c040e4540c100c3c00c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 109497517 1250 109496267 109496279
    0x30b06041d270f1606200a0b041a240112140c040608070302030402010c0224180103060b0306010f11030d0c090e06030a0c140d05010f020306120304 65
    0x801c50070800c41e9680c00740c003a0350b441411076690200b42420980312184009a4020103401291443e8003420307440032103048110080410400c1d0425114200003e41c03802c0d081c055035030081c030000740846400c90448039014415110107a07404c00554040322891000300058038030b00496800140c0c441c080074140d100d00300f018402000061040543d080c10007844001030f0380c4400d00e41e0321aa080001c100200401d51600140d407088075445401980d0100b540e5000055015109008692003140d040c0d42d0300d40c0c2c2c08100d600303000050480c041c55011400c88101030740d0751075403124040d00e121000c0ea030051528289400014003101c00320b030081841e0b414200108401c50f60400d4000c0100105440c1010b0410168081d9a0035802610605070031603007020814107200d9400700520741580c1d020001c40d166a100c03142010380d100c008800007080310014410070080c074407044800d8034042c00301a0842c02000c030180d54150840d01c40a02440030f0aa020007400354078105000138220a000b1000194940703402c0031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 109498767 1250 109497517 109497539
    0x40c0201330b1801080a061a0711090a0609060e1b0a0909020a1706030f06070f0302070203030d091101050c1c0c0503130e1b030105190305150106030b0604 68
    0x14803090020106500e08840114200e07605001464001c54042c0c54828034540b00125540b2040c10740d00213079680e00071900c60342c02803140740c0803145403d0031202005c800100c0100c035a042481c098802e1242d0901d06075598035248105440768445442c000b500c03500b04076892049401c582c200081c108011410400040c0c2004d01810022444003191520340080034000c4505212a801100c0c0450010603111000c035005a400341d503080b4001072a800c0d0382d50710024960348180100450000740d10540200310218020981d940700d43c0101e14001d0f140a500b500131a10310351007540314202107941c946c0c0580c14061400600c2c4105c20f0246051890620340886440d51241c00c9010090b45e810062850500c00d80240103071414280c1c032005480d01d030004a07003c0700d1004001d200d4241e40d004000300080780081c030f1440c0502c0d010782552403141942d08000520181d214102800034803c1080b40001c030102c1e90800012504e840c0a00d000c48003581000c0c0010240c4001c480d030240524802e00082c00005648 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 109500017 1250 109498767 109498811
    0x21020c0105070908301b0a06020702090a0c0203070b04030207080a050601081204030512030606040e0c0c060604110406030b0310060b1c0c090303051617090f060c0d08041704060e040c0201 82
    0x170344141c4031200361250f00951090940c0d104018803e50703103a10100049034014200c06130080360b010203183d031010112025100d800000000503001044100300082074010320ba41c01502a104070740d0282d4450300860f00e0001c1921041c0c440e9031007600108140b1b03c00f009601300705040442c4003802d152840d070f03690b69207070810031400404c46408000580d1549501c4155001807451174a1801c882c142140003115550080703804058a00485c800030703015043c6070041d5000c60301c482031418a41450500114010002c2d07420441d890f0098042620402c1080d00a240152913244d0816641d01c1444051020b9064402607403580c050a21801d0326009822400320401c80e6010f00b42103582e204107095540d040124400c004044442040d41a1012141100a4040d604080d00d0100758114601c0400c074903802594200049c42d070203032401103401c40c840e902c0309410620411804810150425460b80c203908182c00c24800200c80c1e000640607440c1c58068140102e840d80020000c41d00c10b080702c41c484400b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 109501267 1250 109500017 109500103
    0xc01050a0c03020c19030303050a14131707080a02060f01060c060b01020309180702070e042001020f070e040c0501180603051503030f0301051f21020c0105070908 71
    0x80341c18901498000d01550148020003440c820001c0c50155000c1102c010500041e40000c4c82e010014110301500d108507417040070352070010b4256a981c2c014070300e5404210b190480b113100c0c0602c00504900f8244016100461041c01030944410300410001d241a00080036500842c00da04010064a0303080290f00b20183d800c964082036241200300181e01c5c40c842c0c03951903504006c0c000a4005090440480741c4d00030901c60f400d03584510b0381e1740102407060406450191090008510000030044801456089100c040c0141e40f01c00030500b0040d410406a9480303c1e2048140d4000c00040040c04003a0f00041c100900b001e40d00902c00742c1e050340506c0200e00914040c1542c03000420989809080c82c00213101c0c0080850f40d1b194280003640b050381d0000c0c4a214014480500f0603101c884401140300c1c0c442070ba41e59440002603400b0b290f8109420b41c128240c0c0103603801c02103130304808401e029186c4035029548800946510300a4240e02d002400c0d0040f205d2800c094040364042c00d240c140940c04144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 109502517 1250 109501267 109501277
    0x100b2704150e060a0609150303021209040b0913030305060d0b0f070509040c020f0c0607080d020d020d06030b04050d020f19151509140402130f060e01060309140c01050a 74
    0x199944144001c1581180076402071043d4004c0007440340d8203030000360035500406130500401a104100c1c18210b10b00d40030040141c4c00511010175400c284401900c0302c0f810003000030900c04c1105005c0707141120140c030807800c12000c600d00041803542500a1355000320065420362064100340d1214400b00c10003410103194001e404000ca94160f10410a94084401c002c0c01080200e81d8010041c0d50340a000543c0301303050040020348a031510b001401e80d05204d400c110444c2c9420b100c03c9880b00258000401d0b0016190f00b0322214039034113558071420740a10711403100b0400701c0c2082d007002d1f0320746030744d078158103085500005190010343d501140642009400f881c190407441882c1c5041010001700201c0c4100241c5801046842070303402c00003007401c440560030704000d885000c40b0301c000806400ca501941004036136811a919001d1580080748451966200040080e1600007214030200207074032841c002501c403d56081400b4030311041c2c2c0041b0101000511405440d000060014000c07854aa01806 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 109503767 1250 109502517 109502543
    0x7030f060504170d0209030c0a050105040e0703090606031a0f1506090d0b2707080303010e04210207050a080102040e010317160506010e0708060f15070203100b2704 72
    0x81001010398030030556114025468491480130000290840d13460a4881d110701b0703603012620305010341031405903032041e960649040c0c00c082040c2582013020b0181e108041d0755903202004034120340b10b040045c5114070600f001e81c96a0284e10400f6135005840c603035825100005000c0050910103c0c0101c41000b0361b15180c49200e4600003c0004a1282002d01100e5102e020844841c00000161103010740010081d0f20350030301c81e59110755504080c001c42c4500e610810040c448244c6100e8241d0380b0900c80c915442d43c520910840140b40000c2c10b89400150348412000e0005181035402030019044440c003c50500b460203010200d000707010301c0045c0400d80c81950f40c000c0c5084180440d21180c030b0381e040814540103645450703070f40c0b07c10901c0b804120b00d80c99404200d1562080c0521030042d44010a4008152141c004000c3e91081601d09104444801c000100060700d0a0206540e00c1600000005140e00248188501350201c000145141012024091107030300c050500c103900545c00c00b0b901170840e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 109505017 1250 109503767 109503773
    0x30b09090d0e0a0f18050903070c1a0f0a020c03010501060507050a0602070807080406050c0c0109050907081815060a050402070201020706050702040f06030803070e010806010903020405100e040c0905070207030f060504 95
    0xa400c45810a108000c002040410310310485c02c40f00320b107500749120801896884505594a90140400041c0381c2a14883c08100350b0800302144030b00988100c5425240070b00f8000c02010a911804404000d41c0148a54940c0c1e46820b104e01801400745043c82c034505202e40d90f4080c1c5034091000000d04e01c5601142400a01c500c61040e03588180d800014190760307039101e4401621030b0300407024942b4980714540707440240d940f00351a904110345c80504402c007a9202c1000c2a034075108001d00c0c08a40528104507080164030400210350b8a0401c05048102c41c2000340a10241103a560041070186004100400c0180d83c00658042140d5003850034680750500c5100240c007030301510082d0722034103003001c0021042c040e81c0c03401540204099103d24600c140036400543d4800c0d01215040c2c04944180e0b002c00c0503041c55000b0a520240f40da0100c41c0c0c0540711400183c01c0c400c1643c0c00d4610326210002840011000d100c0c0507040204d500050100d1881e66035130a034108481600184040e031210089010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 109506267 1250 109505017 109505029
    0xf0a060f0209060406050d05060d080a0503040f080307030b09010e1018090c060e0f03060714070c0e0c0a091a030109090302161710020c03070807050a081207030b09090d0e 75
    0x40450000d1070f00e03599aa0310400140141c0105120100051401000c5202e81c51f1401007014803a80c000020350605068204c00d86d03403600001c2066a03043d86143c141c8000441c694011441000c1517100054185a250f0902052082c1608401043e045d0001441000e10710500c0e0101180c40d58404038082cac410003046d0300080c1c01c02d0180200b54a07888800400c0d01d5802103003903900f9080c01e0780c051005d00155401c042ea0b8410695450001c03a40c4e002c50002e4103d6003c00a02d01e650186c4501c10202e507840b941300002c82d50840302a10b0b08100400e5800b085940420b600b070041c8111001d15400d42c00344402650603104c18807501442560f01c12148040500901c900c1d8030b0000980b4296036032035030b1868444402d17000500e0114441c0581000c90020041c5842690002207101c0e004609003509a41c6a06060303101400951300c41c450681e115000800440042140381d00d880410040c0381000e08026045e41e082d0a40d00340705141c85c1d010080b03036240015890a1000c0e03181340c00d41c954460310001c030311 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 109507517 1250 109506267 109506277
    0x206040e010308091507020a09020906071401090201020f07151808010c030903031104030807020d1407060c0201031d0c0108041704030609020a0515031b0f0d090b07020f0a060f02 78
    0x540c0c490000d000206214124000c0c20000400755a8218281c5c056584c030a10b510501034002c0d40100440020302a001c02170f03002c0c0890000141c0094035000329500c90800184d500700320400642e443c1c06c0d600b000c65a060281e0a4a000d0b9031004080c030070700f0300450b09034811070301468204010000001c610f25958031607889004180150003001031240106009010300384094003500402d041400104840035203000329411aa006070103681030084a500b00302502c18500030580352a0217580034617000b10403e0003050f0041c1125100c81107071000c41c2c4000f40550f0750660340c02602c0c461301c0ea202c0c0400e003c049000049400300b440c1c001901d0b40d036031812071000d801d640c0881d400c00001107030100170070203940e100280050080380d40f482403540d0f41c0100300c1a824903065072059400c003800401d2104410f001c0740650600d42404042c1801e904803d940116008941000072223030300c1d1480e110034483c1209109401c60785500c00b6242100b000c0541a42d60500e41c14010589076489079002000d10030b07607041d22 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 109508767 1250 109507517 109507529
    0xf0402031f140108030a0e0114040905010b030f0610080103060b030a1202070323030405010f0e060f04090b040509060c090d0503030112030219020112020304030e040f020d0b01021b0d020604 83
    0xd07500249032030080182201c01d0700c01d02d061001000421001400001d5615514160b0b4503013814009541c011949410446490380e141181841302007a8a0b00d40d0240c203000e0702c11030410f1512072034043e0180c200c500c8054004e40c000d1210a0f00c140d01643c0c44034000f41076940028020032044151000300c2c0c40c0000b40307640501240340c5a100b9045840d80031800d10708076030184000403148801510524030710f480303026400c080c80c0d108000803c2194011030b1140301001c154106a0a46000b0741c000c41e030070758441c103904107400c400040d0a2002c482e1520482141403001d4804000d90b15000700401d660381405448218080004103041042d981c90140104051b984101548d8482d44d40b01c1900c0714034014008101c1c090300803410780800f10012003414170740305901691550f041c4501840504000c0d400540b0550410a071a40d41010707075103883c02455480d945101006aa5200c0c94040d00100c0d11f04010f00d07411900120b0042150308242c1034001c801e040b0031650803119510910000f010380c0309940c401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 109510017 1250 109508767 109508803
    0x3030503180d0509120705030c090705040306020d1b030c0c02060903030d060e160c050c100e370f030b06270a0605060f0307080c0f07050a0203150606030f040203 71
    0xa6594840f01034000c4c10b80959650300300d140c0000fa1140c6030340b2540260340d0554018400c01000e840d1107107070a0703045021030404600d000d4591f15041e045c0d03031128400c0d1b6400c1d0b44600d5017140018048c40000030f09121403504002c510709034179004001d000040d501920500000c121022176640920840300c4c5081c619004100c0d06640302903085500c94200e0321114100c2290140c200024041d1001c2c0031925804005407042d00d02210401070302182c1140701d0010841d0311404241031341c9a040e0606a0352201143e403480d080a0005440c00003900380b0114618924508003c0040d4a1004000d0003503c1c1c0c0000d100c10250303110404134603010090441c4018490781600c07144980d107104141d20b401001c0ca14400d00c140ba4a1b1800e01450b481100030241e108201080001c0c04036105501943d0003400b6641654642f103041da9211591b03800001c03041e00d0035040754600600b1490304002d0034044100b01c524040302440c0c840002481400020811502c0101d134500003011540c040c4a150700c141c00003440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 109511267 1250 109510017 109510033
    0x12070504090c18150f0305100f06021e07150e040f1404110f090a020318030408030a0e04060b070209070e13050702011a03101e0207030816030c02070303050318 70
    0x10311a400a800e0041810090701c008130b1200c0981e215803411450545034081041c490500850040a000300700e0301080701f0780003010030b503200c0c05180c40380101800d81c000c000a495a00d49030003100000480301d40d0356402207608110071240041c5400c0803109a05014219140c030201080140600d00b1984140340e180000b0703e5420041d007030480380902d01410175040c80c81204d20511001c0d013400030702603900074420303000102900f009400855006640c40300c060384010f480c0460a1458001c1e0b000044582c10108038204181e600040001c121442150180219864400c58410324402d21001900403d03004000035461401181c58002c0c1c07030000341040120520b08103100c00145401d0314000015401d108001c4001c04240d008840f5400008020300031303c202420106009210f5100c6141e40d81003407800100c40c4110724030250508c24080e440d200c00516290100540300c0c0405200c5000345403030b151420300c2d1641c0c00182e041c00e40354541030260b40c039210402d00b058a030b9005810030459105604c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 109512517 1250 109511267 109511291
    0xd0203070809070905012105160803090f0406030b04231f050708040309090c120e030309070b0301031a13200f0f031b1207090e0d050304081207050409 66
    0xa982c03007000c6020a40c2c207000e8413141e002064034000c0c0303d4042d01e054030301d42d048180e00800782480340c494401c030b00304c13415005040c2449030150b0441e03100034441e4101003000c4841d4100400c0761220000304482c100032907801c607600c3e00c0e411000684041c1814210300d00200c10111550358840c07040c1c00090856209604940c85500a04603040d291003100d81440d01107030200b4011a0214000c07a4181c50700c40410f820140354000038003200e0803e01c2001402401c180c0307a0502c91203079007500c3c850380010355a00c1c03030000c44661810803103520030341201c90b04000400201d00c04100700b072007603130701d14410041c180c403003419401607460324400c003801c61003000c00c500d28085449651050700403016100e00303200c40081810840c2210303002d88016055044202900c2c60241b180030b6131200487d0043c900c2e085546481c2c1342e2458011070341c0025800680e00e2140c40024072080145500300d03005031912901d90f01d00703569698258056102c900d01c0351001da0012a80981c003074025240500600745d81000030901d80c0c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 109513767 1250 109512517 109512527
    0x80d150e04150608031815040914060d0314070201090302180a0615020d0c0215030f07020111091804050f01020c0d030605030d080402060307090902040b0c1902010f0c06020d020307 79
    0x3441c1201ea44014450350030903a01c10307000b0402142c41d07030009141803402c419442d201040301c501640382d00034104c418024018885001901c0604021a00040c424007080c01d85180d014000d003945204065043c913942c0040d5000705500b8494026074400c0740c0b500594401070300d18503031325003009500c81c50b50030800c80c083c0c0b103003070740684078005e1200244030595035141c607042125020940d150042c0c0000b4a98032509020311017004a09202504013200400d14040e6120550001c0d10307039040b003c203a00280015140c1c2400b030365040307242e020300140c542014100000c0e600c43c144441c3c40ea1414420000400780441071101003450100c01c1c0080d5515040005100d848001002105001c83d2030828080394606001416001c172421988500351070380c450383c003048500c3d00000e00c1001040301011002c03c08a100d80080e200810240d40120340b01c045101a090501058169200788076030440c00e510f0250303a0000060070041c0782402c011541c1855800d04001078030520741d400e0741241c000024001c500c3e81c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 109515017 1250 109513767 109513771
    0xa030c051504120e04090201020706030c05090a090209091b09040e0c0904060203100b040302030721080f04062606060c16080f0607020303160807091d040b090a0201020307080d150e 79
    0x7540d600c80380a848501080101c1c6e00c0702c81c020340160300210702400400c0c003d60041d1034401442c100241004d0507000048c50301c1800390403400050f44c01084019280c06d00380140e0384c110840180403030404000c1e0768280321900402807824800c40d12400841c584c0c02e0103011986443e0005000b501c000d01d814204000650f109450350300d1003010032540090641125010346040d42d0340100074007a41454541600400880d402d010300d000c0080500321b0707002902840051420002600070075440301c0c81c080303014101c0a0342c401d100c0074107040b115041503400c01809030300703600c06030840d08113490394030000c40a89019805020158420301c0c00801091981001a41d00c9160f1480f5040751556034400508989a01050f900405004810318402444501070980142d01100c540b0b4022942541c0b5104442c88161015242d11981020001c0c0004d1201642c10320760300450b490020840c82c03019600003582d901c0707660000b6045940104030f41000c00305903007000d0220341140617002031307680d25950003201c0c400301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 109516267 1250 109515017 109515053
    0x70f1b030905060a030914030a1b0c05060418050a02030c160606091119020c030a0f02030a0204020301150305070905061e120415050708040209041e080c0703110604080a030c051504 79
    0xd081c40447e061a0001c03c681c41e106580da2805024840200c43c1c0c1030445580e4411590018498408181c5403680c01c05840180340184420b1f90040100540100700c40002c1c1030114024010401c12201c00d01d140101ca10341102c4010b41258001c0301d080110080c0143d81200b0a070a05040c203d000102d092006040c14070400c84248010001070035050f40d0301c0035115142d941542020901801107803843d2441100d5a00240546040300d405600003822644240c0080c0041d0302e66852010206600d4403620303a0040aa042142034181450002242e84c000c050444400090140510094400b44015030769006130807900e41a81d4141490316141c1a554070000741c040d0f52400d00065540792180880c0c5000b1030b000742035401142c4450712041a6080500851120041000e20803000908084000d14000031683c018145550441c42c2400005101c1e03040c1d1846444107101c10311203541d001c910b00141c25810b040a10340075401d07140c10360a00940b0f05040e00392011135010407041c4540d100c40d0501e00c0d08 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 109517517 1250 109516267 109516283
    0x100b0d2a05040e07061b11191203030204150207050102060a0c0311071406100e06090601020a1b0f0b0711041d010603030f03060815070509030a060504110405070f1b030905060a0309 79
    0xc0d07001c072001c8480c5105800f50650150482c44c060310304041c0e038918044400b159232401b4107a260042140ca944d01010103d0029a000500700060181001c4020192500744043c02c00140b411000070341d10300014059500b00345e80d5410301980035000ea4001d13081124610704080d00c3d203e060511480c40340040d5401c1009014800004a40700c24421a480903500301082c5241d00383c890304280003000382d009144a040d072050a555201003110140240c80381560340000f003400d2801c100d070030440100c496000c60021f040920911000442c464184485007800b0740b00000c1d041122442050015446d0104c1030895103422000710034160700602066180304036450a016060b42c40c1c060681d6105100303046a20b421088001c01e01561040d0300600703a01c5001411141922820344a1504984040e50b007256096204114515581800e02600f64042c980b0300f030000746d41c594940701624440000b2403524920a280b00e1520405014440c040083c1401410f4071f0741320f500150300540145030900060759410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 109518767 1250 109517517 109517537
    0x90109020a140a0c080a09031401060918050709090c1a0405030d0f050702090c09040204120b070503090a11011707050903010f0b0a14060408030a02100b0d2a05040e0706 74
    0x481c49104584500e44a80e6031308071441d50544600c001c036004070340b210b010800803802c0040803c07a14406480c4009910000041044c64180d83d60210b9044202c07800841011400210204030040740840c100c07030190002089040942c940301907081c44c0b58001c90200b04a40c4602c052040b000c4024100750341d429800c8908528a040064aa0140c0a505540080d904211510040c203241c0899a002056400100c6c00c0c1140100041d059070003e40103035080d40c2c01c00c84008240040c00009a07045001418460324604200f007009032200c1d00c503007001d40b4800d00c0c44001c4a240e440b440c0713030383c0c04044803000390181800c1c200801000c80c1d101c510300c98480d600300020390500e20001e12580c5895500288a200f0440c41c00b102c58552074103802003252b211030140070000e00030b403040c0000c2c442c614650380a001041e003101100002c4039042000140580619441503000503090f540b0901a048840031007100290302c10b5406560301442e4120b540c00c039007030147c40743e00030400007110002d84500c1d440c0c4140034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 109520017 1250 109518767 109518797
    0xe0a050f010507171f0504110d0609110910020307060203010f03050c040c080601120b0306040b0711030906040b07060b031518030c0c12120f090a09090f021c02090109020a 75
    0x1c500c140001c00b003004d540002055990100429103480224900080c1958980d202e0002c0c048480da440c419800c8100000c1d10304141e00d0a124102c054032001004001c3c0d510441d0b05c0394038500407a80210f00800400c3e210841e81c0303000300141c1c0c9a040d4400010344d0b90390b0315960728a01c40380040c4000c584503c034400c54680381c0d15090140c40d45c0140240d032080d4155441c1801150001d4014880344132203a5540c80e00405900c007070207603d00c00c03070150500ca039984c2401c140003040209000c2400c0c0c480d0b042481003a0b0503503104422241100c0801150903110203ea0808000411741403003c5176051140d00300c40004040e4840309030384140c200c100419040e1014501c11600d174030400c1e94101217a004008100300524242c0101038220140c8030440b021803220301008100c941c820b0b000344100700c1c07000c100e030f401e6803500c0b40c13110010f000072580a1240d2000d60356030b2681c1075662080284212510349010955111038102211a950020031204407135039195166002540000d19410000e440484d4441c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 109521267 1250 109520017 109520027
    0x102090a0506030717060a12051b010c0c060302030408190e01022406060c071802030610030612140f070e06030c010c0c03060c020705090a14010f0b1c0e0a050f010507 73
    0x4141300540f0f0700000c240700d9480c13540c2c101800904481d408610082d011880c20241c280c00442144551300070051030358514440c15078002e18000d8141000b0300ea048280000c1d004049441c22154503003005a101c0e02c1d2450851fa941c0101001558440c100c403440d190040e500030410b090000007a003e039444804e55801c0100700803105080500c240c2c1540300822180e08084000305206e0461b04242c0c1d010310b8442d40100241c4c0d03100481524065008020702c010b6150460b5020171540707140c2000c1018074642a2039041065010074080d00ea542c403d031740c0d049000d500748040b0f10300c00681d07410f1f1511607031600741d100800c03201542d00318000e01c200501c031402075018078070101c4042e410050b03e540592450703031180c0203071400d4002c41c01140101e05001942e51100c030045070041500003400305801c1140d60700503e200805901c42200c010341031208220229000e011585000716424451842c0103610014a020b004103003281202c0e4440d480b101010301ca0046204520066800000d100e41d846640c01111 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 109522517 1250 109521267 109521271
    0xd0f0201090605040f0302060c010e03130303020c010f0f0c0c030803100e0109020f070f0f1b0509100f05040b040605090a09050d0507021507050a020307030506010f38070804080102090a050603 84
    0x60402045010b0001d80b824201801c61180c9d4400045044001511316506541052808800b40313011003100b44205501404980c4424030f0a180000d12400b40300c1c002000d00c0240c00e208010321144030f080e48103016803404940b02035a0030507005a500c2c14044840c82552003d0710400000e540710f02c00100f04801030780202c0d0039040f00509840c0c00e04256441d6034060001c0d05034102c41c2d0840e004081d41c0000c40950302110203b1a00c240e440304c161a100503c1003441004150104480074140180100107142c0304010646105035000030b82c0ba08140d020038010903c980144d58044240420040103209a40020381076902c28816220801c0100741d041e515405001c10080d8012000c00700c041c020ba0341500a000f02c107005404a8400071420380203e400c0c12210741090315190800c1d0010300008d261003c2440082140c94200c400f90030b0704040078440d0704010300c6041c081c00c07124290407003081c2358901902d03102c40d040a203655941d5524030441b8000d52062110070300a80c0c1d0800001110b180c810181c034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 109523767 1250 109522517 109522529
    0x5120106050a1401200c04050901151401050705060c090a050a031203020d0902040e0604020f0a0e0f090c0a080304031511030a2a020102030114060c0d1404050d0f020109060504 77
    0x66826080040f00300780c030000180f501e03040060076020202e08020502542180403400000b800e1441202e030700340419107100800540f0f403070381801c4500d8142c400c0b050b003c0080701d42081c0b0081c4180344810040702e040c030072120f0260031403003403000344464215444020200300380704076040d40400d45e50b002800380d100d0b03841c84058500b11811100c0d01c180f42c065001407141601103c000034041a6550028003207403210358000e480750307010004220450520201d001c0c0011001ca0740300005031b25240e299080c880b401001c02d2249580c2d800410b014900030001d80400900080c020301121703495202159403030708584026582800c210b0b5040403071003c6032141028100004041d0752440e92404502c03005800c2d1166104505041300d443c52450040c1300b040d030603da1503150300240e903a514002e01d008100c60b800d041c1c64407420040118250040d80010442424629802d25540d503003140e607151141c500959002540280c5000c50000410818003411070a66200340c0b140140c4a4694200f11003601560280e8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 109525017 1250 109523767 109523779
    0x4020705010b18010605030703020d060f0303120b030f0705040b0a08070b030f0a0614061309050a0209040605031518120d02071a04120c050118060e060a0908030a0b0d050a0b010512010605 82
    0x82000d8274425001031014808005001c1450b50f55800c120902c01c405510540c00240c2c02e60086074543c0c41350061244200003103000301424401c400d05140c86204038401c0920070b0b561011005e941380c80b140c001c68001c0050348151071800d503898514504903442126403441a920750030000301c1e4400306110358030580c1c64400410494040e40382c1400030320f034020802d01d9030164850782d0000d070055050080d184901500350300903807141070031418072064580a0300302c10f206ea007204070340b04103419144a0f500e40c1f116405401200c42074034000380500b0480202002003000d138000541c608110b066800a01041c0c4c410001e444007121030a0240039484003d803001001c2120340035101c1119881003503021602c034051800090360420034400000e00d092218800c8031010385130103101078221014880d05a10201200003803140316040d5135402140d100081c030304081c01d0780e50303512040701d6124100c002c42481c1d030103012215081c8290a00328002042481030301d00c03c6d4000000d0baa0a110103008080c104e4101800c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 109526267 1250 109525017 109525021
    0xa03270b06130f050c0a0e0307030b040f02060c030a030b09090c0d030305070e03030c070815070504030b1b070c150905180702120f0711010809060a091104020705010b1801060503 78
    0x41000202203015400c07002c80e2200a550440f110a20031035001d1044402c20540d24000340d000038080700d4004100ca803003500030740300401c0802c1c6002100f0b5449071303206410321041c81c81840081c000303000703054108041b80300100714078a200da059408141080e5046032031084542d60501450f560b01201c010f09a00041c1d03160960000078042c1d000f09030005490704000701006082000b081c0f440d0011040000039074408042007008010034403442c0007880740820840a185801900646135102d01e110085c82c00078041c0000c0c204045102070b69003c030300191805070f130315500c1e4100f03255001024040c41080007013080c2241c0350b043c00344015030100c90018214640120b07004d0061411440014410350a60241126406800d81d100b80102202021341c3c42407511222a82815458000e1806942d41402010802c0c002906000110382d644807401001c040b070403038402d2800340c00605002c1000c80c0c20600101d826000c100040d00501014041a00c605a0341e1403080e00700e04001c4030a11460001c2441000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 109527517 1250 109526267 109526269
    0x909020f0f0406080a150c0e0913050114010902030603060702030c0c0f041814010c020303040309171203091509060f070c0305090a03151a0a06030c09030501020a03270b06 75
    0x4100e240422000b00b00048040e61000d00b035040c42c1039a04c04640148a22084000465151082e2400e001c544c2c03070301905080c02003010945031600544074003481d03803216000c0d5040000c00d400c00082c403d03924095444075651120750401035041654068428050390001400035480003060380c20903403a1a0060409140351000e100d1600da01c1704a0542068440042ca0700c215600342e10301309014072821004604501e405a11800c540c2091905c00454000300140000300b40c0c00400c601c2516015484030154158204866240c03200092401d03034a542d0200810984c064003045c92012655900c1c10a881c594540ca1541e4642c50304960107804521201c010030b0080d13104030b808122076171007070070140c1c60042c1d0500007034424031942c0e204403071140e034952040d40f0008890084503401c218401c16440550300750000901d0406190164000301507403078801000e03862044030001d0046820030300031541d82e258128000c02a000030004042d0403030b0140c40ca0501c81c2001c0d8506c000d1a0380081550100d512180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 109528767 1250 109527517 109527529
    0x1180209120d0210090201080402010302030c090a090204180203010f03080309030715060311030d0903060b150c01020904051b03060907030905030c0a03020d02010c120c020a050f010f05010909020f 86
    0x4005004559800d000622a036103445003102010348195004000c40d80c05400002c0c680810b810b1011019030078086800d0060360410099904194242405070701c07540e4410380e4810310300414007101d600480510700042d0340c00c00e5500810903540102280018007001ca101441070344420700c0b88580c121203800701003010607000405140c1106100c01500c2ca82141d54880100726107845818084090341c40d1010000c01138240c03204c0c42030000503030161803100c01c01c16000e00841050710020708901c0e202d06c404025a81e800041c418820741e905001c503120b100f080311850017900076030480c601662420010403a10510011110b1079000035406492655482400341f114000300504030790241921801c2c980005241400508066400d860040c5002100307030400a107010040c039002c0f000d591420086c0880341e07900401c0c641a5118195000c9260303541c0c980120701c3c003030a4410190282c09443c0f00ca4042e400117401c4210103120b00e071402d2003c0d0741c98001e0101210b151503002507104070400920140f13400c041d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 109530017 1250 109528767 109528799
    0xf0b0709270b090c03010e0112030c030815060c1b0103020304021003020a120f020a020114060102031b070b03160e040b2b02060316080c040324111204060b09040201020601 75
    0x90744000c00c40c401100046500008207550852500d07078044014800d0410b6042201e0060100441c10946102d040d1000361101c4180c2d9005402c0000201c0014842400751040d02d000020140400d96560030806a80d84c0b16007148040d544411842d9000c05410f40c0300e4004e072070080ea001080b4500403807001406800a5100460640070301800e00c0b010040f0500a01c82d0301c20407100000056a0b920801030020b003100c011400c8a85050a1603080c03146a0341d0001c183da10b0700c90403003081d102c4850700ca541c11385410000d6121a044120000c200200c0c0c0c0029044601783c40c1282d1110403074003041f00100410340301d180c4101074001c2486c00c05c41c2c0021651302d00c040803000f051901d036446a030098010a00f81e920807900000d40259a1070160100740e803040c51141c1c09032403800e05c80d06060450740c075208591005813400000c10181102c6442c040020740c4030b0b08191649910703065a43e0b035031502c03c114111080b00c055038100d18003110b1844508018240074400d96050340580b180e40c0c20044020b00382844 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 109531267 1250 109530017 109530089
    0xa0501320a03140c090f060d020d060c02010b090c07030807120902030d21090503030c07170c010501050f01050315010f050d050c13080a0f02040207060b04090f0b0709 73
    0xd908508045403911000d01014500800468800d4419424818901401c0154450007465220100070045020415a07a049002140d61540c00c03405400000c000c13289507040903101c40c2c038201035500c1103501503001901d100000d0310542c1c03403591150380d441454001c10101601144000c0001812039208802808191075840e100060040840c1c0100c1d2030710300c0c230600d03d0001ca005040454a800d05002d104d03409400d04240078016603050f96076150301da0102502640102d003011503103104004c84992011450041805440d40300c10001c1c0070755000c0c010a01c14180104141c2813030f002a54842c804480c42545109407a4118003081001124414030210b00502085014844041d848026003e024003600b000803500351984100d07041c030000140240d12100495002030816400a035180990006035a0101c80060300c4a003a801e01001510002060039440741c940a552030400c460801006441401002101d20725500d00c4810381740d4031640d0044240c0c00c4000501119500c0e10078600724140c5403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 109532374 1107 109531267 109531349
    0x605010b0a02100509190f0308060405040209040f02060d0c021509030c0a1b03060c02061b04050a0b0702030304030b090a170406120f060f15080a0501 66
    0x20b003110b00c15842c1688410005d1034821041c00b0342030b50007144840354404803400340352640ba412448041200820b41240216850303060510880e03100b640c2c0030740322540a461703540700c0e00900c18180504a900810404c03860700b14695600a0f80038080c2980c00402d100c00401041580701400208640311990042c001d0104444001462404207500010f4090800b5110f130f0758018107041030741010b00540e0401844001b01a80000d105104800703403001c03040c1402c009010a00300d40b003544604c940c0010408002d03c1352000c900024500030703100900f141d10f0150b9940d10000c8004049410003410b0308108201010320180c00c4990a5446900c00c8040c502800c0c101d000c5c0c04e641440000e2181c2d16502c0c130b0044965400d5a00280240c00c0b42900800d800d603035620341109c0101141d110f040000c1c1c28001040203104640a0541a00ca0607641d02808184071a4600300302d04100c00c460f1441a = true := by decide +kernel

theorem cover : BRFrame.Cov 109352517 109532374 := by
  have h0 := BRFrame.cov_init 109352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 109352517 ≤ n) (h2 : n < 109532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
