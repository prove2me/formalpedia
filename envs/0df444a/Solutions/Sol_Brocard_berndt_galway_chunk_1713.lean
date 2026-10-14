-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1713
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:24:23.236103+00:00
-- url     : https://prove2.me/submissions/f5832972-06c6-4186-a969-a2479c27717d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 307913669 ≤ n < 308093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 307914919 1250 307913669 307913687
    0x30f060a03150c02011d0a11030a0816030e0d080a0314100308220f080111040b0318010e1c0212030408030106080711241515090a0e01120c061107030201 67
    0x84d03560f5404821b0740108600e041034412100e0201805182115140c000345039071008800a0299001c0d02603000001d908808640d041c040304541c10411401c5072404170341240106a19941182c24180d0400402049201078201a64984c5052008451407094560051030446600d40414940d60041022452030303c01000b40c0017086030300100d0130212041c412203401a55000c103000003a11501000240c5083c03048121801400280502d050700d000a045102d002c06401200350780440c5914820303020303003540f11560a0f0000000c1d40c107441d40c4049011802d0a4a07a00d06015000e103e1300c82a0122902040328411984420642e08503403c0c104210b5001400505a1042c48030348851044984000c0200d0076124400d1400d000382e20800c012a90b2000b54041c04010134018401602c0c0004c2e5125240840d032101000002d984502c04000040d014440a9002c1914085048008182c40031498041000d1030300038010381c0f0000b40d07500380840b030b1900c909000400135001070100344012f41c8078008103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 307916169 1250 307914919 307914941
    0x4020903070305121c06080c0f010c0605041401060e13030c14011103240a140103020702040e0c0126010b0f0f1813060605160804030c0b030f060a0315 66
    0x50389165180d6a410f440c0a80710b45104c0e00051001c20060394801e201005041703040760564007480064542a002c50707a40c81001c0d01c00b40318500c60480b1020503480381400084442c0c0180c01070040303091a003840985043d10f0480d0240355401c1030404114102c012400600410b00081c031001500303110f0f10200ca41c1d03960050100da600031180e0400706048400d0080003001c034080054a40e40307040c94290448804601c00240b28005c0c1611111281c2d682c40c1d881000071a103008074007030918541d40004070001e00c02c5040095016140031125850b120000800c2c004559080e200d1110400d502c2d54240411810141c1503030241c1303038960042c402552144003400002181c440480e040401030703803550001d4ac20242a00d036100707042d4080c003250303460101a02006030040728003c00540c0d040020003070443c4175030010721040d080310309a104200035090044900442c0c01464030b41e00591280170a005a91041d40c01c00c503c0102040402c0701482c005a48004982d4060700482c0707401074202d44031029203042c0c400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 307917419 1250 307916169 307916173
    0xf07050705090702010609060501091d09010b0604060801030507122339060c030f18100203041a090f040515040e210a02060103021201060308070b090c010e030c04020903 74
    0x60030742c8036040050701a5900b81c00105945d400c00d9203000c21501300e54031550420204081c2084004500d0359666003000600341c50b26030585c2c900084501400f0640d030002e400050000b40060001d40c40b1103071314180d80c40b40b419181895601c02a0203a106a20000a844c0e500c500036401c4c0d5808541201100c031a6000d01640c2070169400340050844440e07500510f0160034203140b40b0044c60b0f000b00b01e8040703200300711174984c28180749030411507503030086030380c6104070b03040004400300400c1d220000b0000347c25000341030102c050703d41c21000351260001c0c4180c0c4500035040000040c806503190588510302d0b4003510715141001d00104100c05090042c02d602803400c2d40c482e0000c460b444a00076240e03070007400d20041c010548520080d45007150300003030a403c040c405101d0612141c1c0d011503036030b0449404542d40c0280703244140d1410f0041c80aa84010064200003900c3c071b0420081c07000d120700c5040800b0958419410303020055684040244000b0340c180c0001c40c101d0560b02d0b0640c00ba050149010303007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 307918669 1250 307917419 307917433
    0x13603090f09020301210c050409020f130219050403020603060d0609050a0302030a110106050906010509221a040b09010e0c1303050f0c030f0d0f03110307030b10030b01050f0705 78
    0x88214080c14003904032100c1c107a000070040c84007528004840110038211b0701e0741513820701c2c2a200d07420030030417074014a44201e48410041042d0b41e20111241d40c0248000d0400c070780d68551039101d0000303500502c214500e0103c960300749400b960080040d80d08a0b50060100c900e165609820000c0800c1419000c80c0c0781c0d5a19a01e40002c01c40c1005180e180307a100c2d400641c0c0e10301d009403024ac60200302d61851030486c2e06207082402a40c64628800390016800c2c2810398030b804000001955148100384010103c0d03500b03501003503803071440d90460080d800081064a0810100109100c281c60b00c1d555455044000c00b0010042c5442c040500e81d480a0b81d07802c0d40741020a2412282185d03603c07940180c80c198844082d40e03116400030b21030310810200490040c00c0d00c044d46000180c0700c2501403810403d000305007903c450494044d8002000400e821082181c3d68505000c014004241110145001c1c4512720080e444241c00303072043c032070b1002050315070a0070016401420021548080b000b1202401480 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 307919919 1250 307918669 307918679
    0xb010207180213080109050d0206010909050703020d0512120411011d15090307030b190c020a14070e0103081315091208090301110c010f02030609070c110a120501360309 74
    0x84200707a41c10b03114002230403000d00c4641c2c0003840c095042e00101100e500c0c1c282590005180080c1c15400c503541900c044260024909003a42030032504418400590030000e48001414108103415208500c5001540171102c0c80d2801102c0054000402d180c4c0300241440c0d461a528010f0b03c50100c808814010a00e4400300c0c5010a080600c1c591007258241003c45c244030f02400410860107078050712140800c80300b60704560080d9580d11440d40034040e64803800e580900c04c5004e012040c00f41103c0c800c50007895940780b814403510350180380400050032014102044010075031010a005604079954010802d041c992a00381140f100c0404541d41c18003013000403103545084c010030007041c140004442c1c0382c0311080301490a69154050240e0000d104000300441c03550754121107038100d407052610002c0000146403091380329040010065100103c2400003452a41c0c040b8024045803041c8024040c00c15280440400702c01c100c4c0e4400154218008269907031032010220b0070005000e4542031310b226543d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 307921169 1250 307919919 307919921
    0xf041806081614121b010e03010911090c1317010b240c0a05160810020310090513050a0506160c0b010e041b06090303140921010b0909010f0b0102071802130801 70
    0xc5074401104600d91043e10355583c21561024012502350003e11450301c29540e82d41c4c0200400a4840c403400030340c400310782800c640d403059a1f4410b50710680c0c0e0700401e848961891401c0d40d110003070000e540c2880c00015150411000c8c2c03d44020038002c0041a0380c00786600c41c08240c22105243c01c0d544200f144a001156003000b0851598514200c131007402411f08000a0910860010000c42180104288850003068460b08021160b10302c20024207500c0f40c035401060002c182c078000d85103205602040060100100d40e03140a440c08400c006680310061400752220500f0301c074064850b0413514010170080e102454480d030b00030703c03401c0311000d6080c01840351803404401c1e0300204000742d60500705000701500079001540741d0901c0c054540c2895849000100240b0926450040c4a4407460031015618425009031182d14401020480c0621b01045410f0003002c0c0e1081d038540c00340c100007407d4800d5001181c11000e0303642054810f0807040d12013031960040d40c86854401c00c903c0f040c80d0001107008003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 307922419 1250 307921169 307921183
    0x30a061211040507032c16080d030c2c09060301060303050904020f13080703051b030d12020c120702040507030b1c02030c0607150c080903041206020f04180608161412 73
    0x4510002d1010941c042003461a092644440e0400c152031f20300d051017004800900d0450754956860040782010708504125030b07066804410113910880d05111969010034112810140c81050302c1409541c2e032000105401d0303440780e10010300803440c100082481420320750020040c04004514075441c2890500e65801c8640c80d80d400006d80350000c0100b801003120502c001d500c141000705260351640e24000000e620782c901c448002c0f0078000b0304c0c140a81a0101754068880e1049080140d4801b0b095a900302d1055030700c00b0704101e10440c54040000e0080b07021b03102e101081100941107441980d040300080c00b18903011300702aa413511a1280020a0340d0342c2d407004040442c0b15410b0310341048505a51482541d40040d80c1d101070041d40010008440000000e5070200d03118101e044c0c40b241c0e02420120020310858145080c440c038006404960612041240d0000c0042c25108005040e600c405144e02d6498000c000040816803400030000021404046070500b94000c009064400c0da8032441887c040c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 307923669 1250 307922419 307922471
    0x30403050301060e03010626120a0f0215010807060c080c01090f060b0f06030c0f0d1508070b070f140c040507030b0103140408030f0c0c0111030a06121104050703 71
    0x4014080264000040100c04e82c06a00a204060a12006840c000410403440440030303014000c0a12000c1704015955070030f2594081d882d41c880746c1d03800003000e55504902c03d41c00352280c0703194001207020ad00e10440c100d50600c400b070700c101c034100708040303407640036041007610740300c00c140100000721400f032207082e00302072144c40401015078461a20200f903402c0316a0251040700840c00030445a02c0d900100c9601c828441441940c0e140214110221801807040d4002c5d40c078a8104c1c200d00075800c880d0f20400742c0750440110b030000d5030f807509464054450440c005092044405804001582f40c4159009505030303001681d0b01002c40002141c1252002c81d68030300000d440710700d2140c06d0f50301881400382d005422801820907203803980f91806a448082c1030030140700c0c981e00c00506a481000159120008018024029042d00c00401c1e581c40d0419540204901d28104001481d04001100300440303c1d40b1aa040d2654078008007000001d00c0010608001d141d20341d80ea100d0400b8a00809101c012 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 307924919 1250 307923669 307923677
    0xc0308031501031b0c032106030f0b01080f0a0602090a05060a080121110f0414010902070b1005010c030810050d060213082a0a0317090102060610050d0b15030403 71
    0x610341e8400101a6a2000038180c03c880d04401c0e80b1240c1e0b503200030020300403501400c1000c000c4c070320881c0050200c01c4108403400310764074040012007040303545140c0121150094800c80d0150740ca07203004980700c2a5100c0c0554260b0f1004e010f02000411035000341000540c02441c506c0c84940c0c81011403110b43c4040018400560800014000380d04c3d100c1d9611490182d11140035031380da1080d6a42801450705000041c840d01096185802e20f03900e54008824032030070003454111a5030764000c3e400194001e11000c982c00000000050b446e208184110030441e401691030b80c0030303440151403e0390b081e103002e403440c0c0d2440a498000700300b40c0c0303866400d2000c017485041c005940308040700704044a041c1316004404190000c580ea07450004030084440d04144154840f05001100303000002c0c44600d460f8030040808200d80200090408201c0c0a0315009500ba029540e00e0f954007070400070014003100c0101d01091b41070064803d100300c181c3c85070f0060300d405400c01d14841e241c1088000103400841b0120006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 307926169 1250 307924919 307924951
    0x6130c11010606050f0f1303060908030910110702040e01060504020c0c0108063a021302040e0f0421050c0a08070210140304060506030a0c14010f090e0c070c030803 72
    0x10024491000204058504103040010612904c90b41b0b02c03c034910200351100108840310503014400e00b5000559015804001100140c03521042940040700c120b4120301442c4446030118049000707500c203c030030300046586000c00950801005021091480d2113965841d407002c80e0a4403140300908110924400401042c2901c200043c44030000410301e6000e0584403403507000d0703028042c00c00801800212019082d840300c5401c6140c1080c01e405020b03501c6602002d00c01c2c5c00050310341c0203000740c0741800040e0368a96180f82c0e4004030f80c1d8040c3c500a000391045290142c0b40b6071000180701c0d10500701d03d00189080c03040081640340010308002520b8858000424200310f20b0305820000301001c2d2810440710103c44030080500394000103101400081e10303031f030000d0701c0c595042c00000c206c0c6610a046480003070300e0710305200340e02c80c0d01f8520382c1c04510500c41000c41d041c014102070040354140320034000c1b00e40d2414420b81054002d08400c0340c426109034070101c00200b50601551080500c45045264 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 307927419 1250 307926169 307926197
    0x3040f050a03091e3f0605011406070302061503070810020a0801080615060901051b07050a09020c0a020409030507020d0b0a1107031707140d050a0f06081506130c 71
    0xa0100401c000780c03041c13940582007011030505000d0703005a0b170704650384038a800f1140040599a084024001d42004540d90b0541d08110a5601c400d050714281c3c07144528450340340007405441d11038603c0240169201100003010543d030341c1c2840c40d85100180648215542d80d034045850b01c182c4409050180d41c01084001c80c090303001c00da2500502c00900100418103001c00c00801f490303040500c1900500001481201d00d9000314200c1f45450402c41d1040141100c003080c0c50344a00540c0146480b900ca081000902c0b400d10307000762411503040c2e00c0030f404007000e2542004000c00c11068220240901030240300d0240c2d4a0f075075041c09840c000c1035801d0042c50420703641801ca035084006040d6a00c0180510800300741d1186c2c8013003000e030812003d004551542441501c501d08407186c0604204400281c01000c0401d5070041c0e0300070003542c503042c040808605045800c0e40d0351030041c0c55047d0b000040b04010903c1043c1d0302e5802c0a0064050380c51040300300c810724203643c9040c20001c0032070340903005440303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 307928669 1250 307927419 307927439
    0x1504020412082701050d020a17040f0201030c030506010e09190504030c050106060203031017070b0a091d01240e060a0305040203060a1506030209120708070303080906070801090203040f050a0309 85
    0x1e603a090303c009000e61240c0d40041c000f405801c0d000300981313a0102d03152010038040e0590140711003c4800c2103507035150910700684c1c0c82e800c201007280068144102c8010701d030301900a950044005845041d00c8039100018080c0d03268004000380714070401c55111204080391481040d0007140645c3c4c03034072151449070902c1d5007500c03082da100e0340440d8801c0081050a00351100f0b1a401e4030f034042511003c0c800c080301c13450310f005460b41014001c1140011001005900080182d045854010524040000384145c01c5072080c024491040884064400900800c4200e410122900c1181c1410300a0340421000700790160450301c5c114002c255034209101c1503140c00c009499001d800407405020700d2900c04400090311b1003505c2490309044c0c000c2000c440a035100307146182d40c02d0480702101c10203551080180d5031513a03940310aa000c50780940100741c0711f510118480c1d00c5602d5070344680400341d191980180c02580b000748152420245508401c001590904c00040342900a9640e4641c16081139580e132 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 307929919 1250 307928669 307928707
    0x11413050106180f0501050708072a0801060605031909030c060e0304031104020a1215080a1b0b040b0304030e010309060203130b0a0b03151b19091d150402041208 71
    0x1c0d03041c4c2c0380c8441c10040360f070f48403045500b0303135500140c0162a19241c0c82c081c148400ca209107a000c3d07005100041c5841584840301740e0460b03043e40024007130f003995200140c501b4881524030101c030524078654085c0c585460b4010402d941e1103442e04640318190398490401301c03843c1ca08c407402d09400000c0c04205205046400000c04801140c1c11841d200d440c0c54054410400280b040c40e2258a84030102c02801003102079800400c90704058131a1142249802222541149002c001403400c0000200b0b55020010070f990030703030303040c1d841c00c03440d58445403025203c10070841803950406484a04150004600c1d001460088107135840503036103107840e460408150200182025265850110074220b641d4001401182040500d1480b2a1984074005481099141d43c00464403a54000030201001c40600c240603101080c40e5403001201d9840307541c40c02c1652144206055110100c002044220300e008034000c0e962500144014681035803000201003203c0728030400c0d1454007000c039040c05040207d8082d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 307931169 1250 307929919 307929929
    0xc1f020c0c060a1b03021c050705011505010f11010605040207060213090e070e060409080a020f0607020714040f092004050109020f03010e0406140412030c080c0301141305010618 78
    0x2d281450038030f8500420000f606104420303400558003110041c540240441401025030f242002010564650054056070042c034044549610700106040080c009820580035104140e44d56210b022043c54211414240112008229581c500000034079076610310081c0000c0e849420003503290049010100250101c40c1e00c0800e290b42405110024088040380d900309480c60701544442c43e03201e810100d0002d0046140040040d100060311840340b640005040969003203020841c0c080c0d5640080403a1100030714420380040c42828002d0a03018586130b040703006110100343d00010300b14869215520122087c035502c41c40700354100048880b50400c0e00809000d4500e10f4403d62411100e405280410300c0305105034000301c0e071590042410807a080c3c02000d088404440031030100d003010b00b010b00d07403800b5281d50040401d1600555503a61402184405d11403440c40030750909580c47c120300341c0034542480c0c0060350312013001c02d071440d007001c641d00c24a0f000e00200d645403131100885204602e09001d1395000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 307932419 1250 307931169 307931179
    0x90e0a080904020a020106050d060e070611101107050607080106020f030f03010905070c08071a0f04030f0e030708010e0a0501150e04020d08161407050f0f060c1f020c0c 74
    0x10080410310600440340c07481c4090790700582c1c074900100100e0040045400c40d0790300120003a400d0781400140d400810700140510240d506803960b41e4400d44602494400c0d01e00580c005e1000e0b00c041c007405a106181d0001c1d0401d000303291540c43c2c5c0e84d0604040c41203c05601040d80900140403c0e541000f02d03000c60f038051300003585803104c610200b0100780414850150a00d0b280c43c0007604251203030819000da00c4e0f1251480391a118a46407400d02e10021203003550401c5680c900080f10010303401105809140c15440e01624402d6501c021180b000440700f109402d40b02c1c40000142c00d5900b4842c15810650079000307000d041e4968036000e0300f511040f81d00c04107a8040080180080e60603a802c46400c80d60480d44850f50391001d03d04080d0500032407400c00494212680500d090059580b440e1110450b0030f02030f11441c41c0c86a08101003140c2c0c440c46503030041406d51811401d0b0601c54000d0042d1510107084902c0203030011030540d00c47da83c0c210595403882c5c000c9034190b4000401c101140d694078084030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 307933669 1250 307932419 307932433
    0x170d08090f06011404090c0806071b020d150b10020f10061a030702010b090f0a0506040c050906070204020403020a080717060f1f080d230313120201060e070801090e 72
    0x6072260703500e1041c000c44000700000818826150b40d19032248031420f41c41020058801e6565502c25102c10b030845805c0702142030681d0480c0c4014001031100d94003980242a2045440c0e030780c480c1030303d400a001d20f000300b9030395079620510141d590f1202d5541140d9245c0c02081007000c0f0030344260030300814a0544042500b402400c2c48030001182c0554000b800c00b5042039100d070b60324a0100e0141c00024859900801000305124060a034040310a12903101200103001070f0b2030380018401100c00240341440040c3c4213009506540c606600140007450000b040941031949030b40018800610503400920a64080c01c41000003180840c1c2503032540301c0309009048903107443d60b080446840e00808821845840e1100540c07030002040098010388008012580e100201754006000b01c001034003445014100780140e0445049500101c034030440d5012807143c8440da6950303540b5030300345040c10f80005554940d9400300c0c0d844241d842e02ca101e940c0c695900340840d454125080100c6a10500d009455040a4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 307934919 1250 307933669 307933693
    0xf17010909111c12020304050607060e1e0705060a0c171b0c01140702180f06040b060f0d0213030f2004150312140304060204051005030103031403040606170d0809 71
    0x5a00f07082e016400c602d4540051032007880803400e512890b003190b40d0106010910b801031044986c01030303461803600b01c22105000034254041c022003000b140c911003640e2103030600344264140f1101500c8408018206446e40050907541c942d42090048249491032a001c03902c404040d49811541c1e81d0aa850000340c284444013400007407d14618962402c10f01c02d0024241c0119200c20001c00000c1000d000700481500780010020f17500c03082900c0343c83c4107504100d0350504516000003141c0048201e040c806282c43c00c03000d001c0d0042c2d0403d041d4031320400a14603000003c1804030500c0460913110350488040c080c015145608014141140c56000b54038240044a54982c2040c500c426a0703080100300c01c0894003001c048450a0314200841071821000c0140410040d4540142040d1103045506040d5104901e404981900007480003400182d44040240c0020454800850304180140d00208005850b2007080c01e42d801c102d2020a0036134086c83c02c203d0429400500c00740c00075a85006040398002c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 307936169 1250 307934919 307934959
    0x3020601171b0f0d120212270a1a0409052809020604080d0806120d0507080d1b0806040c02010501080a020108100e070f03050c0313030f1701090911 65
    0xe0710801c91800722808041c2c406a692075159004404010a8024000c3c41880c00d4000c0c2100e50700400c1c0544908403104a41e2030501050322140045403500607010700d41126882031031061070392029044040c0e540003040e41c2da000c0c0c10404240c0400103515641d00d242a00380e000300c030300007066070380d01d500b049660405088003151002e0b07444034460000700d0540030a000151480c03140e40d00109607841801018008560059040740c03150604130380746a41804602c48a84e2101100c040d02d40c0003c0c82042180002544200a08600c05005400098003216904031448034003180d01a40c000c074280c402000311714585409224000c900901c002c0c0101c0d45407040455503a02c043d40f00a0522800700c001441204500b618170b00100400d02d80d001c0b81d030400540c05021543c400400d800041e00300340c0000c0d03008501204507030141c911a2080c0345840c1b6140c0342102d404c5280d460400c00c101c460120420f0b90072000b00910b0181070300040004881c00245403503488502d82441782801b404000700310346109411 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 307937419 1250 307936169 307936183
    0x2802010c06090c051201060617040c0b0d1b20070b0904090809040c1107080a05060105010c0602090a080c1009030809040518010509070e070528020a02120a0302060117 73
    0x2014401044400d00c0d40b0b0b00303e009200c6a00300507000311190341d0a0408003c1504200d0886005031160b000c2c441d24031030000362402040700d020300080050302041003072205800090420181c004000100d420041c0070780b00d001c0700f070b90924000142d8444e501300007a422207030016942c0c0805000604000349014512103a0340540d10f4864804e40d0350712821410300401e18111100c4400c010020002d6010064001d00030320300440140e4074a1240d10000310f0581d5000602da882603402c0001055103a20389030044a4600f840442290722903000d014601442e07c80c0c00344200a02010740160240c6030401c0107100da40c1c3c1041c6000d20400030b40d10420408a0318440440b250391509940c0400c40385c1c1c0300340e1f40140d8210400e1b50000b4a6103003e0402c9112300000c14414203507106079030f0345d11031901e540700e04440ca80500417075441c1d503881a208141d201180640c41c1c1164481500544000418540024540900c4030000c1c1107142c1180d080b0508155060208a014055641d50140300007540c1120650320a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 307938669 1250 307937419 307937423
    0x6070305070e040e0105040c0b04061205190e1c0302040b03060f010c02150702090a05060603191b031a0301020712110a06020f070b09061306050402120304082802010c 73
    0x2a035480030485841c80b40c920700c0e60155000e0700c18803940480714403a0707000300412901550908019040410501880d400f04c1d01160b403560b0f143c24243e100b9110140c0288406003041e0351005250141d00b12101c29806140622003603c4050403c0e0b201001a001c1656500320045041510421052152880d4202920340207042900d070b0200c00f24071840140c44400d101070010758004001030341d086040d0003400040c0700c01c41c404d5880c40980c1e00c4070901c600075206c0c2a10155031140040c80050078001256842500341e00030068041400741e41110401e00341e00d4140c0403540000c0c1c40741d1803100820260aa141c0c023014040d4004c51602e5080c1d154480c40d5800c0b0082c40003001032020b07503219034070410030035440040e4119604554845d24114582c1c0d41c1d5001103001c485008044000503c442000b150380e0b4810181017180c40501c421941d943c0004040041089900c01401444141d00c0c4104201800251144000801e15190314204066039040500d1043d01150001080080180d03408160610959 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 307939919 1250 307938669 307938671
    0x30415051b0714010509030301150e0105032a0a1701080a080f180301110d0e0c0a1a0c0a0b04050f0d051911011a01120603050c010e13180b010608040302060703 70
    0x20b41034a0164408400c0f080f0f001029803c00061202031040480207504031200386020230900c0b07185102c15100d5030301d07180780d50740824000d02c0018202502200008110020361800c82c0c0040120500103046401040002c00000d80800b03403902c070040e44140c0240945207110040401c4a5299210b541a00c00c21868226018012503564041083e00401c1c140c2b4080081c020300450840c0c940c00b031034030b1304400120109203050401040210001043c0612a10409404c202c410340c280301e0500e40d4a01000c40307021a02c04104010007443d4824004016801d118024004c82401c113070800d5071510b141c0718100c2000e40c01000d01c000c6501c0e0020200c95007500a081400500070b24841c0c1038138080c1d40b410702c403a12542010720414001410014200b14140c0c2600c07200340040003100303950111381c480c0c0030040540c3d016042c0d0040c150300440c01640c00710402040034008010310b0200070180e4034914000e58a03404043d40b69420015078991050241405180002652400c1d8070000e55428024204c1808c0c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 307941169 1250 307939919 307939927
    0x3080409020a091a0904050a0515060906090406030b060307150e19080f151609030803060607150c020d14090411041205070f08121206010c17030415051b 67
    0x503500440d40d51000700452807511180d84c060405140345580000d44031407181e841c12000581d201c8191152900448800400e03040c81620322050060781d9104207440da5224400744a01041503845000d54806188210910840b504141007810314000094204c21142c1030840e51005c005d0b94080080b0907007003402c41d6031000510b4460200c01c0c034440d480e000aa818000c00240d01314100000400d44080360074010b03040300b940c2c6c131000803e50392120708510200040f201c40d41040401c2c40c60001e542c1145004001d94030700350f95a41c4410030032404006a054032a141c6008841440d018800c0e04103034001400c0c203072020f4a41d41480b905500c07c04400074851940c4031482c023080405241518050f00c81e6815040c034401c00c90130078941d03940e0a0303c1411100c00b50303202c1c08124080040b6640b41410400e0780f03550308001800b00d00c6040c0b1203005259604011030000403202080c062039030810111500741840303a50703003480d04148581c0c00c4d9072061140b1060800090080c0d000c5008a1400c0310f45c0015a0203480f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 307942419 1250 307941169 307941187
    0x3020708120613090f0201020c0f0a06030f1d1605090c2a011d0606030a0f1e060920040605030316080702090906070f0c08120c070c030c06180308040902 67
    0x503400f0040c10815840d04c0c0210200c20840f04150001e0360383c0c000d03001c41d8000f03c0010f0800c01d020110a0366039400074080c0c45d04010050080d0400035000c1000f12005c110083c01803171100d282c0c000c84100d6140c561051440000c560403060302d08024002c15181c0c2c100c0b901e0840c0344207005101c0c4d94580001201c400031000300401c0414200000307120110024440004c07440d00c10941280000c1c04641a4041c03040460721a1800003119204c2c1c0340e01c04400100e814083c1c460f0f5480b11603d160a42e05d1801d104c450400141c0648144046d0f54898010922511090080d40c1215142c3e0850b080c015440d0480c10b2003965030000a5803503011508604184114152410b120b150056410007908442550244042c80001250070b03803281c50b05994490941d44140401c4480f2012007c007e880c080c010041c904104406410440e4041c501e00c1c0c0d610714000c01ba0b603c20b40b0760385083e442a01d00703000382c010500070746034848510100344058019680803241143c89160390b504c40c6100b01c14600342c0c0002c40c551 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 307943669 1250 307942419 307942429
    0x70201050912011514010504240c1403190203090109050f130219020105060612010e040206040b03190f021e0a14040f0602010b18040f02040e0706050d0c030207081206 73
    0x4140303a80340c00a00c01a50012880c41e00e190082c000d0341105041ca1442c099503507c664160340481c7c04602c807003000c2c8054186000c581144019903801008170110150000c0f50080085040910544000316541c41c005088034440400b0300910108640040200c11820f80e0301071003500030f6590490f00007040c0005c0c8000202c8241481c908003405034004525494949442500105001481d8009001d00e50f10002040356a11035001d580d400d8a04c104010300041080141d80b55100c0e00c080c01c030524141e110032200c2050307001140d100400014104d14034034401c049026503117116000400a60600d060070703030344c0707001d408950f100001103a6012031140ca00c2886041c4510204045a03245a03a45450705041c81c11070815000321809582015131011392801d04238103d001c103060108019599440c2ca0f5150030782c5024400041e40d1160320f58214141c4200c09001c00c82c010200d13070700d4031580c500e403051140c4152440102c4400604d881030204070b0220303982804461042e910001c0c480d40603514803001038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 307944919 1250 307943669 307943689
    0xb09040b090115080304030c0e100b073201200d020d06030804060f0216030809010e030c09011e171507030e060109020301030201110c0f12010b190e0a0b060702010509 73
    0x412103c00b884000424440110050090341d0240160000c890b4444201903200f0000b0fa8000b50499112142040782443c00301c003404c0c031103100303510343c0c0140c44a441d9160a2030400ca240c001c408500300d8500a0b05800c244111042200c01c1071080c4000051913809218500609801044990300020804001840380d44040081c550101055071601e44854000740340980382c1582c00302502c50341401e0810500681c11480440340d0004009203064242e8004581102c41340d61143c1c2c051044a4950324556242c0059501824803480c501c030941c15400ca41c600c0c8100241e1022207202d2148480d00b04160004c5005180c42c030454071101420340350140100d0040000010b42d42d40350103a440007040d807400b10740046040342d000340d0310b500c014041624180d4888211442d02d55025842404076005030500c00c440b810303c090008000a0354000680c0400d0100d0380c101d081d80315010005105000394100038443c540c0003a0f070010704105180844001c070310b80e071050201c0a414020046244121070361149041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 307946169 1250 307944919 307944941
    0x1c1b0f020306011205120403240b04090b1006081303140705120909150a14040f230f041a040c1d0a0e011107060921020309010e040b09040b0901 63
    0x807045980e42c1c0e201c1e90354250050b9012643e40c01b4440c00c40c8100f0710954150713411361740c105544801f6612404500f0074603075204038005003101e0303c51580d00c078039585034072642545a014040c501043d2078081c000700b42500054009000b8010200c09011420b840140142d52945c3d160400341110031075100c803484980240385008000340f0880800d100d000050340f01030400c8803025161016540c80314980c40c001481c215038100c0d0050078011007040b043c040461000101c1c00701401c00244ca10b4080036100540f01c0e00e0405030b9402071202000720340100348808199105400754001015401c1c65920700d018a101c82440c900c0324000300000c1401d010380384c09004010308141984241d40b1181d09070407000844120794501d0303201e00e08000310450141c18010441103800c00c134101e503d08003c55640d4001001e2200d0190758504007515020651503501c07000f0148003095400954079807003a4000149150500700009010b00d00b48003046085480d0b10b95500d400980c0100030324540c1c1da4450070240107021a40c04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 307947419 1250 307946169 307946173
    0x3081306061203020c0f0a030506070f11030706090b060d02030307030e0310021b101a04112101090b03031c05040f1205070302160e01150923031c1b0f0203 68
    0x44401010780001d0000043c5501b40d5400400c0c400680c00c002c0568980c0c44042c04640003400042c1040f8030402000c5143c0c61035013880c03040d21064a0001e480c0d6002000c00325009552041c01d40280030b80840035035886142142c0e40b00b504d80d296404a92a8029000000c00340284c0c080006515a003d1001558942c658001151921000c885940300c03910301c104c20110034080d500442c1d0820b0101e00a03521318142c0000d4454120b40d00c5001d000c003c200019840342c2821003445002c0b20020701140d0031100d100b0210306096194185038a03202111220501c03203100754000c01000403c000c0c1c81540a80d850a6450b000481da5a141803650203891030290003040c182040f01e5401c0b0040d08800034000c210301941c00c60300c2990380400c48041e00c02280c0a0740c1d0101428200410004880302c1c514001510b203450a047d455503154800c6101c02c40c140344801402c07008405c0c8a08a040810400d408141c0341c011500003c02003c4000e03107804e418040c44140ea00c1400c0e080c41c24032030b450f11109060760340542 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 307948669 1250 307947419 307947449
    0xf02030a0605040f0903021c12140105030d1d01030b01050904050f091b0d0f0512040603050115031407050c010905120c250905100b16020a09090308130606 68
    0x4800c4028a818001c00f4851403610456100c0341d9014441c140000354150000c7c66144008580c001100d1100390004c070401401d000e091002c845507024011044041e800000c0c60343d4100010542403200107a60407040244d103100124003407022019501611100f801c000078450441001210940305e1410703100d810038148006d118034101640d40d5103105900744070030340d95054400e0000c4032100781309c8004654421140b00c0a403000c1001d82603120041c0b0701c0341d01140e1035801d500514a01c6a003140c0d001c180840d6032130300100708003985488084a00b90b4146010442d2907840c0203c0c059200b000352485040200c04200c01c0c8a8007401d600c007003455600314045480c1c2484a440c0c03222598007041e2842c48074000c564294080c190401c01c80c1c4542812800c40841d100d040ca28003000500d40140907031040c14400c680002c04083c1000140034020903500203400c030340802e0050203000a040c1d8440607615290100c21408683d00c00500754200740403040c031240382e00150034003002a000c0d5800c50b00d65240710b04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 307949919 1250 307948669 307948681
    0x318080c0a0308150a03061a09040c050a06090602100b0f060409230601020a0b04110a0b0903060903030c090f040204091d06090a0f0f0c03171206030a030203090d060f0203 75
    0x40e040701151095031079000559802003034a00000200c054541c1100350440c0c03e0000a020343c0118070032446006540c54612600000200002000d550660f0300b40c22458081c081402c102032a03901511050030b000001c13618103d4020b5460794400284c0110356900d0900000c26a22480302149404008080c90b403995143c0a400d401030a8440d00100d1048910b184084450210361400f4400e0205130050b18102d00151500354070580d00500c2180c011f84006550070b09a650260182d0140240c84040c1d40c54070041c0090629003000070b040110303941c0c17041c0108a81402410100c501e41001580d901c00f8040382c800205010703014640109914034140551014a05140407070019608101c00171108151030310320b5120746030700302c0d4070024050b012112002c001086020500004c803501c20101c5104049d900d072555400c00b00940240b440200c03002907a0702c100000c100c0390030f4004804401900f840752180d500a5a03912071003000c0350140307000241410601c030701984013064080201d0320a6540349044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 307951169 1250 307949919 307949923
    0x302040b0d0215090307050a0503060705070f021011011404050c0111070b28030b030d0e130c03020a180e0a0c02120706060e070e0a3807050601050315070318080c 71
    0x130100380d4003d104a100002e4035107046000042202c00240c0504402d4480020481d15580240c2007174400444203021200162640788541c0d41161569403a0394005508c0d1249a080d20510708208a10450510903c40401c40109030301807000000d00700f400d061a030100c000c50414046074020b00710303a40c003c0303035844080030200c140842e0a0384000b0764411950484406400b182c042080d0740350164401d000c0040914019100c20b9140d203802400390f150101c0c54a02207056a0404003c200000d0300800c0040d0f480c1c0d0000034626502503040d41000300b250030407800c80c2c050407000342701d0003540d510751070501403903802480f000320803103038a440284d500e01c41820464007500d442d11030041840304040c0041c898600c1501d150081d00c4009256240b45481c040c00382120b101d0118680c0d041410030064003030441d49401e0450445c03407042001070b40b07500d0581082d504108050740320310f009802800c220003000f000503c0e02c82d80048103040007e07185013007110400490118001c020201f11001401101030440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 307952419 1250 307951169 307951177
    0x11a03192d0911180a020f0706050a06030618050c13060e0106090602070e15010309020102010e0a11270a0222080f160617091212070305060607020a0302040b0d0215 72
    0x40c100d42051031682824070403103404c0800264030504001c00401e00200a0340c00500303500708001e2025090184503121002115001d07995002159a1580c0420070400103003c0d806511412000f400500409500d50588402c1c001c050103108aa812040d140c2c3e6031001e80c008c04c00707040070044a85243d0303100e030ba002d41205500d00603040540700c0c0410004d2052030000d0194443e00540301d40355000d0407400f005401410040c101203040d95220854004080ca041110148640c02040000288480780e03090146200140c40403140d60003600c40031081c2541524000b03500400401310040e40e410449042c03400c4c0c072015581480d0007050b8404002414240002c001d07030b1660155027503a5010038460111005a007083c480c2c0c1c0041861006513408102c0a02d904a81c0305500e8000c0d5001d12074034405154450303000c04003440e08544007a050128566142c07040503805401591003a243c841c13075400191081c201d52000912454640300001c907540c6941445182e5942c0c00f03042049803602c02e800421035904 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 307953669 1250 307952419 307952423
    0x50a050706020f0313031203090819031107020a0605031803030408030405010509070312140c1207053d0f0507020606030c06070803010e061c060203011a03192d09 71
    0x200c1e0700f07490f075503552000c4203c41c0c4800e01d500c000b0021505e1541d03104c1c2040c18040400050660b80c808001c01b08001030001c061038107800d40e5203a40307580c1800025049581c5c24102e401e048205010300c4e40180c40d40c07050041034440c0e90500030b031a5a00d000100443c0c51450411140600010080c00700300200d180103940600d00c1103000b4095640c68540a036954803d510018052816000c102041e09019401c1c041400c5021a9203e2400705010400d5107454521049090340131130021390501402401e1220020701401441128203485841c665605d265480060780c0c0c50f405131004d2142405c1c1031035801440981d50402c0103120f540740c0310501940b0344c4000c41b0110301900800003101c1071490482c0444000c036034881d0400303007140d00306030240d122035800900c81504019030004c039200d00300c624200c050355144101e0000d40d90758100525000c18018585842c0f103601c00030720501c485001d0b01c4c4040c035001800344400081401c0f8140100c40c044603800051000f980583d00c04d211f2607405504410b000c94 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 307954919 1250 307953669 307953673
    0x501060b07020a05060306031b131104080145120909050127020a1701092901050d0c021f1505010203090105030703050601050403060212100506040f051c050a05070602 73
    0x182c4d031841800114402110340d19030540044458800e04a060818841800009040465180010310312a0101d40c0b0309aa8890b01c44d0b008a020170a81d0000d000b40603001e059000700c0c0c3e2902d40d0303003031343c01c090020602e202c214060300442900b48410ba081039024071950308186030084a034502480608649004d004100b0110705007400482c850402c01024600580c0c14425022124041c0c01c0d440020b4104d0701901e004c001c45000246004a242c14119018240c610000200104400c4150328401c08450103034400000c241c10080c2130ba0f80190564181404c07550010401c401152b05c101e007442c91807a40380d6040c0b480c920309003418075961360215910611000240c1005c0d40c4440040e640c80c001c2c003103403c0c00260b0400000314501e01ca504000d81283e018101181030640301c0e510001680c2000007032a034031141007004c010180d10b44421f000010001a40d0042c605070526223180306142031030003014040e034070041401b450743c462080040d034015005415183d58120a1820a444000ca8410300f0014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 307956169 1250 307954919 307954939
    0x5040c0506030705040603022a0303160813020d170d0f05010504060b0708130b0a0f0e090f0115090503100203011a03060f04050406140414070801050f0718030501060b0702 75
    0xd007408822280a02d8042d00d681e82810f190110841c042d50040c90420040b003604480b041c42600780d6003080504803042e0004d5074491910301240d49502c00c01001c0201000411420300c4519030101031941c13141da40544141d0181c04541c10320360703058210082105074840000969168044155102080c6c0002c01c4c4000d012a0340d8803001c1000740c44142c0900c26403a40700308140000204104014000040d11601810b00f0f950384100001c92074014900c040003240d50300c00515000341d0301100100c0b01050407a80264039081c9100a07001400d8140100c040604142224441e683e00541c1c03000004c110003000c60310744407208401e800113074100384101213030485420320071801c1c2c54120084e00e1181d507001d810200c43e03c14280400c00901350140064483e03d0b550058003110485a44407580300e1400303a09800b819889815600d8030785022940203203450b92500302803048450300650a01c2d004090b0346044d48542140741108405a2b6507507000034125841d12a0001e1440307001c0c0041c0c000b01d03000302c80000003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 307957419 1250 307956169 307956179
    0x10603060b0306090a0903090b03190e0118030509030a140a031b050a020d0c03061d06070f021506031f0b0319030e220903080a051005010f230d05040c 66
    0x381e4001a20582e0f4852041400904880315940c0500e4510303002c0e18244800d940d80d0b6000e04860340c0213481602d003948040407175000100e074074010b801d2103070f00c001c0081044940c0c0440e1032003c600310b2000142040000640c28086a40400002891035080031002d9044100703140c2260782d0300d0708408c017200407903a156039400103400520b00203d0401d030007202500220500d6030030020102800074084409075080030707000c404142c841c4203e0007030300c0b940180070b9150281c00e8141883c16000500030400c00c10b204020294207940842d44580150f03910003000d245407100b0b40005d09116500b00402c04001050b01c425a140b072207034010300303ca510294103035841c500043c000c48009845640000d0049202c80040c1035503030401841300d45692070155000a180c40c003011040c02038401000c0706400144809092003040062842015000702e0305541d4808141d14200020b04180c245078400402e002007010070142c207611075000502c1b0144041c14644d601c415400145008090070395098070310180e034800c0807403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 307958669 1250 307957419 307957439
    0x20a0e0a150207031b1203051201080309010e090a02040e091b012d020c0a080c040609050610050307020309030a06140a0c0503010909020607050304090c0809010605011205090a1a01060306 82
    0x2841a04076030181120784e0564403446207401c100104c00044440110b00080c02845036418003142c01d210741e484d50359502c0d01c0401c0d103200c0001070300701442d13035041000100b0b016a0810217030604658180c0300704043c1d80d100d0301420000d000e16030140464111000c1006000c4e04042002c50060308076a00d503040f10282e20300116002205080c1d07061001c44101c01c490201f20001c288403143c10440d10454050441d6040030409411159103d861b09910480c4c414400c0c1c503103400303003501403c3c00f50010400c502e0a9030018403490f1543d03041070b051020000200f40c64038401d004481080d0405800c0f100e210141e0701d000b400030304294640510611031000412801c08042c023608600300da03980d982c0c038110303400e0443c0e000051480c0c07982240d00c140204004400110705201910051400100010b05038801c00c40140c0a0b1000810141c0944d16000c005d20083e80c100703030303108400d000490b80050139590f003050a5252400141d0f000e00120030f5103003007202c9000c00c40742c2d40e8182e4949a40c10700c01190745101c28a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 307959919 1250 307958669 307958699
    0x703021c060b030606181f0f08090a0f1a09100b12060a05090709060e0603010507050c0a030e0103020d1a0f0103090203070b0703050f04080609011d060721020a0e0a 72
    0xc03410070b410000b240300c80c5440805044150028400f404641580c44005000303074480da820941848000550300807401d130069409075508116040c034409503d450215a510b40006800003003042038182d42260a1082216641300d08c0254040d03a200769041c081d8809690700c0301802040c2ea9142071030701c006914240f200141c015041d00c08001c061645540790b00001600717005007140454403904c1d40000c0d010b1410f005180040c0200d814031800c03030404000f45425940c0041c05141800410841c425030540001000003003260035281c4801c0019503103004070046d100302c243d120129410f0680030a000e00c1720010000e1125000c552505a1025800041d800d4441c546006549500000c604102c180c4485e002410100e10a2034200d180c82c1d40449102c0c8280c20603040b01c1c46560100040044150091042200080314032902080d540c499500040d5600300080410081250480152031309070716040c280c01c6d940d95045010f41d21941e1424004088986c1c400b8664415108100001001d2030640c10013 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 307961169 1250 307959919 307959929
    0x60c03111b1006260c040f0f0b09041203020a05160305090301051b04031103010e06071e02011509020901031b0e0114030702030403080307090807030b180f1b06090301050703021c06 79
    0x5140091307081c50300141c540e24540304800322400380c072010358401d95580c0b040e48015582e0791000548000003180e080120381551034050301840086052001045481c1c04242404403e450096034070b5950090885450140d200d15200d0400a03040c10400c051f0080041c1403070b0982a002004556100600f041200c40031a80654041d2010030080c40825000c2d51450440703034003c0d00204200c14640006031074030108803940400916004d1f4103603140b040d000040d0100f88a5440240a90f000c560340f0b1001d010b04500c11b035481640c1c001100788850340250441c1d14814203894203000f0701806c04001500c00d5800d504102d00280d40f64440c1203100d011101501d00903840c80d40154201800e59462100b580d00250003803007405810400010b20100800c2649d000c0c52151604030b40604103824023125094142c5040c542d290410445d94990351000504010204034407070320700b8661820b1002081c0540315001721187c05508100c01c101407aa05500100001000702410505010703c00c80e07400110390003400342c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 307962419 1250 307961169 307961189
    0xf09010c09230312070606210309060f0c0203010603051608011812090803030109061401020607080f0c07050304080307020312070803070e0f0402190305070f0804060c03111b1006 78
    0x40c1941c1414410300d1185500b030090704072610790040d401040142d40041004507680354503910309101303515803c4003804800b0107072001c103166240720780e07030181ca00038480c000c3d04100030501055640e004e11a038010110190050003c20100380c807424099110f0007002508811100c401c40d0015080c50144220501001d140190a0140c191030b60f80040e60030f1121a072208000a0007004205804103200660083c0041c000000d030306481c054094000e41c18a011003410b6400a00030014141d4005910507480001c00d200c4624541e601d2248496902030000c01505911020501040ca04400001404c100b80210126000200c038042e40c101d0600c143d480042c0404018070105480c54090400154100c0c00103000d40ca414a100b0040303801ca0f04800351481100405c4031203119141e805215042d00608c035442c1000c40450b80910243c58541c02400007032249955944450320984640c0c08208031403a1521101da07188003a41ca403540d1301007203c61800c40c5000e18840d11140405601c180000c0b900c0a000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 307963669 1250 307962419 307962449
    0x220905060106020d170114030124030c050904020906040903050f04030506011a0c120918040f0303050a061511070e0c07030305090106050d0204021309020a05041809050a1e05060f09010c09 82
    0x1160340800c205c4607d030f41d0159201d4034004170942c0070920a1200c149040d0b6a050400d1950405842d210310f180e001500485060061002603214106600d9004505a070081558a681d20701220641b0840281000c07850000c078010081044c00700301c96048550030f0901314400d40c410a0103031260710420302006031030f0b80300030400b05d4120384140250174584402002001213102050b050b0321840b0381202d040b80e03044020a0b2a03410141c052085903000220715008220781401c00015480e0f10701078400c050b00348140724215058441c410050203000e005400782035650350600c804040c0c42c82c0c21082045003c2402c182c00100d6a11f014800c110442d4001009820109002d070244070003540081c00515015103414404641104640000c2c0f219140966401e552230f071500018003000b4824900d03142081c2d007440c92a20200314001803500400d608010400d22060051580e50b03010104801d00804500072035003007003581e6141a0030184541490802404080076481048940036130500800480380b840c59 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 307964919 1250 307963669 307963679
    0x1207061d010c140a0c0b220b03130c15020a17130303050a020124080f0303240a0e0108060a18120807020c0d110f01020303010b09220905060106020d1701 67
    0xc865600c41d069600c01c0c1d80340748005445e241c017000b800303400000d040c260010345001e40b12880281c0b4104034849a03d188070079402c1040b82c0b862840080c0c203002e02803a442c03a9003410321001041400c007e000d41160b01c01100c8203240b0180d1180841602a60307803090501103645018400011140c03480d183c944501c4582d41981d5042d503164002c4000f4900b15075031030610f0b600307140315003240f55900302d47c103081c0158003031811451900e0007404601421380c0c1c1c1c0090003444070034036400348008103091600f070b00380c1d51109001d8045203914020b40d00c8a210602540000030703110302c012a0682c000e0100c01e009000c000d412420618681401d03403c0140a00da02d9110480000c0c814404103401c041c43c0d08c1618454540c10000070700740d112129090710f04103240441e80129252a03001c034007030b8460038005181198034001d10b400d214007c009819005811040c1d001c0101010850301c04090040301c203003008011424207000b652190240104005032240d08280c502d43d601030414103d080c0c02d0b45481d111076130700381 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 307966169 1250 307964919 307964933
    0xa0f0806070f0314070c1502070308010e0a0b0303070321060302010e01080603010b1011060106090b160f06020d09120306140d05010e03070308090601050a0b07030c030903021207061d010c 82
    0x140c2c8400040680d95030009403601d2428000a010707245558600e95442c1203030511129448507041103030311180c07040004500007a04051907504440420316204080e40d1200c4011000c0c1400314510382c0e0501001507614109600585031056620f004031212400380080d50810b401c0b1122400007030301003074440f0758a42d40ca42c401c61500c0e92100d4060004102c105080c004250340314010800c2c4c0c00811038025014500c0c0008010850050500d49401045140381141182e018807841c2242c0da40c8582c1d481d0400309005e5902440c881940d40f09208542e0303140255660801010011000c4541d2403180d044241850300c80d000307000540e00009220f07080e4140340c004000000404800c101c0e1a5520384610002149040c00604022402600c2d060607501e0800311050030008141c12944c400c209120040c0300700c841104c19275540c4c03540750404901d21071701070a050761054007550009600c000d0700d8540307502c440c20100c0c8980031111280c4072000402a107641002c180403201440a000855852070704c004140c0d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 307967419 1250 307966169 307966187
    0x40f050907030b03030d020409051f0506030405160e01030213151211030a03170f07050d1d120c0c1e06070206070b270d020706030e01180507050a0f080607 68
    0x41d40c18002400d0426a01007400e40d0406000c20710483c3d4040f82c1000b04010501030035920425500c00f0b0341503807420108022804003240140c50042c2c00c00300001c0d0030000304100c14001d041c030703460380200c3c47c40c0d98960030702c0100000d020480c001c8040030480710b0304074003074001c8e56140c2c2c55629801c0c0b501c509156401e60420b94040f0280e402d4145002d03d013020b61001e000901c4014040e9807040381e0750782c10400d5107a07408000b43c48440740000010802032156031040c02d40300c25840c16000032800d03030f400c105040340c2e84085240100a6025640104411a580000070070701d02c04c4440554440d04510702c02c00010031744214448203000740d40b845120291401500411302548020001d50401d00c0a459003045c85100f100c0343c51040d10201c0d212103a082d481c00411400d019110f00411240f028904002d490707401d903120b01428181c40e031225900c640001e41008500c0e10b0400e44d001d10800c16414000d54680d0144207203402240003520229400d201002c40e4015903800800603c00b50701e45440464131010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 307968669 1250 307967419 307967431
    0x6030304030605010b04140d080702210105070908060a0c080a0c020a0506040f050115080a02040b01090b070309031208090d0e0406030807060b0102010501060806130902030a0803010605040608010803040f0509 91
    0x400c4003000107455403141501a101400300951502c1c00c0103080700c04010300e81d4429101340007082080c8009030036003007201c0c0302c1031b4103036089148015407441d191003056611200c1d44880d420b010800016550000f600c9044504520448200d602c1c1c030200c0a04403140030381c400c0005081c2c41c000482d8000d054008401c1034a040c81190721100301c40e115076080c13580c20f45040310240035031460001072120900401034041800400c0c00340711817030b240080395115207080009000d00d441d03d02844660b80100d240c6001024000802c6542e4140c6190061070141503020449a060442c1c4a088010307100301050361146596a0082480a60385401581d000c40c0628280ea0b020351078880120008403440064000b4070320460f00841c020350340f00006030a499058001d01c040140d0030003007142656800c446580d000c190354000296462581c00824101540c040c409406000c000000140b002d51200042084450f25503520000c2d90700c0381c0d075083d01e82c4141c1c8161a88544515424032141c6032042c590341d0844 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 307969919 1250 307968669 307968673
    0x6122a080a06120212070e13050d08060901210503030a0207020406090c200c060a03021b010b01090512190506270a170c0706020f010c090305031b2a15030702150603 72
    0x6580c0d00100280e03081c210755450230300b4400000d0404000c403c01c42d1132505070017410100d003140744c818042400144144900305015410010040c0281110715a525501d9041003c1d40c0d524580302000501a42c0308a00c100e0260307141070702c00600b5524034031800000110070340d600c02000c4c10307800440300d07409903800c011503a40c02540d511042c5c5640f600003e2110040c280c4002d42c41e03814403555070040071123413407105c08140d0415210030070030303a405200403007070707d10132a450508185480841d40c50102d20200e44003240503022002d4090107000240340380301c1c102901c0c0300303011750005034070300c2c009407048a41c0c0a140794442c05c107480001e04074241c1d42400040040703c55027000c194080140c41e000309a880b0001580000c00340321b006003c203024080c138142e440c0c10300d0400c80b031550744d40c103a07640f00e44060307a4410032002040814052041c401810b03c0a18141c050980c0104208080310400010300d602d441060000c04001030600c2010030b4038814a0340d500604407a6004100021440b00b000300501d5042c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 307971169 1250 307969919 307969933
    0x1205061501090f0e0412020d120c1106040609020306100e040602071a040b0103141207020405070c17030601031407020d08040305040801090b0105030607030b060406122a080a06120212 80
    0x918610400f080140b0790710700c0c400300500b402e04103110680f544080403011904000e1031008100c5c2c1080a40050621401c00013400015036031040790202d00c0152284030600986041c001400500e0b000b1040c0385000b03c064420340c0e100c000b8007100120b854800c035444072510030f0010700820b425601501d516806070002c8c0700ca55100c1c403a01240d00204036411940104e80d880144244401014440c04030107042004215100080961400c9806010002481180c907131001494082c4600b2035090040e910400300b40c1600030007502c04d843c03604119000360000340340401003902c14980c05121030107881650041e28211404500488003500b004100ba030030f1090070000015041000d00c912000c807802183d000c112541000f0030076081c400003500c054101410039003070203440c2da2158105c5089401c2c1e400d00a0620462500c150302800000805004d0404c40c15010f07100940c01a254100c602c00640d40c0c0d5007a91354210707010040b07482c2805640c0800e6a4241e500c0d0041c2044246a2032a00b0001d04503444 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 307972419 1250 307971169 307971179
    0x90b03100b0c0d0f1b1b050607300e041a03030c07030314030915091c0e030606090c030604180c120c0603110d0902010507120216120506150109 63
    0x69200c4002000c02d58400500381100c0f81c2d0000c850070364041c403482c00c0b201c100c0005d429940d00358414000640040d2a80e0034400314044004201d4001f0b01020b815035031500c525007810030300342c080d1300f0351880401030305655841640c4040c034521900400700e80b6038006011071042031000610038601102c80080780009822465902003019281c0307070103003c00401240c0e041d4900289000041d03002600468810720034025520f0000c2540c0e052607040000503941d550310290074900d008036078040310080000760183d120311542c0c05035400c0b082c000d050302282d141c1d4903003070f050003084081183e088400c1c080610101d031151500d5086a00000c006c0312590320b161200d074440f010000b00540c000e5120380a503110041c01c110854507403000802041c01c003004036902c09a00c0036004d1089201541160b6529949c00086a000f50242e5082c5a04007805044c4031450030000b0359120300020594a20001c0c003180081c0d046001d402420b84564410060f100399102c54502000c00008003424905001d0b44200c0898 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 307973669 1250 307972419 307972439
    0x306220c031104060501021b010f02120d05010e070816050a030b3a05030306010305070c050d020f1605031510230f090106020a0b10182307090b0310 65
    0x24500505141c810305684604201c2140c4c52944403034155005000e04044039a411901009640300c2070800c941c1c01ca4040500b00e08000c00e803400d80f80b0f014001b0030212058540b0381c0c8014140c0309403003400782e415221004181d921580844000303000410800c00003403414425800f800d035060813410045080d0798000001141e1144029010420b8034244040002c514420180f01d1840c14801c206801c02e0005611102c0e1280b100501d05418140c9035808940514407030564010b03045d4002c4165025003c0502c40291120a41b11340d000440c42010741c01c0000c21606464002152001001442c100e025011110400c0d10000c1a0910303480040c031002403003001401c0c500012402126429086406820810281d001c0e00c10b01c070350082c0e000a005110b1960000383d03404100b0f40122280c0110756551402c0305510b4001e0300501c1c11000403504064251049411024840c030002c0c25103240c100085180c0b600401041303600348005800010304210704580800116000300d600c1c0ca802c0e080f1038881902903 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 307974919 1250 307973669 307973693
    0x709050c0a1d0d0302010f0b040209010c14030d0207081201170a030e13060e01030b01060c0b01051c081305011b0c0501050c010e0106060e091006091a090a03030e030d02010b030622 79
    0x80e026035150690201f540103a840303a03010882d0119000c50030400028002000c000c0403e1000b4180458003554201c4d183c410000d80310a1507450005554131041480c0c803d170150881230b04850542480800441c0c1800b0301c1012060502103100109072610064804450140810f502e40b600022150210100075406006502c003516805810f0300080d455842d000b1902d50b8164000810415041052000a882240300f107044800480d900800041141c60f07400c481592a0303401410b490380040c080e6a80c1a581080c1c0d400c071ba200b62204440759204a07000764070908284402000710054900921896024201800310150200700000b903c0c43e00c00002400c43d903036900880c4c085044000300c0b2000e450300f10001c90f402861900c1d80d020851800340007a02a41e2540190a0700b208501149628000c0d0078054842005008001c624055600e04015003034882d540c00c0e250185c011114450800d074014081c00040c2c20000d001000c6070340ea0079110030301c3c9032038030f0384148492504a9020f0012819060400e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 307976169 1250 307974919 307974923
    0x30206011a0a21021204120f170a0c090e0c0d06120b04150207050105180d080405061b04031b0807061803020f03010207150e0709050c0a1d0d 62
    0x100155410102841040081c88410707003a8440108400e0445540c01440258000c443c1442a20203072107074800c0c01c010307001c1c005000192030741e00c004101c103001002022200702e81c495200e0309080040f10700b040f40c88030019800e89045075188408504d04100c291f1200124101c2881c1c580308403503c03001d012005140c191008104101c1c04600b00c00c0c4102948180801010701240c01c02102c80681e0b2090110f240c01403000d02200001091000c1c1f044c0c85804955460303500c0300007001070307180503081c00c0120241010300b15482e20078060440341031400b41000344d001c0c94110380248010340c0c40e00d4084c3d1107110f40002044140809020010000f485115007070410307044040f60754181414071180906e070000b607a000304204142c0e000300f02c2d80c81030661800030541360159420040c007280000442d01910405800819039080d2804601d030020059011030400c4e41020195103c0e5513076846c58005550060714903600b40c1d1410445882c80314020386408949810004942c01d00c0d08104001031040741d41e400c02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 307977419 1250 307976169 307976173
    0x6050a030339051b0d0308070809160b0403050c0a05031b1f0806012309060306180103030203030f0a1b08071701141201020307050702060a18140310060819031b0302 72
    0x10b181d204da00200c10010184015201040b9507101034400520340c22000e4014420b10034660b01103502000184a8015140310040c2c074600b205a0b140034440c0c6a43c031901c410340c1c031402502c10388030607072410108179001c841005000f0441d0281c0c00d00c50121400c803810003d50b1054107800c07011660741010411401400c0ad940380d044a41c40d0600c000341018100d040d03942d01d516461115070f426458144191003000c02c0c107660045e01d030341d2220041101400070048071080319401c0c000010402d03a0010081d40300308001e40b84400c0303e44800340808250742c010a054140b84189400c54044d89100d4001d407940240d440c5483ca024a004010b1200b40020030b130440800d03540f40c00e80112250410702ca60040b8250340200842c81c61501113802021402218002445a44000b850902e154030602c4803121440040004000050f580e005855040303205500c44c034020301414142c00304851561288d036040320110340103801404000750789551020312140c0b080f01401703510f0b6480802e01e0036881001d00c0b10362091700 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 307978669 1250 307977419 307977433
    0x2040b0717120411090906060105032d0103050607110a0c03030807030212160e010c110d03050c010e0c041802010804022701080303101a07030302030a0204180f06050a03033905 77
    0x206102003105d00038a1482c003039003e20103106050340d0000c216030781f0036203510741014400f41d02c0f1819520300c0705407001245442e41020012040c8000455081c1c0240e907a45c40d10441c03a20081e940307030b4941580303d00281035001f60440800203c0d000340b99403540129145401480c284401c02981c4400c107040d540c0f203149040f400082c0f00f6203500209000908842402e103540300038990b0fa1245d62610b030000c1e401d8003c0c40315903807550426005009a82c402d00e00300c030003444180081215282e40303074120f0b404140302d103043c000c000da981014440501c12468040c0d594050740d5681d038082c05001440c0700f1503804070066005481c10652521007910307001c1c050f0503001c2d55070b0b410b041410384412507003508480b5910342c0e8102c4880c401d500240c21228074035070504000d80c503a501c41c800e0b00c0081c001c2d03a00401109903044185840c20016a01824842500d518100507240d11002405591140d9010080c007003110381c4c051041413101c000c000d03800060011400001c0b020f040034501420b01d580381044803e40d01c401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 307979919 1250 307978669 307978703
    0x6020d0c020106050411030105040911120a050c01080408030a0c18030c0906080102030705031602160b3c070f020303040b071707150504230f07080102040b07171204 72
    0x1c0910030013800c0440d401d020302d0748440c0405001e4401031064034403072a913642480d000c224003000083c8001c400104000c190104007030129880b490500c004132001e0040c02005051507020f000c405020725001b21545040d80c3c2e400d200c07200200844880c1c0c10500031540d00040c0004611500c803c0034510550800c1c0c01e2601c2c2520b000145c85c0d480d0051102d41c0d005004110400b54810181d1b5880048141c1c0c00f6450350821000307900302148240b1400217510390f0300b00422091101c100412240400300c43d01b13103540494002c690642e6080380115a40b506036406142103c1000030040c0010340e0140082441c40f403a140d000919582c0140d01c03040310140c0210f00801849601040c0c4003000c0f1400b21007500e08880b6030b444d4a0540002040b007216103680700c0110701840f1085d5542840c047c041c0e061207900d1b801c1c8101055441814481d0662184150714000c2004031040c0241e4044442c69003c2504202d0a07951f0111074094140f6040b8045105111444101c40300700101c43c00381d401040340740c455040c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 307981169 1250 307979919 307979921
    0x70806011208091513170c030c030618030d020d06051002070b07021c0b070201051006021209060307050d0f06180b0906101725020607020d0e010c06020d0c0201 70
    0x1640469094400c0641c000080341c03005044800d100d4040301d49007035201e1076081c4044a40207820490b50402c0c610301000c205032040e07441e442c81c4032910000301d4051039002401c241e07942203005003041c2c043e0030190204010aa5400450342a03014020a03a03007000400c0c0c00303150898100f400580c4120762504030800103070402c03070400400c0e1006c51001e05901420402410010320130404000d0090f0940340620003091000d01c00d50b406c1560007460310501e418500c0b8000d010b4601030342c01c5a00c8000d4190700060340c81c000503415080d045180090750500041004020f010b4100610b81c0050100400c0301c542d03003082500c24542c1c42550028006445418240010000f40c043c6040118492400c124803099542d050007840d070041c1c0803030320b10302e00045042c0c0449590310704202c4540b034280d50750103110541000d408409a4070711942100c113141c40801c9070403a5521400e44a040268000803d0014a1841010f070400300c1039040c1003a420007041c942c1c0d420101d1b8440c1c3c8207060301641e0340410054060382 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 307982419 1250 307981169 307981171
    0x30406050132090a0e0303100e09030a140304050f0601031a0c0a0e0f0109050a06050702030d0206040210030902040b0603010303020d08010e060f040b03120301080604030e100806010807020f0f070806 87
    0x941c2200b03100380340c0c828090880c0290780c48880e900c140c5503040020f9580c1e44030740160f0781540c2c56105072516403c025402113544402c0340039074500300141d4000500c1100e00001568403501060359403545201d985c0d0a150800d40c40a0f0055400f07004032585580141000c11403240203500c00c100107420142c000d01e0200e0303000e0024140b15443e80040101d6000700340d002402c064071480460380840e480710342d80010384140312a039000d250420b280b250700058550b0440060300c6003038000c0c0c0584989002d030400480c0c603801c2c11034000f07501ca8440d0000c1c201540c482d5020802840c8003810024445900800080d8190070036032045005a0201c2d111404942d03005c1c80b16401032a40b00711420550805500181024401c444403038001c03642c60511440c0d50340c040120380024407041d14102c3d0baa58507400f0b0580c440c0021101600468031020241c1c0709400c003040b500c0c510765039540e90134910391508401104c035910050111030441c400e100c684501071005010002c0f0308021200103200c1540781ca0507990400c84 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 307983669 1250 307982419 307982459
    0x190c08010e220201121415040612031b0f06020d02210610030c020c0d1a012106020c0a060e03130806010803030106051c0608030d1107020d15090501020304060501 71
    0x244052110100203101d20350b40080350790900702680150401e0207994014080482000036803070a02e014480c1000e01c014801e95000010750341400b483d9100d420794005130103c0d01c4010b0000350310261210484800612418049200d00b4060b030006d07c164403040309076006030306075007a190390004850402800841d1204901c0c5601401c50349245804800901d00301c4540401c602495210a000c600c0940700f4854840b42c910010024158403405081401d092550104901003482c1060000306400701c80c10b907050030401c4160003200e44115507548450107034200321040c0c880b82c0f00e4521001c0c00140d16000b15503004130345000441d00c1e071903c04c8103258910741c0d0380e02c5605140c00c80001131003809000300440b07041d40d0b210f0411656800c019070383d80702001c4452890400302442c0520110312160013000410040041c4801480990454446030040e8810300b4070003980b2840c6490080001070000608284c00b0900200016283c090741c3c40d0f00b0b00f60380c4112000c8500507038070700c01840107520315004c055601d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 307984919 1250 307983669 307983691
    0x905040506090f1003020d0c0812040f21060f1a0d05032512021015080d030e011e0e071e060e1908010b040605040b1503190c08010e 58
    0x401c0100101c0c401c80d1020305410204030f58100001c2c106070341c000f16a0021540074292031001180da003840d1000c0d541501a80189008164030700c00d10101c0601a24191400b2501615006140085a0100c1032940340d132070001000c20020540400d1441c8030390300b40c4111880021520003c684442c0a66140350b09001d4420080754600c03a000c2440001034400c00600c80d5030b801081c4658017160800c0d84580c02e0000c0041c40c1d844504141a40e0200b80622401e41040050048140c05015410040a9401081c6603130744100c103031a0425100f070b0042d00c5814180c40000425030794003899501c02080c2865042e440300e44546d403528440b2402c200b104010101601d0030510314400d0b0b04c03911595100c0b80b0a488c108074902d041200990b860302e0000304100300c00729240041d00d58031481c40e80078002800c4014491890800001200e04080c01107002c4c00100400c80c0d0026186200242c006170000360004910b0041e0441049100880d48a507001c0c052a40e104d00d00c0c0c543c5070080d10f2a48100c002d103408401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 307986169 1250 307984919 307984921
    0xd0c020c031b120102091002031305010309080307050a110102040b04031109271f0b0405061009170c03010c03270f03080a0e160f06020f0606040905031b070609050405 73
    0x1690301c0c0b0240300076048044484600c1c40741d0071880a40a8001e13054107591165000d110360343c2440d0004014029100c0204001c0703d0035035140019412980e41071000780c9151000c1000070003080c494001400100c005080180000f0440542d01c1d00320380040d048910100d900240074010300624070781c14030310b2841c110340c00c1110340b0388090100340c1001196011159241040c42c01c0c04104018000307400c0b8203000c904400c030b40503517500c2c00c00043c080c0c4200b0b0901851505000c1100f038103007032600101c02c0304a904c2d04008286807040f03203c0300070344041104510740600c400204c2540e03828010307940c2e02e00c5a90341c04194101e02c01d4018684175004400e0808206140c91600300085961001c00d01668050400a40b44d0f910680080d0240900da2240500c43c024010410940d8103003400106c1038500f0480319030031080d2030340c8041e1307078030400c0078007414444d400785001640929060300030780d41e5188280f0030743e81400000600d0007050031201e0300802d0103070080c0400780482039000c0605401844216824011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 307987419 1250 307986169 307986193
    0x712090810020309030d0b030304090207260c150a09080d0c020105100315050705040e0f0a0609111b030c0615010e060a080f04030302040f0801061707081f0609020d0c020c03 76
    0x81c0b486201403106c200b68035030a4000c0e542e54240f060714002e002052040d90749800e180740c18001c2c40508032030004410456602510210360110941e401011a00e005204542c0d610300708540411005001102040c0c0b00e4403014000b8480001510b1081c1110001042d807403410400a801d50f10020001851840070660420200d102001030352002040200e001455444d100390032140c4c1d00c11500300300202c0d41d01c1c0342403002219540c10124403800406c1010084141c55002440a548800d6a00c40c03103c2414441e650012144280300103a54594904680c60400c42845550528108580540044c000325041d12110750304400d840000110448115280c440511009030a10340b014088880b48007a040010702014082d41c1182d001e0301000f8280031815a4400340706010f0000c50140803141107242000240c003603000500b00c0b0688500c0380107002c00304081142c9040100c1100f40d00c0c0c1c8241d403103c0c80007410510520003814120007aa4000c142c4240140303000c0c0c648050310091600035031080f150054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 307988669 1250 307987419 307987423
    0x5060702061006050705010b1e130c0c020f0307050d0b1509010b030103031d0301060807060e0603271005180c01020f0d0e0109031208060a090902091603020712090810020309 76
    0x36107209013880340c0c0710240350606500400c5010005a044024280351003040002220340c900d441c20203d41c42c3c0e001c94046c0ca0500251000900f07248086062036141030014501002140b1102c10043c0441e0b0543c2d40e203000080c503101070720130180c17011b40d05081480f1a0480202d503c40c00342c50281d94403405035242500d50095480148005800c00501018074401e107804015000c1c5c04ea00003e0092222544800601792100b03c20310410b008500041016151130070f040040d02c0c404d0f1105103541e240d50340351414411a02c4801e100714807040c0101032007040b144810344209030141401500d070f40c1000c00002007281c0f4200a50344818150341c407030510b03100c1e4040001002c0c0c0400300385261070301003c40603c005842c5c5140c0b98000a0407201c00c00780030ba85880d48075809a1203404106c401500c003540c1c8514000458502100103504031801030001072020b490818440c4000c3c1c494500140380034926107404100100c0c900b00a000640c841c1c03410031180d04100450110590380c02006c5203141441d483c141c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 307989919 1250 307988669 307988701
    0x5120406290d08160c240315050910030b09010b0f0d020a090e100509010209010807051e18031506040b010203252409031d06090f0f0a030501090506070206 68
    0x61440100007012519207400011491340b00345d00c02180e009003a124000d421600c1e02c80e00c1120740030580303c50400e040c07920034011300c800c1e00112102d8804c0c0508080c1400f868000c020500032200445840000006d48140100e5201d224158000202d0a42c40000c20500104220303056102c6e90030071202c2805a0780703840707201c000c9030904500061403550038640c071401d06010000101e0500d28001c02c0200d6101c040d00117124031242660340c1080f5598145047c0d880780070f2209600d8018503007200381c07214910800300030f00403490703605403001039203a00500291074469400f201c0c0140c2920602880550b00b418000c280040c0c1c000d0010314103280f074444100d540d019102c6e1807101311911894100041c005a03003142e203841d5600c008104a2000c100c5281405480079a00482c00151141e04501e080c3d10030f040c00c0c0841c03c00040099203000c407103030104058070308031540b4941d004007004c070036680305d40c1e07084801c40c01144074000115140c0e589041460a00e10300030084019900000100300d4059519980a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 307991169 1250 307989919 307989923
    0x9020a020606181503100f02070506060a080601031205070c0312021e030a0c060b0306070206071103030c0d020307090504050a06030c080304150516020301140603011b020303060105090105120406290d 87
    0x14a1140c00385000284c44c20341c0d100704410702e0071f1514015948416480e001416154011012038202e500c801d4180b0a016545124804072a04080c00500c009200d42d0b80c44a0000840d00d0305d2414040c443e00c2c2c200c01502c107548111600035112402d411004d0301440300c81d801c2004e20800b610a17199103031400762684620030103181007002d01301c03140003049201d510501c09140003804545443c54100c40182d07440c4003d94441e00440c500804c00386e002100081180d00c641e0480001078201142c80031580d0181d0006400300c014815400c9001c01e01e9110b07440b40c0c0b4030810302044089100c03807035070414486070110b9401c541c4003604100800d01c090300c002058104100510f00c1c005a5032644400c0041065441d500001c0d403650800000c603a040e0071044089000d008100c008001d0102058008d4103040724801800000d41c00a10002d446980500702038048105e040c1442480c1c25102000d500c00c600007250221041d556a4000c444a13610144600d000c12400300046410301c06c1420010341550a201c0c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 307992419 1250 307991169 307991191
    0x3020f0103021318230601090501030e0a050a0308011406070b06191d070e10020d0e01020a0510050103050d08040c0e131e03020105060316050907030e030409020a02060618 75
    0x1410166039803041550010302c00b010034480406205200c003000340c08a4005068184040e501a0031136848a0342c2c10340c01b805050719030240d250326082c0154050315041602116900500b030941000c940144145ca01d810300c06c1d034484540f50b04108030351494101c40b0700030350300030902400385000180500305040e8024000b2900c4840c104078005040440301c4054000c1d401703003540713a54011046d100c2c2c0d01c100e80c041c000c640c4560055456074410721840e40034050843c801a404006071024003400740811900d0a001807041d180304075111303140e070342c43c145c1c520304100005990b0f0001001440803d05c904020300c0d0091412480c42d080540300c0c56000304030f42c050320341f100310301801060800e41800c0360316216560117280c40400f0341c603803200b0300b4120443e0b6a06501550030100010582c1ca8003003580c0b10380040c9000b002c2005c500b807030240b001c508002010340090650b0703045801c00e580300400151004000c0490003595800841c0002810150003070019400384501c00c1a00c1c0e1003112a0311010b5000301d1000c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 307993669 1250 307992419 307992427
    0xb04050d08090a0230030c030406030b06030408071104020c03130f12081903090f080d0b060c100207050703020405130c0609050603150103110d091e0b0f090f1e0607030603020f010302 80
    0x1440709071681490403585c40c0340c807001079500c40000f0080007410480e05140c401f0401e0307148120600241d032008690080c400c803020050b00000442c1c1d0440b0420700500a8001400e10a04651f02ea14640c0010914055401019820041051a032200c0c00c0500a242c034080024215940e802025004110070b10910703407030383c0808040141c032a52109132603a8104148841030b07001030400418030b601001407540c0c180d043c054600e80e642058401c4400490805004101806001d070700c00000f900201d8048402e8014040c001015035514050180070f0404504074041003060382c03420020184441c2d2001c0144944540c04201c91794484d801c1c0d13580301d0460340e4202c0c2c01c4000c20004070f00502045078070000c40f50300801ca090101c0030300d500038034006124090402003e400032110440c0316103c0d45005003034600203000240c44c07000c1c4403941504001c1c40390441c1c41e0480c2442409040c200601c80c1e0b041840314209403203503c514204a0640c100b25142402c2140303d041d900840c80d0b100840880d036061540010b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 307994919 1250 307993669 307993729
    0x1a0f120a0b13061d0f070612020a05091203041508060f0105070f0b010603020a09060c020f1c050106140a120b01090c110106030807060606170109180b04050d08090a02 73
    0x21649034045034801001c105600b011007545a104d600250200741d1446003000e41e90340ca03400010420150b031115150841c0022070000c629001c0d5002c82001e00421070b050011000300c0d00c981801510707a00b54540a59115414100365030580f8210100f10420001c3c614140280c039102c1404c2c9554621081c64415505c11950420111890101700010301081c03a45000041c5258580c0c00303001c844070036580c0c580c449a03a44008469060401d030700030b5400700303810000310004d15280e01420601c01700c407020041c9019032038682c00c0c01c4911507070154040412541c0c0a200614220003034002602006203005c02009aa40700c90560301d10501840d000969a01803040e1070b240100b98064555125000a10410740c407403800544941003c40201c03440d5084c440c0c0401d40300d0003544402038000d91203a05000585c60015000c019081c00c3c01304020407021034008102080201d88030354071a90146006142c6001000b00040074017000034116030785038001c140c0c41001aa901f86a000104409418841c031102011f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 307996169 1250 307994919 307994941
    0xf0601140909061c0b010f08160504020304050c060a020601050f0a06080a0f1b020c0316180c0912030804050c030102250c0f1502010b0604031a0405010f1a0f120a0b 72
    0x1030728000002408a01c4c420100500c440146040e0f402c000f0303a40c80c41c136a4450b0b0341a41c40c0700030315220f44441840030b01480541019800385902034000c2d02201c00303101e0b07007101040680e0302120030100180c01038070060242d03050050903589800010394000f9032181c500760b4001c0c400440941110001d98461090728404002d58000d1440c010030f1000c481c5a81c074441802940d81d54544403002e000740506000c8684465112030b0708811203100c001c540480c0400000050001e04440c1460014090700308030116050141580091445101b5100c4036901c2c202400d0480c40e0110b02d01000c0d101e1f0303004124030000045903103d080d160514826001e9444a05494064455002504400103120211900082a8604820180285030941c008100303600d60380040c40403070b1089000160001d02c2d40d01c1065600d103402074003940e1090160000003500c0c0340c0070010710255030007044580251200800000c40720b01e0a140f1880441c0000c07601089441c085020300784d103507401004040c00d21144840050040491 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 307997419 1250 307996169 307996189
    0x5070c05060c0904110405011b0303150b0304060f050103050712080405120303040b090105010b0313081603120b0405011211010c0803090a200d060e010608150f060114090906 76
    0x12100940e00700380380c200205a8250401c2018601c22801c0850303000a00d034003101214240c0340180c2d51003602160240d181c07159100050000c90402d641d034810602d0340c030390313412509000e00350f0031104030350300c0c00c00f07041480035600326880c654100d80c948401000000c030000b80c01011280031101411404000b410150194007850b4000f80e049103180500400f5094040002c1d0300c96485400c414990b40c031600819400c1303840c240165070302d40008002007181c0850b030340c0712100340c1441074038200d2811a80a00229000111642c01c0300484e006090f80e10600074580105020507800ba02c0030403082d031400380411074000c3c0c840f1014008032991500c0d00600c0c4d11805009200640001c0241d50324205460402d0b0344010000b011340d90640010380c0c06030310454615016405030002010030301d2000c4191184030050521095402040d96140d0000130f841105214000c0350404511002105203800344181c081e03580020000d504200096540c250510124411b403150748406503a00c100c15620000030800d0048 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 307998669 1250 307997419 307997423
    0x501080706300b0a0b1603031b08041104020c16030506090f120903010e0a080c0610061d01090f0e0a14130308130804090209030c010f020a0b0c07060c050a030b0d030503070305070c 79
    0x217070015549403019070601c00e4603019482950100905c0114111145000c12041440c50001c0c0151020501145525076203041035140140300510384228074140e1480c0c1200918503203905442c203001001032000612040c0d9000406030701820b0648020343c4410348030200c02141210b07841011910066a0b01e0035802510b0080c0003c08550341e9080d6820104025000142d80a01c03501c140c40000c0c00005807008050308407a215118014590b060001a05000340308421160400c240508001840c50300420307040e00409104188103900d01b002c2180105481d4003800c44170107011050305101182d040c5004e2907000d6070f054030709944580c440340c5d9020012100140043c201c500c0104000c03800d01090390003081191012000c5030b400c41c0c41c040054031501007428003440540c01c84407e55000c100030f140c11590000d0050b546c0b500c2d1032195903400c01140c0c0c2660360100041c1000c120100300c3d5400d0b100d4058202d000b1500450000016a030080c140c0c40000c201d80101500c40300881e18050007061100b68442d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 307999919 1250 307998669 307998689
    0xd050903120d02041d1816090504021203160614060f060a051204121107030c0b160602070506010501110c0d150b180603010b0402030c030f090307060501080706300b0a 73
    0x994064415680030b0003d944581e4504117128003043d00140000e021440d402e60007c8600d46a0310300090b800042400078010782e0802d4a00c0a00c100140081c0002c15588031088803402d180c81150500d03800312240c035017809200c81c070340c481030000a60729145641400c40041f14125610039907000221200d0180c071560490a03000300b004d0000b0044040501652455140d440790b04042e0072035086540c60307005d840050920030001b0741c00d00800c80c00d440181110750a40d03001c490410425941c81040364080113040e1140c0c0c01c03800043c0300a60784050042c41240700180202125090000002c0b01d071100980c000f01200c4120054154900c007503081b026600e00010500752070b8510010015441c41b904880d410710035481d00c00317a41078611b072034070a0703c1c0100c82e40e017610360031507440000e11982800e0103000d035001448280021300005501d4002c40d806403450202804036070385040c40c0a440319650100c500d88a004405064010b482c540e0114244100e40038404556421842c010038500749050300504021 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 308001169 1250 307999919 307999949
    0x1b120904020a41090a0603110903070b030402030f1c0807030914010f060807030c051504030b011d01060305060d0303151d16020c03120f0904050106030e0d050903120d0204 75
    0x7003541a1030441c448581a9100d00501c180c0d03c0b018414400c6000499114401e0902032100c20303c00d61041c07400154003480c4618040b04c990001e4509003e5510043d4140390000422003141010b010402e64815030400601d11202c250041d1041480c2c402c100f0700801174024000b030b0045110703070080102c40d500f1140c41021070a2003d002030180c10b9650740e40a03514107180c00010240000510203007140c1e0000e00c540b21060428080200403040d080010010040520020000c686410002402030141c168180808400c0c03a9140d079020905a1200090600c0e1604120007502c030000345a10301c9030304d441c1c00108031405800030303001071081d604003440340c0c105201c002d820b206100381003a00038410413030354001c5414034140403a92a60002829034054218003248a80340c1e0610014019166400e0051420514244040750031564241c0c0a00300184d101d54240310700007404e000d108001c3d5141d02d409031410f014200480c0d60340002507440610080b000480d101040700c82d82c1903c2c054600d400600c0a8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 308002419 1250 308001169 308001227
    0x90b01030605250e0907020705030d05130905011707060203130b0a170c070201020f0c010f1101061a0702090709030b1801090c030302071a03090d0e01231b120904020a 73
    0xe4031616803582da01a05c180d00114015500000700c0714126480103004001404c81903200311910b400003000d4040305440d8500c04154802a8001d582c080e011079600c441203544c4000c03025240c81c1042d8009401d64208100449040304517240d0441550880c1000300c0e0707207420f44501100c000300b021207041c03003600b00702c400d0102d00c01c0d8010082490314001d0f422281c0702d03000b0f83d81c569210a00d66403010f011440c82401c40c501280110404a02d44460300000105030380e4510040c0200c5003014801075814a0001d1a034007145486581a6000307841403400c52041825640d9500d00950701a0020035125524a803070002d40809410070344640f507000b2a840c000a5030703440c2c0a940c8401c2801140c0d00340c500b2100c098409521702c800c3d030388240441c9000b003070f17002c0310340809a0f4027500912000d410003000080303010b49180c401503000c04c3d60800003a40c40e680d0700c01041d021111052811586110f81101012580e42d1700300b20281d078818039045500680e21005160141d8541d0481000355415a51070210f00c56 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 308003669 1250 308002419 308002427
    0x120d0504080705010e0d060e120a12240504020306030a060f050603010605190504050c0d0219110d0210050c0c150a0506040506091503031b0307060e01090b0103060525 73
    0x4407211002120101500c40b001034441d00703003d500700c9412000704144c410224045400c1032a014203800b00f550132260705840c0b441450707800b81300300d00c01240b2003044031450f010442c0718050740800c0c032120740c2d04000c18101b590001148a4800c00b442950003002080d11542c052003040c074859403000041059555112201c1c000d0103046a400c1d200c0c0d4a060030004203070419500e0383c3c481c545001000c0c1811750070001004014130010344400881c6509000c2e40142c40c13054402008049000c0d1044218001c0c0740e0350003090380020920601042e00320010300003180d500018060304d03102c6504070100f40d41c4d54110001c2c000e80901c101c812400d01c01c1052809414804100c9280a040d4048061143c1c2d0350315002e000c00d81d90b003502c5a540180b0050000b500c0801cac040000c1e04807070402030590340b52042d0300e00820406103412010418903000040c810007080018071030f025124991100a01401c10320fa1220003504d0414440038000d5600c8000082030a0803a41948030386613202220202c0e20995000014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 308004919 1250 308003669 308003677
    0x3020c041802030f070509130809060c031308030c070b0d0f0c0503010305060105011b0809040905071409100b03180a020312030a0509060103080301090c0c02030a1118130f02120d05 79
    0x83c1c000d000f89000d0004940011030b070041500d13400751202c0701e0ba440b5000c00b0780a040c9031480665140c42d0601200100b03984400080641c40602c20045403a100030400d1151031b45502d40c00700b16079903c00c2100401c50180401c144045403482580305032111610500c04003c0d00c005440c1c030840b54504619100c0503034108000c4c5050364041d004642c00d680c0c80380015a1480415620180380c40c3e90f07031782000002039442c40207141c00d50000e400494071000c10342c2e07402e01d400720b5504510042440064182d1490910b41703d05503001c00500c2441c101945028482480740c40050f03c0b034035400c40d12800708012050200007140c105030780a421101c00529061003564280c005490b40c180203030416021404580e400509d09050301d070801e03083d0380303540d10301025100200420f000b40003d002001d209900941c1d418003202e190700317000e04402541e040c005810485c05981460001007251840014411080c561186032951a5440103040322151010300010390501a215501600c80c810b40040b0745009a03c00702034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 308006169 1250 308004919 308004923
    0x7030507030c060c03050f0a0e090114030d02010216020f190b190c0201020c09060a0e01080f0c12210720040605100203070219120308060a090902030c01080403020c0418 74
    0x3858030f440e00c00480d0008007045010300092810f2000c40c03450050600140050000c604098444010325804696952001d0344800002c00200744140514141840403030b002c1038261000f1850652040402c9411001220000e400307030a21000341800390721061014011440b51806c6007207990b80e5074007840c803640e2009014140c0c1e21690400c210145000d02c1d13400300d59a50580280403444416170601060410091819501c41d41720030002a41c0019500b21a020704a020b0241c015040c0400350646820384002001c0c2c050f030f40e06007240ca000000862004c1d5034038001117400007848062003404905010b6032038054070310055100030941c0c01d81944483e0f08440d0003580d007401000d075a00100480c0c0490b0024603000b68108024140061505d000440301e03003450210300d440d4450700c1c0c2e0740e5100d800c48070001c1180880d1220051061524080318940001c00c4206001d0107082c00c1c641c08203490f04540c000042c11b1000070800300e42018024010022261b6010740304112859140d5904403040c0012502 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 308007419 1250 308006169 308006183
    0x40c090c0507020d060e0331140a060c02040908160203060702062a1201030b010f051507030507060b100e01091d06060d020706050a0e01050f06090c07060605030703050703 75
    0x14550000d8081c4050b142e956400070420190940d00340c0f55a4050880c100600c200c50104004c03040ca0304500078043c6250f00c40c0b10225084041511041c50403650702900140d86510885a001c2035943d12000240c1c00c1d5082450702445984d640d00c00300d009401039240040000d5804101c02901c009604841490f150088085484c1c64585200998580e4405e40c0e400142000c025032009a600d0041e00f40c4040b84030a910082c07804101c526401b420f44000c0c4c20880e801c0c1018001082504d44c2c0001c0e00003c0c0000701c403401201c0101003022140740c0f241101c010305011012038103409000803a80180074000024090003540741c0150b84c000c21000c242e03e0114007203030041c80d001c01e05c411580c02d01032200081c01110741e4280c8a203c1009a260040200303410842e800b0041d900004125000f41170183c08000000b040042030340b0102820f45034003c140303017424240c60040010036682c03206a0358021600f00842966841075007003074405060780da0401c68051094280000800000007a00412603014900c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 308008669 1250 308007419 308007431
    0x812090d030e030a0c0c0305030a02010e0607030e03091302120703050105030d05040e010b031f0b040303090b090306041b030c0e0402040c0906050703031505040507021501060315030b060105070506040c09 89
    0x1806800319440d0301108200e6a20030311180c4c0f40540160244141c850007004422241d50f50f83c1d0300c032803950b808508030b54010703511160b03898047c103001c010f140d4000d54681014800250381c0300c5081d61302c2c0200150741388501c60b1807500d801d10b8000c4c3c0d0b040311010385a00c041d41a482c6030508000c2c0c050102031007018001e1040c29108000c540c80f4600340d034291501003041c040079920f00600060340d500050100b0b140358500481b50703240d081007501c03040028881c07100720503202c0e4034604000c6c01d02101c5600c070011b0f0351410481d281240d600420815807055020081290a000c0703103440003403000464000900d1002c1c15403020071924001300d0b03503e220314402c84051000307550200702165245003500c034110204a050200f000064081d8129a103440303d8051100440303a44d0300c0015003503840070385e00007001d6001400d241c0c104031940c000903409801039040501014255100602d4401540d110240c1880940c4010501607071146048540c1c0681140885000f400c0c64101020b26404c03030f115001140c2d180803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 308009919 1250 308008669 308008693
    0xd020609160b09090403050c160602070f35010606030603021906050304110303090405040312060b09010905150c03040b120604271a0703061d010b09120109081209 71
    0x180c07800aa440c21406a410600807a0078012040d9002d0411030504c40180b00c5104551810080d6041c900c6900140c801da40d8a0241d029040c04081d41018a06440c0b04505100711411003106c51008a03840d0f403d401c031800c0841c018840c0c44c020140c04a2554240100001c14a6068103e00c003075078000c44003100020512504051080110301c1808003060040c40003078085a9200030300900444050141d80c6445080c0f0002011034000b00d90890116013000340c0050100010b110300400b80a1052101d440c1c1001c120000e03080065922846101c0e080440301c0444024040d0203480f0000d0030b410469444079290442c041058204c04078460780c0300c880c2e030001003844c5858010041500d00c6502d61b028503107a5400311b0114a003100781d0a03181c800c42003143c1c1c00c0c0e0b26030440c81e1a104c0c0b1801c1d500018000e0826000314140d0407800c01048401c00b003800140720078480081180c040300c0084402c144903550083c1c013207016002c0e01c200504003e001140d403000c128030240d192031184400710299051031800c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 308011169 1250 308009919 308009953
    0x3120f14060a080c210109060606080a090c1202010908030d0209190b0a0323010e070e011112032203050a0306080619020a031d0c0907050406020d08180d020609 70
    0x500c2001030550001c0102c1d00070f03003050902e00301131100b07a143c0203007100c022110345ca0079100d44041c211540351780c0f41401c204199200030019048050314030f082c4003800c46602c915414a215000d42e03510b401d86ca076900403c580c0a051508001c0504509480e126801d03503580700000d4210494660041c0700f070022080d980420300301203074141d41403c2106400c1200b107200880c0141200d031080a108030300300442503000030307514200c14020916080643c940e0300c0c1c04880140402040c0e88000e06205070940300c42d03114280491425100d02420364a56166a282080d1441c107082c15104072140104006032a014168040010160207403151000d0164583d900f40850f40d8020484202203000c010800c549200d904c150010032280140e4500443c044a0103483c0d0b0031082006041c0140b00d51158070149143d041050025034011107a0600508042c0340490180d01c4070b01c1d00138224200940d0500050003208040c083c540400f204d401150545c43c842540695101000c3d02c080801d41729442080d0011811 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 308012419 1250 308011169 308011189
    0x11a06030106050a08060a08010207050705011d0108010b070201170c030a050708060d170c011103010305010b01051c2f0315121e01020403060203040c030b01050f0d020d03120f1406 79
    0x5a5601e031850600744100440d40c809004c6c0c14280c0c00b0072036113000140d40400f40090301040303008001900c16245048009442e60390013504d642c221401500c003a5085030b8001c00c13841d0458032441c056036504c000364401210300070042c81c0c540c100f1511000070b0012070301919010b544544a8883d00b0011078549180036a11244121074450f40702500c42c1141e0700203403e181e01e404c0c5050300101e5003801c0c650585101e60035502600010719000e48040010000e00800b400781c209240801e08209242c12002200310100ca0042d01e10407424548499061000b2040d2407241c0d01003011003c0000c0d04c1180740120390342c0590003654440d01e1003a4540c6840300b24940382e140010300414000041c00009544088200900f5880c5400b09244d5428480040800c0c15400150300c2284940b0409010360b0552401e0480c042041c1c20003402007418003601300403500d075820f14080c07050b01100c0840204c440e03840c0c211502d1f2520404214807900b4040340e903200000c141c00040005228003008142d540c0c400040c4040e5140c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 308013669 1250 308012419 308012429
    0x8030c06060618240f07020102100b0a0e0408071203050f06010914040911030a12020d090317092d011b0b150102030412030903030807080f040209091608011a060301 72
    0x803450f041240380c64141140c0070781a100c288554040888036015209603000103000d4403043c40000364100440d07070305001c40e1054401c8424200040461007000c04e200ca402c0d8003500a16008100c0800d040c070115400740d07451203034013045c54042000d1126004002e000180c0d184142e4100b41800b080443d80180e01210960b20385006a4600c0900c0e0740070800600407010055900c41c8200c94119001d40382800119416406a4038124480c07042902c020b181840d83c0342c0280810182030030910004450181c000c81e044011a41261211319890000342c9215100480c1400d0121442070000800020f86030040310b02d50076260801ba1600001c00407403100c2c41000010300c000180000503203031011000180c4080da0701881200d040035180c40b0841c6039003d074101b00750045110640d080080507444034025a011300c0c0f6150446240c2006444c3d01008003000d0f000910441d800c200041d0314010801503004100003d038000d0b100380b6558203425000b0704d5800d40803900168000c01a000c0c6052002c01c0320b040710 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 308014919 1250 308013669 308013697
    0x6060809010203090a1211062706070905010e04020f0304030909050a020708030f04030c15020408070605090d03360305010b0d0b15060415050a0f18060e150408030c060606 75
    0x800e142c2e5900382c1c100040e10103c1d0500000c1c546407c0c6007481005064840c000d0100468814159201c0607851b6402408036901c10354010420890060780c0700c42c40c0000c0320700a00300321010038051000200a402a90091881174202104100516611168000840b40c201300b08001d2030b101d49018100340d21034a1800350100401300040390110345c040d200c196115000b0320300072000c9000c940e10303404016190314076907001c0368000c01c042c000340381c06120040c01804a400c0581c904100000440c040b40041240541440f00c154403281c41280700e051050140d280b5408a4480c51020442821440b0034501050351a903183c0300f9200e4090600c209411a040d8000151b40704940d00c40d0b4a40740b1030f0381507800385600283c090000107049091b4180b03045005d0016260141c4500003803100070915401c3c0c0070000c0411045c042204007032a03008042c0000e0356002d02c0c1840d1b42003403400214884030201b00ea401264000000d00058809002c805440844290002d407821615800c0401c040790180e20001c2100d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 308016169 1250 308014919 308014933
    0xc11030601050307140301060506030f041b031e0c0506030c1b0d09030807031403040609030e150d02090103021e0306130204030c0e04150c0e0a0803042102180a0606080901020309 78
    0x400c8142c491104017150060010800780e80380e2001c030720700350800e5802281005108080c8800c001340d0f80c056803500001d0b640402c650504e503440d202500b4185640c40c003980402d001c01032007803218000f01040905005041544d803810a200e4410b465440304128041c40d20304101011145600881c60440039299a51602a5181143c64601280c3e002c514224244052040c502c80c680c02485c010b14440c1c0d002e2100040e4180302c0f0b0602810403005907414500c50303400d80800302d04903141c0009039262824905001601e075254500141c0091050780030441500c0c1350b0a18002c0511b0002004501c04c0c001580d5800c0610850101802a4021804010141c00320b004040c401407421012141d8000e0042c6484907890080d02c0400040f24440e41103c40081c01c0c3d1120300c0e1860a0a00d41800148600c2000350b16192402c00c98045c5522450300c0d18040b01400c00b0300703106540d685d074444071580200b071000c4421800c200f81c0240c01440e2a1040305e0201c2e00000c0014820441842500d106034100c10203003040e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 308017419 1250 308016169 308016179
    0x9030a02041d07030c03061a010f030c0e0306180c0607080a050f07020616060e0a031205040318090f05160507031202040b0d0501030501180f030e0307090c0c11030601050307 76
    0x240c680504840c4140301c0c2c05502007600e810400515000754024a03c1844403400c1d414250283e80140d02000007201100c004421983d0380095650030000303584c40d00160b06c1d10810021102194110b1103d40d06110324028003000920b20060403185900510854429091004c1802940c3c004e01c403001d060b00b9001d000c41c6002c54043d9004001e00800560030501d8003800b40e0002e0001c0c0c10900c020607031000410081000c0003010f00c02c4403132445070400103200c1c032203143ea80140101ca03c00d41e841503036074941c000705003010b00030010300c0d035410041090521200d4680100c0380050822103008503000e820107000c18440d00c074019607020210200da07902844c10b022070300c0549411407012040320031203508000015008190101810340350001600204080d4550308101c1e00b514882c0903000d0040035115003410010f90300040500381d09a1508281c0583c01e60b80c1c0000741800385030b610402c0b40a052400d5650b1655000d2303025007065104002640d070b4101130105150b91004c0900442c2c0d0541d1103a581400f07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 308018669 1250 308017419 308017421
    0xd020604030c060204050d05010b011205060a0513060302041b021b10031a031207020109090b09071214130b0717070c0f05070e010f0902030613020d0f090c0602100209030a0204 77
    0x40302c1c0740540c5015181507652404242d50400b030a005a556940d0346410441ea0b69108160900131403031081c0610140c10420300060842c1540c1c0f08181c822160036542e0b2642444682000c1c00440d0000c1080081c1c04403826000488401d41e00141e00500600794920700c0c2c0301c0395140c006515900030b08440b00520702c0c6402580201050141e00325840c2c480111810960340802a11501894071115a0740740c0300c0e5440050071440d40d58200c5440d83d400c040c011009034035010056680f0000e5498141c25213140c2c103d464009004451088850600020030020345038450340c00300844600c5482c4040b12680c650b04101e44c1d0340340c040384031480368944a001c42e40e61441000c40c4c081903401088010180c40031961030310304c1c190080d848250a081507000400140320000c05100c0208a0007506520354902400099401481140b0b074808060703000c1035402d4010903560004014030102801000301c41c04a040c04c84400000e0720030400144241e0080d086049154002c2da400184041c000304101e4401703a003000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 308019919 1250 308018669 308018687
    0x807031b0c0305031c0b030c01051c02030a0b10080f041202070803030405060604110414100c0f0b15030109020a03020906010309081b0c120d0c051204061d030d02060403 74
    0x2203440c9088805503000c15115411080214460001156224100e00041d00d002d00308041c1d000c140351030010000c009460125407540642024a00300359140700e001496800b1004498010022910100401c105a402c942c04080780702011680d8110940119400721070825045406041c8802d49601080000321410704400c1c4008590040d41e00180d00d6005040c84c5800840d400c0e5032662100c018410740c0d00b01840f07849640060303d04601e1a081c213002e01700e000c2c0c2d00c21103082ea000d0001e03015142c0c0074038860030724644a80c2d844440440c482c4828148607070002c1e02944d40c00000380401800c9281450b05120306440c03554050711390b507403180c0b82d90200084514001c0260f4107040d00d84900c1c00c00540e506c0001c018003540031100984403045204000e00d040c444480c01c40c02802c4c18590680d240c6070028020079500214600455501340d1031a10508084041130f021000708400700b004600d480d00030140003003510001d4000c1c0c4028848004140c1d075540054006005604036802042c00300344034502075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 308021169 1250 308019919 308019947
    0x50f04080d0905011b0e090601111e210304030e12120306060706020412031202031e06040b15070209060406031703071e0c0506070206091207020a1203052203080703 72
    0x2d10b003d0202620784210208007040720018040c502204801e1405407d25a084030b003e1034010804100344440c0c0ba038074011254501c008900c4e00b0700c66060483c0070000340c03059408a01d000e00c0201e00340704500183d5002a17404402040d6401d007141e42c2810003019401306603407070381e00904031380701401d034071031900c0c0d1002d041d03103411140402c0030b0707000320344035000900003031000b811110342d01e102c0f50070024075140981802c1d5001c00e00400600c0395042c120032b01c04121407188400d200c059252400018018503e019142d0340081022201d940804141d1010384440da009440c41c2103d503540342c1c100800c0300d40f42c0c04005d0240050001c4d00d40c1010495016503800082403c00c5e85c0c0032000504c005150031190b2550340d001958190010040040500c100c680000c56400105502d04002d81c01d2919070028030b06840483c4004521002503656024a00303008107103032185020303407070000e0400801640c09075460081d03d0410024610381d43c204800100c1c100d03070f0004c0c0518245441c650313080302c46c07100000c02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 308022419 1250 308021169 308021171
    0x60e0f030c040c0c020604150908030f030403030c020a020a081b040618020f2104140d0c02130917090a0b040f06140c061509010801060501051c0e0d03060306050f04080d090501 77
    0x11350001a150480108003402c01021b002c654110342500081c00854950007942141d041400419080300901c1306403034000d42c0c98100442d00b005a510b0032440c00c48001d41c081d40c841c0d280040001c003003402180044451780c189059402480e0b02d01c0500098450714807990f200051040c02c0d200001c562076018010711514103800030310b41074810034500c22071150016113440c3d690328202408104000c130368101902004207806480c5200621700d014003c1e00d4098400303400b40c0c282118a4050b5102680805220742d4400300615915181040f1030303109420000f4000d0040900c00404900c5401c1c80b420742d406c90304904015801a41441000c03119000803848448061a003484103420552041c80650700c943c0b207524044092900440400a8010040e4032030803850b45010b4083c030607640e0010480d09011800608142c0718006c601c440300003404020342400c0e2070700680061030483c59142c0c12240840340203480030f01603600e404184038011101039030020820346041200b03845880d52034100051042c05140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 308023669 1250 308022419 308022437
    0x203060f1206060f0d0b0402210114060910180b0607200f0405010f030305070206040f240305010b190e1e03101802130b0a03030306060e0f030c040c 65
    0xc111000001c6081559541008003004038508060108070b100c10802c89440c036040d4240d8940309110710010304040d000321011490081041503484003101c00c402440020041c24140c00050340810fa4142c404911660b08500131840e46001c0303030120f00c181c41402145a41c0c0800540401004202d070041e03554019a0910090010600703980d0f440752299414140203454450783c00c200034502c44910002c500c940d181400520840c640540c25409607585410310705c0d07407040503000056003801998440015a000c4c06401300309600d0309801485081105642201e80210a0100f5015500240520280701c0000d0081c03c41c507200c0c18102c5a03e010242c103180750600003140208032000340b0711a0100c080e01d411112646a42030800101440d8604448104101507141031042801c000d9018040d00c07c09000542d202403841ea5400914a000c0040c00a08034507640c3c0b401501a01c55446407038017080f14200d0904e0300c2c5c2040c10b80c000500b4001800303409400032181c100002020116001d20170031036000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 308024919 1250 308023669 308023699
    0x5060603221a01090b120303130c03080a0314070309170306120105011e05030c030c01050906131d06030a0c0b0c01020903030c0f0c0a0b0d090201050712090611030c060406020306 78
    0x1801542c007503240701040119814108000e017030710b024114a500903c00c02c00c61000500010080e650403c9072050f031081d0750070240c10001005004c6400c05410310390b0000e4400d010301d801d07920034012544204040129a5a2103034140c00311000300001418014003581c800191242200c01190f011100418004c03030896140400c50840d00242c0002103178506001141e0403010b000c000080040c0411402000e0700d140110100f604c802d0f00c0c2500c0c5040c010040790b54000b566038903068402210841400300101d9036a008507000c690184400c2e8500f01480d580811198240032a040c00e20640000ca80000f4a05d08507401030740e60320898801007a0b541c00d0007010500d581c20302c02001c00c09401030007880c03100d1000031100d0403c041040300b507118506181c410001c0342100c0060f40c640d40e4a0a00000d60000d032400144c41c14820460020481100400300c1c68045401c00745400070342d41d81f65240740c081103075040350301e07aa4480c141c004245580000000390000d8056001154400005094221240009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 308026169 1250 308024919 308024933
    0x207050303040f02010e04020a05040e0c09120a0b0f010617040302070f0e010e01061b060b03030708031f0906050102030d05090c1009030615050a0306050a090c090204050901090506060322 82
    0x103450445184007080d03c10000d5603071244030110509011102149850382050010706184540c0c03164241c007a255000081c01540208142d5040102c06003d400d500d8900c400216101c4108039800c44000501801140826000d080d07041c0c180d55840d20b65580e070720150044845c4d44003006004604601c00c03401d01080c1c4a40c0010004018240c3c40c02c6000700394101114405008016002201000b00111645144044254a00d0700054004600040542650f0b01003421881100c40151052030008248900c1d0354921880140707014420001e000816107402031b4805440c0355108050040c5c3c010710a87c50390301c409921864001c070707007030701110203105d5080d01051034006848004e03000300e0501c039420028032016000e50742000842c0352009a40909000c00aa42154a8040605410358483c00601700c1107455003d8076075181c008040000c540d0307131131030020041c0d0b004c2d00030366000e02107035000041d504a4600681d0302a0710000d00150640e40c030001e0302c0c0382c11180075410441c40d20140031700d03401048003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 308027419 1250 308026169 308026171
    0x305130305120703031a0d08030a2c0d0e010f030b0315070f020f0a03020a080c030d090507140603010308162109050424030b0703111b0105011a09060304060207050303 73
    0x40c0c0c0036010749407883e40c1405000c459040850801440000004940d00d80d00c4a01090b000780c0d005112030b44a0320385410031001080395658910708403d060340c0584c0c424070409403004c80c03906003100715903030600e400070100c641ea01c0106007107000c40c82000c68107a0040c0240c0006000030b50140c2210541f416002b0100c508100581c0c030007000c68101d070842480703941e06010509010090f00d0013801c00b44220f03540203503a0000f140d0301501c03206010407544940c02d418000c940f0500140482400440c0300c07401c10a81f19851392050103846070108640380418108002920704894000c00401e041610084501034041841f00080300c0341c1e065a10b18a0f0306030784c005810800d0a040c1d0392200071050419040c08221501e240400f80810108a10600e0640ca080c0010064942c408481c81d0546c07941d60052300a0300800190303c042e0400400d821409808108c0c0c040000b0441c10002e0100e660f8a044200505001d601c22406d0f400b0208410341840c00c0050007140c0003841002e005180072040e8840344d095407c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 308028669 1250 308027419 308027443
    0xa06030b1e06131e090b1e0f040c030209041b061b02060c120a03060302090c030103120c030e030d020120031e0402130513020a090c0504030f020a08011409010c09120305130305 77
    0x143c1c030085c004c10710038040c80c010380c000303212030085414034103420900b0300600780101407028403d00a0002010081046200402943d0190442c42c00b401c0c01c0ca0107802550205420001010b00d0f075200048240c418108035004071500b5400f00c051007050380911405501c01c1c2074841151103604400d042c00014a00100007481480e03800107009400c2d44100b01c110b15024003540002c40e001c0c401071000c261000c401607580c1c0d940f8144603c2c582510301c1c007130710300404942009515020300c0855105068042d00070f800550b40c006803610145680000402c45800240c0e2048002640d04803a241c072440c4200941d078100340000c2080d460074a507000480e06850040750302c2c4000f011140140011810b003003101e940580302503101803100c5556200020564007030361001a12104403404002c0664070703902008405441040000d118000c084070344481001d42c1a900807846610381b0300d00c049a54440c601c0c540544e00e00c002d2020704a121034404407500d41040d60109040a41644000300144041203545a410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 308029919 1250 308028669 308028671
    0xb1207051827090a050706050403080301090b0f1201020a17010305030a1d040603080a120b012a05010e070303110c0d1202010b1906030612260c060a06030b1e06131e 72
    0xc0e00902d0704501b00f05241e80800b0500200b40002d2000030303048015a4103640b07007480001a5036032140d00041000d40300740d040a401810500503c01c0c402c4041d0014650782480381c0302d00c52041941081841054800d21019103190001d002203032140e4804e1032440c0311205280700e0142c058001d40d000070100c07032881c1e000315040e080000e1812081030f040b089241e900e8140400030082c51140c000080e1090a5000c0325004001c0d064800d0790074002c00da0002c03100317103800500030000c20300700b10800c41d070b02e10940c00241e022815076040400750700780c0040d140081103400341c81280c42c060640c0e40d0320540031120400c2c10035552a58038a080685580c5a210010188007090340c04142c5400400b40c12200ea503000044200030311407004000ca10700441d04503a014000400801d503082c00d880c0b4000318068800240b80600031013061180051041e0408020b41703000348280210354941d01c4c5203901c1c04015440d6982c1000442c4c0008002e80340c220304100c02000c0b18100446c00c1c8440d0b5041e1040034498010502ca50703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 308031169 1250 308029919 308029933
    0x70b09010306060230070b0f040b2503090c0b03070201050121081b0316060c17040510110d060603050a11070201021203040f020a0b120705182709 64
    0x140d0380c5030040c81c0050945001400b80d05c050407080c141811150b509441c0e01c1500005e9401c4180403607402c40310031301e401412608441c100380080703030140c40058400b076602078040d10104203224400e8007100004030700072501e103015a05524041d40070f0444031000751500c07200981c00040b8100c5400c011442001190f00010b0150704048105241c00e540030200314007070840c12140000a04080121740410303012801c4101d104144051103803461081c0c41c256584c00c00d01c4481c0c041040000e80080440c0051030f19120980001c1510700c0f411050210303000b0307017254465000301c180300030542d2000d054003003050705807480c10030002c000006890702940002d00207951141085035295042c4200e0301e001d4000040d480c03400b006900000d5131091070031807091035100e0000c045410010010f40418005a016050004040d642d03869440c840d04030001e10400c00200d5000030704803a106000b101c110105007820301000c00a0202840750b110b00248040c0b004031a84203000e41c0000002400b0751152114078000d11403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 308032419 1250 308031169 308031187
    0xa1b05100e03150105060d050a0b04020c0a060b03010b1c020a0302030610170f060714090301061212141801021f061a0c0d0507050a0c0e07032702060703050c070b 71
    0x103840c3c0c1285440c1c011008010040c03009a41d100700b1034100045851000c0f0385a03e44a00c520001c0001100c6030750b10070b04c000b9420726802008502401d0310340c0900e40421a4544a0303040c03500382c4404106c60340c0d004840c004c4a05103032000e01100800b07980068440019142c0702c2d40070034a4601c0540c1c481030300780c0c00003c0400021103090752141d10750850401405080c00c4180d0750781d980d840040c000505124041c00728039a02c6041c00140c034401c3c2e00c010000d00650399200c0080c01039100115082d1421140c5c1115044884d0050907401f42c07402c011090307103241a16403021111444604150710381140030300020f08041030040401505042c1c1048800142c081c6442400807881e02d4070700560340f25072810301c100d980d260000706030140003030040e041c026030300d0750708d0300c0c0c4a07040001c070183c010300f22149000042200a1110145840340d0f0544d2010408548114081d003c0b0005140200c0b055400c0d482002c0014140700c4003a12041d842800d099080101d1040b0140c10a0115040000a600c011503c2c0d58 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 308033669 1250 308032419 308032423
    0x70f030f0f1b1103030c071b0b070b0105030a030c1101031103010306051005190e071403040c05040c020f100b06040b04120b06010309020d021203130e15030304080a1b05100e03 77
    0x20740300342d075410b041d00c1c0e01ca94000c1c036646901004151203040d0300c0101d0710794107000c12405035050540344044078682950310381c0d1001180350002107055a90001800021915080010380081101d0309621240880c8210307a641244813a00102503604054848003490380d83c0b03a4000c041c6010f584074000c081918913001c85a841e0111095005074820b8001c4901c41105050f040c007190252003001c120840345545001065560480ca401203562a41c8004100800e02c036244940c10140c40084900b440b0016a1007800c903507880d41040c0d450452b402504040303000522a500005c0c80c2e80340600340f981020394844032503c20360441c0c0c0c000c0d48122000034041c0b040111a511584c0c0c00311b002d007070400c11056141c010400711482004024000c4901d0001140b110030200301b074500c210140f801d9515259100e071100c1135400401e90345d001360041c42507001d81e0342d450044103503801d458000004004652180c1c03030301c0c0d00a81150b0440588206000004169601d8808126100c0c2c8240e8440301c440c01c0b00c03c01414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 308034919 1250 308033669 308033711
    0x70e0420130e0c0708030103080711100809070b1306030209031c09030303050c03100504050a0f020a02010b0306010f030302030919081002070b0a06081c0e100c02090c040608070f030f0f 81
    0x881021010813680c80042d001a0660341904e4003c1c0d8406d0325660030340f41c10503003a2650048207030f000c401c6420344640150f0181e90144110804070650301e44a45d22440301285000d5004404002d041e80300c000d2059070720940c064100040e0050485010741ca11a030123500c4000e041d10100300060b0044030030310604d500350203466000710f00c0034601407030361a000c402106080600c0c000c2a02c62a110000706d401c01e000394001800c61754500c4001c564032503000c2c9000e8028400c2e50241ca00030300600000103000340c0900c028208994154014505c0c00011000b0400c001c0c41c40641ca42c60078072140408a004401048210300f030b01d100c09030059554001d801c0c01c1b40b41410041400080c1c07401c000c0203103d00e100210768684030b0110100320050031883d100050780c0410804c0382c11904404a644203001003170780308411954042c002d591542e0240c5a00118100a20450180c080412551004500f1562240e610514100390b10301d40058103903040c841d43c1003603840c1e851481c610306440300c00e099007005c0c44000c00b03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 308036169 1250 308034919 308034931
    0xc0a120206160e01170a0b181503030304120807230d1a03120a0c050a060501090b10021906060e1003020a05030c0f0909010605060d0c17070e0420130e 66
    0xc84410803048002884040e090b040000c0020718040401c0608505030041d401c1100022314100e0a1240e4502594090400700c1c0c42070810303080407042207400e08010040b13034060790b04100010f00c0d00801d0f640950b043c41e8090501d40030441420841c000b0385150344041c1104000354240c82d42c4e0380f0503000040041d038400440031900078012440340e658540c0c0c00a202c140540503d480d1a0301c079100701a080c2d61344001a00045d205019801c0303450100012039106074182c8200000821042000b10203000101c0100b10302c450160707100110801c48180781c11060000c09224440115080c0d0300c130141c0c003003210425030310088515002e02c0c1c24030031031030000e22007009850140c004020745030503030b00040c5010040344055401420614007103610b17801c5c207400100c007401018250968844003c0415030007841100c240c2d4001408042901c58802d030202c07102d07801040c85950300386490500a0800c40242520001200e000c8140d000d03120036182c040340a041d00001480b11050103500c3c1420b55494003000401c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 308037419 1250 308036169 308036177
    0x7030207080c0609060a08060312130e18030307050c120403030206070f1d0904020d0503030c032203050316030f050c0d06091103070c08070b010b031504060303020d050c0a12020616 79
    0x5240d03102c000940315881507a03d0500c41584130303d008241000101e07200f0748801070b00081d220b05041c40c00003102045500d0000f40cc2c0d00366851118074100101d0400415540750410804900b009100c1c4025040c0c200c815070985040307186802028a81d94080c0c1e00890140e00403c080240c203e41010340314540080f41d040c480e040103002500c10480c5400000214070503900700c00400d05644900c0080c0d13041c55400005c07285e5900f0700307101440c543c0c0c0085030300703000c580140c002d403002100389038541c0c030103c55140c0c0303c150030768942c0408080681c00f09003000c805c05070381e050800a800c42500441e03002d200b4000400340d031052069000800e6411a400c09019142000d00c520300c80300d03694048030b52082d0709203050300190354685403005052040b85c0014210701810070000c0341143c2d40c4001140180c0d1904015848030750f1900910044d034083d07210150140c0c00141602c02c071a4002c00c0101000c0030302100351803012140d1b59a0b803400b56800388a520050340000b00b080101c200f015040b0403018441d0070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 308038669 1250 308037419 308037427
    0x2a0406090e280501030b24040903110303070806090108030a0507020d03050c010f0b010f020a050d0c0807050f011a03160501081f0308070c120c1a120421091211120307030207080c06 79
    0x1f40c0c2c404d228441d070380c0d1903000c0d660743c0c8a00c400f4507200b91110f4544540220549580e410880b000a2000700281e82282c81900131800001e07041e480041120445011a00ca10341059015020403070b4800080c1000e03000c1c000204420040c0c10350078410300050609050b00001d802d201400010316580495215006542c445028000803c1c0000303400301840d016490074803144d400500d000141e034080d00b60010301500c01c1f1007600800c80010341040f840146c5c0c01d003801174242d9000c3c04040e0740d0403030b00821a41d4204000c0007401554862210282c1c08002522040b0700f000d21390152101510542d8404d41d00c807440803417400b00f040b040c00300000080c004903e6401c03407201542c0342c80c82e03150b0a91158420b01003800741042c20840e03011090311b20310a14181d04081d42e2400b800c0c0011945101480c00403610244802400c407240601c10100c16071300070b59182d10b581c0c8038a0340c915040f050700e1000c195100070656281c802b0108100024168544243d002d0542a40b038003451601c0c03d5120900d01380f0500081c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 308039919 1250 308038669 308038711
    0x3050105010c0c0b0a051c1a042315181e0402090f04060917090111010204060504140f0d0c090b0d150203060a0e2a0406090e280501030b 60
    0x3c081d041551180991039654003075401c403e5510303100300748030038080c0ca815918020b80070100794009401d801850050140c03d01d400c80c100030403a005800d04094084072604180349450031081c41a41c410103003128800000d4900000070542003d805000c003001400d001001100c14030120b4440c46004203542100c0d89081590000d006400c000f8100c40751100034100240030300c0403a410070046950000758203448140f110414050b59800044240d000c6645107203502c060307000520883e0200d95040d65107609090524450320050070480104641c010a1070101500c0d690385c0320103002c1091320440c0c0e81d244103458000c8850507600e0546202d0721889480b101e65010940e61141c01ca601007003140c006a803030355914009000324117503400003580350044608014a40a0b0084031030032455558103512810b0381d001c0c1400c8442c0c4542e00a0000060026004020a1110b040398030381054181100c1d0314082960310060107865440341550a1160302c4200401c20b200010003480d8204124810124001e2030f04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 308041169 1250 308039919 308039933
    0x18171c0b060a0c030905060d0f0c0908071202130204060206160201110901050702030118060506010228080310080a080403060f0525021e0f010e031603080712180303050105010c 77
    0x401e00303040500c8500f140500030548650803283c0a09001040191100d03080030807400103026082c1490380040c9042c65540025005411100c00c460024008000c40380c180205a41c00c043c06803000c80c0c010801904c1d075504040d040c0090b0002d40440d030b00030300c058070703103404089920b142c3d5000000941e49440000798241203648101e0f20742c146c080c00d01680c0c0300e0039840802d0050001340100c10303408801c0c500c4182044821b070010350050800b41d0884400c1c05030f69103180885680d0882003022000c0103030060740041c0b484006943d0200d1021400e1569540d2130082c0c41c1840d41e940740c1109c7d0301000080c1841006101d1042c400e001c92407240401c8035141554558000141d5403d4004074074070410181c01d1a20300c200603010312003020b5003061005000600056583e02d011400ca420594280b4004011074600001603403502d0402c2059441080d0550324190790f9400c000e8014410454125290105042c00780035031124203944075888000310780a0704004003150410380007141000284813068012900d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 308042419 1250 308041169 308041177
    0x5031006081506030f04031e1d0303090a08060106090902040e0a0f0b03070303110105010503010225030215070f120c05090111010609050c1902030f0d18171c0b06 71
    0x10707050460301900d4108041c0e1a1075181007001c0ea106400001308141d07261200c0425009501c291030340710300c038084a450b1155400d0048a01000140f55514907507071070b40502c5045034040b4018043c0d83c80c00300d111005c41c14122864201c0701d10b40d4004001002039683c002c002d80010301c2d09010450419003001c04890401401411000c1c4942e01d811301e07810102200e03880080b0a540080454130000d0362460040c1c04010180b8000843d54a41000090642018000c0ba0301038101c28189036a4800b640c2c0003189442c0306400300350214810040c2c140c824000006d5103900403025520340c0400703050541c0004201c50140030081c0907050405049801c42ca403c082504e8581d1001d003850441a105011000d00401141c2d000c8034201d802e0006202540c0740703500041c011403520030501000c3c00c02250042c2e990f440307200c02c00f80800c1000c03c88008008084c2d84412001003542082d0010f04016803981d110401455111007450a000280302411600d0425902507110101400b48030210b142c500062031401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 308043669 1250 308042419 308042429
    0x90f010e0a0806090a152c0708030a0809010b01090b2a0a0602040e010801020304020a0323010507030e0f120f090a03050f07210b011701020f040e070f050310 69
    0x514041860340c0da9120000c40d000b03424000219111458809019550741c0d074a820143c0d040d142da06082000100f641c02905000d50402c10840f43c50761041e0b610102091414442d40c6540c040c5010100d0688018001000000c41580d1441c80904000b020a800c6640f0000c3c03aa042c4014503e08202141070764090740c00c1c224413903520f2000c051007020301c2001c6103481ea2b003d02450080c4140c0800f00406079010b0001e03680103008a001d1680c95519890807440156800b035440608aa0100005070201000101e4850364014003044402103040c0c01c0c0c20b65000f071301d410012a4482c00070500040c001c1141d00b031407104800040c0440051121000d00f0340c41400e40203900740200090008254442101407070081d640301003154044080d82540549030f03c0907005d9256008440f40140291500301082c0d011155008600e040859107042c0c2c49000040202c0d0850080c4d5400380100400039600b80003030801004c00d242c4002d100d10701400028400c030b0404002c40d0a001c4284140480b00b00450300b03980c04c2d60303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 308044919 1250 308043669 308043677
    0x311060915030a090614010303080702060c030c070804050d150b0109030f14010b060f0c0607030902010e011805060408010506040509010507020a0f11060a050a110d300501061e05090f01 81
    0x5260754807441e024180c0d410020f46003905044054013045000c4107a07d0480c2e01907a01c904468a07501c0c01240c64403401d0320000c5002000380082114000e0140c0141421882000590310f0140d031600811008905451300f030310000c20b0080c2d8083c01040d6405010b0206200b40b8011140505598610707081d84440c04001c1c105000030200d040c0c182000758072100c04260001c207001d855807181a541e00c600d9200c69401e0150340580b0b00418140da002e4003407041e41e82d505031a02401011000011603520351001820f0b90b0100352800b0000c0c0035158080104094890310001141619010090000b07035080a05030420b140c0c509010020140d078081204140e00da408290420031802d281001d80b40144100165a4400800038105403440c8c0c0000050070629175541700d100c81e90001a90942d201c210b4843d41102040c0c0703204080e55a80200103a4008044407540c4882008030991000300c1201c800341c200300b022a50040034201e2240c440c054032818507646241c01d625151411000c5503240c401040814180 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 308046169 1250 308044919 308044921
    0x10504021305070f0522030f0302010c031a010309030e0406080a0215180603040809040c2a0b010b09060c01020706020a18080703021215160e010302070b01050d05160e01031106091503 80
    0x10300c581071800020703003100c4240201b5040d103a0904100d40e00c01d61104130059880c0201501e141802401079001440700d01c00441041345403030005401402800c1022010020401800340e4a40e4542c8600c6014209440080c0751400311441401b159881280342840e0000c424440719640c400010000905504c00392125a1a6140c40c079002e6000d0080511041e8840c0c03c101c0340300c81c040da21004504a1440c48401c0401d0111010f4568846004c400d001030019404400140301010401e4018102c0d20f9010780710301c0c40c1445038002c1a003240c0104501b11881a0000340743c448455000202d410180d60040c43e2101a80c07400c001d9566681c01848024060070580040c0484c5c47d600b031144200d641c405443d00405441c0030014103921800c0d901e03400740030034201400401c540d40700384203032a4031645c8400390b41c410b40d090a0410000b2820f1000072100c603c00ca45400f24018241c5422000405036103803004495411032501400c4071404101903401450f081c49107402e42d90b140d50184a072061412440d90743c0e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 308047419 1250 308046169 308046187
    0xf0301090c1106040b0a050c030f040b1027050f130f060b1f0f0309020102060f060a260723010c08091e090601030212010b03130c08010504021305070f05 67
    0x2c0c214031250308480d80550020082400050070b2101d1145000c10001c00c02c0d03039100e013202d142a00007599018000c000741400a03000a0003180e006400480d0b40444002156840585a08910103421004070140310921102019402402442d8000e034a0015220051130007603110310400301d00a030301a0000e41c2c009802e00030301900d940100068040540100900806c460aa02d0981150704004002408481807080c2052082c49000039060781603001d0011034883c0c041840b8030080192409a00420840000622210b14078964084141c4d05400d503070040b00e0910082e00b48501688603140b542d00701030420401100d071195504c0049424241040301c09142c0c20a502c0600641c078440c1d0708000c846803581480c0340c007130f14044600e134000c480b02d1a560b40c13203400440071390150513501c100030081e1200502010401202a6a07c0a058960301c940b9070581e88a21700f03240c2840c1e11403c05a50345600388019403c02d01003100001040d1102801340d420000402401c2c031681a66120400c0004242085 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 308048669 1250 308047419 308047427
    0x40807080909041b08030406271d0f0708130318050303130920090919060608010608072309130c0e130c050d0b04140403050307090b0f0301090c 63
    0x100d801602c0c1d840b00e454245011913018900180b0f41601c07202c030f80c90004d12880004103e500755280d81da100340c0b11142d15508600f0f030400c04a440c9451030720405022940010413011004066490b0a600c080d5040048610100210107401282081130341d50810018042e0040002c8000d5031500d0b0410100c5001d100d418254070716500695450b000026036000c0c03e141091504041d591000820807000350811101d5980340000c02441444500a0000001b6840e041000307682c0305100b20010082842c8043c5054101c4026402040102d20a203005009507540f02944540c044501c0c02c0009000b40c8010022006088103150b0703503504030001403404282d8503240b0074444200102c410521801c101144081c00080030305031960b0090148940304185a4968050030100142540300d162800c0e0400c500c0e940580b48809c219500300d515044200c0b081d002c2c08140300d101d03d00a41c0d8140e00c03420080d80003801810541d010240c4200c0c1480700c282c0e800001c8003100e0440c1c2c0c103c9400203201e42d505100340c17 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 308049919 1250 308048669 308048677
    0x1503040302010e25080c0a03030e030a06050a090314031905180307111921061b0f1d210f070f060f090e0f06030c0307060e1c05030304080708 62
    0x1c0c0180607007400c282103c04c41001c0ca030203445a901d01c02008503103810080344d0380c0383c101e884198002c00d501d000700040b034020362454100110142c16502140310507100d9500b980d1050703071a0082c0e103684003810000d15600903880c0c1c00403030030500303200d1071805d00f400b12000103040915100b40550381c17200803c03200480242401250302118090382d0300c821060914419440b0341e40c10300c50003800f264061245807105111000156482c008d90017200400c191f100d40d81d41941c00c00203d80b21591126150354800d020003005252800655070240111100300005210201302048ac807201213030300c46102099a030300038031180d00c0910381c0011082100c04805103071a02d1203071513465a60b0302810002203060a003182c003c80540b800d64545081c00340c0340c030034110f640c00c0080c03140c94601800076005c5241c8812450440c0c0d0030110043c01c59043d1601800022704000680e803002e030118003242c001c140e213401c00700d02030005070f100300d51070f00c080e001d941d00d0320341c1c4074030000388024246080010008100144e240c162 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 308051169 1250 308049919 308049941
    0x412060b040204091a0f0102030301030302060c0a0e040204030f03030605060c0d030203130804030b010303111605042004090c030509010b03030304030c0309120c030515060f04020705030702151215150304030201 92
    0x900c1750f40d004007611640341c10a048414060b80c443d001c0c20752030f03500010840741201c3e4940c1c01403c0710b948030b40c0c000c04160010301d0f0740020019a407140c00d0301075aa078005840a0f50060404140d02c201c14680a4110b840982c0300d10b004031030511400111403000302d80e45850320b0031810056940e6440140d4855102c1002d03000802111000c1408000d0203100140749042c0c3e40f2a0b11482034600d80c0b0460540d880d999000290544101c1c00014070143c10150800e01ba130795000c0045c080c562007003102c03400311034000c4d8101882c150707030b90440314800f60b505004030b40e0000170b45030080001c1140d440102c1c3d181d01c40100b000e03062290150749a000c1610802c20170380101903180714801908441c3c07401c500003070340a210036141445000d412445962220110318019000144015180c086010511003c2d401255040d269408107002d85005a207940031407004d60700196032100e580c1c03d1200c0c10004003150141180348640d458202d144402e841d061a019445024440419241d03580c03841c0480c090210b031814 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 308052419 1250 308051169 308051171
    0xa0f120609090b0a0b0307090e031201060e010f05090f0108130b0406050f2409060402271f09030303091401020c060609010603090305070803310210050412060b04020409 74
    0x1002186580001102c2d4440d5501545a0302d030201d8203010b03210422001ca41c113070410f01042200d01da05a120002d61340e8144103481c1000d5810011480b089000d90202c00820982c2c40240c2e00b945e07000905424600b005c4c2001e500b04100d4001089021903032091160501034103c1c0400e01000b501007482030041d41c0203000c92054a00743c50b0580c094070068480424000510001c249800317884e00e40c000c110314004c00c501207442140c004208a50384042d008942003542002195410325102090f40e88a50744100c08480781f00f1700201340000900348000a5044014030144200f41c20751004500c0c08580d00b500e40400d40c943d0a041070700b1121441104400a580f00141e200ba446c1c80c04188544180d00440e20310425a985880c00e809403000c000c002000110304000c19000115401c000d59000f040e4000c0342d043c4c4040c1d0030458030780f0201440803480030072055202c500841c40e01c12403459501600d41740841c01c062910000605407501014001e05040c2c507110381c411591120b9040d90010314000314 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 308053669 1250 308052419 308052431
    0x80307050d0212040510080606091c051009031b051006030f030908060c040b0d061703040806070905100f11070f09050f0601170a0605150d0e0607050a0f12 68
    0x240240d9904040e00700e00700940100940f4280300320300c400c169011508007800c85042040c400a044500420040c2110340c0003900780007043c101d459070f03600b100100141b001104940d101908140f46880c1d488500c03105400d007400301490000c0e07070050340d00c1400c03010600202c0c43c0c5082e40c075103181004200648816014070b4904000203104071040b1200c140d9011b0b40b00e4101c615224106161250340464424200c20f90030030040140c0c0310088020185600311060000c0d0440c1c848410502c2c04008012446651b8804141480030303003018040160000c0b480d0a202d0b00d981c0c54017010034403140d080d100351010300021402003801075008603160855491040143c0c1c000c2ea032034800d0003491749030078050f0b403e0280c5000300250301904451000c0f0b02820303050311031092411202000004505009060050b5192036443c000742da03484410380e149004011a80b0345403502010000b41040f11032502c4171820b150310480910007015000000c403003071201176181c2011a143d00705e0b400e9400941c04840850400d103840 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 308054919 1250 308053669 308053673
    0x1020a0503070f020f061303050409020304030f1206140d21021b0105030603060604150803030a0f0c031e0c0504080f010906060b0703050316110a060c090506070b1b04080307 76
    0x300065100349079645800400010072039040780c0d138803031002d0040034030390109000c1042c01d98800000e42010307200b468510705d0162035401040c20f0b42c00a540440101710003642c24140390b90040f0403201d0b520b0450700f0410500e4681a00d0084084a68032460701904140d0f0340725040c000240d03404035080c0c0d4841d001c076a0300742c6c850310025a0780160316912000c0300c2801c80040c10b90341c414000c0300c1c0507000085c0144aa52601c80412000300969844480075000360b1800054102c07044c8041e504c0383c24010000580301c1c4904100d1026a9280d603510000c062904000c404902c401010284240300348040000300c03290401c0f016038641c07040d038001039240d01c01e4000034070703506005402500e10a4429001407010a90301d8995645038001d805005000c183d00380005010100440340704a04c4000364a4150981c0d603030010700b181001d01880c001c1d03455030740341c07500500b0039504061071400800c0300369000d502d0007442c1d88a070b401c07141001d0000d48c54844442c10b1300494900540640340034104180c00e4075980d00c214 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 308056169 1250 308054919 308054927
    0x5010b03100504112514010c0915020708070e04030314160c08130e0402030d02010c0507080c240402100e010c060506030f0303010b03160305010612020702030703060f020c010608030c15100801020a 86
    0x45c020454491800c8a40c0050260060080d10311030b607a15114840c501e410607450508030000c5094060443c850504006001070041117060000c00e2103014600032424241001800da034459851080310503818018445800d00996074188d041c11103160002e404007142c40c00500c03a1140544440c6648404d02001c6540303814100070034003030ba00c01c030101c40c080300f900801030f4240c3d88403030b800c800440e40620500d07020403449001048049060401e4800206210400031144411030b50310310041d50511040200714104452500c042011504180251090f0000006c24a0a1005004005648031700114880f07403400c001a00c81042d000c41036980325070715504451f603550007c4410030f1580302e041c220b054106000348980e40c10384246550343c45e6070300e691010860180d448000c08a03098414454000089002d5105205a90208034400b5a50f070468503046030940e1941c0d0007079125900204424000c4034000101422480000090014190340b00540701100380c00c144d0003400700e5400094204402548 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 308057419 1250 308056169 308056237
    0x121302030f0f160f0315020c0610090b090f1816060201050907090b0609040e21090a140f090702100c080a061707172e05010b0310050411 60
    0x400441c1c0346a0b400c07101c083c041803220320404280180d03500041c000f24a80c04260b150764022848050703c2c201d04004080e14005081710380607214030300300030700b4403021181d4000c018510904032020586404c2806014140a0000d8080c40c0701450300e0896807241003007802a500750014015800044965a0202a0282070100e0b640f032801d0007010701c007203004403c40c410280c0740700c00a81607504010001c41407100400d40a1030000a520a0700d50300300030342c2d6200500380c1d03040d00c807411389688607615178091000e00720140d0840006900741221810050b11a903001503500d180441e5500e41980354040f099003045030001c51700c034109003044203842c0c6850300326081c07501401d4884010040340f0794035118013600401030390110303010b500441030800c02c022686c88264824090901a43c100601006880f403c10010039a64a48201c40b195101100d50341c0f481010300505a4250403444e43c9400040b00ba90042c00b400b4442c411552000c0f40200c206038074007640d0030030b520707111030b10134a600c502c1498900c040c2c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 308058669 1250 308057419 308057443
    0x603050105010f120c0501050d27020a080c0303310605040f0e0702150406062c07020106291303060209040e0c0607140c030d050406020708070605121302030f 69
    0x81c1c00040c00030740c02c81c42184e020307400903100c60b01c0c5400c0c81c004483c20360100110264154032911102610060b050380401400303103e08142c49200e8061045c00480d241c140d0000701150005401e043c1d0945000c400c940c88140d031041c404a0354090700e111014031005c44507184003010325104010644903044401407040c0c0d1a909149064196510700081408004840440050300583c101c1c100041900103226000340c41a90b011658540300d05c01c3c1810751510258604c44801221617124003a590b4803100d40d00030140307200038414a03090151003c14101300d0400d1103250740c005c690801d1420b0342442521201440c00200c101d410761b5a08004010b50020028036101e0303031824070300390a08a000500c4a248e032a000d0043d0741440390585501e00141d00c0751100710fa880c012016402c1290b5014052580a0813544c0c41d46503c6904150000346003000b00e4001a44550140800744282500241a942c90800114440002d513032656148003070040c1182000750148600d843c5041c5460011501014201c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 308059919 1250 308058669 308058689
    0x1e0f13020a051e0f0405090406060b0c030a2604080715050406060302010201140f0c0d060e071116030c140d050a03020d1803020a06081b030a05040c060c030f0f020c04060305010501 79
    0x10100030f0305481144038541405500e03070800c200030403e6082a4070741950003405230000060b82c1d5950713501c0d40b642d0f900c5568441125080000d0703035906190010894005d0100202c40d12001e8400c004501c110084090409400b4120114620040110010070380149100719401480345007418a88140070704031501041b0b01550070804180d0003005003004552003000700d508484425290348138908150f82c03203402d08601c060303240c0c3c401007003455480340494018181d0759102c10980900d0100d50341000380800a4082044a0040c1040420041c54551041c0e6040f00601c400c0d00c101d80c0001980032101e0507009045000f16000300d0203140c0c000c070300c400b104115034075a4158403101c40a00782440701e070b40c00020750040b880e12051011600c078044141e4024410000075044440d422000380310742e007085410b0b2000c1c649070410001007085036402c001c0244018140002c030301c0425075019040b0021002e4140c20812244945001c562007008403060004029004001064480c207016020300024040e0710110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 308061169 1250 308059919 308059957
    0x61803090b0307020d1d0603100e06031902060901030603290a0b1c021c110102070e0f0601080601050d020406050c010e0d0c20060a08090105061e0f13020a05 69
    0x1500e410085a200d043c20344d010f85001c448400050b1841400c0c0010a046070103a101c403d07020341c0320000210700950078810a0b1b82d54034600711111103070090007032400f03019400884070611105071812001050960460f41d1548500e03180700101c004000386e6002602100380500c0b119419000d00e00003111a244400c14054a90b84200c9501d094800e860030035508207000c0851036aa4640460b00194407520007031464240884c8600c800b40070480282040c0c1c2d040f2083c0e600c0c0e486640c2c04010300da00500000340840c1c10781c505080010045240105800d06014401d000101c05038031550848401c002d191204546450700c40b40000c10a8100e5490800d0350342c40c0c5005419540740c0024480b40d84403156844030070204541d540c15041440035a1010010710029501c080d860351440041c107102003a42d55010b01510302450414213545000d480700d03014a54041c1c4810807a44c10290042e10b851041c4c644005016608000c01c4071003003e044040d6800788082000c802c0c0a500c000104141e0381a050355042c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 308062419 1250 308061169 308061179
    0x3060405070e06040902070c0801050117010606030501120f05010e0102030c0915040b0334210510060c050f010c0903050f060702100b040b0306010f05041a0d030c050a06180309 77
    0x1001d840c2c110707075640c09403040c4010404520307079400801d0750b02d10410300351203010340d1801940d0941c2c4081e0020320303160503490030842d62100240304040080c90546001c1c8401e503d8805a00d80c0003e8651028001001030600784d010302509403c84003819051400855403494031901e20300090700280c03c25481503c1000300c94a01c20b41d560150b5042e10b035080081461511160009a912503500440c0102500d06c1660ba04078030762503c0403903000700e02c4d03921803000d00403c1000c4c100d1009030032042c1100c058608000d000c0302008003509042560203504000c00c3c00d107140e04025207803116015602c18603600381a107116856a0200c0c41d10203ca2180b4103c90359080785e0081552500000c0361070301e00691005070311891000958020964001e806800010017100c06030201e42016400d81188275408e005440400003400d062044040381c030031440c0302000741e18101000601080b800704015080091401e10f040510009204004015a000004003c200807200000c00580860740060b80440c2d00c10500041d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 308063669 1250 308062419 308062427
    0x901060504150806330a050d0f020a09050103020f131205010e0325020a03020d0605010e1305120315060301090c021c02151f090e1c0f030b150f0306040507 68
    0x2c00f034600200842100c95500403109003045401e295840f85e910200b0000c4e03c0080c0200041500b24204c0d0344030303561094041c0859040d94200c2c5060f4908a104200b081c7c0059801030444040d290700b40f1380580c0c1c80441700d4180201c1c0c0144040290903d00340f00001403030000710a45a008184254002e2003c0880d98100c1d54481c000c0380c410106040d1650b1f55120510120030302c1850003403005268000c41e03038a0b9004207102e1220003100f2200e00c0c0c0d5860043c0300c440d40504c210b50340445014140c00700c54030180c5c2c8698a60b4102074080c0d040d40d05c0400880c040b1194081c04000800c0e001d4005901d039a9921509800341101c91130040150103405028a800d0b00502d0344030b00318840780e030024600e80d401a038400c1c4d4003050080842070340e41c58154182043c1041080300350010204114049030110403c074a2038103050407600071042001000244048560700311507040c60f119014140041e803085203e0108036070801c6d01104030300c41c08001480090480c90480958005e0401f56007c104039580d650041c1e07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 308064919 1250 308063669 308063671
    0x180f1014011e031b0312021506120307140a1202070603050c040e070f020a0203010e0c030c030d1e0201020702090708010905150102061b0c0a0b071713150b09010605041508 75
    0x18600c0302c68a48107001184800070b0441c01ca07003a00440b89202a5070703442d011403c2200002e01030040c1c1008001440c0514075480c4950000f07400c1b280400c0d40b200a6494075941e1113294002005070548818100c0149820f110800c2000d03000301e013210300a201104e000351540460b0144e100070901e00404600c44030383c583e00380c40655401035003151850b110042c0603074101c0d20002100d011445003411050044c1c13028020507075040400002054684d0780e14007018204880b88101c580070f070b405400d0384070105030301054240115207280d03102665000000c0080380a44100036021790003502010910501c142c0c8840014100c0301d1552040215481c0d80341c640c0a10320040c031180340140d01c140c000c10700481290ba60111000309e69480d10707182c1100c804c500e600f0140200e03c00d070385a000440800c40c10541007100d07801c651070700103003051186c80c0c026401c000500c15008003915440e42c21803600c1c90304804d6400300005090003000b81c00103681d01d00c001845a84180a94002d0340c150043c0d03000c44900480000e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 308066169 1250 308064919 308064959
    0xc1e0b01060e03030904051320030c01030213050f030307050604081c150e060a091b0809030a022e02130311030c0612130c1d060d050303180f101401 65
    0x16601e000c80917010000503083c042c044014070071080a51000203400603200c11b60002e1000c42302040f0000041c105401c0515020005040c940100000c1041b155a646074600b5a43c04844520f900203204003c82d1440c000d0440041207481840240700900c44000e000d0310100105008541d40d11400302c00311019100e803580004e0300c5407407940301449044211440c0302d41c44074028244201284ea1001924282d41c9000318503005c20001d803010860301540907800c2a0710401040045141000c0080000e55070100c6181030200540c0032103010700105404d00d000e0001415401040d5228148081200008049488100c0d10034240b114040054140400c0030007a1100c018602030400d032001040c1c261007180181191440005c400c5a4000500f80b42c00c80300103404103030107807c005403031100030042056000c0c0105200c1c01242c0311000c00145e002080341d80c010317003d0401c541c51503c445074a40c0f03410000348800c4454003a40e1410440c030380a40d40b040e00751840d01580c20740c04e0b0340e840c021030621400550700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 308067419 1250 308066169 308066173
    0x30912090315050a0f020f0403020a0f0806151f021506031f0e0c06041206050108150a021305030f0309090a060803092206170105070e01050306100c1e0b01060e03 71
    0xb030680380180300c2d401a584503030407101c00704828502d40b20001c1241d00040300c01082681c0407800f801503042012803080900220700c4070b1034080e406c041d64155036050081c41d12084059503051428140c89000d4100212040a03041c1c440041c0e000030065144c1d0006030003000d80740608800a082482c00268104650088031070034419100c910b8400c1c0058159041c101d11207100361000168641c848500600c020031b00d10b60b104000320002e00d40300c000c0c1e46040c1e10400c12603004038041ca1041c1818012a5003200c000200107a6a02c003030001c481c0f00c500b89a000e01d5060051891540360064044000d01d0713000021202c0000d19500c014801084400b10701683c11a68414840e0510038140301d140c2400f042d42282000c1c1d00e18040c80702d03500a40e00282c0101c1141d141000790344036400400d0007925000390503400d08004a080182c0004d000303000080266104218600c140300300e1500840f10a91280e400141880a00803981e80d40c0440014004003180c960811000010b91584202486004a080180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 308068669 1250 308067419 308067443
    0x61802091311090108030310080102040e06011d0405010609080c010206100e18010c02010f0c02060f0705031302090a0207030206310c180e0f24150607030309120903 72
    0x340c0400e811070201089071858100c1c1d039011460740c2d9215035070f802040c0f10802181d40c0d00d008021445c00950320b52216045030300520013030002d40c2c0700c4208181d2103082840e00e004400241505031058894011595820a10300000407038050707030110b800000e176030321384044558240500d401240c0d100c3c02120307882001c1248030390074042c82c02c03031103845c0740c200355559811400c00e00b02103075907821105001c0d0541e003d40e6459092007202c052502400038020b1450014181d280340054490071810b200a00c044208178000001075245241415807010f050707005000f038085482c120303858400070340c811034066015104510010341001c018401070007100101000001100c00003503e03141d14141d448404903806c1c504214042020040201c5000d007480c4000408075540b48180010760800d074a827100d2280d1604204c500c20410020301c04040e4030b50700d40f800c404842da540c8900005900602001080d84800c0000f000400d1561640003141c50b40d0061a009889000070309099031051502c1c40000e0030710040c2c072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 308069919 1250 308068669 308068681
    0x15040f09050a020c0f0f071a1c060801020c03031b07050703030c05010f09110109080601080a0f060b0a29040515070615090c02070803030603120307020a06051306180209 74
    0x1800440d00070082c96405814074aa2125241c20310382141105000c9a00060070800c0345902040140000e150011813000c080010300f000ba02540b042030f030304400c01108055104800c2c3c059500182c000c06d000347c021901c800d10550354540b60350050300c0100100a8660044c0e01118140040741d600903407102c001d150391855a42c0a41e0002c103562001e465a5603248034041e044e6145009062506205084c248480d145480014141c0c2c4029002800d06501c19070046c00001c40001e0404111500141403000c004200d182175000782c000081c010b81c0240314410001800407500e000b00880552510610302a400919100c002a000c0c903c66298004c2c08080046040c0c4940001044080c3c028040850903564101c0c50203040b9617280e104c80011613480c04020b511a81c10f02100c0068260140030314030750308040d800242d60b4095081c43d12150100003020555440c0200b00c0145560b520082c184801c0c541000b08080d026246a020f40f591030030126006014a2412491076019a00900d40c43d440e031030f29 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 308071169 1250 308069919 308069921
    0x103050a2a0c0206070b0601021902030705010c05030d0c080402150c06270106080f070e060604090c02160b04060e040510090203100e0f010302030d0f0903080f040306020705010b15040f09 82
    0x4850074024490742c15907a80258035607074000c00b26940030b1460310926050000c002881c18200619902038808119041030050381d0102d6201d044a2092030301070118092424024190720804a58003209443c1c0788003005542d0300401c410703208900840b0b6100442c0e903400e41c054006e100b00034090308541c00410005005a042080309204401c00710341c40e45e18840d0201c106400c541135504400001c1e030081c0d9100301d0b485010000301c405081001e6844440781019000f05038a80954000d10142d00e4030303521f4080a062080101030841d00100d044010f0050340c5140e04056540320f801900300080000041649078200303030090398020340c0340f41c4059000c145808100e10083d08042c1900103503020b00000068880d030340290880c090300b8800f41d8005035501d1481014540704502010905102641810444443c0c011505104480e000381045a4661042c1d5014140d4415900010400c600c04610b400c140301056220101280f819541c4220344201fa405402c024056440303100071580030b101d014009080c00d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 308072419 1250 308071169 308071241
    0x20d090b0307180306090506040c050303090117060111060f0417030112120234082e0b0d060c02070f080703080c0c060f0703080c0310121403180103050a 67
    0x1c3c42010036841501c0343d942a0a42c0c44004d070070744203540701c9801d00040c810100c64100041c80120300440c0303411100c0d40003a0000800e24100c91181d12008001280da901900f00c84001100c5d00c000d075603103440c2c480403a0112480569066454922400c00e8440340b82d0220101e80c180c038190140e000c0c460149560301c100e1603800510850840c0185640d40c0004150712142c0c5029036811542403811040b0b07251202001314141d4801d010585c490742000c1507005254000510494103c48212941c0c500c0030042c40217031001c03494064001605484900034840c0700d0340030600322070590707080c0c03244203030341740c2c110121071806010f101120782124004100040d41a8001e100d203102013804e9504428484002458580007041c3c1c200341480d000942c2020164050101c6500144445006046041424880540c005240107c10300c10449a0055040c0051007011300400c01c6a031045070390351410034483c4144242c0a240c074a011a04000108040c076100b070146003031200184a400c1c0100811130862140281c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 308073669 1250 308072419 308072447
    0xd0c0506130b1611030102040f1811030406141303020606040911060412170a0801120f140c0102150f070f0c080c1506091504051906030b0403020d090b0307 68
    0x26040400035110b0000006080000c01d01c00c14042d07014014144860301c80c205116442c0301e030f4410002401400504844201522540d403038041008102c3d00701c1c0f42c001c00620a41c90a0b614001c020002041841c1d000364010014454100b46903450b1070698503002e0320042002800341c4c0080000603490b04207507000d01451405030070100040f00303510010800940c0903030404c8096111041510042c0405501e81c0c110400300d03203003500d26146c210003004001200602420b0a118002c40000003485038440c0400325030354100c094045a00c104040e000e030f40c0c0c002c41b02d40a002d4016904c8200303104420100c80c520607255810400140e5a507078604580102d003102d980014060210303038601c0818401006170824100301002081500002185d410820b0070061240784a100311b481000f11402158038203080c0100b0950f0040343d1505e580c0c0c19460320710107040010f0b0320f25281020000c00e005104101c140103c0c02602135800719400190119424140c0380100560043c04001203100b031340c0b14a5407929494 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 308074919 1250 308073669 308073697
    0x109060f170117010606110d0c020604030203030307081902040b07080a1403040807030915020a11060d020c0c090c0a1b0312020c0102031605190309020d020d0311010b0d0c0506 77
    0x500610707610a0001d400c2c3c000d40300180c14030541e00d810803402d100304e0000d44414200514403901020500d03030340b800383c0030800d401c201614101c1300c11501c0f450103407000781d680101a40d8076442d18001c000c010480c00c40d2510401940d00c03141460300000e0303100720740c140c82c141c51070035140c80d5542c0c44004550380003000c0e45080054800310f8074404074110010350b009520451105640c0e10044c20018191182c47d00090711000800e8030300c00303220703800042c9030303111541c0004240d26103e000000a1742c4c50140080082d905400003c0e90141c0f1000410b860040980442e07511300140c07510714003d0418020a80781a001c51300d5408800103000030018412602846850300440900710350741c0b81001e90b082801d8444c80c607074010007480900c0c0745200100e1450503541c50031a08003010202110b0b003200080d403400041c155500c411030150345a0184000c0081d4010700755003400a8545401450301d440c2d0340503040035501c5c2c264081d0051604541c0e03450060340140144030582e06000401109601c5403042c80d0300da03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 308076169 1250 308074919 308074937
    0x70b09062802010e0c22151805090d081f03050a0c05010f08090303010b1602061902100603020303030403080c0d0c080106090b03190504030504032a090203060109060f 73
    0x480348005036070035403608200511040c07200102001e425207012454560030368000030858189520b03010310705000009054100500010940074420007003400c2c4440001001e5110700c003068983e0704001c01d0002c1c1c66000802c0081d03646540d0402d4075400c0e0b40c00c981000407050000300300c181b1804422042e000003210a20955035550795a00c610f8401c0000003122100c80c1d80700108887d6070800701010183c69142031403003592500c0750f20300d5120f101c14060034407141c40125140003182042840400c1943d0301812643d82c442555a01c051001900800e8000501c0317240201e06204645000f000101c0b81d01500450958441d59810344201070b00070f18101210805200307a203a269082e004180c04e0910381c0c1c80f0000b0795410701d44004c2245d01c2d1038000003074090040081c0908040c0b0601007000001c10040c000815031111300d17040310544202d51000c0d21090200040b50510710000390b00011016000c044464426aa02041400e03070000f03c500c0c501280000504001c0700e030150b80d60b620801002c0c64020a8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 308077419 1250 308076169 308076187
    0xe0a08060f130c091503140a050a020103051e0c180102070303050703030c171807120503090411040302181512101109040f0e1006080601150c14100c030203010602070b0906 75
    0x3c450405a9134194820065000c0047c00766030030b0a00320f507000c5032002e8100d00030326866550341d404074824001c0c10940d0312400110840c4410b102c0080e0001102d001100500380031184800a81003070840010103083c841d0203034225800090044100d0327515485a50a08650362000d0303004080380d00781c43c028400400d604812420b4201c030180d100710305170852102048034542e110b07841c001654008100c031941600c2500085800081641e417100c008950208a03036086030031003840f600555000035084007101200e54242079503113018138410503007595a00e01a804242c10007203183e41140e8070251581107690282c010000c16045103003c01e000a946a25210014000c14201e0b01008983c1c00490394511940ca01100305124000c003004016506000d0203080159458070740720103125541c00703c418900303044551405032021040c202d401041a400109040040d02e4454150f850b080020f146030032401c00d4603501034400d90781a41d1031b550050207818148076482d000780d0f000b0380146a00134030074007450030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 308078669 1250 308077419 308077421
    0xa0b0a0f18060903120c120b03030f1b0309030610030302010e1c08060f0604060c0b0c0c070512010e06040b0f0702150c070204090b010b091305070c020402090f0a060e0a08060f130c09 80
    0x1a0841b03242c1d1b6440014070b06850303540116107209802c0b0b4440d4004101b01c01c2e5854450041d64400090000d100c00c00409015000b481d40c4519102590107009403001c214401c18440341d4102183c2c0203400a2260180c001e00158072207090b01e50a4403420070060000303030781c2031213800e002d5802a400f13805180c0c895a02000101d06400a502460010f0040b40c000010040141061500301e42055880c608101ca01c00d042511a841406101c0c0100b60030301300601918030942010400c0e1215030180c0f003e6080909080c81c4c103050444e205003461a41201003040244000340c2214510050703d541e50041d1184484150300798010641641e02540310511f8801003210000070754000c00c2c041e5180703a500c11071242801001940070a8402d41d2518000400540c0e40d0000c400c0016140d0440d00107943e8482d07440045d6641260307540c03032904484070b161301040c455004031104603400011a803280c034642da9110300568484080302c4452000048102051071750369885448003a8070b00c030707030304600c08961a0718150b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 308079919 1250 308078669 308078681
    0x30b100f021509100b0901030c0306110f0c0c1008091515060f040e010f0311010503060105040b070c060816020a0f0201110f0124030b07080405030c0a0b0a0f1806090312 74
    0x581000c40d109401c0091031261791044042a601e00c0000c1d85140c80c1e1804030352041c80041c0c49140c841407129650005e0601f00c42c00700400124003515140705008443c3c0c2c618544816a008d455201c8150078628081e03282107100b9007450000700a43e40c511103100c0e1030380e00d014000100c0006a070468021035940d0001030818203404000c401e85031440e03c51511005401a404100b1081a464091002c58103005c0a40405403081c00c107199aa00c1d030200494652080e54421380b102c0e00003180b404200180010448211001e555441107151101c4808008098040304605d0140e484662040d001803242d40c51454450300506240e801e111110003100d0804e400c44416556507550350201c030240c0c0c02c6106201401400480d0700d10305040c02c5588510f030010020305510140710507480010b08008040046801944140f416902c000c2d0141c0703084503c1c072070152480d0807100d08181080440380700074451000001600c1440320702030000360311018002d0442c92419002c100c524107c00c3c4000341c49000344 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 308081169 1250 308079919 308079931
    0x302160305091008250219140c060906090f0f040501080601060809120901081f0f0e061c0b04050a0b01030c0e0f090304050103020901020708010f1b030b100f0215 71
    0x500e80e902c2548041101480710281403d042c0310045042c00895140c20941808400c3c1c0d003001408240ba102000784c0c40c1201c0e0414007500900030101c40010801d140f580e004000c01407200f2035105096000802955004000b44aa00300800703005007146844c0052947c00e03100e0340500700a44a064800203d41611800d03007000c0459840840100841c40c1c0c8644c40b40e92100381900600400c2030480b520007001d2103413500c00340c1040030500200d48082c0781d00c203040d00a0744903651510803135540da403c0c000961215104a26500c940f503400100103017000780d402c010081031024908000301c1c66540f5012002805002a01c5a01c101c6100500098801c549140130318000c03041085502c0c038140026445000041815006000990501054041c0001903d094500900740580c50303e85100c0100c0ca880c020340d0105880b58202010418000316583c480a90303802d811445251051a25409809940c80859016048a1500c10850700540b0031030700b10070300500b1881500c011107a50201a20f05c0c0030250340d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 308082419 1250 308081169 308081177
    0x30903030b0d0f03020d0c02060301050108041103010f0f0f060b030705130320040b06070201020d140705060a05100605070305040b03150301020d050906091506060c15010305030702011218060c03021603 88
    0x70b0580410607940c2941c0c41f450800300046040d404910303d400306209030390510581c8008a000c004180000c0450003d015008021520702c020084002d09016150b0a00c0c861619000d0451580e83e40a03400640b44181075051458480081c110340710746c840802d0040e01c0301b90b1403002c00017070190220384440104c407030940c4000380c40603000c20040f9483c0b09051381c0304150400803280141d030045060680b0481034107000101740030100021505200d84000202603000d00c4040200d40d8106a01c464003030742d5810080704403e078455109440501c5680300181c0420400e110400c003800007200219880080700a49a03100003900000ca03080e03800110010341010340b50803c1110b048000c00190342e0008014000749460749048181407051480030f41603e004440008000121810400c032035101712007022000e1a4135a03607410110340740c7d008a0012030008510350303d0f1191110040c020540b80081103000840010001d94840d40113100c0d000c0c0107424142c0034440000c0300355400181402050190703e03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 308083669 1250 308082419 308082443
    0xa17040b1c0204051801050411041d190905160518150a0b03011203181809140f16061e0507020a030501050a060302040e0609121b06070906030b0f0f01030903030b0d 72
    0x10070231050b661102070a00e5080d8052100300400706041c20040c9101e40401030207480c54846944121400c940075001220700c81c203061141041000c0001c00c4943c0b040c02903041c411b000c0e203d40800603843e9007038417441c884600040c04141c0d5054224035a503c40c0f20000e0a42e09040d0b500c54450b950368109078084021005448007402c28941c00c201c07000744c3c588001490394219400e00e030701e0401500d01d200680920b81ea8030300e159070400170b0301d405d542e44841c800401c80e513254401c034035415580ea003007000b287c0e64007000390400155980982c000d00705d00f2000d0071004112014060301241c4940100005907031003043c102000000c110207119150203080540701c003103140750841c010b2000340d40301181d4030152540407100b00108040045100d810600028401d10f075200d00d41280b0180e61f00e24103445800358010603081c06000b5801000c2082214020344081c4440c004140030042c0d10001007030003540002c440070140f504d0798460ba021000d05446400d000508041880c041020700c2040030b0103d80441ca140c07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 308084919 1250 308083669 308083679
    0x806100203090d030e011b021f051e1b0f1513150203060423060d0c0f06020102070209070315030b0c040807081e06040309030206070f02120a17040b1c0204051801 71
    0x4410501803031f824901c421104002d03030100710080c01c3c0396810808403e0999074211000c1c410801c80d1411404c1c5401c42040a4a081c002c202d20750040c64031130310050140c82c8072401e068002c50100b8440c0005005009580000995103412501c01407903d280d40000e00706220005a10413400c0011504d5180e0040c0c81e03191079001e00003141c0314903410941c521071078804040042c0548052680c01101a61052590100340c07400c165200900d8100004d680f1030200f02080c8241d0542c040c01646000b21802811500c8585007641215251102d0b042070030300120342440030501d140c0301c0c04c0d000030100750318510385a950325450b8100030241d0082e40a580006801d2002d801c89480d900c00701c0d000c5c0901a041e90b0502e560b0180104006110080c0a070310041a46070a011990116031a070a80203010780c00c7c1e5200140c40d1945070b00039047c048440c4240d0468141c4141020b800796803d4a05074201d02e031910510305015070402644585104841c1c0d020840400d240d125038208154070410310800a100b54142 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 308086169 1250 308084919 308084927
    0x411060f12010602061b18010c020603090d0e040b0306071409030d0c0605010902030606180411030103060b03060106080615070c03080703050d0c03020a121e0e030702120a030806100203090d030e01 86
    0x1910111051056403001000c680c1d21101f242c3d0404c44004101da2104a07040060310800341541001c7e610120203c10810041c1c0081408034502025503540c00c00d002d50a01000b08441c800560f454140d440724000a00c054004d60034200d242d0305801c021400c03c3c5101c0006854000310b0005000001d107000f90030b030100660b030702946015000c0c200702942145045c0000c10401d0003600300e8403c080c01c411020321850345072940007007000000a082c00e5076a40e140d05064002d010300c0003881c4c0c00f0340300c1c5400001d4164843e940060041400512448420784014800a0380d40c01025054030613620000b00000014000b100900480780319480f40b64903030308076240c043c04640d5080d0741101810b0040049148090380000456070485414000080d00301c16030f41051351b8090b80720130320080300d8500f5000c0b00d0540000009083c4561085036501521201c5000d000d032550410300c2c0060100340381c0d5001ca00c00d0310f4694038020109055104590620303140c81d00040001200308030a81c04540340c7d50a000300380d40d00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 308087419 1250 308086169 308086171
    0x70b1602150a050403051608061609080d050406024c020705060907140d060903300f06030209160212070c0504110307020a060c0201060906090606030b01170411060f1201060206 77
    0x5052407c030f0155150400c0b0035201c1400414a207170f003003080e210600341c941c000c03500130010b01644011105016503000004d813490f40700740641c40c0903220b400d503101131180041540c098404100403500d604204840310300c030011412a124107034120807060321110024000c0c80038000480c00b400080040b0300304101100d00301a9143c001c140140c2045600711079a84480308a41e8420b0350202000592040605084a0014017480100c44803441204103100400c503908600380d105000401c01c1082151041a11701118814031000b034124942070700150310240c40c1101120420428019120b034001c3c000c801e05001e51005804842d1140d4840081c8614201842401315030035060000314650704140d44080c2d6110349501e4028002e580340c2c44da102c1c400b4400c1d08030100a0407504810b201c41a1508070000203800030f0b00419002a240010a13032140d071040c0c9100300e101c20b00c2881e070f03803c54030b968031107480d0005518045c0b5002441001b1440c8107011120003000c1c05981c0030802c041a504080d002428098 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 308088669 1250 308087419 308087443
    0x30e011a12190308060f0d11030f0d2106030218010e010f0b0d0507211a01080709170703241b0203181906081503070b1602150a05040305 60
    0x800880c0c0000c2c018684211070000d19014140410742c0d030f81d0000000d00c050007101e005600300e200c068401d0200f220131540500344200490603202c0104504810f01e40d640c118400300e20002e06501c00e0105030091001c510900d044040c80c01155107030301c070340126203440051b140c04125601d00030010801c48541c0e0f8452030151040c4107a510f0b4540c501a80c3c01c0d128010b001c2800404c0f5541c801085040d4000d1140d040e0140400f010000350020041ca00402451b40703150700311800d0200101c560141d881070000c1c610844c00d85e22241a00350074840e200444080c030741140306491060210110104078501c1d9000e602000c2106030106c200c03030300f4800405a443d92480c42035500c01c40c01c2407590302c82c0c011040d0b079100c0300b0900062035110003842c0000d070b0381010340e031050040e0000d928021600300d520503c0787d40f180e440d1107401031200c001c45061655848591060f9440d8240520940030214a1104042c1c010b500040c0b001884400303044c1030851a42c003100301c1c0740c08a0000502001041400d00c41405880 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 308089919 1250 308088669 308088673
    0x7060203091e0a020603011707051c031206060c030f0302040801020d0b0111150a090c050607060e070605030609010905071e091d10090203041703010905040314071104020307030e011a12 81
    0x554030b40c01701c0d0440c00107000d2444e65500b8040442c180c0c40b001c101c220018400203110b140c414130715210103040406070b0302090340061a0010203a070048424080d41b01160b0f0141d444005228060b141180c081c65080035401c1010b808000000d8003075024009415140102e040c000b07100e070b40e100000341007039801c9041e0790f80542000610170518021445003981c010040f18000c2940385d202d1410008540b04e54000c5640001d0104081003030050aa02c007942c900c90b0f8508903416030f610b844040c0c41c00e00085518543c4015188010720201f0300300c1d00722542000710781c14803108506480c4402040800072454000000d00814810002004440001d044d07803038800804060900381154044100451401084607103a0008045401c014148074440c00390108614401d40b6941c5030100c1c00081d060070354050700029680c1016a83d012000800c890b805513020001c4120101e05000340400713500b008180d40e040c5981c4220380c001d04bc8007070151403001292075180c0640c841c9410100210b0326032003101c0724403903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 308091169 1250 308089919 308089933
    0x501090611060406020d061d0a180506190e150a05070504030c0b2b050a1a0f2b050f0d0e0112110403020d080a0f0e1804060207060203091e 61
    0x40700049802c42d0000d070401400b507610a140381040001e804141e00261485004600702c01d260368240e243d00340210038041017440440310400c06543d600c0032130700003e03107a5086040031030015142d4030743d0741a0301d08100d00c0c046603c0031b81d14240f03401c02c0d0704243d0454a0454000c200302111980382f2a0030303400440d0b400e05074105811516082d88445481c004c0f500c032681d00040c400041003d402e401c40b035216075000c0c0601e12407605103000d401f0709415140e442c84141060f08001840070300d41500f044d180c4015001d03031149503e100c1080002c4200919605840314072480c04c03200ea04400c1c0d101c02d407090140d40101003c2a42108052034070361645030030810001b4210700c0c40d180380c1c0d000540c3c1ca0078020200f0003203409802c070a902540751050f07a03c020342c003e9000c0c0d4483c04009400c0f010700800201a140c4506016110b5410307104030000304021548558000d00c02075000d00e11001c40e075002800369400500b0000c0303941c0d64000303c0c1d105413160385032540100c03403003070310017000036201c0b250104890060081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 308092419 1250 308091169 308091197
    0x607020a0b04050f16170307150c0c020909011410030b0118020c0703150b011701050409110d050a120504060f0e03152404020c03040b0906070501090305030105010906 73
    0x31694400390042060000102181c248001040002e524405000680d2a803c144c4078414503131072114494110500c405050704c0c00b4072a00482510012138100b080880d031042c030318020f00e006142d501a14402d1203203d80c1038102588a12805622031102c2da4000034200e1050401c100c2d03440f0005080076241d580c0742e007081c80041c68507008141154010a4020243d400290042003c0c0c01142d615486a01c00c4000002c1440b03025144444100041030040140e604020011100c03062100e1082042000d00401000241010340c41040f00d00e019145503400c4107000c50024201c3c4c13504580a54080c2c1c48003010b401445101500510581c3c09400c050346420301e0702001515810344c00181c10144414000564040d45082c0043c14542008000016180ca800b10103021109068040000d030700008416040f07160400d41308079000e030b5a420004600b4146020600000d0b039101404046c5c11240511180c00001c0e42400f41060051298661a40300c3d17044c94001010300580350301c45400c00018041c0422 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 308093525 1106 308092419 308092423
    0x30f050a0b01140a180f0216060c0503090c040c0c0203030304061a0105070c05040507050f040f050306071b030809161205070e0903031f030605041a09060702 69
    0x72643c07140400c12654980850281d00420b034040c003030180c4084500105034411100102091500031040344009a8210314030b201c0640d10000520002c120b568010f80c0b1503949140740c42d81c2107140c03c0005035595542d814005016698903015100d4042c030079000c41100369000b030102d03652030400b031a100c0000c1c0400d01c2800c400d6840c00304800d03400d62203541242c00541d04540070412031802d01e0100b0009141c05070042c407d003c010489c0e91b41000040e00980001c21020091002d6a441c10040c181007660003060001045489040f45180c598418038864040d42c15151140d0306a88150142c4e1400500d445414060340422000040861200c015200d1203403190084ea800c01e075580e207030001c00c0c0205480c0d1405681041c00000ca042c0c4648603103004181d00b400d00c40b01e031541c0d60b484010445500b604c007500c58140c200ea80c4401026820011500056007500030540b51074000d000039 = true := by decide +kernel

theorem cover : BRFrame.Cov 307913669 308093525 := by
  have h0 := BRFrame.cov_init 307913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 307913669 ≤ n) (h2 : n < 308093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
