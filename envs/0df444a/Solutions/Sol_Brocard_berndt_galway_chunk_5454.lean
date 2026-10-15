-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5454
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:55:09.759996+00:00
-- url     : https://prove2.me/submissions/0f17567d-5dda-416e-be80-33fe332cc9b3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 980755395 ≤ n < 980935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 980756645 1250 980755395 980755403
    0xd0c0b090105040f23121804150b1e0d0510090b09010302330403020a081b04090201120c0c06050c0a080f0703090503133002150f13080d030603 63
    0x700d4101c81d55040e134001d48070481c3e4021600802c900352174090040198001d85442e200c40b69554040751200202518200014107210307e00742841c0000c1c040c6801d50700c50880ba05421a10b03100c05c200c031012038040d00c48141504050300045030041c1060f10f42d400a901030343c04002c5241040b9101d02c018410746202d07112058209000c1e81c01040141030940e80e03220781684041b10f917071201c160074003926030801d40d5602421060802260034000d52400c861144000c081240c0186002c00100c40700f003441a4906401d54425a50f420701d56055901410342035000c0390b90b103034042011f8241d0b44006807809203007103000e035000c80c60040000e03003051101c012031704000310646502ca029980c0000c41c4e014040001c04480030035444251800015404002902c500c90550210f020700c01d0600400328541040c0240040c0c840c24040c1c1c4c0860441000070280420540507a100c980c0f139092414404103602c900003400240303050014502c07402000c010546c0e070540d5809000e407403881400000440948420707001c094 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 980757895 1250 980756645 980756663
    0x1a1b090904240e06090d02190609170d1406040209030a1104140103080c0d0201050c0f2a01021206040207030e191a04060f0207030b070c03110d0c0b09010504 69
    0xc020484408041d0b00c0da804a060314001404002003440503228500c89024255000c40c05000200f8000e00c901c14840c0202d00c02000403841641e4003000c101e043c58805820740703581c0c030b55a8042c030410140d0001071848044c60240d81d0802c4038401802080f144580450442d001004a1000e2520b07000320360340c0007001070003070820070525212500b50360350b00e00c03450790f100d0754074110f030258540d16101440c02903024110403901d0b4058101c2c20342c01d0403a400d095034216494070080045000710402604d5075500c4126400c2c2d100d007e0140e07a00c0c4007960000140802c0300402100e1201c00105400404900296401028440d12a5018071041c2e000d0808014041351030060b022415007000a0a8040101c0402004003826a1185076055140740c00300341c1100c0b4440010240006900100601800900c5d44020b0840c2844d6403107100e0002002703003d4408000c00d1607900001d041c854410b00c65400c8803402a1349155181050140030340a0b001012120340007000000358550006104142c45560010340704 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 980759145 1250 980757895 980757901
    0x270907020d140c0d0503090f0a0210111005090c030c09060d080702010c0b090709180f080a020a021801290702010f12050901050103110d08040b070f1a1b0909 69
    0x60754885203000e00ca0707240c08030922540c40d1035a004c129071158007080e5207502d5503e0501e01000382c104495a00344d000640d114048003401a00c0e5003000c002c04480c031303161120b00c85030480c264070306000c041c801200380b60342002c09000c2c2e125000310341d07540340313000403403c484140c40307580240180644111003d0703a0040c040d10929000c143e082004000d01ca01c140350103d81c0c8400f41c0c0c1c594a240c4000d6400400c11741c840034061050301001c1c850003000412a18202406169030355441e41c1c412240d140041601402040f40b0020500070420141966402410710070704200c0c584500c0a0340d9030904c100d96140480007102000100c0c582d40d88010800c00f810b40603d4204030b82c00540d9101c000000620421510038a030f1004244c10384111801231008000200d4154075500700302d02e00842c125601807060a80801d0400040d1082c0100c404441e01203000a80301c20141c1484a40c00c00b142030f018000710078030307000700c00e59030042c004592003a04c10008682c450024040a480c81e40035034000260029244004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 980760395 1250 980759145 980759147
    0x121101090911040b13050319170405030a1103160801240303050d020f0403020901230301020306010c110d050105180d140d1d010f06061119031211270907020d 69
    0x3d00d0382c460807980e114000c581d1800840d02e401200d0090504682e00010523404000300507081d0340c441d418002102d4109414600043d0300d40c490140000c01c6000040d66411658074140400c20207000c1e17401d141088a0340c1c4808050203072032468492074015460440c1a11403240320640f541c2503e0301940e0b024281903070116400c0003075010560b01d061f1203030140030000050741d451004a0103030403800c040300140e03e071162405c412070714550a5944664014000c210240c0d0b4000300c0003420603084207210000304440300210b0458a00c0350070143c015406d100420200c1c000685848c401aa40142141c81840c0c404004885610100030004001c060420264410f501d0b41d40040d80c0200060144e801014406440142141e88001c080402c03103444032400c100c80da401481c00900850307520040c204400e5105c2e075100e010004860003c081c003111a0400c0b000038800d902c00302e6000c40b03040c5002d60744e2085201e03040d038900402955200c0001041183c002c0c03070070000d050a015403035136001800d544c084550 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 980761645 1250 980760395 980760397
    0x3060f190b060708190309023307030e0306101805060418210c020a090c0c05032109160e06030c0405010e0f06060f0d090804121101090911040b 63
    0x18002452500c80c07208441e1941e0b100010405288184602641da4501c0d100e1000c00c810250499401e00d450000c1c000d003d41c5801182060801c44004d9600714030b401c251040001c10b403031100116901e80c01103240000c268200e0300100c4401c000320111940c90b0b43d4205d80d461903040318010411000745011201c0c036001c200350001600494014004240c4c0984035240103503441d201c0d4000d6440328188540d00149030f502910f0b5030714640f85458000c0002003907030040354040e2101c0c4149411aa5210f0103040800d1041070b0b50003c0d60b600c0070507a45d40d006203240302809104148010020b0052502c040f07040b1060000d0001d80b041c071803404100d62a80b401c95103945051006041a42601070002100c1103070b030ba00d22910b8080c10506400e0962400c0170340795110360aa00400c89806240c00700620300024007170340c0c00d841d655110440d000c60440d1302407410b201135001d01da01030000401003002c0d0f9001c03c82d651410000318807082e42d41100642c0c0e102c41c0c42094600b103420a00039801c04000601084030040c3c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 980762895 1250 980761645 980761681
    0x30423031f05060409080a022b171b030408040303030506060a0f0e010e0d03020106080607110a060b0402090d0f0b0609060f062208030309070b03040308071b0605090a0302010b03060f 80
    0x6000081c0c4001540f5103030388550040e4820f80c01a00800e400205409d00d50040710082c0781d103584486904410f0800250041ea02c14120720b01c1100c05800144d543c0303104e440802e600280c075649458503401d0034900712010b9046030000b14082410f181c00a112030801e43c1c00c0d1003248140d50388403039018802203015034051103403014041c1000040000300f10603071600700e030300c400141c802d41c00003840134580b20304142031190180c00700c401c01c007620003000309600c0c0000700341101c00d402440001d0000c0038100090020f104072007947d81c104c1090003805017484078851250300d03d64007456422a030b9598032020000c0c1e2400481e01554011444070701d1054604208010304802022090903044c8601010710807500d41049500020259000008000e002402480001c00074a800c0c01c515081d400e00d6035001c0c3c07252708018100c1080288020101003004000c4034070760804c0360481c00400150616500300398a84580050035005907007041034981300e90074001038262103602180301440341d580395482c60303035040d07038040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 980764145 1250 980762895 980762899
    0x1c1118040902040e10061502071a090d0809031005010b0d020f0d020414120a1e0f0b070906140405100c02011215180209030706050d0905030423031f0506 67
    0x151000700c01030f20307688180f11030111044024440082804898825180640c00000001d1100180040415000585038050341c628a2012500159010b416001800780d0203010f98051034262281042c806510001e290000d4103800303a880360b40c4202d0b0464180e0380c00388180c5000c240c0410488030b03542415405404050111b42c1454070b80301c95a0046c405980043d000b1380c40e20801d807642d00c1181c1c50320a43c404150585940581114551502e074100d915840c900700c007a0720901030280c1820400300306040255503038800001c1469003803020009003050000d00030140030031000c410701e6002d08424810380707088400c000c0c04d111400c4031888044410306a80f15003203062150a014900d20b505d0140540c1a140c132200010343d100e00d01c3c081c41c0d88043d22032901d000b80d855204101070003540e1030100c1c9503000e4403524241070317035521300480300240288158100580540001320700800c0c1c0400701c444401c1e803002c0010380480c1c1254030808040c0c90f464140329080c038040d41c2c0406e0100ca11a01e81016a1040d80 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 980765395 1250 980764145 980764151
    0x603050c071b140d050601030f0c031a010504061d15180412020c0a05090f040510020d050406110c030a0c11041b08010e0603120706110f1c111804 64
    0x1c6a84590140c04044251400074092900902010b105448240341003501207414801000458607003d0300c41070103000140c000c551040c40601800005030885c1e0046a002140c0b0b1840318940c08540d540708030038001d10744114182040054401d460b01c6918081d400da640300741c049520740305081240303901010301054001f481c01d043c101040000003021881280200d4060442651225000b030801c078202c0c41103840343c00c04107014001515036000543e0306c9019201e00095641701e50400b18582040c0005044020340002803100c44e480c00d6800c1540070310703c200014000c03000301316180d008500851002d048580e10a1007804043d9115104a1110900600503500118041d0303010601307461401449050b940741e8507540c43c80580d80290902c3c018084841219801d0400d140080e0715100300c0cbc070591905240115000003800303400d44c044c06521003068a280c1e520406400c040580360001c0c20440845000200d03d401422020300031607500b00707003007900b0714908103113081044015a49224a00e4219076 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 980766645 1250 980765395 980765407
    0x3090a020f270604090c23011e050306030a080d0e06010b030c0a080c090301060320030d09050d111c0309060206250201150632190c050a061401050d05070603050c 71
    0x69101c03000c0c087c149040071041070a241d21643d142c100005401355040002008908031101ea489141d0744101d0384a1404580d25203480000928000d40c03c04058040c0034001818006200c00f40d001a16480c82e0308165141aaa1802d4401c560b00080320010040d1004116000c2e4462180c40b110790310007065148030382045807040100c0d007180c8041e0000c41d00c4c011000c2850341c4e640c0030141c0404032031000701d000300306c2e00000c0360005005440c0e0b48202d5000780309941405003081801721010070358490240c012140c0b10480c841d40341071074420001c141c021544009000c0b60051011441d2031007809001c9018503600303909048a44108100a4442c1c2155603036003c444800c07000e42030000081420781e4520004c0c400d02c603843c02d000020110121042c903984441c000c1141000320564444c600f1005004a0400381428240d4a01c0010311008085016891002d0200003d6078080b140c4100380d440300034026a01c400c288440050980d401408607070060f00200003e07032203030704200d84c03008407040844d003485 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 980767895 1250 980766645 980766653
    0x51002100504061422020f01140c0c010e0a03051513081603090f0e150303120a1407090b03240310060e0702070308030f07020304050603090a020f27060409 68
    0x10340507501222403540316480c081d500044c40c82d007190044070000341e8550510100319440d0002138284002409040440c40061150b8043c03458510030300302322810140d865003501c203030a8480c00e40701d402c9070104100a88011650a1998072101580d90100c0248002c101d40c0f03440314172000b4010101100e0019644002000521440c0500404210001c160030481507518001d800682182c200240c080802c1c00704200c1da14110300b00540004858031405500b060341004030b401c40c411002e1020801d480d04040c043d11000740d40c031081da20144980700280b1a1100c200c112130141c040c0c45410b540c1c40b030600c0030448403040309003c4800d00218414142d0400028000310381821001d00c141100a075544501708035406c40ca0f5200c1c2e03484400d42c405084030f50300f0345c0d903541c40b41e001c064404020035008000086005000700202c5002d05002095551645080c1c81f40382e5841002c1c1e0030032800381030305141203003550424866000f00500510107010305070300c4110031007040220040250f588aa26100c40401003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 980769145 1250 980767895 980767901
    0x40f060905150f090c0f0a0f03230105071709070f0f0503061e0106110f060c1c0902060306060a0c020d0b04050d08090a020405040201020c150409060605070203060105100210 76
    0x1031040014140000b114a005164107000400f00e516206008040000d00c0001081d000c003e502d046610b1242c0d002c294000c00d440c12055003003050242101e44020084c854800104094214024054404035614040389426a6429201c03440030603000d210285854070bd10004991002e0b00408640c6020740c0d640011003180d500380c1c440705080483c020180f0150805100c41a0310130300d0940319200c1c5040315000c095984105110324020864041d140c40541c1354180072111080e0140ca0465510741017203620a0846c6d8000d0020800110606071441c0860140d030180d05002d6400420041c2150743d10340500030b40303070b0194200d40c041000c1d020b40500140c0ea01100070000c0b034083c00c41e03403403c0c2c81c040c58000d20301035510b4140400d100164081142241c0000340402003d54161004200d544a80c80142e1610300e80d210040d501110f46080c0040c600501c5028000b00c80710f85600f8064642d5680099075070307109845019401d5000300300140250700301404140403101e00385c4102c1d00c120a84a041c4011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 980770395 1250 980769145 980769161
    0xf150e0d03021b07030f11060417100b030c101416050d030c21110c060a090606060306050d08210c0d05070801050d061d0102130503060a0213030b040f06 67
    0x401d90200743d110070014043d00c44000242c0940051200c4c2d415502d401000095200000700803c40c010154115515400240c45c02021880c41c0351000340342c0c3e0101641c4400300e881c50844060b1410302014424600024a02100100034180e201c0b0800588401c031841c4000c000c44001d41c084c00c00044200c03510300c2c21a00d040a020b0005040c080708454402010381e8032820b110781c20448401804003c8190204040c405020b150307a0000d00220703180568441400742031090001030040004021400b6001d41040000c9882440c00b000166155001641101d41d0340c01190780010a0704e400c0310008592000078140707013001d03646107031040c014052148034164080740c2100b8990f4010842c2d07448000280500b0f5009965401e0480640d03040201241b0061100721000d045d403070b100d0300c00529900410b66100c0d10511144001d6584008141c0905230354040c91003054001d10030580002c1c0004030520035604074040a100031020113147d600c8061131020050800c1c0c0b0008034120001000446a00c24200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 980771645 1250 980770395 980770397
    0x7200a06140c03070918090f050a03030e060c1e0906040b1801090608060105070f051903200c090903090901090c03053108071401140a02070f150e0d 65
    0x642001d000300442408102428003024203405109001c0c0d81600000724005a60341102c0303040c5041009201c42c40600b00100300a820071124861843c1405804030f040300b6428082e40702405216800c140d290340d6103804071080c40300408240800c0d44103c2c040c103034116a0543c0b818065051021400026015a02540c0b01e4000450006a110310799007a803803880720b1510007401c2c000c21481c43c000000d001800d0042c0007a0401100090750381c01c20041e014030386032076a001001c54080d08007240b4150015640c1d194290080790b0700b02191104561b03c0840304592140c03603009010501b41140078000b240601605140560109000381005912204403040c000d0102c1b0101050029402101400300d07400503202c2e08010000404140580d28a0340729145203880c0844034210701e4101e42081c076001e000724a40100b078134041001600a5003015040054000990440120035403103282082c022485080d4004003141008201480483c644001010380c0340140c2d02e002c00c1142511011034113002c0c4440301c0b04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 980772895 1250 980771645 980771651
    0x1e140409020405010909020a09031103030d06080c030c0d081911060709170c0d1b12080301030512130b03070c1e050c0a0b09120c0a0314150f07200a06 66
    0x515039005d182c91008201c07170441140f4110710a10000c0c448902d43c00301078030f8040c0c4024442002d0320104101c5040b800d0008041200075102e01603142c840c0c4c004081c5d20301c03a225500032481c1916140400707291099200d120035183c540a011881140d01c0d00110704c80c00d100f901c5148900b44203003444940d21480144d80c4601440f82002100302107000764000301500b03a4006504a0215111051001d190030340000b540e0301c3c2001e400b16905c0c40b500d240d4010352001425010700c8010050200d0186059901c03980540c0c00e81040701c0c0d950840d07030050212000e4100010f02c810802034401d000210b421141c5480e15200503001c41d200c1220300b48128107010843c4100100c1d110622900b03000f0340c40384210860b4406070b59031038010f414420740a03965819200303800c4503034080f11a620401c462204110040d1400b4419956428024000105030404a405001d40344400d195291710000b00392044021610156080d105c1200031600d803425980440c00c60342c8000310b402480703e8104480d2a00900c80c002c04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 980774145 1250 980772895 980772899
    0xa05011e020724170f15060c100911030f03190c081c1523041d10050606070b01091503061a010210091a0a060504060b09040509070302011e1404090204 66
    0x1412542041a040b1480707050005102c00c40500c0e45e5400e0704031703040721840c4904445a00005a0500c9840f00800c0c0c03d00c02c1c110700e041d103407205402c400a890700803203200070714151010030f158407501e100c06104426007080201c120b100c0c01c0700113040408004c40c540030903014080c2d40c070014280e000c1c40039210f013120340c1e0385038070128640c50081e1280300c886400468102d81c5442c00c0d10f0746031081a00d4581d01d48a01c1080074165407140d6114102c0c0700d00700100d0399444a0140f84543e1110b101083c1400002d00703100c005019030400d50111079031264484095503580e0300c1d082c410001072480c004008154400c6002c00004640e141c0a0f9180300d0888003154400300700300c1000603142a280351407044180303043c8200740010500006410340c0e00040e50b4512041903a689038041c1c000c00040d008180c0c41490048041913851100001d44104a01034404000c180c07600d440c01540c80913640310003800110814201c4e1160701600032a8200f03003009007804000e0240b1034803050050b03003064101850307081c4e0104003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 980775395 1250 980774145 980774147
    0x607081207030e0c01090305030405150c1b090906010e06060a02012a0906020a05070e1308041503230604020f07021e010f0f1b1419020406050a05011e020724 69
    0xd0103030104c0c401d00b8000c901600e181d40d040d4481c000c6100700361050076002e401096010204045a413451044c1080d2485459052000580004a0703841e050046045100080d0300c000d0000f0f07010b060380c02d5045001c0b1a40da1700000c20a1580c440c0e5251003c654803409161000840706000258680050701e1a110300c501d0100010303c404800c0d408036086601c001c5854000c0b4002084043c03c1d00e803a1300c240702440c1c0d502c02c0c4c40e044400aa2100038000e0000260001300c0181c80c090301041d45685503811b2201c3d01d0360400c0b20341d8136080070745480c40070310f200004101d1710f25160f0f0040c081901084030301410a4041e07000611305420100041404000000c2100969039001021484e08407103800c107002041c103071a40c0208540307100d039600c0699540e0756420000f400002e18803100c0c0108500100c55071900308083c030824014000c03500b01c2c002c40c1008000f040500d17040e0015410b9034010394481d020600b0141c0701c1080b101000c1c2000c01580680b0402190f0300c5079107007009408141a9220200200d640f0741c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 980776645 1250 980775395 980775403
    0xb0a0905030123040609140a08040f0b0f09010c031b0f020406240c150501092a050a0e06040e07540b18012604020607081207030e 57
    0x4043c031801e543c1804007481035a810702c1c04940244d0030100c0011419028641150204070b0543d09002c0f600c1610030410401c949403004100f502d08d0b02c45010103450355290b0300101401403215044a62405001402c15944101c404098041c00b03440c3c0b010f406000d010620021845100043c0c5481035484c08000035402c10740220402002d01c10010080d404030a066500d8079602a0003030400c02010004400902c050104145006502c40c401040307996540d0381540000d15041200381d10400c2e032a101c2c2c02e00044550032281c0010003580b11036140c10b10070b07c8115810902c00401ca0750104090001040d041507004101d4880c0c00b0a0301c820841c8210075078494060820a021400c19003402c1340f00300c034074242003d292145c0d00890368072909080c2c01c10b0700750302c0da551154224425201d0003040046070131000c0400080180d000307807038282c0b4040745900b49440c0c40c5121145108180d100c9404600107040250062032168012404281400412040c0c0d5030088815a05640066106d000799040920b00740 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 980777895 1250 980776645 980776661
    0x14030a060f080a0206072009070c060b221d0f0a020108010909020312070819021b0306012d080d230306010903030f0c0b1f060503070203160201090b0a09050301 70
    0x3c002c00e010310703800500548600000140764203240f4030030107100300e81d42da00d00600c0e8400030031851852520341401018003032101001d842c589e007001040422400c25014129150035502d28940300406041c20310005400300c46404445440b640ca0009100c010038031550f1290203403d00070b0042c1d140203000040c100c0c901a0410b42c801407611040e030005960008491843e040405146900c41c58981405d0120340a510072048181000016a80015174046880360201c580b615404aa100300c6905050380e480b03090081d56002c00071041e0908003070a2940310f01e9a072800903900703d0285615426010f00389440d984003800811071540304d5980542110362400761003000c1ca82d000e410340c80c084c00024001c1040313100c06003c0c400002d104800c603910491031144c500380c01c00c4103a00b50b401c1c95400140300210720f6000251103840d012012900342c3c458406c1700e0007500c03580c1c015810f0900986860101c0300002104a0500540c1040000c1d441072040207020520741c035450300404185044245801d40700b9170 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 980779145 1250 980777895 980777909
    0x1b0c03050d080f101206061d010812121b0c0d0207060306090e060403210e06180316110d0b01080307231e010605030f0a03020d170c0a14030a060f 64
    0xc0108a5890341e40301c84c0208480140130800c080e20310700c0c02c000d00101207a0704144a404910300046003030300c68412445040302c4003a000c454413248007a4011102d8020301d040c401046085501142c1220300c11540034490355030b1025030b80d280c2615040400d00e0b000c00c8522500250f000400200480e6030580310fa600107065000c0c00b4407a500400f10301d1502d40800602c0103083c000c00c22045039043d8000002d0a030035074031441c020002d8030300802d800f0340d95100032100f601c070524010100303040e201c2000c0290b07031a003803c5421510f4030740101d40d610b06602c02540983d980000040d131101c004135018928280c0244010030180d541c503c2c1c1402d140c0c541c0b0100f01100d10081000b0b41c041c0b0449000001e03003a0720f80310360301113010301b0300c2c81e504c2e00602402650340b04503494482c41302401d0700d40398041440810345200c0e030210380041341c0300751081d50700d681d01d034000160044583d0000340540360b02800030281500180340400031011414039001e40e981041e00e0310402c1950f1a98240034000c00203101e0b8015142c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 980780395 1250 980779145 980779171
    0x303060b0316080703200d0510080a02121f141609050609010c0c03030302250b1b0d0c09060224151f031401060e09071b0c03050d08 58
    0x30b2084908014450440040100020003d05020312a41c05002d0307204200c2c66820728042c1110613101d07203810000c50700c4a12860907000c100310300c07252640300048070b501a000d04507030f8800f40c003000142040701e00d070a1050f000f1a00c1e10f040c00b500040406410390091a0700007542ca000501c0c0b204640701c010031046040e981c02c0d80005040f600040c255044800c01c0b5441e951b00c0b8100c10048580080e1a80010094401064080101901a0007811030350861000c000484001c00b8540b102201101002034440b580c40c40200303144803036500c021200a510f42e80c00a1601e28a04000e40440d0040c1310303014005600101d05101944d07040c07264614501d041800c0640310340e898044075418643c007400c0c400d03045210001141c065150324000e900306490581042c0c8000940c144040c1c00b601d01038040405440980001041150040c100d4440061f406410442a039a07440029900c1030001004a03907c000d1100c50840014001c10924001d944100040e14000004881c09494180c2c081c1108903260b803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 980781645 1250 980780395 980780401
    0x160c08031905030f06040509070302040f0501091104060c06021e03090a12020703020102061302010309170306010f1b0609060e010c030e01060602120f0f16030201090b0604050c1606060806130303060b03 88
    0x4c11050040d404c21310460300003c5a80311491514500f01c03065100940040c1051610413402d03400c0e60080c1e049841d504d0081c0183d4100c114405080c0c4146c0c00b0b0309020808a260308004503a0560242c85952100e1000808440d280b4140c4102038004030740d00855a80300309102400c020705080c04c0400c0d410301e40001c003c40c40c1103500103911828002c01e2003100e0300c000c0d81801c0c15a8440c0d00701004007604440e46079403c15146082d40629403007160107502085251120103005441050184803480d0102c1c01940d00300e400da0717200e001400800340c1c155010b079216a000c0000d144207102d001a107800a8800041d408800354005007552025030066080d90840704581c2c482450110446000400d40c8080c81e81d241c40740e01c11810b0034000e0500c0d525801d00166404000c050f01540000303c1640030701010b01150b03550800f0041a035000311860714003101c2c1481088080020b4070204149148108070200304c41d525040185d00d4007400303c0b01450412407180b880d105258040c40317403902801e94210164a985 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 980782895 1250 980781645 980781661
    0x2040506090f04020708030709060806010c210e15040504141006051c060308280917190609021201061d071704060606020106050603041502160c0803190503 68
    0x700501d0036072801000701000c0c9a4071503495504640141d40e00c14412a01c900740400020680b51040c001c51010a00c0c407404145250300074811400103d501c041030010103101c4040407110a14903030350090a0110302c038012403056944551041245540704030a40d200e92400c400c100940360f41a060590b40b40004041c069147c880c0a440380a030390340b1b0704205a0b102d465189040002190440b50602103180402c0481000500b170000c11090141d8020450603860209030030f50a0301800b544000413443c54401001540341e003510f040203104001041c0c88200401020965070204150b41c220342203070752141c0c080110b29003240303a00c40400a41d8020080d40313081000061000300c20300c907608860100d01001402480c856903514272030903a102d844680b18105454000098007580c0504000f55082000c0440c1c40e00700103040d01c1c86a5044074039031520103136131b8414078001c2d482250408c0d80301c122006900085841c43c0b4100340242902401035540e4050b264205d017400c496018240f040042c10014420700e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 980784145 1250 980782895 980782897
    0xb0705060403080414100b100f0f080601110615040c0203040f06030203180109060b01091409011703041e090506040c120b060c012901090315020f040f080c031002040506 74
    0x40d42c103007807008050f262030611200d141ca0800c0401407901c0f50142c45002125280c01c1030b00e408005031150401d0607207046041d0741e401c600c1c480b0140082d403101c000741c02051044005e650026810b0402c1d81c244400320441c28280343e41164003a000d01d01d80d0000d050141080d205840c4440c0d500e201031810b05007400c00341023440503030b40704540426030003102040344603030062038000307880c0307900402000031064a00d072038405484096501c0b80441c84006001800d1044916040305035100100342c0d0440340e0070140d0840240b2445e8880140500c0b003840041060002d0300302e241d41e51009001420307030b0b0510703224065080e070b000201028051410042042416038003c038452074036845100001c9500d003901c1010401c0c500550841d00d02a6007081902c49000510100c55150500840a4151080714040c01580ca4460600c001822107044203000f506c4101c166028100c408901c0786202e15195642500e002c00c841c064000c80c0280e0041c007000c044500e0104040d4070f0180f080340e0f003541401e141170009102 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 980785395 1250 980784145 980784151
    0x90605030703020705070b030108061927110409051e030406080109090f0204060605040815062d09040b150f0a1e050d080c060a11040909080c07080607090b070506 71
    0x241074011890300101701061259001604125104c00d40300e40e510741109503685030907500c640002c442004603585c0c0100718040d821502d0800e56607480402c1003800219800c25415500752000801e8003a00c1d0641d0b640c0d030003101002c1e80104001e1144110310018816840554290003541d81c0c01007208116107a04481d02e0303811242c4c0d400d80000e18405508246510310390041c0d000b9441441e24a01180b0720790054007a1080d1401c400071100d619903060420001c0030819110150320580c001e05010425082c5000c034007140ca800d44411103001d90340c0c0e010a0a1490a90b0b0499000e0390600c100007289003410f010100e5407a0498410000310038034404101200458001c0e907c042040b401c00b0350b240c400c1411043c004040103407003d007203a2190f0030002c409400c03c0c03881e580309004803c00f103554010a405103101d8946c5c07100300c1a1230301d4a002040300042c804e100085401680c20f10111200b240306111000007040c0d2000641030600d00010000c0540b44180c000070f82070300060003000302081001510f030364 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 980786645 1250 980785395 980785397
    0xb01200d0c02030a0c0602010204150903050c0f030304030c0b031509160503070e061308120307120f06121202160e16140406050904060e06060327030c07030c060906050307 75
    0xc000820b4000700e41019440c04020302078031074620000039215815402442198450445038a16440541089407900018840503010750320001e03c4080e00c0c90600c19035001e4020080031a4035080c0d07a41d80311400800c090b40041c410848c08403c0095115101c1440c44d8241030490306014103181000d07404101c00b09407040d520800c940840010341076400742c01030000481d801800700f51112940441039a500c0032034000e45c5010300503d10304a00c18440038041d28059402600d5070040c44080510070300040040311a400500340c0c8075100002c41200a004420603180a152290b8452056000c064940140b60504842e4501d003d00100140e4100102c0f0541160031070308441b08150240700100c48900e0b03030041d44503281b08000b400141d042d40180060900309000d03141440306903030f5080c40d24080002115610b130480c00400000b44c1854440250214641e0380345801d150540d5180d0701c00349150810540a040c0703500045081c030070300c48080c4946008108074030706034080a0406600038214080a4030f940 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 980787895 1250 980786645 980786657
    0xc06163009032a0203010c020102031b07020604050d03031b020303090c0906280303020c011806080703110f09040f0b01170c04120c09051803030c090a030204050a0b01200d 75
    0x41090300c2601c542c107400040e81caa050707612007903c3c84003107416038140e000c03882580380210080100d4018004e480c8035201000309401f030b52500c10748602085d88410000c981c091010407011601c1e5a40150400d0b005000b540d002a414200703005200700c614035110040b0179176006108111130310000003481c0d1140d00007a076108041d5250100840c000421142c00918019001c21894103400c00c07203001130f030484c0d000b0307400c4904e07a0301c84030019588900c0300d00719400ea2101c00ea00c180101da008410840d0003000300e1a00081c03035601a0b00d0220250020401c100d090b500000e0000e441e450180126040c44195050400c026600040041c1070300c1000d03401076050741c0c1080d00081d102c005100036900184110400c000f4000c01034902444a140d0718052504810b18000c081003001880b40240b02d81d4411000065203103489284021210b074205000700c0398010000980880162210701a50303010312102640820a0405880050240307640c0a0040075054260f6048502d0200f000941c9030005626003098 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 980789145 1250 980787895 980787911
    0x1908030a050d38040f06140a0611060c0a1803032c091b0408101d03090a030311101b033608071b0e0c071106030c0c061630 54
    0x10134082e152074444501c182d40343c41c00000341188092004007070740340c0441d241550b691700c038901a1000c6d466818100b84590000c0c001513078040005008210004031030501021034424201c2800c03845945410071000070750031b041d40009040da0241011826042c19010341040029440400c00d98135005100c00004013103028001140f03440c1d042200d0252543e0b009481c840440c801c6120003131300c02c5290400041c192100c900d00f04a00100a48817440d900a080e41041032954400300c80702520500c42d241d0600404008031410b14440c844e07a0100c0401c4a40e071072010344c0b12200038049800c2d00480c02c0990111040407465040031400300c100002186541c0f04c41c08074142001c1d9850300076004e00030404103503544038031a030b10f0000c0001307401c0305c880403100c041c02d0751514241c216900618000a0110030942a907040524100c1c3c007440d030056055a0366030a002018201070703d800c000361042400b07000c0d00d00700000303550362040c6c6801070300d4084182c0072840c800c0350b485072100310364001803815030035555450 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 980790395 1250 980789145 980789149
    0x3100c141308060705041a0309030a030b0f1002100b03030f04062a0506090c0f0f0423010303050c100b0d03030c0903061b02011b09051908030a050d38 66
    0x1414002d0311250703040b038059240054000d03001c2c1d0f0290043da03020558041c0154064582074045070310608420001e14101007044c94180c0140552003502944140d40703038403482d0a42c0740d00700c008a41c01002d034010310040050700b0003981224019101680a5002080340040d01c084a0040ba0111034a80c58900c05034035140180d000c44841000d4201c2c501100e0007030301c0303061180c00503801d4002c903d13800c00e40300d4002020003042074040c5c0014284d60001541d5540784070b03501e083c0d80180381844400f84034451819410790808501c89003604110082075000c01d00541c0d0f5031080240340c40100300300c007041082d0181100001c4003101a5200201016210103190400c18405d40921009541c044c07001d00c030360500b030801422800b40042c1608010f40c60310141c10f60384071071501002c0500802d901d0301107250381000203000489c42c5040c81c040400c6007100300012101c008000078590140c04d540c455468202281400d01a50440d4850b100326845029074074181181485050014080c19001410305800c4400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 980791645 1250 980790395 980790427
    0x42c0321060d02010c1b03030e01110601061409040603080c010e070602030703090e06120d0306090c0503060d02060a0228020f0d0b0a1d030301090603020109080604030c06050c2703100c14 82
    0x6c60740300751240341000008054100a141919850913250300c070f8000b01e01c04200740e66850910031800003a04003040d51f00301c40b589000600308a00058404108241c80c0d85500043e948064451980d45c1c0d56070307520b615000d0080c8100d00160200d44003661420805481c0207017803410500414281d14807460200340c035a55000c11302c5a41c2c3e020701051716240081d140d8041d00a044a10590344800c4c101982c0700c81da54468801c607032290708020011070007150a5001d01c6440e0300203e2030307141540f00359503ca840c03540904ca92855484403191007124404c905105000020300004c013554055030503038206c2c0e0002112031041c154481c1810100061028070b814611002c80890516281540400000800e880001e45c0213030042e28001e803907840e44c460f17484000a03070380c2ea02100c000d0001008c0200741000141070340c00180d04000e000c20b1007400c140303101c00d441c01c6a10011884484c10000020310204d6410309000002c0168070b24001000711404080b40034110a0003006c0c0d91460442c00031b840c0380d050300c80358 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 980792895 1250 980791645 980791673
    0x16090617130b0a151703070f11150901020c040c020642031b1008060a050a09020703110609120d02042d050d11042c0321060d02010c 58
    0x1e80e1000c5403c120b102d500040a103058858212148100c020030100303400d02d02000c441e10031500642c0703040281d441c0c0751030200e0034450480304414048400b140f90390b2008104140511021407450b50b41003a040007a00d04221291104d01860802005594070303900411741c982c3c03128a8000c03903540300c0003c01d5010481c0d000d8004040d80300f00803803000022100031074803c030140c00c0240e04981e003031031071a0014401070704525460359014011507006000a03210b8007125400c04409404491402d84640c00200180c1043c0c00c600030080d40451850f080c90b81c08400d4459a0781c00001810450078100307952925843d03441c0c2140380c074400006007030f03254101c55030494004008032008c01d001020044450044e49a40c00d1119030600c008003000304140c40c01107803040302681e02c40001e84181100c80180805401c4201e091240d060f02c2050b000c5900b084041c95918600c140030165503038111111503c48003c0a10721440003605000c0100911a2a6031420103411902424510304420840c50b0022a1403001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 980794145 1250 980792895 980792903
    0x60b030c19081212010b0f041a0a020d1805270a1b0201060b04090b0301091203060f0e06060a181a030406111e090406030215031609061713 61
    0x1681501d021400519a400195811102501c0c0c4181d00a0301010301401031340f1042c1142e11600c0e00401040051790f00a00c030318024402c845041c2647d41102649000c50880070380485c0c6170000710072904a60501002904004d51300303082c2c0c1c188001500e00c4860103200e0099500800d401410910760000482c502c0000161880c0f902c07002e0b140a0a044016213145000313410601884441d03244050300601840d0213640024441c5420145005c203500090b2a082ca03503d5055541c811f050004210042d13000c9210038031945020801d146060007825014189602400c0310720300807005d10880759100300440345081c515142005440c540054101340c3c850341c41d801071902e41898042d00407041e1510780554800c50040c0410400461180b602e41d04030b00c51110000703445032650200f809800b20034400741071708ca10040c0001402a40301d502041141c10344000380722042c4004001c108403080c0700051000c3c00d0b4082d242400c840343c54104040d100d0400c02c4010002c0e0900c440001e0401c2100308141c906580d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 980795395 1250 980794145 980794159
    0x17090d080a02120a020c0d020f0a020409021c1b050a05010212130506270d05060f0406020f04090b0f03010b0105070b0a02120411010905011b0b040501020904020403150501050a0b07060b030c 83
    0x1044c2603c074001d5106038568000360003040070b00241c1d60b0020884004491400003d04001310707036075003000000c09c20400100d0b030003007440850390740481c18640e1428645200d041300700c03403179050070b01100c81d02039036a4404c900c11003c0070020b00031359901080f407601000803466201d8680312240c80081e41a0165000103400c004041030300d20358191403114200f800c60111207460b1042c404101800100503155034040c0c07107948a100451108102039010302d0f845800b4060040c10080220465a07599001d54040c0d00f41e9600d0b0401d415a0740340100741b404e0780c40802c81c001c000e0f1012420020307000740940031000d049010554009081102d00d901115a40e040c02c04419501c2e140501e00f40c00104c2c0002545030001d070030a80301003201d5001c1d00100c6c1c401c29003050400710029855440d091104030080003141c080d5028803400ea010744490001d0710240d841a0b100701c400d00031641c002e00445105a00c07d61040605030010402070a151040310400380e005980842c150f4403040200b03140c044404802d5800030300e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 980796645 1250 980795395 980795401
    0x30705040902400b360a080c0f0618060f07050115090e070f09180605010b090306070e091302040b030a08030a1109150a141917090d080a0212 62
    0x103c0380c00c44118190000e080000b080b80c40e940104000d005071000704c521440551114418030f054120740000789400100003d0344035041102090150840d0381c401c3c0c03082c0d4041d40828586241c540c0440d444401c00b40e03005400d004482c004144401c0401c4800c90169600244030a1510114030407100075a422000034880401840c8410949a4542c858001c0042c074011a564908002180c11000c0f10422540d00c41e150b030802c00b01c82c1c002c1414003100e140002020460780001100380c00340d50b0013000100c00d0903446910f44400e2509124008060208000c050b542d00c642c9956440c4005401c107071234000484c055a014404500141100020f4560520075109003404005802c801544602c092800a00841000c8026249030340a408041c0764440b0080540d245e000b2078190181241a4007417420b4041c03d1914413400c14a0307071014600081e20007500c3c0980c08282c2d000980600c034180700818100f807500d0400d0300e81e40c80c0d0f41114462401c110780c000c0801c0d9000842c2c1c06541528103d510b82e140141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 980797895 1250 980796645 980796727
    0x11130605030f0c091807031e0501030201020c0a060c0f0309180912090b030c03040206040e0108060a05070f20030c07081c03090f0b0402031002070b0912030705040902 73
    0x1030012504121000c0000c00000d120f4a240341c1918038800001c1c3c078118401c0d000314040d1840580041c81e4208150382c400044410729041c00318015600fa03484c80004855045000082c140a44214094001d0a1030202000030540c4100d540b40030541001400380941e10398941264000316550022a500d0030134074032036005100581c40951642c1c40340000c55100c16094405a40581040c40307582800b140601c0001c41d560a070070025680644000c0c24645860f0b01c44031070014102c003e811801070f5500440420141c0020761040c20341100b100c1c02d0804001042d010010011012103140a21a200001524418082c100142d4804560900c1912409515031030290b0b070742c1c04000c51480741241400c82c0300c0c903414024850424502c0e003026162822045075299a00c8040000c0c104907014803a650b0b084410b4400751000d031004901c00c00800895040001840b840d2044c0c0d0640d040c0c2d0104c08105101c1c42c50380000c01c544c2100c1d107024007d6103e5900c01d62004171207611541e00c1105054400c6082354030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 980799145 1250 980797895 980797897
    0xf0d060b1509100e030115081608010c020d080411060f03040303060801051605070c03170d06090507080c070c0b16060f1b0e03070806012c07020a06020d0b0415081b09040611130605 79
    0x101d01c003001d6098052b40c03079941a00ba505012424000b5810080c40745407803d110351540c0c0c0d032240c054200280008083c6010503c55445004112420b590200501c400c055160180000074402640240414117020b40c03c0328980c40405005401d210000071520100540049024001d50708007011400546104110a00c3d90b40420900b070441032818002082903c01da1007400d015041617580d01d03a680e5540103001d04203a001150070f58880c01a2800012500c51010050566050300c000d2089507042901d0494142e4407903038044401107043c1380141c8100b640717090b00d040c0b1b12042c601e040030106450001003400c0150300c1c1c03c0074101380640c070b00209a84018400000c03982c680d41c0301c00d15400c0c00c603001c3c0c81001c84090755404c0060b0448401c40000ca80e941d00039021a005400d03002409000c0c02c1e0001d41160f840490000b444c051540b42049100f0080c03010b004004004501d0485540e960f40000d00448801000180604e0340c03040c107132014103510000d5908800c1d468144001d001d840705000782031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 980800395 1250 980799145 980799163
    0x140105010e1501030207120804021311091c171606020301090207050c01180b070c05030a03121109060910020a0506131b0605070605060f0d060b1509100e03011508 71
    0xa00101e2030b1012255511070720032111801c0c0c00040d80440081d110070211030201000c0c106a0380080100d1a9200340c03c00344c0301d03804150032b806d04000d940d1201d5109005100f03401803080080260a9281100414540700c0c040082072502256542e89244628000440003183d6030003801180c03000c0000700e901545030b0300034070000d03000701d040b0792032314200100450f01e106460304001c0c10307024004001c20250100402414078544102000e0b42c01ca611000400d14219155405400286003560390759000500e0340700b0300032070088100c50245400e0b412800302d000f0344140c05003903010f0301a1074015041544240144c661030343e40034003620024201000f10b580c0e000d00f010429185603410008000c4040c0c00040d8107022940d80b80c80701380c240002616000d00400d030041c400c94002500c0400c15904d6035074030081c0041c0a10401e40011141200c2d02407024419a195030046d00e90004c00c40c40c201e6660300c6201c40c2000946141c000000d00990001c02d01400202c40c450001c0d084000e000301d516040420440c030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 980801645 1250 980800395 980800411
    0x1006140414060a03120e120a0611030c0406050d0213030f060c09140f0307181e0905070506211e07020a031e14030403080f1602060a0207140105010e 65
    0x510701e6008089000800c1d01c245038030150164080000945140b40c60078003104500703014a524240c0350208880c0b801c0c5020040d5a81c0206d1a01d804102a904c1001c55a2211003609410745c80c0461041c011803043d4000c0505000c000b0031402030408143d0102d0b01c0c0300c000d182018015035070700d1a043c940309480c0b0a08070350f140e0400700c480d81854070030803910381102c260a510000a80c0821300340080c130582000c0054040c00b0700310340415a60640f181800b0310b02000000002c0048003d50440e042c400741c9901007100071304040d6810003190001540d0820395130100d40c070750781c0c6a5000c03c0201ca0301c000c040c1d582d40101c1080d000c020700c074210102803018203424445c04005559849000320384817a84040000e020600320081001c055400c9020b0002a07403035414a441c140d05d5038210340d40e143c0c208660450005040808200c01640d803240b039540c0003030401c4081c802c6500c4481c00030351a81c000600401c940c943c0031410805016441c00100c4015640c20001c21095860b2800c50201001c2112519 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 980802895 1250 980801645 980801651
    0x40309061403060103020904090b0718060c05060a0c1e090302010906031418120c0109061506020307030e010e0d140c060c0c061b070603060602190515040510061404 72
    0x910340740285000d0580007181c403000c9141d07568000043d030080d0810b603070320b94200d0360b6603401500150f8003030700b954003403601c1d512121141c100080c0940c13005421034001c2800c009032030b01d100000800000d203254018030400300206213580d0194041b01c140c1c00062140010740d01d000340384122560088601c209481c000c0c0e86140000f61501c4044d81a5641415020651b4460200040c650860100e46490041503031003038803072820800d88990b116801c03031100440c2c80e96403514000100002e51252008404d9a0548808030b00c0c90020b02030340f40d02603904081c1c1403102c0540d9540c100e81c400d1201c0d00002c4c500030010b211000c0c003400e00f40f540d0607944080101600c10580940c1c06441d103081940c40460301d0b040100180903403c003c0c030610707401a80030301042052488898a41c030b8428840080a441d041d900050607a150100091500d40c0019003000e0803000324000b072010131008990241600f107080c0007a02e29440d5890894079112550081642962400b0f001191203034180040101c4102c08407428 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 980804145 1250 980802895 980802899
    0x1401120b011a03070c030210020708090f0a030803180c0a0801051b130b0c01060b0c0d09120809090612010203070504170d1e0c080412062f070c03050304090203040309 73
    0x602c00304518101121800502440001c803040c0c81031240103442803080c41030396441c07010a260741d020b90b046010222140780d008104400c031401c00c0b0314400c004030001c540c04120140340d030300c81c814544805401000c1c040000b030031150103804108900e901d591b202a200720311080c1c2c0c50508a00900c025540c460700d441c46038081581407508041961307101d4143c03101040803180b500301c0c0810302c1d600c80c0540003820354a82d50001a4161503c0140c9084140c0320041d00210384000c0c0010b10803a07840d00003400c080c12041c100300c00302c0d1802c2c0036a00c0a60099440c0c5006485500004080080b41102c12406600000400c080c00764080094400c54070100582d0020741c1520400c03903101c1240030031440c0044c0005a402d2407211303032800102101c07012414854440c07041c030340303401d8034680c410b030082c44001880c9e4510004100c00c0f880754041801d080600d00c6003c50b01110b104905600003405c00b40000c0e004aa4031084c0170f180c000c0e5000441c0d0000032a81d4950350307404560080d400c01c40301507000c11141080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 980805395 1250 980804145 980804159
    0x5030f07030606050f1b010c0e0901060903170711030a1103010e0613060b061e0403021516080315040e0604020118210c050d030c0b0c070503030103080901031401120b01 74
    0x30b100183c8000341c03138440c01c0c1041d111151680760010036003868101c12160516056620a110740d55086007556a0215100d541600b40042001c041c4e0120042140ba6801040458000c681804070481213564883c0e407501c0f1800c0103080d100c641400d45038180580c62304e810803c01c80d0038507104c41d08802d500910281104030052903d4140131541004400d40314002c0d40d00007021607200d8003c510b0010300d84c609040140d000406c100c06a41704000181d6030020703050056162200d805100444c90380340721071428103468440042d0b45e2900c4001000c01c080480410103001d04c14413040380e20715024101700900001c412280d84d43d114240c8040c3e01048482c41100e1043c4001008001a614134611400c0e40300300c044014103101c034080c8810b40b400381c504000452283c0e42c1011102c03400d40207a40d101c0c1400d200e0300300414605400342076980c03441d00402101d00069808400c1c0d0b411240c1100d40903845610802c01680941441512074200ca04110004291007c04980c0b81075100d010784060800e81ea22515 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 980806645 1250 980805395 980805401
    0x190501060c0b0c0307020a08070f15020f071b1a040906080303060612063f010e0a0204050a09020607051005060a06091203020a0b0709080f010507092c0705030f0703 72
    0x7074000381025001410043c0b00d500115003202c2d0b80d204580c104822074880000a8006d01011500099501d4809050100300c2c50480003407400080c04500d05403000c031400040b44a1890001c00341041c1c80d04030a00301d482c18060100402294580015032501141d00e0b8805034010b006240400b4a03210380400c1e4103d0000a41307100d504007503c0c0c24a071038030891114042c84002021103a1017640340307134075160030b50089403440c40d5291079101c01c3d141c01002c03265a101100b61b0f14100c0388140c0c9040b0524840c000c001440c1040141c0503100002c85489440501c405008030000180d04854005401c0b0304001c40041e140f02d40d201ca00404118585801081115038640e0b4454100042d003010414445118040010992136103e40121450300a06503500e14000000700c6203980410249402080401c00a0246000c503504600003000315203014070300504411341038052030506414096010340d1102062814190341c2d81c81c03075074107650703850700510062940d4406c80b0714010a10500004c100340c2d40c0280 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 980807895 1250 980806645 980806667
    0x90309140105032206140601110a080301090c02010b100e150910030e0c120c150f250f061a03030309070306020d06051f030c11060a0c03020c030319050106 68
    0x6541c591460301c4002041d40f150528104d4003051a00c0040407030001203091198406038600f03036017105018a030800015154101c030300e010000d1a00140462000a21840c0489040d141b4011000031000c0710710401324010070400c107020307400c0788881e02015221070300070030f4560352840103c8001042500840c44a10903010b00d01090344c01900c8040c030100003e009070403109010f00544203c9000c0b01560f0001507041c42d140038000c04580014200d0881814408060302003081c414915902d00203071440c088801c1e11404007034803450092b02da010080201ca42c500c007242c29400450f400055450750a08400610341d90301c051685100e05c50380d204041c1004401c2e45c5c440c03800c40000d800d140d451750300d6182c042c1d4410090302082554406000c0b900707664440c909441c0748034002c5280d030740340283c0602408413a074041030042401600001300b000c0c1c40d800508030743c2c400f44880000c10340d000043c00036006030084c400344120310302020041054002540200755100d501c414000e00c01c82e40e030f60600362294a550 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 980809145 1250 980807895 980807897
    0x18050c0c070306020927160e0310050c0c0d0306090510230622080f03091f201c03020a020304050409110405010602060a0c0201060e0708041b090903091401 68
    0x807802080401c030140d0140541c0480a0001c990303011454440300b481c51106807136281c0f240b40100900c41008800e0002903846e601c1d07820281a40c12180c1c00081d9664020203034219425111000030720380c02c04050a8420b4605c100080f030701c04883d600c05c06000f900560184e00c604928000000c1c0545810a00400440b14501ca20b0144040c00015641c90f000704a2421a0031550401600e108290700e103041100700246030b0440c61300c0300c2c10004158202800d07c031001d140e96005100c6050300c0c2c0e460007001004403005500f040c00620380030f20240d541e41551500c042064440e04040b0394046004281a4245a00b0340c0200e98041c0e0001030990480c000c0103824070042e401800148180c2c281940300c0b40f56240261011411555220002425640c00340c20110060304007405100380200240103908010045000170321201e420007826502094000b00b404040142000c00b1409006581c1c107291155026414a00481911408400040d00342c07401c0441c0080d503e0000080c0c4c2e20301c1c825000955000c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 980810395 1250 980809145 980809153
    0x2c0303160203072102070b040f05090105270a0f060e04031b120c150c051b0304060e040911191d0c2a01090c0f06030507120e0f0718050c0c 61
    0x42c04a400010002c40c1d41360040d407141d144082a045290000b400007840e036404440c95050400703040c0b085080c01a40f045000307003484c46c08042204202d10b44071015100301d004825582da11002807074080c01034689540300c51032501030701190802da0132102d90b11442c021307102c521150302049074500241c0c0b4010b038003410302d460842160007881e00c00c0644070340f06805074082007169240800c0310320448504441c00d1003c40c50000d500001c003d00720380002e0303260b83c02a0103181080e141c10400390801061000c0203200307030364401c05041000002800500440b4000d4000503220b840c50701c00c4458001c50b402442080410300c083c6808040e07800362002d109140c5a0b000504019801610441040580c0100380c1030070038410092003201d100340f0488036190b00031105456010700d07220000c48040070640205040508040420520b25005200c1700709501141ea8001032403210340103d2400c000980c04002050700410800250541c0301541800105101e810200300030b89a003001c982c10351181c44910030709604 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 980811645 1250 980810395 980810423
    0x6040c030204110405090109020a11030715050a020d050a0b0108240f0303070b0f060a050f01020a2a061809050103020d030507030201060e01150e0906010c062c030316020307 76
    0x4054111001c080082140340f41095140d40010b003201b0f009030000b0b0302040c0d01089115105900841070005904c800028518041880e229a1102c2d9054107140a050f40c641c00401d124411a40c1110a0b418005a041145007404505240940266030200b400a01c0240202300310b10b030034107003a441001907421189d102c0c060703450030300c081d103907019900c0c40d17150105100c4180407800402c0134520484034a41c6d00382491420303104001c02c910305034100b50f028680004401400c0d0341c0002e00036000301d03001242111002c0030f47c68104140c3d50742c50380f200d003001045100001c0c042c0d000280040000c280c5030703005912039140c1d0500000c5400910000e5030107100c80140700c020901800050100e14021b10000c0750a6455002c1644541401c0c0e102c13441c8200c550780403001a96101c1d044010302103045508485a003400c500081030500c070544060204d641e03401c808107140f11580e07a00d0183c000100040d501c40f1f008400d0f0f0f0f58882e04200c031082078217605a81c112030403d102004840007030794403014401900c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 980812895 1250 980811645 980811649
    0x120a0c080a0225180b06070803070f1b0c0905060f03010c0c110d03051603050903120307030c020f0c2205070503040b01081207030806011110050108010c1d061c0609050402010e0306040c0302 83
    0x5ca10b000c0c41c607411081c10400b10010881400003144542d000b038985420141d411400213104020104074881010f107039103034100010b040310b030400003107408540c40031600d40c40341c0c0b001030100c013104070746154190300e41200d9980c0030b6017101007210003c0c0212000b0740494000014802c82c0100e102e8004d001420800071601c01800307194103409030501920f007041c00c0440d21070102c2e1805140d104041c00001d000f0082240d046da1502502c000c8050174030241c10004039054005580d00c101e00c4a01d81b0584450749012200301039401d081e064100e903c3c1080c80a42084040648258802d03601624030300741107000030071203000000c2c0c28034820052240c014501417454504880910020b4907160410035041d8011038a400e003004480d200080c2d110002407c0e52400f01810708480c441402c0c2000d02082c3c0b951f500f0140d12001600300c06400a4640640c1c416540e0004000c00020050b039060b40303441e1070408580840d25a008034422407007030302c0d414100e40f854420144e032506c084030018040001c10500380014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 980814145 1250 980812895 980812901
    0x10b060c030403080a050c0607080a1a0a060f0507051c02070e07020a03120e0a060b01030605010e0307050d051c02010603030201050a0212130215070f0b0105060705120a0c080a022518 80
    0xc411700d01d03000d801e0030851021a804c01d6003c0d81c000000802d24803c0c0310700d07000c003031141c2c044404403041c01c04000c4143c1c4010910144003445003a00f8440035101441441e4003c90440e24019800008d549112808082900701124114a0303000107100340030001c00c0c11602d05207290300400840d00100400902540c0c1120f07262100e9500041094403540005500d00703003041854407052007108042140d0025000060440700e403039004034100b103910640702d1460313140441d00da41a924280d5400614505a0826900d018000c1c201c00c08440b14010000b403920381e042d8080c1090368400e5000744200c0d20b80034440000e074020762101ca084402c481d00400c50070403000040041c4240b000d06155840b4030582009521030700102c0007601c0482d010f25512080240c0b00c0070250142c10103e0f509803c040705501c0d207542d03070150160000c403690000621101d46900400e119103410794045045541c50220200003904c413105000844070707031400540525020305c40c9025400507101004020120b15007060015005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 980815395 1250 980814145 980814157
    0xf10110409110702040e0622020d020a03030801031b060806040e01150609051311121302060a0921030e0402090d08040815070503040812181509010b060c03040308 71
    0x4908040000141803040c81c01152039034603070460b05030346442c1140107110070b0726503005240b20035030880401c00c09010344e8200340c3e05800e01c00502c50b642e00c2c1501d01c00b01d0229184064040d5200c0c10141d000402c059104182c20b040e01e22408100581e10321070000c084076034075140036180203d51010005417041c14107078464a61030b21240b0020a10800c055801202124183c02400000e00410703021b2000c2d041103146c5d041d581c800c482c42009000d0080c0c407240d44c1d5028031001c0b259070f0700407200821034403460105261502c980041203955038294128020b04920420b00c91600e035589030140103100c400c01d52036003029440c0c2586650300c1002800040000a5005000659001c0e03001016080402c2d031507409000a803030300c100144918806058211190b00000b0f00c0b9000b0007404108100c0055a050300341c07044000b41d180d01095680303600c040440c9013a14400251910320070317804c20551078412001c0b50b034003828400340204050900b06050045030310900c1400080c951042004100040c03201d03000f018 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 980816645 1250 980815395 980815421
    0xc031403120a0e071a0f130f0914090109030e01180807120308010b07080d0902040b03010e06100618170f0f0c13020427110a080f090f10 60
    0x324140035a0005a04058241d418080c0243d40b00000100c00d042040244090150896030403500d501d40c280c2e82d601d42c8680407203484141800b181803284001019040d0300a03096031080180c115480d41c20b600c0041041900011049403003602203195401d040c070445c0c2800c4c1e09651f507071000b4030800c3c005540000707500c3d1201908410282002581132018040c51010b84150022060091f02c5401d005140c2d042c10b130000903001384108800740010307040d4000c980340b82c0803452002c60700a5460000600500c94030074240e80550802035990101c00740400c81500c14000744c518a2a05502c40c00704071303113a20007810101411707080100c050002c1c0211030003c2c052000800200da00d600e58017488241422125004a14136a0050175242d600d850b2021202030b02c581560011030919282000c2101c5150507851540103150304100d6121018040da04076440000348440026522080c50340c1c000d00158040720080000603080d4080740140d0000f203000b20210f0a03200c0140305008181c0b002c0801080c2501c0821 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 980817895 1250 980816645 980816647
    0x6180103030c0b060a08011e241a072004061a0f161a0115032903100203091b030313231005040810060f140418140d0c0c031403 56
    0x40e401405d00070460042c400499006c6010054000c0c02c00351103200702e804119271001c2082c1d61400b20100e00c8a01250ba44424441040400101c607140b5480342e02d40117020400108201c02600040044941c40d40006031406c010141d5594152500c1c2c015910384010b000004100c0000e07441d2a07400513150b0503400c1c07132a9058a44840d076403a0600c29801c046060140f460800401038201d070044420760520706030509108000403814440341a0700306200b0810540e602c91090389103030310200640d05490101443c1190340c0d050038190710390340300c0074010072144003014807215040504000c003d0360000b40f0000c110000c1c103824001481c0b080129100f510417000030003e00b011a46e0780e4002e100c02110140c1d154144d071281010348036414048080d84400381c2600307140b4200074031015442c1c03060494a860100401801030300c0000740140840080a226920401c004c06003817000e440c1803d0308001c1c41c3d5084590240c0300c0780701690300c140c00351000781c92030f00001020008a20021001c5040b80f051001787d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 980819145 1250 980817895 980817899
    0x120306120f0a0b1608010b030609040813030809100203070b01050909030f160605060d02090703020903190605100e010e0c070201050c19020a06092907020904060506180103030c0b060a 80
    0x640c682040b4500a0300c0000640d030500030502401118400e80c104a480c064810303604040d1080d00c1480041d010078021a5444001418082c0c81000d440010303030008a4200c1c0785503681000511a00050301452040b90141501e4055a000204880d54581c1c4900001c03c546e19007020040c03c10341c000c01c0203445010401100004010b50170041ca0402903940c21944142203d0520000700c0704002e1a10f40150324880e54400540d031200310113684040a840e01590b20703201400481c0c2052280c003407200c8000200b924840800c00603800040c4200400b12502c4406541d400c0e03000c01a00c030a202d103440311228a4045150221001d0081a0850060600c2c900e08130303034569428505400084810300001c5140c0d0b031031045107803c401540003003299190001d5014144402c156070b000c2c280e141030554001c980100c8004c0c0f45084141e0301d15980041210343e03185428140600600f0080710200e106c1c0e041d11802c840710109407100d96040c4e94141d0355600e1322090607664100030701405070510b07a02503032074000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 980820395 1250 980819145 980819173
    0x50102040e0f010e060f030a12180b04030615061b0f0f3f0c0c05040519060b04060f0f2a17091c06020d0c2012030612 52
    0x2142c1c080c1c4822000310403550b14004402444440c007500282c030540001500100d20741e0005a405503654200c0c51f0fa01d0f210811050a4643c07590500501c07540c80e8034070b180000c2020040d00a44100d0307000349414443c1120301d00f03a00a0030045401102d000c10402c90402c40c46480342009500e606209070590380b1207003038580710b2258603083d080040380c0c03001f00d00c40440c1420000d21000c04080100c3d03440b01e11840000700142c0300740040280d6190810505071120030034010410002002030a01070020409030038035555848082080044811075541003039000200c8460a20842d001c0314299074034242541d0303181008035403082c000c0101c0030401610140156001508014002190070b0007403a002c4400a20701c1c082c412a1000c0c0310361400307100c2c1803003841d015446503503583e902e4080e03118107040c4408280c508540240210701150700c0e914640f2142c1c0a1803031700071405240d00640c1703000c0c1d241c200e28000c001c2d0f0360303d11403a4884100d0305818004120507061101c035202c54103080b00c00765141e03100d000d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 980821645 1250 980820395 980820419
    0x3070305030a02120a0b03010f14060609030705060c010b180c04260f0706030c090e0a020703050c0d080105120303071709030702041e050c0a050315060c06100e0108010605030703020d05010204 84
    0x25513105c0079543c0d94100d62103482c091141c001411603082c000c0c0b00150700707041d40e6070150000a1010f4051000001d0b04403403968240000b001402c001482151503c0d8200c2c00640284452411140540c00c1c0326081c07000c4000504a4602c10200c502c0d0452410b8140b0617101d1000455151401c0444110b00d00348100e07030414068a2040b07003031000148451840c0a000405480c1c0041a031010b00081d50707c14402801c015100e1503001c0d10b900c2c3c0250b07a4102c14036003103500e0302c1410604045c50041400803600d403a07003d103400f03040b40c1e000c8600010985d01088101c0d128031060f06c551380411b044441100300e544c0030394440e5522200b10015642402000e4010400355298044c11b0440f0780d4043d03200c03005003050b5210f801d40201428203042e09000141901a001c0d100c082c1c00d255034001502101c2480c1e07600c4000300c0f605026101d0a07510b01d410242400d240240d140d00038902c04102d864004a6949014424102200c01c01001458294516000e105042824220a49003035400f00070124460690301d07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 980822895 1250 980821645 980821651
    0x10030f26120405010b0423061504120506161706030304050409080c0d030912050d060906081c03020a020d0e06040312020f0f06010302090f0a0902121510060203070305030a0212 77
    0x71041c8180e00c0c040c9001403c44403041c0c100380c07041c0d10380000225220b03865a00184892400d200c7c108594440100084100c12170040000a09000150200d2480301c200d0b14070400910450844000707444442c400e40104c04201c42141c00200310300d640702e4803200c0c44001d103a04110042d0603245059100ca010a060306c14078402500e000400081001d800001046005c1003441c1518041095452940d2060028951040a0810000c0100b10100360900d02e60021008109900042141076511030640d602c5000761a1581401c407010030340d95210364064000c455010b0440c2c6e010300703040040761205664011411034225040502800302000041d4202c603015440744980d0001c01004070b44e01c100c1c5c2d10b006004482412141c010400410050704c038504125044000c00c2c8055510b0341d240307440b00c0000c0c21119000b2754000c840001d486500e4201281c40e460782008901b6104807039030741d18003090340c040580c402c0500580c020800b80c00400c0c401e801440e00490210005032410003c040411440f401c15 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 980824145 1250 980822895 980822917
    0xc0313021c080d06080f07030c151202130303080a06180f0b03060a1416092102030d18050411040605130f1409180c040b1c060506040510030f26 63
    0x380d139041c01341210030403c0c07a2216000d03400404d00d2034250f503914040d9051610800940407c126410100540221440c00c2c46224060085440c2c40880e825a80a2121403000380c001c80c2c404000305221021070b02504064541d42c0106110340a070048410300201000010122102e55400d01d0044554050041c9801840014004201600d00c03010f806d03145407000d00440c00f01200490304105154000c0300d80c400710303600082240680b100000c0605850a620300d002917050040030200499140c00096101c245451b4040c054111602c0714240701c12104e0b4100c02540c140000c3c07104011a520410050511174214038000d18119071358050011040c60075001011101880b4a4621450030017403207166000d2016000b058a260f442c10105440f0555406103601482d111480c22000d40c03101a038801844d24409420b400e01da9641c140315000b0041070768040c0c440d0f828580030440000404500d0005d0380d070001c050b030070642d285684880c0c1e103010718409182c04041501d50070010f000000b0103440741c0f00c42 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 980825395 1250 980824145 980824151
    0x1e0804033f11121b0c1011070501051f06090602121602060403030302030702010f09033204060302040807050a030506010b030417180103140106020a081e1306080c0313021c080d 77
    0x20104c5540c11040c1164400036001100344216550316100250709991000d00d07900004804c0034182004000b40328200002d0901e608290500c5071900d1940e8181c4454031101d900103218548859089950f4107492280d940144d10480304c5c1c07852075103400d0080c40035030090041d601900d506540810364a2700a0303401a80400d601100300701d249602030107990081f10800300200494421650b015240d01084030a030030185c401d961003078419100041c40307002000e214460241d1100d030b540358010065409800703141218051180000b0b83d50600c070340d04074140d03540440604466801d060010103580c01c01801503584c56154a8400c00490841c002040013210071034159513050081c2d03001606461a200e4902c01e1a0b5220340100300f1030f54040741444c1020342c030103030300740d500c4c8103002c0d01c40590f844070140c510401c44001418606602030064003011a8a1503c3e401d03d640d0b241d4200c0300703241c0002c0303c03c9072403918400c00501c01460440282242448034a428035400141c9444800a40c0c2145d02d111032016072b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 980826645 1250 980825395 980825401
    0x6091908060105010c0f060507020c0405010807170318090a060306090b011d0106120e030702040501061e0201020f09040b13150807050d110108071e0804033f1112 71
    0xd800d00070340d405800c00b800c042d6140307a0345544468010340404005000d1555400200314058800d000035161110014028001541c442c2c1841d80c841d8040d10500051042c2110987c06000f004015140400407650686d440584d034181400300c0fa400003090b281ca5680e503444040b001500522451315424064280340e489507041801c0100d03042c1c90f503100704a110300400c00408c002c0c0d504c2200300005c00d10b501d4001c1018120004050303d54003c01a00960290401c1c0000c00c0c0c03039034402c0703116041b2922150550f415422000c0243d0813445003645015800c0d0b4100020182801c0a0304a40c01c89000a842c01d00c0b510204200002141d19091510001c0c8440400400102d4030420002020b800704481030400b9504e20340d29040700c404a244441d042c40110000926118000c4006880088118080844211104000501425040703c040340401c00760210382062950102d4640c02654804103006805181d001c0c0c14040c04e6006c2c0301070078070301e9101d4418182c040381e060f003e002d1030002c95810038480c0c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 980827895 1250 980826645 980826659
    0x1b0813060501030b0f0702340503011e0506010903030f0f0c060f05040507091103040f02030f0307062c0303040303110c070303021b1c080705120f0304020a08030c0a080306060919 78
    0x8117003e03000908540c001e8480341600e402030340e440e03171088400c11000c1d1100a8000c0004580c5101d9a100d654075520340b8880030480303071445007112843e0030407000410107640d5100040d030b0808458000500000c030f00c0d402182c061806605000b04078038030380c00e0060310141c00e6514003081c0e85c043da03034800e00b45441d8001d10040090800026001e8420241c041c0400304580f03a0300e00c0306000c0200003405401400000f44251b460511900210744102010f50307507104214100000a01202c030b910104103050300d881803403044410071182d101d074400344025600d0341d00c440d01d0450241c202c8140d0340486501c1006109400b1000300700c2c00c03004611940241055850310308103030310741d10000d088940c00748200d030900c1d0024411a8424114043c0c0c40703481162500303a2810142e281c90080098009020800541c11014054540145106034404c83e18410a55112640703284c40340110140314400c0d501c41ea00700400540310101469005001814040c207020b80ca6001442089a000003400c410b02040424002d003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 980829145 1250 980827895 980827921
    0x4050f070602010e10091b1d0c16030819051801050901110403120c05010603081c09021c030e1306210201050d051f0f0510031b0813060501030b 63
    0x1c0041d80000c003d55510884119118118104400c90940e42d80050f1010403040f2440c1d00c650b000d040100200d4140c448035000903001e0780c13400c0b01e098251484005414828460120f8843c1d0000102050900c45242c0e810385610502030300340500c944149202e2405c414861240d58429190303482107090b080040c103d4542103802c050240c01043c0d040070b9400440e07a10004c116001c481d444445005500c0302800708840910000c103008200e5402c20030700005201040c0b020b071100d2b2414213a800000d01503120180101c5031401c40094014154146d04402000800141602c090107800c03c0c0705c0705143c0d900040d90341b4061030501d00201d641c5100a004200c25406c0ca1303080f130000d191400340750304c1143e000a8028002c0040308000c03583c03079200013000170612032040c105070003d4102d500c0220351583c001c000183d031540182c40c003407035000e5058015039102c2d00400c4280368003610000300720785100f0002c450110004181c0b00400920905201c00a202441114000d6024502e000d28904150301d07101c1d00303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 980830395 1250 980829145 980829149
    0x2702030a0212241c0f030908060a02030a0b1f031806020c06150306010b0708070809060a02010603060c09030308010905090703050607030b01021203160806030c060705070824180a0b04050f07 83
    0x3c030b80f20b4a01344072030080b402102d0a4581c002d07180141c0d804e514039040702c030f8108940100145000e120f09001e6000c0842d00a50301511903c20f00b405071200f03e41c10701c59080c1c14403003890950309401c0c3c2852030440c0a640003028001740d941340955200f640340ca405080c0d81c0801098002580321108008070004032042494400308200c0192800e0351604070902100c0c040c44c2030117404444000303040320400c1104000c544040b00b002e0401a1504c49114000e0300170030140c401501d0840c00c01c0382d50343d407903032089080005503035040c0c85000713450342043e18400c02000e005201000b0352103580ea011000c91820005c451080400340d80204002e24000c0009082c16070100000140003003d109010751010a41644100c031011454030b40040d40d10a000607103480c180301152904404001000360078440d012031a031040c2c0d030240c030840b0080e000417807090241710560410103038462901c1d0080b49550090050800c81449010211500d180d4551210340d005402580c04565540c0043e4a00015100a101700e40c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 980831645 1250 980830395 980830399
    0x5060301050607080a0e0a03120810120f08090415031506061209110603090102270d0b07210603260d0c0c0b18072702030a021224 57
    0x208551500020528a005150380202042e00125050321428400c0d00e960b1603041c401025150203541e68100404581e400001d0003000504410001311542508605c03030b012a024500340d040d44501503140e1803158145c084049403078401c10003000c802a40d42c0d014507589805c0c4040c400d4141c0380b0398a46681c04d01c1100b5588100c450812004200080d04090590309202c500345022410004914202e0100c40c030f0b60035469441440401072042d40403055000d0544102c1e080700120007085c0c10202d80c500f0100d0303540880e40c0031440c00c00e4003000414a00c002d540007400750034844135081c80b001580c0710000300d8031160500184d5810381003042c8400c24800342510150380c06400c11a0050488a41040c8550340c00c01d2901e9841c0c100c0d00180d01e1203001191680e6410584480d100d0a2542c800c40102e00c1032229070801d8030414a01040c101d81300c9072110001d410032540503105240711b10207480a500005c120709280f43e42803050290040039507102a100f00003060720b03049483c60541d08162410940c043c498 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 980832895 1250 980831645 980831647
    0x5010602071706190e06161205010305060115053123060f0906030a020a0215090d080a090222050705040f0b1605101506260a1508160506 60
    0x1189a40214180b90810000000e19800ea2403c0550b40e003d07003603442e000006481244200035070314105100100d00921f580da2080c2c0c02d1001d0f10a0181501c000707020140613a0000c00040200301d1055942c4940350015080c01030422100c0007515548551040903907103825450301c2605a021011203017200540b1150f404a0071500380c0c0301110060100058000340560b60014058803a18021010780d280c0e020000c04207641c901c3c1080a50300650020034085c03015104074124100d40001084400e441075003031a009040f4407462100450706048050080000781d907031036540d000980c8946941104080f0f08429480144500284481c11140000c1a5404100b018041400300b405131070040411940185505d545514200049042100c12940020002d118000c00b1a54182e0244c01c200710148050800ea55125500c0b141980e4a089198a1583d150140e0759454010381030101a0341c0c00103684000004e005101417801ea490301c0c140d070085481036010020b0b13441e50704081d08040b800342900b5070b451 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 980834145 1250 980832895 980832929
    0x9050a03050705100824060f160b0702010203011d04061506050c12040501020705040203040204110712031a09011215020c01020c0601120803160c0c031103010b0307230a1502010501060207 82
    0x100d909010a06103e60411b404505504810b03600c520503910464942900e03035588047d4070440030850407042d80110390113440c2c080040d40650040c420ba0303040710700c42d800e04000300303070701c1100780c104041c1c0240201d50380e0399904048588201901006800381204d9102c49035541c0a00c0c0302c41d80750001540401454400801061085990100e000e404aa03810780d0090b8a81d240e520001e40a420501103403032000e00c3c00f00307072007060081d491060205900b45447c10001c45a089801c0c031481201c00c540b96402c20f00c2c00c001000b08801d62014420f10b04d0084100d411951008540a020380e071014664101d80c4c1c1d000b082c0d24040d0402072004500408501d14101d01e10b44040e81c404810307000040c0301c1100002d03195040c40c0440c1c0900f0180d012130b60311802414020791240f515011345c10141065070b0085d0f10700040319559003800100d180c281d40000748805980c80100107003411800040e14465004030b1480e0740012203009441d826010040c09070008510780d8100f100003440d00c6143d41c800d00c05180c5642403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 980835395 1250 980834145 980834161
    0x4060b18070207092021010e010e13060f14150906090106140c0f010f0b0603061806010203070b100501080f0123041b03090209160206130309050a030507051008 70
    0x140c0f007141c1d044900465482d50002d40c0340c00c210280e05200c080c44200249400ba01102d207140410700c0b0320116006120717a6210040041d150009009840c12205a01c011820f010380608041030010300c02c1101003207202ca047c800000b6104d03044a0842441034100a01211926629407004580380680300800c2c0c1e40b03800300010f10100c006101c0c0e00b0a108001166802413440241290140e08002003150a0f80d800141028024000110350058107480c00c00d080b20309241c81c3d41101d00450b0020119600c0100b1413400044500d00a0800760540c40100300d503c00040d80c1801103441400305845429050346040005007844c140181201c8100d61300000510410304030112001004a120040c101134518102c00300f0000d0003241c4074121310302e4400d1880424144d150b0413848104c0d101799000340198482903189100620400090380c0035030001c03000202551580d4141444050080c03900e900030340c1d6102d010078240d0603135810613200394004503c18403d505020304800a03112691421030200e19004013 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 980836645 1250 980835395 980835403
    0x9130215280206040611040b0703111009080405030d1b030320071b060e0607110f0901080d1d180a06080d0513090203040c0e0a06090504060b180702 65
    0x51603080400e0045500c1c0001002010a24030741000d0500c1c40100c40e80d510070203540c814049404940340c50a080b40c0d11031070702200302170381c0803190340040260514030142e40a9450700f030042c0791040140b040804039074443c40e20703014440240e40030f0017505e6520f5051805150410010038812000d2022240e00198540c2c0052004249960503280001c2c4006042004019081c0c0c0d54030080402d000100d40c04050080c04801c1100d0342c0b10303034050865420358a0109850000b9500d01c40f50340803d0a1100502180c1c841e9020303518010010401d0124160440005200303c400703030000c0c1741d9588024a520a12900568005d00034a41b0510001c070036900f500c002801002c0d2540c1c1005c0f4000380e040480e4091141d900a0805040850181c03840451851070081864001c0c0c11030102d00541458002070203192031003201d0041d90001c15000740b00303013010300010b400b40010308450100c540d0340710002102111446040d0256220710004102d40e02c4035020000c0001c8051750000c40300c6040c4042c00704c2c040d0005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 980837895 1250 980836645 980836669
    0x3071d040b09161403040c23060316180e0601090e09030d0c0e1e10050408070e090f060106201b09092a151303111309030806091302 58
    0x543c881c154603c6410b01200d1501500810074070304840030041c070003001122944e80094805040760061111810912500c4030a003560b41c5540001c0f0400c0410720611b9164280603940c0230303d060880703907014001c042c102d0900441d4807010741c03500c0303500a1140942c1c0c884101001040501031046160501825080d200e2151a10351100d0f035965140f00419540295501081c6200040680d5010090f60310030b11109100713201a284150307113013001c450146010310b0584003690703c590020800303541420750f5007000320340250030107040d031080c0c8015080e40c40b030810089020344801d0340c0e15020011101014144e40e10450310003101da8010000558850a43d00c034000b01411085803a40d4030368583d00b40f01c40c00c003c1080d5160309816413a40b00f00040c0e00340e16012603400300e02611090182541420101014014206006e01c18040840c04101060410b0003120071440010100301205443c404054101e03040c42d18100c0224041c20104801ca103092564903521800200c506002e490b1550300140c91030103e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 980839145 1250 980837895 980837911
    0xd05060102033408190905030111161b061e0c050a0209070504050324061c1205190206070315080a1407150210470603071d040b09 57
    0x340c250240034840c001d50b00c90295800074a00c0e81c5d280c480c1d10300030080795181814080481c90310200001c00d030030705202d00c0103100308894006042c0b4541890040d0309419111060305d101000e1405141d032265001402ca004080d540c0b2403034001a510324801060302e03455035400f07040c000c0000800c408104081448074141e40d040343e21211301d83d039480054540e030207180c010741d41620480301d09000c0a0885007075a00c5030000207021034019070718031040203003000407924005441c2c401c140304040054015155090410150b0521b03030306007018002005009000440600010b0b0701403401d21102c3d503050b00c101900320100c0c248940303200b428114410381d1b03110b030b07070f180141007100c40700c0703076041d55102805180b001d0f040242c0e82c40b500b241079060095468903090100010180390601c0c103800d5000c64442c0007000c0b158102801098500e00b050a50685104d01031100d8030000711012a02540c0c400f40114410103164407102a044044048944150009a40e09000354039140b90740321280d5505044036402064 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 980840395 1250 980839145 980839207
    0x10506070f1b091503031202090f0d0f0807060c2007290304050d082809140f033013030c1a250c11030712080d0506010203 54
    0x54210020302c5100b40d5004030503040c6030480c0c10903004524074000e03084a0081c2c3d074075211249040d604030124451446000e03440080d04010940d1424040401001280505d501e41e203203081c56141c102590348140c004036502e560b03d84194111540000344903503810029020f0200b5282c80000c1c05a1300c0c5118000c1c40c0c009400c00329000140d02d002c200c048032050030052026140c0c24549040741c0c0d15a043c00c016130104420b58001078402403d80100e80c07242c1403090303010320b039420581c440100a100000c41901e201008440620000d40200062503007184000700440d903e0785c005c5105010054900300c10b100c0381019081e10a08146041d80c0c0c9034000950307800050400006140613209031005d0b00008203240003103074070702d04030010a40855105072000d1741c0c428544c400d1074245480b10109040c10318041801c100d401404a464103100c1e031b10300003001c0c048034880c2d5126a14031001e044c2c00b00e400c40e84901c000030003840204440c001c607600305100b030006604050b66038204d40360005075401b000300f000344 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 980841645 1250 980840395 980840423
    0x70509060f030f030d0605060a0518010309050a120815030a0b0604090b0f0604061202011205060f060c06220302101a040204030f020111210318011401030506010506070f 74
    0x580c0711000040044024101c52240d24001001600c03034200318180400c40c2d240c80c40c00180341c100b6200300c07041202a0340d107141c905101000f18240302d22058035030604040e62030200d080042d004010403659180540c0840c0c10300c88485100078230301d11001b04001102102c214010140d83c134000754111545900100f0301803d683c0d84004100106400a4060001c00c410410b100214001242042c02014181d8040c0031082d101c070200fa22001f0350500080c000742c4040d40b51914690250b000c2c0c0d0704001300524a600e17410b2441d0001b00690044c0034119100c4c0c0001c0309102d8002034914030325902100d4200302c00c00045550b200070b07445964810003100c039180c840382c114103504210700300c1d0740d82c000c0d00401c01c548403a100e00708401101005c00040f804600700726041007100d000040e0b140584c020b2b00d030b85a020b1359009400c088190b0030142540c00c00315203040034401580401c0c0515510104c111020400d0340d0b143d410001d1a0003010390266020b403004110940100e007548403183c0c215504241e8407100d100f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 980842895 1250 980841645 980841649
    0x6090b120417030f0414012904060806091b090129041a0403022e1803020a031a07081306021614010606030c050c15060a090212010e01120507050906 65
    0x26600c95121102c00c003001042041c600aa04076850245014100c03d0401820000307145080b250680ca949240b5042c1c0851102c0d08038090509900107a0080c03c0401c2c025901c0100920f08002612443d90981041080408404440c2c4034411030040c100c07541c10655140900010318070000100c0e0380e13941c000300000349609003c410102c8000300005120f1103405456011601182e40090000720300c46d18240b68031220200b5166404811442802650340e8800280d600590700c120102d900e004500c0d019101c0000540d86160340c42c0021070041c1100000b0a40e124464144803c0050090341404004001d000380c2e940201200c1c001164082c2e0010390702d1044405250703041800040080a54607a0034440309448019000841102c900b501d00f03120102c00c3c1202984c080c0140c210180c120352049010fa15404038010009420003000f40c142400300b83c4035041ca81c141d0707200366050b030041480700340100103c1400d100103a0043c12b40075230b44119a40d003590750503214042c0c0c0c86030500c2070000c01c022030065 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 980844145 1250 980842895 980842913
    0x3020a2c04091e05010204031202031e0c0a0b100312140307081302040c0c020102070918120314090f06011a030f0a0e0a03030e010c05070c1505070206070302100606090b1204 76
    0x1124410f141012212458405d001c0d42c403901013200c1001100d000c01c200140000b0540d41c4d0015001401c4004044012000d0488e410000c482811440303000b00325004a211314151500410022141c44140d5095040040c0071429450541c81007000c1515010303046000301055a401c5545c924008e0200d45450340441d0002040c5403010f544980f4011044140913000307401032045078400e80030b440c143d41e582c850340c400f11441512140e00038819041d0741c0700001e29040304040411018100041c4600302c050045039015030495503440c07030380c0c00440d242124140030070000b401410b039a40800d0b81074030b42c1e9010000c00d01001c2c040514180500740840c3c2107003000c1d00301502400250080300c0e140c00450400034050107c03003003580b9881d40780c20890691140305a00311804a0b80107001c2c0c0a525151100b01390300070761880312043c10040c00740001c000581d1000300605080d0300a50050002842030050801202c082d544107034140900d06034200801fa840c102600d4085a404c03004940780c1d41d4500b492008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 980845395 1250 980844145 980844173
    0x8030a03090201020705100c110a08070513060905070203070c210618020618040615080705160b07050403031d01020d2312100e040b0412020c030d03020a2c0409 70
    0x1102c500410b80741f003c40e0784410342041160143c855040d00941c0307902404241c1c07015010b04c030b14070f400c43c2800b8086401d181c0b542d03a1080514840018009030b072a018101250405d540a80041e000000c0d017405022840040101800c800c0b8070100e8a0a540c1c048625100780f2150001c02c1c554507004080e01204003a0642e944042c1c015010aa480d85410b1001e014101c40b0520648034518002c8045040500b28840345520b034059220b11086032a0f0300425a0030f074012048208882560004420005200d028100c1c01001140c443c55143c0782180b0300a0301c85100020710420006403010355405c26a40019601196502ca051110056824143e003401d6410b030810621340a050001d400001983c820f003040c0c2c4200b0700654607902d0f841d241e0b81108100d040a80c0d01602c1906031001082c00310314017103c0c800712040640122161162a0001711741480d030610070400100c0d6004c0f030240210703904200d48a03800754504403442c6503050a0f10300c2e00c103080003600c149070085544a800000300a404001198 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 980846645 1250 980845395 980845399
    0x20405100f0201150f0602190209041b0308161109040c030b0a1104081c050403031403071e0905030d0906210e0a05071409010b19140d0504140708030a03090201020705 73
    0x35a11800c01700c209a005104450062052040340c0220b07407101e1601c403a450307500410705034040e2075588881c200e100c04846505000d800401e4000009402600100154002c2a080c05417900b124144068220160020305001d8030051b4100400901c66050301c4054030350100c3c24600c291210b0004000500c400313131809a00080006001c2542c090019900d5040c0c0c4401c01c58981111a4200c229424007441c070008020911084042c04401c050101540d4045240e1820303205810440c20b020191055620301500820584031007031241d8141440080381c003c4490801d02c8800b490a01c1c0200300c022a6502c4840c500d4a01103290190b180640129100500340c00899400c0704050400c55140c0c40c840c400c1c0031030301c3d6420074120b103181800c580a504a0344041e050504003118201803d0405a925060f8010000001747d0606024071310400340080201c0010300040514080c6071014100c4205032040174030754081a0f041140c00c500108030f6040e4581803070081850080b92006078580311560304559 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 980847895 1250 980846645 980846681
    0x6100e090d1202130b0d0e0309100c02010c02040f020903062239080d030507090504020706090c0b0405041a030703030f0c29070c0203030307051602120619020405100f0201 75
    0x20b0b0001d0080c02400d092000c1c440d080001f003240c0c0c07144039900d00c154803100350050040005d08040c0d40c0180410000ea81c0181011141030200ba03000030220340c51a01802c4c4403580c00700d20511641420010190702484400c0180d1424900d140a8000c03180d00c0c010003006034000403011140b181c2d00c0300b0502010004080004c644e90002031004c0b0302c0da042402224424495002c88003a80781c40385c0917183c0940c1440d00d400074014200700910010350310188056641d651140e02e9240001d07204c0703600780024420031144907151420b041c10081a94000501c600140302c00301c0700c1010507503002c501e0700c044a034141000007107158001c0080d50300c02108130000c0e000005880d04650103c40601060182c02d01160840d00d4035a1900740c1034940c14100d4002a401d5807040c00041c0406000700300800c12015100944d800461040c1c0c0001c900842c40102403020f40c2291040c04014441d000740e04200011400003981050f040001103807030360380c07140032100400035800026034499001794003220124240c00f0320a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 980849145 1250 980847895 980847899
    0x204090b07081603050601051603270504060f050f09130f03030207170a0f0516080409390c170d1506031e021e03010806100e090d120213 60
    0x2401c401e60407290074503010444840441298441e204086c4184016112281071441080d01c1040703039120090110140302c0341c40d4410300f07000304955020320307800c1102401440302401d240600c000c1d83d140780d001001c4000b0303078141440a80e4030002e14480c2078500b030b44c0360035250b529010400800c80142002400802420b528135040c1039040d0000e00d9098002d41c603000a020300c0d00440c0e43c1078410103e5607000030381d104c1140c1c11110b101d0070040c410340610540c4200780c2c000644400e00243e00641c0034130721031035680401c0100440b091120f0141c00122a82d000c050103104444c40c00e4942c1c110030b41078100700c2c41280c0302c2d04110240224041c00a4015075180d151100e00348030a000740000c0c03416100300e5104400004c1c4403842805001d00c82141d040029840a20070410400a03402254806002c620510b1803540c1202c0301380c002e14000c0007a500140f126044c00c49074078518071996044007041e00e9141c4208611031000080400300d626451400b440741c030110045100080c0102005005400301cbe0382c3e00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 980850395 1250 980849145 980849147
    0x106230604150305090c15030f040c15020303180c100f090b0409050405150903040e04020a0314031b120a0518090c041e08151803030a0911100909090204090b07 70
    0x410311950116013180c1d5030b60303505401c0000f204044030b40084086d50420009e84441c50002c2640d401c2403150016550300c9440e8a40e43c1c1440300320a2848006a10120400c002c0c0e03082041007012151800300507250008d9158049403548400755260410300003024680e5401c0c902c06d420520043c181c0400e80c98030fa645600b90b5030050503042e60281c6051142c2c400522402204101c59801a01114000d40c41c01b4500710380e055821000400c142d900843d12000080840d900c2407050010350a0305028558070790071100310140710600b010041c2070365032010074412203102d074200484100310414100030b601c03003c411a0501854420203011a044100031062002c200f4800e0094400c0d00d0304280700100f000100d00750a02e10840e0352040b100c86901c0044000b5180505c1c84000303070082075403201045007000b4035512900c1c550040da070401d003040d40c664030501840190040821214811519441c00d40b2014100a0002030309025000d0b101d41e1714816403003190344903803111020643c416070200042c03030080c01c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 980851645 1250 980850395 980850401
    0x605193311010b0a180f0908181c0f0b090c0a0b0405041103102c1e0601020102120a1116080304061805070b03070c050115031401062306041503 63
    0x690804039820702e61007a01d0343c9840381a601c00e81703000e0345410400402c035410717807409018002d00500c803ea540301c0d000c00100392008010840490340c0400500d611011009100300a54907a00d560051003441d02c2803000900540c60098100b6000f284024440d00d0303200006081803420856903a00880001d800201d40e01c00c40050400c850f0308a40400026558a00d0b051251004a80340028801140d0050150011145c0290064500c10080300003024207a02c0c5d14412100c160340c2d01c10205141e40c1140482141c00c40002c0d4402001e1009500340944c2d417200c42102c3c4c0000d40b1081d003d54aa2100320700428401c0269000e08081d11740714511217005043c060304a500036641603802c1d41c10154a01c80c03480d01602d880b500c0c280d20030300030074034680340ca020b00b5800c1c1c00251031101008401103200010510234000c00410042d0300141d16480740c55413030090107038091101100a16410403400b040b0034140c03241242d4942c500d0811200241701400d0000d82a44140e400040a1010904030008002e034558 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 980852895 1250 980851645 980851667
    0x70c38010609060504050f04020a090315090c060f170601050d0906050603060603070509010902131a0a0f0e10081f1511010b130207050f0118050106051933 68
    0x34507062095500d810f42194948580c0c000c00e6080b0f080e1183c3c2801c41d08265004104c41c40b000d141a0000301d4483e650507000c2003202c42c1006156440c0e83ca807505001c40c4460120080c80d0390300b400580018901c80141001414200846008020380d000803443c0c1d001c0c0b400c4800a074503480080283c04800c1c0781443c0140416246039000b8450080020114280020740c0c03010f0322002484c6000c01d0f86030203640c001079409121070030a102c00d046c0380000c3d0a50100301061204600c2a01c40d134454a074518020406e843c044d10b1202040300c0580c1d07001e45c0d602c91340d9100c04803c0c45854203810595a085242c011026048020f50390b0002c100000100140740c00c1c580c58543c5203a64685140b5445889581c0c01d940301d6101d1103501007030f9801c502d0550305591b402448594480c0007901c0c0c0f5800c03107100d80790840e1094a240c02c610010380031180c003008400e1040e10040c1034100c0c0c0b0f04c8003485100101c02069a50b5000307800c04c6d140d010015040c1030744045070302403805500248000741080310b131300005c15001d081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 980854145 1250 980852895 980852897
    0x3306040915060e1b040e0a02040305010606030509060f1b0a03020c0307030f0f02060c04060f0c06050906060109050a180b0a030f080703030c050c120a090902040f0807080303070c380106 81
    0x50012503044c0240000c0c410074004280406821300d42000610f280c041c01c080c018180c9180d00300000130000e03a0a01440c40101140d031000101d0785001030142e410800010b18244140c00c01000b00a8104010340c110108590f040690783d854114050083e0300900c1030082102c8280f0001c1000c1080580c0a900043c0b6804140c5e5149403845050609030b03917440c1d082d01c42e030801600921085c481d051041e051a140d0805602c1c04012080864542000b10b44040d280c2058903008841004110750b00010380d00002e210980e40722205600d04041010560800c05018000f036860b500184c42c50340c0d961f400d94019542155160342403c055141541d841c0c2d0102c0c40803000701c0c1c185440b120b0028014001c2e5000700605001401c00100c0307002e20a1105d071320807031540d400d0016410003c6548195440500050911820030030521418003481074a0a1036940c007d0780e1a0384204104500103a1010003110b8a81e44040400402c14103103202000440082c20030410940240710410303864100d00801a04840031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 980855395 1250 980854145 980854169
    0xc15060b03040602191b020d15051e060613030609030c02090a0207030810050d1202011514040b03070f060503060604030b1314010b0f0d05210a02330604091506 70
    0xa6500246d840309035074085080340c0d003c05c42d451405400d007060042d181c40e100354155446070003003000c207404480041d10000e80ca030450401044114911044003a08540221046403d1001a940c1c04021274600d02004000c01d4a500c2d400301011302034011281d030103038014201c908500d070810860b002500069015800034826102180c8a4801c1c40e90800030f030b402c060314403009100340761650900c130741c00c0d400003c0c111740d0303208040c510f012440b0140b5800340c68244403a4641400030420002581c3c071038201c883c40f0340c06c018020804124203a441c0c40c2110140c0c10714940725030341c80c400211780d8019580040c04405841041100c00f079100c54421072003a00c5403110403a042c1c0e401d96400d08803640d10f07a01c90381050480c005200180740c1120b15000161240003100c0398905e15520710003404181148601c4040d40c00b107198038000d80c05104000c114100383d5520307002060940c10326a22401119001c0b07004e04c1020b404190151110f8001402c1240c11002c2c0f51000d44c50001c09000402e0389215466401c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 980856645 1250 980855395 980855437
    0x50402160b0615030a0209031203010801060f091505130608031317010905211b0d0f021501060f1205040c1401212a020a0303050609070c15060b03040602 67
    0x10f070484110002e4800703804820304540c1c8904a442c0254024500c0c26411300c18100d000b002e0030841300045000e020004004540e19142001c21080f100b515040114041c0c1000742403034012441e00d024008862003102d150840b110010050f10041030306400c096a40d0000060054002440c1100c3c1d000300d81d851791205105c0c0d440c54040074226101200002c0040d04420204016207403800710707114200e040035402c1da18001b404803200c001c0b003d502c1c004125913000740e0304446a4a42080307020142c4045400586031203e080307071040070304100500900081c8143c2c514680d5441d0301c42c0540202010842c50200035508180c14000407480581c407585008071801000010310354842c0803508080120034002c00c0d003e44141003000090122144d8141d42e904a02c0f83c000d1070461032108143d0a612150050900312a0a040040607500c008207070b503006007030400074062240e51180000e2156500100c144650580d100c48010140c0003c3d48403c40c0304d4800310070f020078026168000e01c501a0042c001e10b450007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 980857895 1250 980856645 980856649
    0x201140d0e01140c0a0801050103020a141303030e181f090e0f010c180b0306030a08030a020c061b0703080916140a06080c03150607171305010e1513050402160b06 71
    0x3100c5c1e40c039003000042d5001c004002c154026005420100c040782003440e06440361901008894120f024181d20640e07440c03030708009050701304e03e082c5100502034410342d090320000000c0710703003103040a0070300d40403854444544110342c040070500380c000c0c0811140520183c0503805040340d446002a580c004107501c0c055030389038540c1c000e04c61001851002c4c03107502d9607945000e0002010341c00c000d003460b070903010f21280d0400140103d03000318411942002d00607143c4070395012040c54100020404c9522041e1210b000300e00314049015642c94a0b81490050b42d10f5030ba02d003116040c03140586034082e2182c013203940840e0041c030002e4005d10313a00c0b00b600c0c9840c1450751400f044542e042c0a94150790020030401c0030030f00300280455042441c0c00081d20071791800d695580c4055520308207011707600003040007295840001c0c226203000350040c00309281058a00b422400042c007101010004040403620005000700c10001400d402002054020b10854a40581d9110710020103038050b012140030140307100050540c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 980859145 1250 980857895 980857897
    0x1d0903032e1e15120e010e030f040e0c090d0206071a13171305010c080715060314070b03072709050403080903040b040501051c09061b0507020d0201140d0e01140c 71
    0x3c282581c81103090040400b280000344103003200c0e001c055480e40c284541040003003000304502c40c04070301310380d90f181c0c601801c1100140010300700019079482045071006503a50584001c6902d60116409680d808092078042680c2c3e000c5021600314041b8030301001582c2140e001e407194554010340101015880740940c0c00118410b5080d801d006519071038061090354499152030050610401807140307024000c0d1681c2c2e8143e22841c8041c40000d0f15014140200400281911507503c61000184501410b00c1e5009a8600009003840300300300750071402c40d80b40d020616140c40e0703591900f15410301c1aa1140c807400083c0500321802d43c086001c22020500d0040e000080790701302e0300040900750410b41032100464084c4d21103481001c41e00140002c0390791942c81440740840103440740400284042100e100211090086415642848410301c640400b580700c00301c0c005800b96091a1984082100440d010041d0046050000303c152402c24a01340300101507000102c00e22007011030b540c031652044100d40c15 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 980860395 1250 980859145 980859179
    0x60b120106050a1a121317030910020f070204051e130b06060f1b1f02070320031b010b0307050f13050a0b060c03041d0903032e1e 57
    0x104420140c204032445a0406404c500c200c010803c901e02244410704800240c3d09031003001c0c5907407040302a04200107006001170800c000c0707808450308629250b1180b80d11a0301600c042455241c0000342d81c4c08a115000c11107507010380c0240104094107101d8044002c1c08400700c0c910421a045c0004180e0314880204c03001841a48910244400c0d074448051210a8000024a038108003040c0b01607014091141d10204403020400c00920b121980d4005241c0712451510604200d140b04001210100e0751040c41902008c0d84007002d200010f400f00c40140c6984a0740e0440e0480c0700c0010b031402c038580410b412500c00300200b01e0031a040f00e91114200060001311001e842d40c400540814100d442d14560000d551003c3c0f44540044c5a074019400304a0503071117618842482c1d040010b05001c0760b2228801030664112810b6110440e252245c40c90b5a21720001e00005105511036680030050140c0010720f240004a040c180ca440c240d6800031100c012044007010400c641104001046030015003006540c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 980861645 1250 980860395 980860399
    0x6090b0319031107151116060203040501030b0a031a010e0105010806130504020a03171e0703200102160c05120129010e04050106080f090705010c2904060b12010605 72
    0x1d44107032035582c195080018040e10f0400c601801e2400515083e4003018140c4201e01c50b26500054142850094104901da041405405c00750b00b034180b103042d90000a5a080c0d075000c0c00d001540c00f14100016030302028542c001402410800258000c9a1049103124101c800c0580645036903600d850041d5940041103c0c800c4e0041040c0c5071552a01d500754003c030b82c010b80054002c040c131544a8440c01140380940c8003491802c10006038000607150154410f800809103107280c1810600c207540c008104001822050845840c042542d40000c3c10030b41c111b8200e50700307058620450891900c3e10094011051180310310504549080c45c81842043c011180400d00b03401c43d804440c2031403011882500c03e42400e00e410440c2d81401004151a1807051a01800094981400e10320346841007040c0e0450040c4001c000d40c00c40401001566000440d001c0c0386a17211100c81c459000040e0082d5500b2580101c01c0041d0165900780002d2203403543c031580e076810081d50110980340e409415a42600c01320301c039150b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 980862895 1250 980861645 980861683
    0x602030408030a200d030e0708010e03040b2818091a060d242402060118090f0b06040b043614010b01080a09120c080d06060306090b03 59
    0x8003001d116120001c004c40704510301d00d40b010400c41d038881c0742c1050004007002003039984880e280a5413081111400820a0364001c2c071003012880324264a0340280d103e00c035625070000c14269203c0301f44041071400b41c1d42c0d1071100482d100d5844002801d80c04c00a1007d1205111104045a480000c0c0202d4501b0311646804c0c1e00c0142ea0b10003403004036402152030090140c0c3c1da0341025100c4595030828a240c07282c105030079200c42d0904000c0010702a0f04090040701c1e52070103081c140c8107900840c10504681e007047c00b01031025040001384000d003414850007000b20007904020b030b040007034090001d40590000e48040002108041c00e0104650303013200114602605c4a80e840a0000310101d200c80b4180d0301c400011130104c4a42d00c0300030111060081c0da0035039458208141c240d5074000f181c2da41c0007401c80030074044044251a012800e644125400c0b007042a803004031400e100c450004c0b5801d414100908118481d48c8203c001c00070105406001078190030244450300d031385400120302d0700e01c00070310b0310070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 980864145 1250 980862895 980862907
    0x20a1703190e0904110f03011a130519090314030f0703050603071404050a0f1e200702040c02150717100501090612111801030b12071a120916060203040803 68
    0x10443c012120011b5004030340d12000d0340303d03071000c1c080c54101c100a0b90849101048810412900c440c1c43c02012801c24038000401c20f5030289040310349143c80f198500060303810450304040b5611111808030360b0707a44600106001c2040924112184030b200c66640801440d150344013016110800d511951021001641b05041586419031089411401070240000c3c404aa000203d040e05c10728010804e15458452824074003041502034071498000b0302400c84220301c000712a100881c05451000b0303000310780d1180760300c0700180200803c00d107c2000051400c9140b801d801c00130f08902d0401843d0001a600d1004100c05a00c003860003415644141c41d02100a03007060743c11503809911503048240140c0b501c400c010390402800040183d4030070302002846d00c561540014054a40b000e1000f405070500f401c06000010021502b035066134280e0454004000c00080c10300200d01541c80f00c6c98466000800f4020000c900003a41003202158258900c01981e4440701a6202e009600c82c09245030410010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 980865395 1250 980864145 980864153
    0x40c0f0e0111070e07030c0206070c170d090f080301080c1203120910060608160804110f0409051005010510050304030813020a0e04050d080a0c0c0807020a1703190e0904 74
    0x500d88075440c0b00421104410364800c55809040340039240c2601080e80d54044441e184d505100c42c030303403081d003e080c509072111683d0f0710780d00035040c40d00890041210100e1034441e104481d4004001c0250460203131303820002d00c0d00708110564400e203d404294400c2c440d009209042c05119850242404006181400f4a00b0f02e602800c8100a090f241503004005030070440d4095442110302070131680c2d8502200b80341c4041c00300707405035000710704c10140503402d010040003400d4241614000c4c80180e803250b64030074400b008213015203c0003900030f10384e01423451300c86240390300d075480743d030482e0800c551819002d080201c0540342444155005400a1140c80000300c1c60030480f900c81c2c2c21184041d080050081d030b00c0800c80f180820a48048a4641210315054844c80d442501e9039000208404100304500030000041e01c0854081c074001d1141001060090542d07807001a580d00038040c514070308000200c040d131029182d504c000802c03526420040420901c9611030350b020910500007420040541c1c4075622 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 980866645 1250 980865395 980865407
    0xf0d02010c02030f0f0105010e09032212051b0103021201211203020c07050a0501090e151807030e1b0d0f08040902070c0509040c061107050d11040c0f0e01 68
    0x505a040c044400d600d10010b8504120540d070500e003a030081c004280700645181d09541d41a4008280802540107000b071a400c0801110710a0100300c109207007a0059554565140725154003110000c6110002ca00500c01c02003419041c4001d102803200c400c8811000560072801408800d0703040715440401413110100c002c0c1d01d06410700700c94800002140181c0e543c0314452030002030320302c002034010448480c400000c00003180a0581121a01611810b10300002e202040900c2000002c2e9114000b00741c004e805002c2e00d521044d4003405280c0c2c0b244114140031540001501d0f405c00292a00000240700000403424000c040704c120500b0b8490306081d0208900041140c901303489000070600700780d0000d0f95410041c4010100c001001d85c80d400d050501c41b42000c1507900c010301684040c0200400500410001000e0318001d0822440c809040c64007586480c945802068000000c14030440500220030034a40c0b20b064100c07030610004002902c115000d80450303000c403000c280141141c40c263340c0103907 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 980867895 1250 980866645 980866669
    0x11010f050411101715100207032d0609120906050f04090905030d050f010f0801051902210c0714010902030a0210020a1b09060803030c0306040f0b0d03080a05070e0f 72
    0x2c41d2030304c80720103440d64510300d072102554004542c0784c0c000381c01112824011854030341400360340040c00380b4920f1500d95030f40316400d900480e1080031505260285000240b00c07a1004a9003000e1700304020303070040c50842000581101c014022801a5100181d142c1c40303202201c0c5064130340b91091741041e01e0680c88001405c14030500321014007003800320502d10b000300e11807940300700340e10b030324201d9654940001c0500107120783c3c1101c10682d0400041040840b0351444051140d0300c000001a0f40301e40e000b5440460008007410080262030740e07024040014140e00c0540790f402c0c000d64032004038000c02c005113400ca854080000b50990420706081c809450081c003080140102801a10319980c5c082d41e8094024442c5000c200c064114010103001d059200c0c401d038000760400c100214a103040c0419441f12501004100d944569211b0500108611103500543c1c2a10405094603061198614000c0c05030725048451402e07051816000a00c070a2040072450104040500300d410716480388028000200d8940c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 980869145 1250 980867895 980867897
    0x3070515160c081c0e0a020103050a0e0a02300309090a020a0804030e0402040906170c0604120b070203120c070213051620030705100c0e010503010510090b03010611010f05041110 78
    0x818204940705020b00440030700d08425005810b40c0601b44c0300140032501c02038801d013441c926010144003a039000080d40c000103601141c3c449003811200741d0080b03101075524840748040c10320340da851980b19400405031000040482e803030902641c0d2642408100d0080944240002c1d80c0303038020038046400b90018a0800001800241c07801d07450f100000c0643d40070f40c9c45100d08202a0044100f0f001e8180655505418111160391401e40362070401403400310010b4001d80142030400c040b0301000d0003001168404000c80c0a10301c00392410034000c00003a000b5440903806101c0a02d65404510b0051003990b129502200c00e507004890041000c442e0f03d01841d054030024000301101707824a010400140c90954490301c014900c440e0b810404106540451400d5400d0200603400c0a265a800a0540381901c4087d40e0500340034058000c01c4519000c0d81c1e011a6a084000001040207540301d1400101254030320000e000c0c40b001c80241c0790488400b1640900032000343c2d0080c0200e45001e08501d40c8107141 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 980870395 1250 980869145 980869177
    0x70801061e1d040c0210060509010305060103080a18030f1208010b0a031808041202120c0f06091c0803010807170709090203032710020f0c2103070515160c08 69
    0x81d040200f0304546200c00003030302591001c8136121103a1003074040c00b805440140c440072055403442c1c1d034056a489040c0001401c026005c0b0f81c404550384121100e90b150f8118031222103107141c4d241441c6001914200c0e003541c0ca00e40d003100461249004452240c100d840c080c04003454001200012001441000138180818840c400807402040a02020f040a8002034000c03070801041d0344100050880c030a9072441564002000100cbc15541d2001c14031b00b821010303101c155852501e100040e5200c00d01c603200c0b034051001e07a0062004d00049401035811b96000c5400c03140c1c41d5440c0d803c40d50003c0c150403224000359008000c203018050141e003060500901c040c007142d0038410207030110400522580c41c810b0341003c0c040401c1c6013510301001382e081c2e6004a40041d080402e0020149034840301401c1c411070060034240b0928198482d101e2010568416400c152916800c65140094913198108a911440180c96000c2810305084684003075290307403d0344039841d12400a83c3c1e440503d4000c10609614000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 980871645 1250 980870395 980870447
    0x14010e04050c0a1b120f09210302061f1814090a110108070e040515040c020a060501060e010824060d020a0f020601050d060f09080c06070801061e 64
    0x2214000c96000c2c80ca8a82c5903038894000340350041c0303002c00310024941d02070780441400011900c0c08008540c6201c9a03c0d15030742403105035100f55401c0c00c040c2d200d02802080352248260600800910300306143c420b50070303920192241d0f400c0c445c5001110700c4090f03500e44240010071000044044911164080d000e020442d140781c40b0344459007240803030f1304c01501e8100344a1541008070303814401094181c01d080c41c000354200b0b840000c0c180a41a000c96004c0c03540c40d0042602c1001d410740380360461000400510480c0341001d1700135112122020110340e42400c0400109649005820b180301020040c0e484001c00e40d40d10408415510843d0595403002c1c2c2d580001c40401d480c0c820050882c401c806001581d03860f03024400519000003c2209400c64026000610842e0358194040b220b82c0d4126001143c0b0001c01e08411009007240c40c4003c4c205040043c60450015012581a1003420103403550300f6540e0761103e0607200c5140c00840800014054411000e0550243d110709a13130140c1c078924568000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 980872895 1250 980871645 980871649
    0x109050108060a17100e06180a11060703030905030d0f0f050103030f0c0305044407051201061503050108190203100f090f060e07080f07090e12072006070c14010e 71
    0x510a0103420846d8110300100140d1038462a11110740c0d51230314009000720110358036039400014a19022500c5074000140312003c2c54401e401061031030340c000c401d5070b50342d07912100d81000815002c20f0583c05141880d400c00e91060442c4035640c1282c2c1c241d02c0f24070303032120030100885803003c0c070b41002c40c24800c3c1480085101e2680713049008083e80a1103d5005004103408510b001074440030500c06043e00481d02c1c0c0b01500000b0a5980884d082543e1102c1e0141c001010385024212030740001c40d104d2200e2008040743c0750726800190480d1404000c0d944151801c4042c0030b194082e60340017070341540c043e8014601c0c3e4803a940c414400400d440d480058a00240d648151800e0103940c1f0642d512034803081c12000420050207868018198440148406413000501c55218910307072250230303501580c2e810b04404000e024044a0b1001110080c80741d641c1e86a45085040182420441d041030b00920303200585909202c000c4a4010340c000703403082a80e0749082c01c40440d000c4c80648090401014100f0030351742e6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 980874145 1250 980872895 980872901
    0x120509150408063310050f12010911030c041a0903010e0109060b01110715171303030614011b0203100c030207021026060418030e0109050108060a1710 66
    0x40c1003440050141c50400003080c500b01030844c3c04106004c0e015040c05000a001040c840d005000d0a4900305404200100207907041d01600440e412800c01c009844000015132615040c16a04420340408c02841c20004e19507241c04111000140c2050411003842807290074103152840b191814103403441c1407888000f1900355100d01d2a240c41c0d41e91105c50032010010a0300a5041c0300000707203022061580c9195000ea580c082d24407811810300c4010f800504124820710203029100001c4404810500340727507017810f01c90648040c040e00001d28043d004a80c0c0002422103801040050b914002000c80425a4842004201500300d90600c90544492240020780c0242000403c0c5500c005807200c0d006d0040c00b440a1242d810f0008210344209440e900c158246018201c0d08100f40001c0c14550320310000c200200385140c83c40c01c841c5103190344130040650103841c80507003960030798448800559420054070130304020b50707150740d004101080130311000000303200441c250a000f00480f440c1000e181c1c03a110403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 980875395 1250 980874145 980874149
    0x1d2d150f0a0618090213020a2d0f0309020f040e1c03020a0518011701090b09010506070503160c0b0d020c0f0115090218150a0f08090d0e210606100302071205091504 72
    0x104541c410600f001c10441c9e500116180c5030322100048444040000801e681d1811200c003080c10b64a044000954652400e480700001000d0001c002c8403000c918040d585500f09026222814000d4088484292082c025686c4090f00303510f810f070030400d511803980c840548500d040d0f81003103c9414280c01c4428065075841c028100c06000065800c00c9505100071064142c200c20f00404042103000d001440c00011144070820002059281c4075044c41c0010304441c2960200c0951140400e0148000b01d0b1a4001c0030326601c2d0404540e01540084030050036903804440d8180c18000849d0104211405a00202411140d400119095007500c40c002107110b121046086200d40340861020174281d0003101c11851103203d030400198902c7c10340c181a680d0b080c1078040c201000700800110605445100302161140c038071946c5035010000c2101c9156035603408480300b522039218141c42c1c00ca8180070307108a85a007a0849000728a0000d500400d8500d5402074207981d400c009120343d81303d0032110320405000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 980876645 1250 980875395 980875397
    0x5030d1d0d14160504060b12040305360f041419020906070501090303050903120a151203030507181a031f090608011d2d150f0a0618090213020a 63
    0x14485042409020888940c0d07001002c7c000310403c0200c10383d1420010b01039009925103001503884100c0a421000d021085141c00392080034010512640006817030003805120007954140790a40c803031001c10003510b403180003109000d00c44001160301030303824914484000022490252421842002142060344403050550703c1d659100c91420030568180501500640404002c40c186902844140141c68001e41551070722a07680c0c03517009144000d03404030700c024200e003924030b102d0031281d0401401900c411540c480c0010207802c1a00014041c041c4200c040d504090400e0300f0458501181944136800606100c0301d003840000818244800f04140301c01038a02220080780c00c514042c0700d0b80c02d5460071008004aa010041102181600050000c0001c950140c140a0b078280e9040c4501101803462810f0006004511901c0010360108400d00e01070b48c004800242c0380c0e965010710030100d411341e001c0c0310300d10403104495048400454000010050000300f01d01105a6101d8040d0200c0c3c0c00011410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 980877895 1250 980876645 980876683
    0x30a24050606180a051e10091526010605030a11030702030d050a0605150a02210702040506040f1a0f0906011b1a0106080106020d0212091c0c0f05030d1d0d14 69
    0x22416080100c0413814240488c1881602141089506171034045080c0071070381003000540300008210040480524502c10310b581114681d41c61740030050095100b180e1083c1d9881c10300000030400d00b55441100c2c8581c4c502e43c050750405090300c4c55403010b400003802d80d54800780c80d00000b19042d0ba0351110f00d052030b881c04201c6551040500f00103800c1050050810b181c100d24410b201c50b55a020104641c0000d90484000980c0d1340e40000180c01015907010070107589150130b0118500000e00510407003810021110b28042a10703543c20007200c2c0c501102c00c01d0010307114410000020030030b00e903000141440381e50503104010f0030220012407001e00341d0089c000107081e000100015501406400c001c60141e2024140c2185840e00c8402c882c41401c101c24001c1101c0c0402180401c8a254958406548078015005c420359400c121030100107039010f1f65100c0c1c010703814007185450003207a0755960300c0584074020a03044940400c201061511003401d0300e10b2965001d2520703100f0701c103015440140004124107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 980879145 1250 980877895 980877949
    0xe150c0a0f08010815090f070924120b040302120a080a0e0606030703120309080c030d06061706041e020703080117210c0c030a24050606180a05 63
    0x3806038440c00c0c15001407095060050190300c5002c05c06084e50000d45407086551b4541004981c503103c11031060013018003c03208080f5610140340c0005c01c01c40070814010284802c000d03203515060b0094070613903d8145000600b03030005210a01040ea00c80d000b070044d0390601c0b0745802c100c7c02c00d078024103440000500e54802c0089448451199844260702c080060065190141c04030303581d01002e020103884040c1e801208851b06100c1e411220000d5800f4015984440c040c2044583d0780c4c11a080751550141401c03008100c035841680d2547d40c0114103500703440300b41c45d028140001171519092282d81d506411030508080542400140380c203034400d64a0b03103007039890f000e04040d120341004010301d03d5401070300c80102c2805190003d02c0300c0c218007200c3e4550340c2da20360180301e14203042c911f9044e8060044240342400e02c401d140d11421620f40350403107100c080004050040448604940650b0321000a00ca50f03030580c007001520042c03514025155929143d150000904019509031202405482040ba1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 980880395 1250 980879145 980879147
    0x105010b0f090d02030c061204060e0a0c030305031e130308150f041e06030803160302040312030513061a010311070b04030507150c09210201080105040e150c0a 70
    0x54600500000300c0160520800051a140500c00e00c20a03911500c0442da08800b955000e00c05440c3e8190000c2c14140c0d505016406031040c80300c00c0320140c41162405891007d00d62010031064070240d40302c855208074904658080d601604054074075003d0007400c3c1f104060300c184e81074005025110b02c00c000745440450f850002c1a41c800200041d500c64101000d00d0700d00d84501d0108a0040004c8802044000c48505d500040074600d54000e05694100000003003405104001503000341010748512039100b28400007501079100d02d00c0001c1210600307410312006540f0070b82c8a030f600700388030f4100700078106d410b41c440009441d10620003404009041c0001c080c25a0540315140031000c0221b0b10078100241a1282030006000600160511400050007810003501c2081c050380701e505403404209501001600030b041c00c24034090840001e002020034001141d10820144d0b540e0b6050391200c1c0168244024400545a40704480109208800640c4045040c4064180c8181c038010442030703d42c5403201c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 980881645 1250 980880395 980880401
    0x3040f0b12060a050114070807060f0615021603030509011e11011a06070609020d120e0f03030705100e1e010b04111e030414060f010305070b120114010c080307080901 73
    0xc081c0328401c0f40c101000640d80019010600801088a807601c40f06a410403680c0c1b4402e40c800100750519101d4002ca400801d42e10031802e031619801d2031810780c94400c0c8241d9840004600040c0d45035140c170380800000b4030410040c400703002c0624000f429409503807060384c55440f03449282c8001c030308502c0d8030b0448007100340300e40ca02d01c0d012864800342600564020641c10300c1005d80c080d1a0135100c50310503041d501c42d42c1a81c1000b0364403118902d070808190700020302010340c50741f0b80c40c03103170b600c0521844891800009a0301040d030800050300c11005140001e500901a608950b8104e015605540d90620182280c1d00c07080454500003060304440784040004031004008511401c0c081806244d200c2100500d140041e000034181040d0b480d00da90400030b047c0301d02d07010f10700c079107100d41020480424081d241042c104c0c1c0c400e00c02c40310160b0301d40b2106000c174050342002e4000010b500c00104000c04403414404076071581030410740c26003401901c0b480425030046890f400132480d048103100860000344 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 980882895 1250 980881645 980881651
    0x20105011404020f0d110403080408030901120b09072313050a06030c02061303030902040c02030c0f06091b122d030a0e09100929030105010303020309090903040f0b12 73
    0x120b00b145008110344000c20540142d4104410080d9910b0402400c10900411100590b40140380702d0703259075070380caa21503803580006035860010f509403019882d5607407140920004804018062043c40d501e045044803005071040080000201000c400c4940804100040050003100790303c040d036103412304091100300d945d194815800c01d880c02c1602c00c00e465021484a4101e94541c01c100001c032414141140904803401e80a94018607001c41c14020540010003842d10031100e80654401e14911000140c0342e0344111204481900501064542282035480c80040000700400079041e4103010141c141c80c1c0384400d69014811800031110303281e2301c0d0f00d41c1440c18103c88140700075860800d400e600100b240c60b01840203070190188101080c001200d45036410040c180c0d1100800941603610030340e504590700d0102c102d000da040308408184504040c0140c074140c80d00b5800851030714030000240003180700000c2224015010522001c54019140d00301140182a03540605850309120140c105c00182c010f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 980884145 1250 980882895 980882899
    0x9060503030a090315060513020904050f04020a091d03030f0702061f060806040207052a0904021e0303071a012c04020f0d0b040807170406020c1309080a0201050114 72
    0x6200c05003215a03c0039a901c2501d520101d00c02809803a100340b0303009012182c00c8141d0180c020340a0320910640c550240c0174040d4100c6041c085034599401c134002c50002564041d400035030000c01030043c0300c0250410280c49502c08040d196a07407216081d20b003940c0040c0d480b51140c0507400c0c24041c01990401c0b5441d0064403500d0080d011040d030504c0c104000300c562160000740600e11000400756651941684c60641d0408282c4c0c00001070303075010304c000c840c0103418585050f03c480190141c41c00e01544251107154043d2105c03d080c07031070381002c900007000c00d407010f40e0502c001c0200d04001a4001d24801601220300c0c0f584a2179411302d5802c00300e103440050007400c0c05002e060802000c00c0c1441400d0341044d01134503096851080900400d0300314000d050042c01c202d004005200030440c5840052215a00a0400740f80001d510008900284200d100d00c07001070b80302c04103003801ca180c001100102c00b4201c100000f038004003035448060342e070004201140035035507410041118245000c1a01480c600c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 980885395 1250 980884145 980884147
    0x330d0b06180925030f1202060c0a02060f0406061e060e0f01021b0102100e0718060e0f0603011413060608060603070b0f04050a0b07060e03040b030c0d060509070201060906050303 78
    0x1c41c400503a54450450b00454100700c0f0300c000c04103400710480030005140c00c400f1070320660f1041c1c1420550091a02e01d80b10040c0300e0940040c0460700100151040f01000c0d5001e000c1c80c1d15540c40c0c550340c0c00e4018005440c00703690340c500080c01d80f45078803007516003801403040c6031641d40c50100b01038054100350104901402c00e0907980d9102d40e0380030480000d6100c401d240300048401c070100403441c0110600b04030721800d18225664030901c0000421400700c1d0441c110031003000071110726804c00d9880c2c520410000401040104800a816821312980440007400010301c02c1d090112001004609803003280d4245020480041805158024040a0f00c07410000341850309184010030794907409407190610342c65012440700a9545400101c4c0d00411009080400158a40784005040d62200e40111507491070507402d500845c4000c81600e00315600f822425040d9664a000d401c21a803020b41c600303448030750700c8801040d145c0d6000070507409140c5035400090000c0c00c1005a81c111061908900e1203a0703c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 980886645 1250 980885395 980885401
    0x20a050d08162105090f06161e120609021b010e0706180302040501030c050922060b0415030b06030d020318010c0c0b0c24330d0b0618 59
    0x8542e40b07018010400d403410300d41d0450030202d00f6280f02c0e800c1c07800d90601400c0100340600b00c1000500040141610760680f03500e03864980300c0300421310344d207262500460118441044070084500003202a4021403e08015003034140c5803050807141907070010b01d880e641c081500743c00d08482e035a8440109000c1c1000300201c020f01031006940f0901840f031101017000351056811914103080c0c0241c011b60303000c1c0050190303584034a405101c68015025260280c4405800a030025030000c120341108117031403880c0001ca0580d901ca80703024050070480d00e6041074541e080807004403204a001030040d4011901c692007401c00804141c10610f11161030300840d40140402d8580c0c006841c00e80040c0d03842420084014021403500080d03445036641315203038101d4007058200200002007808004e108000107002c0640705040d045a005001c00e03106c040c00c0c80d8040742c82d1000000e803803040510503205110207682100750700c000101001542c400464018081d54144182400c2c001c01c0220b5030100340f8903000040c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 980887895 1250 980886645 980886661
    0x30d050c0c071e210201020105060d12080a02070b16030b0d150203040c12030206161b0611090607050f070807050d060b2403060114030702070303110c10020a050d08 72
    0x9150142501640c12403103042e100c42c0d461a00d6100802104084e071029a40d00f243c3c200403502d01e03040990141d42407000051003407818410408a0542c48000c079590300c0a249004c40360004000c180c001d50945c20000b0b000803c4c0142a0b552248207400d1600546650340b000040684908881007070048148442c3c1c00000380f0a01c0441c95802c540a0006869680724100024602c41d0b581c0185a00900703200004245540455001d21604903041412050624004219407041c10300c0110031454280e24010720000d02213400800031800020003450420914200084c0310798800c1d0003c48070f56004000b040d0000c902403000c2801041c104010703000092070000440c8140c149014028030b07180d542c041e4100d0307580e240c89884a032806000c1e40b50321a80b074901c0d1401c0711980301b60781940c0030407191b074001350b0415401130490f441510250301401099241d03981c01d032100d14061038440100e00805940c9103840d00d8082c0b40260305045540180110310003403c04505124401500c1c90801105108020f840 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 980889145 1250 980887895 980887903
    0x90614071707050d180605040b150a030309090c0201092406080615010f050c011107060e0f0d0c0c15090f0e1003030e0f090906071b0b0601080c070b0405030d050c0c 72
    0x6a00200004030305900c00112410042c0d2485170000c00a40c640700501c03080c030039a400d003681720f2801c6543d024004100030f800c0100480a03480010300084900100f4007551100b07422050881280340004110a205907a5040e030301280c110f10168071b520941181e0f810b00003030303000d9078000302002401b80c541c508101d08011602d00c0782d101444d06100300030400c0310070207104000311400c030003201008003c0e0034030808580000381d204000c00e4030454200b5041604510b008540307494182440002441c240480303120642d030500000300d092307130303a00b010880c00201e0b9001c1008000c080b079401d5491416803800c185001c3c1003549140c008642141d900c0c1c0070032548083c0080444c040c0c0e41c0500f8181271344040c820000d11401c41c01491240c00c24541e4041c000f072108005074580c01004075488922420b50103014100281c2a480d038090400c40407000403034a1540100e50701b641192604004500c0d10f80903403100300e025081590704640300d609c0000c106680c04180d124250300320307000300b8074903140100c01c285840e5a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 980890395 1250 980889145 980889157
    0xf0f150103120e01050403150c0e100815040b04090812011215021309020a0f022e090501090f0807050c0a0312030b010917010509010c0e030d0c0609061407170705 71
    0x28400d00f4251500140e0003103040da0010b650141e1549048101400b800c1e014064200c8808081a95540030309020b240400401a4003401c56540c0c1010b566101022220251255040c641240d80c0c0c80b104015500c840c011034820a0194542c1c1c0c0c0c2e1180310b0342451080762816030007483c2010200c00c8603030000b1944928001c081522520141c0c48206421091281140c00d9100482d41840001c03070b4107035190021f07644640704000f60203640c00d0361140c0006c8041004090031140501c40d0714a22350688413070710f034441082280a2400015080102d90b20390006420400d02901c0402000c03e0010400204200f800c9842d6030542d40301c0da0080c034544d40c00e41c0241c10078007070500b895250f084c03441c070f980d215800b03000c001c1107420242103500d6050540603000b81403e07038840c4c6003542440390f40206240a1b414025103c2300180041c400541d01442c112007409c040c0200301c941d0b603120b06808020a0503030154051070b581d600004a120705000340040c01d01110320b02100d00c0d000100c801c000c0390396004029030300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 980891645 1250 980890395 980890397
    0xf0c0c19110d210e0a1806080601060c12020d0e060304021219050610050a1502100203190b01081627060810090603021c140f0f15010312 60
    0xc0125491074a030041a03403851003a90007100ca2242001406010303107610582c0d115001c4031210300d55100404407070400c03151032599080705100c10104640220b0542214510390305000014005450300245424500282c1c841c500007002d004000781845032101c01d0240c0c00c03a20740002c040c10381c400324018201841c00c003d054400d0501000140035500c603414540740b48505074082e926401a4101da12031148040b0200355400e120b10b100284100c000008054107480f00181007011140c503201340c03403100d0440441490214045d002ca40f00c98140c0e80d00145005041e0415140c0304903403800080012195009120750400840b0001c0c401c001401c85416400e10b8200d1402000c0c48842c444454807050f0880c54070075005800c140009146680301502c0c0c0d0161000c0d020310801160f845000138103468440c04065440070883c160410220075140e009040030307210708079401500b01080e24050802000403540561600020004980b00409000084031482100001b04003541140c407580c10701c0c030320350040c18 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 980892895 1250 980891645 980891683
    0x180c010e0d050a06090605220f08071e03030f0c03151e05190501030b06042d3f08090607030c080c1609021804090c0513050f0c0c 57
    0x4401d109003072095030f1080e90070403014003017604149040002410116240b1b030242642414400c201712001c142010460342001011503818511340320505140c1c81040300700c6402203000c642c01c0d68401c40d640f013024424081d49001400031343d4024100b00362001083e24800305494144044510a10610000107070b40c0e01c408910030341e100c04204000d4100858104c154403441000064503001c0842252409548007039800b03000d000c02c0c2c5000e004a07401a40500c86003e101402d6042600d10140c8101003169540900d40320301c6552841000348503492500c00528420620021102d516403d203082007228040041c494460b0325640ca40c81a40d01810404a1013140f00192500074184180032603000950805400381d510b0030030100840d560400201d1405d03c2c803114290015421810f882620303203058115460900c4642c2500402c4001c00c0300c00310032285107504080102e0292580c40c61014960100c1c1e00002ea02c1c00e020301101a210700c010900034001e0410000032070885400309980007502e000f52454 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 980894145 1250 980892895 980892919
    0x70c0201020c0d110310050702030a030e1507020604120206070f0c061410080c010c0209060910030c060302090a0f06020a1e0b07090e0a0501051005090a03050312180c010e 75
    0x40b801c0000d86100154040c1080c08000d041c003403a0650f903045042d00f141181c0c080d105111001d019a0811145900581c00500a000c0c0c828080e800440e82c90200e41d0503074116201c803107403803010900252425001a8008030800080041e00450220000f640c2d00040c102c030319100c0b0008003201d0f00d03001c10700d04101e10307400120100606600f201c4034211100e0050500c514146151a40c0c8000c0c5124040721841151410015540503c698402c1540c0140c036081e034580c0c459041c42000300b0040d020000e150f071814400004901d003604c0c03a00c05000c0c603a4025a0b500007030740070070860300841e400c0359907242c0200b01e0400c1019000654078450b1f6501200d40d6080c500001188810144003001c0508034408a00801542c5544416240203403846030070740c0d0b03005444424040048071801d018442e00b000d4a06c0c1d4442105002d6000f80901c894001c008100d056140d41d40d03107096400520310304e13a10440701818407410380c4850700700703801c4900c0800c01442980131000008110840102d0030f5401400300e42c0003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 980895395 1250 980894145 980894147
    0x302101b0f030608010203041a0a06050a21051b01230d0c2006010608010e0906010302130e0a0606030302251a190909051003020114180d0f0501050f0708070c0201 71
    0x80f8000800c961402103440c0d06d06400e0000b10315001405c6c0d1090b56204a0014000004a214031010780f80c002c1d0032100200d04124001c1500d10004441011511260a000001a8040090060b1440414258540415050000b40a00943e02c014490005904000150b01041c0c0c100f900c2002c00c20541c0480c6060384e405060343c0400751181c0580000c03140c03903040a080030000030524104c0b201340e9180040c40e0f907122880e101925041c0d41145080d001280100003504d0180009a103402d41194000740050040d00c0322031410802040840e0700d44d8a551301041855014040c2c581040c0080000d01040c00001855503401103280c01600d03020701e403d054480c0410240001d8a40030509001444281214141d01600701003843c490700b405181494005140520815001d00490f541078403880d90115212001038816001030359444140c1d8549100304115035180401c1da011030340103100d081d1a588440c1440c50940e00021f1030640c0c1d42081c0804d0152556024880e984c2c4442c039403600f40c00a03145840 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 980896645 1250 980895395 980895401
    0x206220b360a0e0f13080a08221103010f090203061308040b0301060216051002101a19080d030209010e12070f090c110a08040501051c05130302101b0f03 67
    0x20260704201d44002c0420b140c910442807074018140509400c0c0345a0328200300b04910f1810784002480004103010b032010250141c00342c0c5801070b8413001d40e640020700c5083c12480907404500141d0303141e500c40c144e404203804c080c03013282c582c03805a14050108850700c5d00800c1c0d8401c00502a00d10501100b040d040920200b00300741d4010302402d62840341d0340d582d6450001c1d580d202d001e0700b6007241d44000100040e0f1b4a030206a816220181b50060418000e4102c006801806152045880c8a038422a0488160ba96407000c103c200b14001c0d808000c1c90412911a24080201085106041c410099000030380e82210000100040482d900011079074085145410608282e11005880c4240c0c800400d4200c2150002c44801a060381c0c2d07450304043ca00c0c15107a5945481d4409405c4c00401c02052200c0d500c02c000501c0280c010703441c80503410130900403a1044400484500f000e00d040c100c1442e041543c14040141d13039040650081c030a1707500700c0c58190740200c96080e00c0700602043c0d6111868072070080d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 980897895 1250 980896645 980896747
    0x6050603210309030f1206040b03060106270b070311060c040e040b093a0513090209030703150218061e0c0f01061d0915011505070206220b 61
    0x4179070320741c464400303030782030361003000d0a55240e4812800c0240034103d5080005040741219035030b56441c0314500c105100e408440b1014030b89044040c2c0c06100100d0b01c8003402c4001c1100a04c01e99994141030a0280d0713460902401500d01c60110004020402604000c40c041c580c029400a41550064035405c020790b04d8007500c1102c8941c0551061504d050712400740e2018110100781d020b0401e440070051808403591f10a4800b1840788448011003800481d61680c003030b113072550004c1c080300d0481e9221345642c484403901000a0400503000a0210200c6107030480a100700c1c10241c2d02281080182d00f4aa6503103007036952148a816008140348510200401220000901c890001c2280c107803520721041000c01c6400f4050b80c400e07040004030b00034000c0002c0c0030084c0e4141c81c1e030002c1036074201440071062442014050b020442c06000000150f078480c4014035403112042a295441d40840710391001c41c240f15403040c000e072030090110020605092410305c012a18036406682280f03483d558039a0094016 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 980899145 1250 980897895 980897917
    0xe04060519060e12060f06060f070803060114070807020d23011a03160b07031403011e0602011b1803120807030b0307031a0403020c060a03090605060321030903 70
    0x44440c0c8039504201505120a88010340d0f0341d1000e8590b18003d1010b608100c80c0807840a510082c0010584200c2d40740c001c0d046034000f840d840c501058079424500381d030007d83c010b44031550000300340006980c1241c107a08282070403d18030380c1003030000d441c1e01e4071900451002070301402208405900b000f0f034507400700e0070030640b04000903480200401c0660090030b1325042c80503600c0c0141050581c40c5000241156040c0603e40551011800e0004614081d0800d0604170103010021407500c0c1000800001386010700000013209101226080c070243c0780620701d070300150540e4548150b01c001c09640800031105880c1c141400c01030150710f525520b00c6280e980e88090702000ca04081000015400318065009441641e0203202ca061143c00b016100e01d41c3e8407005259007100030101190200001c0407960207400303401603d0b024090308000c2940b0340e10030541da40003c0d56603c1402c003041031a00c101500800150011b1140301980c00011540e28010740020080c542d011000030342094041048614488003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 980900395 1250 980899145 980899159
    0xf170612031b07050f0901060c0615060e1008042001200c01080a02040501020a02150c01050c0c0d02070803031b0403060606050706050a090f02040b0418080a09170307030e040605 78
    0x104a81d040b081c110100c00200c0d1900488400244a20700380f0700509252000901415650340b0b426800e0740d01f442500000c0311125110300003103180c0c80f070f03040682e8014003003901c4250306040d0900c1001400b01d029083d060503c8118030a11000c2030101026145c03044882c001c0c4a83c03006c80c00b0058481d401002910b4010316a00d00d481a0540c1000c42c20b10100c0f00e007a00c94030003546880c1c41c05403d0f40628010140183c0c4402c1083c03001d0302d81005080344038501020460b2820301c15855042c00d490045501c42c0041600040912140e0000c2050540300c9240e0b2001e007180c40e080404054403403002034170f02400d41c9c1c10811051105454001210015903000300d04000403903031003c01402c190010041614098501000a82d09002e24014446259031140c01100303900c4084d03003044010070340c3e854081d4002d0703a078101c2180c001442c3c041d1120460300a40c880da4480e11580ca0061058080d0f8014900030103100e005075044010020954a81641c14288028005da078200811300910056101c1540300803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 980901645 1250 980900395 980900407
    0x50a03180e1008010e07060806040b01140304051f0c08010e04050f1c0e150a184e0807050118080d0501080102180913050d08070f0f17061203 62
    0x121503400c100440f0102c6009100480400c00303001d441c1c814074420800494401c10001c0c1c40c903e841c0d400b8019200e0141400509602807820000541e0800c4a08440079400300300c100c110084454900048184542d80900450304000c400800ca000306116080d5080403203400f10302045018440340091070116011640e00809140c816907002d0707240048080480d2100d01c00b0740f0360341090300000501d8141010788a2800d90b04480483d00722014000c606644141090049182251050385090810003120980d42d40a488020400851110707822002e8564406000e694a0f0025900703150600d0f81000180d13440c3e40003400c01c240982540000009550b05022016040100c0c41c405004800c16601c0104800c5e078a8203501400c034819840c01d405460a0003001e4070740c80c580310803055480050158448100013580e961585004016925400440c0c580c10070800c0c4503901940c1d1a22003081c6140031980c107005460054510300541c096104014404070014600d6125480450b041c95642003c81c1d030713911 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 980902895 1250 980901645 980901661
    0xb21030c0f0607080109060303050f16120507031803020306070f020705040c080103030314091e011103131703270a022e050f0a1b0803100603110304050a03180e 70
    0x82c0e0110b4102011820090022841c40c2c0d8a100c0e50094030760540312540360099101e50782c41507812100400580203404240c000c001140805540c40e440ca03980c9881e41c80314210314002e0035030509151a5005070010010420250f60006000e58029000b81030032600c900110004030b04054040d0061074005007011205400b1a50050301e050499000ea0b0b0100b03e03581c0d101c1000036920806690704500c540c4046d903802c40c111410b15501100d07501590001614001304070362241c441c0c2040315500040180c101c0040309010440e0143d842c01056810440e1441c13814504442c01c18070020a002c030808500034810703080210402411a11680043c01e08503800b58403600141d1034004484100003140e042d5040d4030702a4000d0059170528000507003039900b400b66040b8112402c81e41c0441c11101d412400d003105c80402c1040c8002c40c06049181c2d800c40e45207051031405410344042c000c061f05204410010400480c0b00840d00b1110310f03515150203c1000340349800e088054500b5003240e030241403a001404218 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 980904145 1250 980902895 980902903
    0x1201050106020307122618100203040c0608010b071704081507090603060b3009010c080f0609061009090c020708210f130f0b0904050a0b21030c0f 64
    0x1c58458001c0010a54010500f01d43d070300060900f04588400e01041d00d0846d491000d002580159402507a10040c4e8000850700d103824034256440042d0380d8000f0500043c0416800441c0242c82d060030301c01040d502d032814045a034444d0400203012400c01c01c010203049a501d80c01c0350024071554003162001050441d01c003682240584a5801003510608001421400ba00511049805030b040c20350400c9140e1002000303045231640342c8842900e409d082c0300210b04403125560301500c000d0000103500b0702a941c000c0d2034000e02038564030107003540804206040e5104501760f6030041055484201c1144080c50503075240c401a000f980f102c0b801c01c503d000c0308550000791070040721244400c03500c8500c1c0200c0c107800140100c0d0082241d19404000d0358071044c00007002010220503092034010000c0d0751b08515201d51186420080d4010000030300d4001c2e5260600880b07800c91609941000398900120000704054044603141829000100007c19100000e000f0765008a9011083ea49244004c41c4c0094403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 980905395 1250 980904145 980904157
    0x9090c0b0706050a200f0711031e070605030f130f08180a090506010503041407030c030b07020c030106140f0f0405040b041e0804060813020a090501051201110901030b12010501060203 80
    0x540c9005840e01c0310a601e41c0850217884000f14016141200081e0042d203240d00049096a84030300c11000b4072340c582c4040240800c181080300320001100c80d0301c0c5640d070406016a1002080020520500007960641c104190300600c40c00741c680003134a5030b0700c0d28000e505103091000d05400000700304001c02d000041402c0311400d40481d8450070302a2101400401c440307066440034000340c1c0502c0001c00003092a400301d68a641c2c828215200e09070f813a501e10340030001030380003215902062000d115441d901000481e8180208070000c1c40142d081c08615031048207540c0007548540b441d0610480c03142c46501501075440c1000d0401c0c400b0385000d06190144140c15079045074a141c00c41e9021004d804085145920301d94803c190500d024503041048510380d0b40507021a404206480c0340d94016582c9400d0180100a200d00200d540e600d0102005009402c21002050590400e000c1607500c40010044450308002401d00003400001000410b5845207c0a6030114941c03130b00300003042294001000c0c00c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 980906645 1250 980905395 980905411
    0x29060307080601030f03030b130501140405180c01123801090b121b0a090806010605041d07140c070312090503030703030f0b031e1903080109090c0b070605 68
    0x4541d840d085280d480000348406000115803611160019201e6080007104860082081038260507440c099011035000380d100d1440c3c036180e1404404641454054654411000c00710042130070307650682c03035490303102401136281004450120f09400c0c0b0020344c081817110340305d500c00304aa5602c44da00268042d20401c0c41c007100c08405110b4174000d6110308603034810394000ca58901d0500d507481000b04018803018100d03c05113620782440742130404d180000317000682c505a8a244910746845840c500f003140c180c0040f810018100424058078054500c580300c1215080001402030b580e0702000c0b13a1034050030114a482c00d80000b110021540c1c00a140e000303a0b40540807030090000911400c1d00c40480350f02c40c1540541007807204402203406688006804800500080303071a8044000082c14414000509035180610101c50302030018200325170000031012626140c030b01c4402e0b850190101005103e4161510346502002041042c000d50f80b10060203074001582e1035081c20303e007a10141c00c0840d241c0d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 980907895 1250 980906645 980906653
    0x6060f2434080c0a061103060a050a0b09010507020f0913060605010e0f0d1104020c0f100c09170f0106151107060905040b120a050718090b13290603 65
    0x510940e016441c101865084880109800980d80e5842080e41140040f03000502607500b034100462410f010b0041e5600070345082039036900d044010030100254a822190241c6056102800050030b58011950200c100342011912008030b80700095136440300e03441440e000f0183e1814048030071203100c0c03441d10461140c01c091000a072140c00446940c0c1d80034800d1903010807954080c00290505408c03004003640101503003480c65140a0106013603038084181018540d000319148585282c0910030741440948a500900c0103c080901c0204081d402d070080c40640006221440f0744600100540c8022003648002030050720340c0c0e650152201c2d030400c00f00e407001c038000040f1607401080c041000e5054414903111441f002d41044103101c001c005240740c04c0d03003042190f40440d41002040088245040c400d00040c41042e0a01c1ea1040d5079800314035518402504100701000040e4002040903405800301c461840580402c0c240442d0141141d6184015000f40d480180003440941294074890002030b0111 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 980909145 1250 980907895 980907937
    0x9020d110a0305061008070e122b0e010302041206020c030415050918040506010b0306040f02043f030c020d1407083007140d0804200306060f24 63
    0x40d50700510466007c0000b0b040c0804c80030144c50b124072603028034104d500403100502d010200701040b0400038880c00b00005900d1880b80102e0f80c0c08840200303226020705e001d608241c60101c10488560001d4030050010f9004034035282142c408205440080c1000304503d803c0002429014056a118841032030282500303d158252000e2408541405154080000c05103030b80ba0140a110340c2e003014101540c0681c0b1384004140c140b4031070010f000604951419407003a0b00c002241c050b0601c03202da410501140804071000c41000741e01e0701545845416041060080d009880020b200d940302e444010440e80304900d490000b801c001546c0019141c45100321804490003003250900d1542d041c440f601c1024030100618045880c060180c090103210b0351005500d081c09100c4107081c600d04802850007d00000104030500044101803c07009070001c124920202c140008179031513038001081240a00c1442e482e5035500c0c0c68801c9150f044d420300500b083e6580d0420002d0100991205130901c03200031142a05c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 980910395 1250 980909145 980909147
    0xb03161d010815180a0c0201110a0f02010b13050a0b060310051c230c010f12150902030903040e0c03060f0d03020f031303050d0e01020709020d110a03050610 69
    0x4442200944001a54190412a801150310b544000d04584010107a803810481076100c907102146409a10303038102100780b0780100c9400803507810015841c00c680c1090060240111a041100d01d4001c50740340a0040406502c1c0583c0508a0000002d4000c450280e036100c4092316a40320030b00825245005000b030280c58400c10800340000d0b141c500c004080b00d03008106516124490540c40101400d074460549415103590120464162119112045070f50401e600f04070148034490b043c203001d01300000443c02c0080001d003c0201c00451004103039071911140c00000c544601200200909102950340c2e1800300051500c0350003074402c0440b02e070301c2c010100f410080600c0543c2c0c070426002c1c00c100c54801159082020504414074264150f00680e03030f15021807001480105070b4800301c101003030482d034507500d8850710700a0706000800070071800c25014015603a0120f003000481d0903012001d82c031680201c0070400109042ca9101c80083d0001408110803074154001c0f030f00c00d5408540c204c0b680084010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 980911645 1250 980910395 980910407
    0x6021b070e010b070c09050c0304020102070b0a0504090203071806030c020705010305040b0c093c040c090e09011e0b091807060513170f010f0e0c0d060b0306010b0316 73
    0x560700084240e400144030000303810001c1c1801d0360140c608154155030398009003044076020b07900c0006040c00001040150b5030104480e00060100304641450481c2003080240540901d001d56a1a50380000104400500c595a00840c1c0c81142c07050714442070b945e03a4083c000b40142c101c05405400740150000d1190700a100c2c2a02c00d07504680010504d9403410044404c5511001081c1d42c0031072a8a92002c0300903181e010000c0c0368401040301144001940707440900b4401002540d031249081041c07404559038054902c10031502c0700c074000c1e090b54075200d4806014001c03480309502803280d05e0700302601e14801500300d040d40110a440400f40c54481000070000c030701c1e24a4101c0a07503403225204100c0c01d4880c50081583c01c0c1c03c80f001802846d141c0c0c000c50f038219080d00c00078116501845078042d04240078400d0000e074000500080091413112210291550707034109145120b0701da203400d202e060107480d8100311401203009080d10980e40e164000c4c2c041c0d58100b9101314070b40104a189401c2002d000d44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 980912895 1250 980911645 980911649
    0x2815050c031204080708130509130f061a03150a0e340b0c010b09062b060212010e0108070801050403050304021c061e14040803070503070203090d06021b07 68
    0x156150106650b0300d9440700754094811104400104820300204072090054600090007001c0c5030105440c050801007a01c0e0090107a02c0100400c41e0300b680010b0080e41c21a10301f5030300200102385150501400100300254458080c2c050240c0801c007510400d4040400c2d129050680b0304000d20885000c400e565088507119103281260081030442c4c209800303400601d880d040349203016007550744400c04d00c0d00e0394000c2d0312013001c03903911a82040313a02d1500c0851154000c80585071000031200c01201051861100131440e10061b280f07506482c18031045804a0b1856201c2c200403201c20b503503035a50b0070b07030750f400902c42c10901c0e002d048030106282406006190207980c040d0f85441c2183c981c1d400b0802120a44400c4000b01c0700e803000c5410000786180180c03000215004001000d6030001c1c000c58080d40d00b2035800c89000c541c0c120400c000500d0700801d03a50042d90038500325071243d03150001039186200700d4a03200e03402544510020204070712a0010400000c3c81c070024250f02e04464041ca90b246403074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 980914145 1250 980912895 980912917
    0x81c14070507200604090504062d02180301020c0f1207030f0e0d02150a091e35070320010816030b0d0b06030d0c08070f02281505 57
    0x812201c400f10b03030a851120002c02e4621690038080443c60300080003940503510030240d5549030700402c41400064410f413903044611000c40110000050300c3c06920500001186034000e601240b84e40d80c50201580807410801c0190003150b075070b607032119600e81d90880080b8401c01446400940c0c50011003160980b4107580d455115490b105c00e8184050f01d02078070084940780c000b11500400c0c8090703a618030440c84a0303204403c1c0d5603074408220070b0003482182250004000032441c1d0700d090f04080000780c5014111864001c00c003204a0500203c03014800840c2940b1040000c0064500e07401c1d5004980c0801300c0788904503104001c412040b07000c5100d001209603d000c141c038000051102103103488060f0021210b45030000f031801c04040000d5400344092801e40310207014208208560a0030042a100700a45090544e928071031a9100480345c820a0702c0208804800b0001e08119110a00d044241800e1031010f50301c8041d400810341c001002303078821444148141c0101d012030601075411140c0740300038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 980915395 1250 980914145 980914147
    0x120f0515060a0c021e13050711010606020709050a0204152109030f0806130c0509100804150e030702090a09120305060604031b0f0602152d060d081c140705 68
    0x10f40030803083c612411000307541d0041c0c0d2020300617169a0344102542c098038002e0f000403182841c00000b0328483d410b80b85000039a1502030103010345a0000340510441e6000480030030142d44403000d1714013078040c9500c882c05044c96a41c01d00040d503040454441c613001c00c80940c0810902140400055410700c0a001d000728044450300711165105003042d960042c0080c5c01d00c01180045000d03201240d5541d04104002440400c040b00d49180c07000c0361411704003162030038900a0030076482d24481141d151076111003059a40758066440c0d00c0c24820744491700c2c1c000740310200c1407070a02442d4001e46144241122080c0500000812060180c07080c2402200041c000c241050b00f50b0741d40c004c6405088041d4611000c01d41c40c00500100130700d481201071f001c140d014002c0c4002d41099003070061006011040d0410503080e00c1d0240490900d110a4040c8140214100c07545480010500204c1903c41c060b10300b440000f910b04810407144051301107005d85140801260b4455440044000401d60300d5900043d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 980916645 1250 980915395 980915417
    0x7030902150c0a0804090902090a050c0412030e0315041104090c15020c0a0b0405101b03050a050c0a03030b0a06090806040803041a01080d0306080c011e120f0515060a 73
    0x40c04040c00000007400d040f242000700507155802d844d08550b02509403140c9030848001141004d000c0590405410301007800141008000b0050034050350140c1800018016202070605200c0e00308640e140802078161080141c2000e0f40350b0354040c08941c00d80d4a0751075644021414100751050011030340d0020403603081242400310890301c1c444d0f104848401c500c1000c4030b021682c0d4940117140001c005007507505943d03910f403005126005034803010f00030902464812488610018009101e240c99041c0b804555071440c01e03505640c54083c0e60030542c158440d8507001c2c070801d03402d54400c51200c5e41c200e850840d02a42d95600b220722013110301408000d504800042000150100041c5030030511640d201c02c0030305000958002e50240c01d030310064066101c06000304e22160140b01c1c034006424501c01818400c07001a001034201400c0c00e10442e601440703503006c2801e15100705a0742120007451101032007001d001c0010070016150036a49240503019810705908145012030803180700d0007807610b585c0752400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 980917895 1250 980916645 980916679
    0x3091501230f0d0c0e070201150602060402060306010917010903020705030703020109180b090c130923090c06070627020a090b01091d090c0f0a0315090204111207030902 74
    0x200d585600386403c044040010400076808813200e0b405040c1c2080c801210345403003180242590390441020304001c00e000c40a102079940458401e070b000b41c05407a031555035199000102c078000d10304d90104202103031010408403044010342212003601e010703500311000151900300301500c034111403100a000c5002c038941040394032080d0902802315010240000b070000307500e40c0420301c0361780111407072a520100003d8500031680c01400b40409881c0036941040b07807080d00342e41401d002c890900c032600000d140d0742c0000e4040d00100b000c03180c0c03940d010301000d4448800c3e240090140c810580c54210040d091100409000c0c0ca202c4050821500201200c2c00340b85030000030030040103403900c2141007041c0640081818940c0c4448481d034a00001d0328a544c52904181d61410900b080810901c5503001c415000c5070341c0e0f500840d4409894001380c600c407210380c0340399220300100301d5690000d420500780328202e0450240712014200040c00804040400c2d0b5801100300c0454040d424025401132035044030880380 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 980919145 1250 980917895 980917909
    0x130507020325021513291318020708030f18070602070518060333010f05040b011d060d061707180e0316020118090e1225170309150123 59
    0xb00301346c1480041402e81e0f111040e500100b4014210f00036458104200607001c80e0691318083c1483c002c5040c02000d5079400458031025001a06815003c00884d41000502c0c4810f540380340404112401c01d40d45003006500e81c44144942441080000001200e040003209024458000200500200b035000040c000e90806034580b110381c80d0001c090b2450403c4400c40c1c0030340c00b0f49080ca00446210703103000c081006480b00b003500c49040014901481c070021220305511650078078201c03001a2a42184100d410040807203912a07200a80042d0785003c0c0304601081107010390320408a61059242081618416150b003010710080c00e91080010751151842c0c040c0410505105143c0b03440120180c0000b55001030031a0407404c44242d4030042d0f0a880c980c100405851007484080480c18110b228190401d401002c5120300c00c03405c0500d5446080003090401040f03500200025580ca03070038414821991024588803003480e20780340f03000110b12801c8004007060390303504101000d0b4900d0b200c20240006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 980920395 1250 980919145 980919179
    0x302210a0501050907090605120601030201030b1503180705031203010326030a14011a2a0a14060105060c030a0e040f060902070b0f06130507020325021513 68
    0x11901035503005200050082c002d550007990460004c103101c0d401c2c110400215051644010301c181c0132448507101542000c03d01c43d04480d0242000100180900d000c20810740486c90402c045480000410290046080c034980000f00400100d5041c00e40740c01c10b25960703103004c88040c005a20300b4001040054071151040100803040400402c9071005e074103031080a5041506d643c0340150721054203402c1c469008030268014110444070610380d08002380e041c0210b120707d41e01e03041109165103e116108102d208040c100c40701c007408882d1f052410b810650781c2140312252040003030088400004440c901007003a01d8554007060702540c54100038101c00e071005c1564a41d490b810a031184200c0f941c1841a10400c0003e1104ca02c004d65600d0b6180703840c01b0680380080c9500d20001051042c003005468103000a8040e403203048000806489042d01640355010313040b000f41d8050380e0642085c100c00e480d603629a81d0580300707840354041480c2a41964070b45000e00940d807552409100300c104030308e40c840741c92021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 980921645 1250 980920395 980920459
    0x9051011120f0702030d09050d020f19030c0f1a04051005010e0a0b0a030210020a170408030f0304080d1107050607031103060d020d060f050124020c0f1206010609080d02070302 77
    0x21910f040c491b0301c10103448003541c06486580281d903102951580500c0f6290a840c4c040014140c002103d130117004420080f440081c040206504030031081164400f2214580c1da0004400604015165030443c40c841003180e0880d1240541c80c0c40b0b4101c80240c0c00341c0d506072080301c0c0c03070003049603038804007007000300031051107540c4c086402d28001000d41c9030348480b4060000d40d503020b88060005420305001484220107200768100341048101300342540841911105e512404140ea03072601eaa040501080c061165541100761074403140040b8810f50000401d00b55215030152601d56640420a40440350245800d0000581c1000000d01c10b01c0e05a0040134900d10090801c0a114426117412080390801001000000c0e502e400500001102d078999410003000c04084aa4081c48010025114030040410b54001c1082030100e0001d80e44c0e540c030f07582c03a0044601c1110b0071981d446c0802440c0580622882030240111040304503000c1c4082034900c00d5a8028206900381c030960036059029080c0601121 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 980922895 1250 980921645 980921647
    0x7030308280c030203180a020a03030804050f070602030d0501051c02100909140f090706020a03230a03050106030c141b0f030d09020f010906021c1209051011120f070203 74
    0x5010070710342c41464400015030b40c0058032442e000c2e5441c0450107103050f1292195200c0020310005035a4000204152a4036181481240c0c4413031030030340c1c030740314540001c0002801a00da0100c1c04950010140c03203290949101444543d0b80d500a100701a20110000c1d4a0b00d400340c642d01000d4101100f01d01c60030301075441c000003603542e16644117003150786903491805030100c0001800311401c55002c1a542290121020305a50b5140110103581c030441400c0040520240081030607885101d4446181030001d860000746d41d8004e400e00040080c00c0034001c130380c0464503002d030480469209556528103040314620031032030400d010050070b80007080301c0e0201701c25100e40c1c3c04900e91100240050845d841e201c00b4007045807006407040105000c80080810304004036010100050380e40041d640c510304042d0a4060200b501c3d0343e808480d202c40e60300680307031000c1c10702241d4010418009078015092003581010008203411040b8180940700700c1c4c09690070701c800c20000c100c0281030540d10b2a00132403203004503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 980924145 1250 980922895 980922961
    0x2041511120f070c09020f07060c09030b1e07020303060a050103050432071e060e0a050306150306090c0108071b0203010c1d010c02031f0617010c090807030308 70
    0x50075056118401880460001040d044100003103d8019805011003c90035410301c40442caa003503650080c050003400c2a40c8956485950a0050000f200515009045040180b514400d02c070804c0381c0074003c800003200440005002c2070b2011081d42e000300001001c441c0d8542ca064011006044064002e17221080410b882c0c3d2001c1680d1554259081c812a00341d4450580b4503802d9410500d46921a1050046c0c940d1032410056881c0c240d681651a9428500d10081030070010452280c02a04015014411241800000f240340068540c0400d0110f080364019601c5001e120746076074449103a03502080c006400710310800d0180c0d16507a5840403124240c031a05506400007802d40300e011004901148000c000d0741c04022a0502440302280c00b800c000005021a6001c41e03907504428035045c11400700b00203004190819a04030900610f96001c1c120032a080c800c0c40035000303217034140403480444e01d04080000c50403000718580f41100d4154407514815030f03e48e12070300701c522a900c4003900341c51041906 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 980925395 1250 980924145 980924173
    0x31216021b0409140f01090c0f0513020d0b090406050604060b070b0720070312081509040209130515100807060e0607140604110a080708030f0708070b0c0a1202041511 73
    0x94514405100c00c00447c1d8a1050300304148a080ca07604048000094050203000e5138035500c48144204680f1000180c0c1d46002e550715038010000c2c100300342ea10998250901003840310359017045024040440d0208002c41e0340301c02c1301e02c0d14400c8180050003210103000041c81d80d80201060690210700d82c2c0800c1c0c1c102c14103000181450f451f60012503100c034040d5014a20350382d010500c81d5000f0011043d90341980c14240008048550045c402885003030b10b80c0024441682a5881050380c03580310701100e060082c80e50030a421441c08036407585400012031300000310481c000402104480c40354071440c5000c4501014003a0507800340405952080c1d4400b468101c0810030011284602e0061400c80400f148001c10003e01d8003045c2e01200c880d0f8800882802035000110071150040010403820f0340c5c400b44d500c0d00c100c4034026524040c00703000420003004403556100c00200b20950007551401c40540103d01c000040740914001c4812021500302c100a82c6030160fa145500ca41255044071001900e8400c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 980926645 1250 980925395 980925403
    0x151e0e09090313050f1305040303110f04091803050d05150a030b07080109020414010e180702060a0b010507110628200c0d02150c031216021b040914 65
    0x5015242640001045900e0340c04411900024050445045c2504511000016185d07400e4505420b401d5607960081010503000741d0051a48000e11b4128039240c6540002c40c00e0760f030b04140b01c1c040d14123040034111003c03964100703034a400b403541c107840f1681442c1d0154642801004010000c0c10a2406070003000700560b101901d480080d441007500e071101c0e1900000003000560706030b01082c10180140002d00000d07290103172403003000c07500386001c90100e2a280000b410039100e0040c4440302c02c6450b42030107005640070a0039807142000309014400c0704103000044a80d48180322000e088184032305008085840c040c030040905880703109951911920603032620315104e42080c0b80c800460159030a03a09004400066011480d5075400070300000c03410640480c6440c1d040c1c640003842036130110240c060781c5158000380d0381c0394822802101d4581011915002e0500800c3d500580b8080148a40e180d5862002865682030950300c14440a07444a800500c40607040d080c00c21038561001c09941119010301304 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 980927895 1250 980926645 980926651
    0x3070822060212010312081614091804171c09020103140a2415052110060905042c01020421030807021c120e0115030606151e0e09 57
    0x43c400c8a1354590f103401e8561030300ca010480103001510b4104501554180190300c1980040d042809800751000e04681651048840c1d555012410621045448001c4044648624441d0f2207104404241800c0700b802409203841512560b100219210815000c3c0d0304881e00d01c62040c10007050b410034041c81c401c0d0036442112a010304070380e68550100c4200f144552050000719656847c0134031801c00c600400000c0428006800748500010407945d551a00001e15142041031050b503559410080d203c42c091152502c25074001a40500011816282074070542c010420350300344250000680f070142f5545802000701c3c03091781e55030070302000030004114401401184886105015540514034005e844200c029010600b103500404445803605046d110380d0007440100c2c100a014130101d41c2c1d45002038200310202200a5081c0310581c1c09c0a2600042c00e815a07110301410700035551039002c403200341400400c0e0040021101c1588e1040590113440200011805241013600c41980c00b0101d07422020079 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 980929145 1250 980927895 980927917
    0x307230a030819020c010c030804020f03030f0315030706030e10050403030b121c030e0a0809030115060c021e03190f0c060809010b090c040603150509101703030708220602 75
    0xf200e19200e0079075041c00290641d050908111018042c81d0710000d099210007000240a010320075030031038560fa13080050781e004403205141590b40f031500901849100c040d241e04075010b032143c0392010801030f000c0e00035251101410b500811455050520a00240102920540515503100b851070300580350082e80e13801c1e010705c0c20018403c1d1140c00295514841046c2c066404140c41c20011114000000c01e403206519007040700e45403240303d020000ba00401103006140c1a07440142400210650465290b981c0b0034001c54a504202c442110301c0740c0f41808035070407654141c2045605009a009045400a1290046666072140f0f1026070f00c04100c500c1c0707a0410008507185208214508000f4006c1e052000800e42d03038441d103410100d40c0102203000340e0241c8800d00d41c90f0009081004c0492084100030400141861400c0c1408a26040c0f14845801040780440c0b5501d110b000606000084a001c3e031556603c42c0c00c5944c50a10780144502418041010051540c0703000001c2500341c00605280544 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 980930395 1250 980929145 980929177
    0x80a0e0a08070b040f052e02011503140c0a08070605160203010504421a0a0e0105030f1f0b010c0605010308030a0506010c050a060f0b12010c0e0307230a0308 69
    0x1c00032010050b25007644600d205d161480000d0310700c00032029001410036000d1f040a0247d0f001d5400680c00340103018401a14441c005d0400002d20100c10b00485030030039400c0645200581c00000d024902d4202c0c040d080c19035210305020412148108010700c0c1400c800f030081aa40d811550001c3e0070b45900351025115600e1482c00e811541001c140e0500207544055940e20545100030100c8440c0341141d42054002641e910418140920000e0f0540b131014005003041411034840203c050007031401c1c0aa07900034811800a00000e8000186011050304003a03603802448002040040c050b00b4402c20301ca0400c50f4100141d0001400c60287c7c1e806148504112070b20380c82d0000d14001100c41c0140204d0400c040806907001107480400c0e039032801600010042202c070074001c070f2100030b06050a40d1076040000c0030340d0504c003144194002041c0055581d90380006c6083e40d010140d48100034040c840741199144070141c504c040d5000d41d141303e8070015048044147d500e0319103c100d80c00c65880072440d641 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 980931645 1250 980930395 980930399
    0xc0e010810030b0f1b0711040510051305040b0c16020f0402040f061d010804020d03110c031002090a0f0321020c090a0b04063501060b03070908010e0307080a0e0a08070b04 75
    0x4e003414078100e2680329140201d00309003140d10741100c800707c1a0b0306680100e50f548040783d0000328805401014041c090110500f40316011200f03070050004680c280c0b2020300c00400705880246060484820303564101030320355942d0154080003844200150b40681c056402c01c0009400850462008020b085a443c0e4030b001000d020503001c0400741074156541001920403c110050344c51042e00b421807605490802501d4000c205020319102c41c505000d6410b2180c0c40588845141a400424074160143e8440c104140d44600302d20201e100d80c0002000002c032100401d120b0410300341c0400810700c3d01e20403120302665200100349009010303038240e080c558a4010a500034181402100001c240d82c8021901c40d07a0b07801404d000500c1404c4291000c591820028240000250040c102412503000c40903600d0504141c080c210851600c10041c065003460fa0b64a40f412010050b1808030790480c81c8140b030092002e00407034540c000003100507400114080045106002080084007511102003500d80c6d0394 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 980932895 1250 980931645 980931661
    0xe2b0b0126120d020a111c120c2106030b0c0309061008030f0702060c010617070e06010e010f02150f1e060f09060114070f0606090c0e010810030b0f 65
    0x9006a00321040d81c2d01540c21810b42c2d411901c00c80b0079001100f68016122a545042200d500264030501191841401d4000301c3c480000c00c4020990400d40c0c030317116050110640714805580000d1041004070314010100c501c48481007000034801a0b00000c0080c840c0c2d22990303554100c3d88140c61070400701901008000307086404101064000c10f0046070700c0d010038500595250f5922802c4405c06800502080810454403004165100e80c1c22441c024000740b0346804a1400710f41c0c120103010a140308000300060100101e2030401d00804040e174841800d6142800191441141c44006000314030a0010b11600d01c8000c40f01c0d1801902510f418011504140c0d80e51071012800c1400100c030365801e01c0030301c6046e941c0c03008080c14040003034134104c00507540d100068543c5179441410598000000991400308140c0b0004043e4141c0b24110401065880d10301c85822980c1400410011891400030039040358020010726901c0b59041240c40f0f4a15180c0d6102050b240b800c0c0d40c11308402d60000c003800140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 980934145 1250 980932895 980932949
    0x7080406050606120606090604080102040b1911070303030b12030c010504030806010e01020705090901150605070c15050702090405010b0d03020a0606050306070906081009090807060c0e2b0b01 84
    0x38003c55810f03003415920a1490112080034003894800c2d0070001d1046130a440d1807007070300d00410548000710346940e0f5551101d25150b00000f55030000302020b0300003e84460282e120041c1082c0d521008100150540d034090b8004d0003e0714003940c1c881c145201c1c1c105901d070100002e0103150361110001c01e450816140c0036107040c1000c1d00003414800b920002600590340002d0340c00450740101c400d61801e07116000c40d1801050341d58030550f040010b180f03000c2250780d008001032084501c56255514850380d641d8a641804c80c4c000310706030004404000d5200940f52401925400030700900c000203803a80b00400040c0010075900d030031030160b041418000d090010505c0f814004010582c042c01291400c000c00808600040c060300e81840502c0003c648a0344023090307108003410070480208402407407804c2005050308209801c4402c1801d00030080b282d10303c615042c001005028003051703000e03150910a04110107049075162902806110580c005c100c100800b980200802c0c48502e400340012412000c071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 980935251 1106 980934145 980934151
    0x5010903020a050d03270c090f240b0a0f140307090e090109050d11030f0f0309060a0b06071e0203010f0e0714100c0f08030708040605 59
    0x4168000401c1c401490043c0308440e41c0f5110540300320159100c4008a040350036a03030003400201c8007403002c0e00e000302e0310a0340358084254030b981100d41100c100890a0b55000c3c1c0300e00340c2c00c841c40b40c00b29050428410440c40c031000a030a1a03010a10780c0b040c94806010420350b1000890020722651801c0284030102e41266074034102502d00800070700860007a218001000303c042105d40714141701d11442554400d000d802c0050380017000b500c00d04030210300c0348580c0c0400c01c8000741e500028001080300b1090794014075140d0600c0b06c521450300c14001c0c202c2d400c161a000c0440036696803c0f081d9203a480c0d102c1c0c1d074419159a841003520801c000356400030b4146d82440f085914034803040e00400c514410850481c0c245030743d03410714808900781071540c042d0421070321a00714048034810111051000d0160940f444180043d07640d8281d80c1e07000321641000514004180710420440b4004c09030 = true := by decide +kernel

theorem cover : BRFrame.Cov 980755395 980935251 := by
  have h0 := BRFrame.cov_init 980755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 980755395 ≤ n) (h2 : n < 980935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
