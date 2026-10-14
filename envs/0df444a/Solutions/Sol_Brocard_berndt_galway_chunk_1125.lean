-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1125
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:20:55.788439+00:00
-- url     : https://prove2.me/submissions/fb699263-45a6-4444-a4d3-0e80cdd61d0e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 202158273 ≤ n < 202338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 202159523 1250 202158273 202158277
    0x3060911030f010507180308091002030705100b0103060b0a08010e060102032512050301230d06020313020910182f040e0f0c09040e07120c1d04080a0e0105 68
    0x4540d42512030300e507042d010b0300d0041d40098040c80d02ca5840441b0030340215924400700080e40800703044548200810712140c503160b00d20b0045152a401030f00d00304030407612070350b0030807440810210040752034a02c02c40305581d15200d10b00c083d001c0040c0040c201201a140100203020501500c445214070a0204025038020402d5400040b0f141d9640366a0700c035515024000c250404004444440000200d0b82c07106000d202a03c1c142c170040d1070260256607201e0909003030383c003000740740030b802034448402c640100d01c01d80029403013282401c030542040394aa106015010070020002010111508028840002c01c009001c100d400c0c0201d0104103043c00070780f20344081d00c0c02c400040d182000100316103e442c0d4083d002d003041311448614000c240c0d071100301e000801107080310007110b8020100600401450309621046600c1c0d407205c11034148940b20b66683d07131080c00541054441000c0703400304000382001c0c0c4140c0d5030b41c060f16030207042e0300b410b02c2e9039401e0050058081e040d091040480c080645a445101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 202160773 1250 202159523 202159553
    0x5090d080c0d0c12020a021806010309140606100504140603061c030c050105011d010b03070e03160906120c030212011b0e031b130b0402090a080f1501030507030609 72
    0xc256106103000c80d0740980b003c2500f0104441e8810a01c40031513009002080e6501803d4014191000c1c045e917400d0040181c1c070300201182d040c9551007007441c010803400d060b42c104040c0614018002401e000040040040001701120100481007009119505030f450407502c0155041c2c4501e5101d46070384000900311149960044002c01d404330b045014181d121151040302c2d4002e02c020041c50740c9545105940c6404001c100108010042c01000003800c0800116448845403078064a00c1e480400021b0900d481801000541c0302041424407c40c002c43c440d0340002d00c10180b41044610180e510ba031004212032201a100d46c284105440000fa002c1d040f09030100d03007008159040451001d409005400c0c00c030042c3c1d0003881100b003140f00e42440030414460003140106429680c1d19003003030380c90140c1303424440383d90055020300442003d078403503043c450044c249000182100c0fa528540b01440d0035802001542204589001000800c80c04112841600d40051f07010516100b1410010000c0f0700c0c2c41 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 202162023 1250 202160773 202160797
    0x10c02060d09030302070c0e041e060b0d08030901060801020c120c07030503071a07110c10030e07030521040609090c03020f16020f0111060a0923060f0c040605090d08 73
    0x20b00c1808065140d4001c041140c4184814440c01d03888101401c4c420030110740081178141c130300c4410012082d51344540e105051140c00c1c0031030550591004201d01340728850003240c10000200502001210a02480014040d2071000b14100b8518100311982d0710981400450714010010710007034101c40501c9054061500079080ba0b80d90300180c600b280d02c0003c0080092011055080880d03030107441240b85c0e2481d001d07500c00803d8202d001908001011640300e04440a16a60741d080c2524201c043c0080d600441c000c801a100c0d10600403c3c10200c001e46d41000c0d9a035100c01c00040c0310b0207401a100d00160781039020002101d5401c2d9800783c0003445a00c407010a90140490203c21405403613101040b030602c2a0740d06c41c1d41140a20056450340e404680340412034000c0400140b4000880e40218000b031b014a1b01400240380c004021501420051054402034202030100081c081442d280d1a40101d10311140a141901d0710000400c240641c00f81d4034403640d0b08130000800e0001e80002e03954120503003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 202163273 1250 202162023 202162031
    0xc030a201912020103140106120509010e070b120901060b0403080c0304050a03050309030c04050709050409050a060c08010e060a05090c0d0b12030a03050a0e0303010315112106030106080c010c02060d 87
    0x5400b03050840c0e40c1c0b1000890020741072094032510f5184210035103040b907030a0b46402d01c8202c44d00302c41202920006008001c250368070082d20000c00800c2141d20014403081311455a6103140c008103020301c102c001c18056098ac100700040002249a804481c12640c002c800e4a8507004541c02842c01c43c0315035030140c0c0d8005161a07000c01400004401010010811002c4890007000b290620082c2e8078101c03106400b2880b40d01c2c0800c000d09140c5c015560041c4918140c8040040990b00c0134201c813800c01015001940c0740c00103126540c40c00781c40c00d40185003122100000d034900000a14a000000c2c0004503100d0302103040c50350031100e0340015845444c018010726200300f00c0507160795260081180700000906040c04510110601d12900c4404003244020314551f83c00c40d12084209400d02c0082c0c21216035404803031180845040141490304030602c00c0511a0090850b07401d40002e004e00400e00c00e901d031030800c110610001400307001c0c4020a00301182d14009900003c3c82d54010302013202112418 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 202164523 1250 202163273 202163279
    0x319050102161203140609071b06050a09050601060203070807110f091602120702060406051e0706140604020910080c28030c0c08091c150501080c030a2019 68
    0x8081d03d91010100503a4007003004041d1900b050f2515001503800b59000303151800840e243c98801c1d5041d0940c5521001c2100180c0c00603903a000440b0700c111141030240e90fa8003900020018103100075401800b03603200850404002c2d4595050520800d60000c207041c2000001c040c00707460746046152104130052104030340b440c8c81100c03400000030703100c8000d0040c02511200c8044052007002c0d21191a0050700850034181840d1042d076540d03005080c02c3c1e00084403010b141ca0418801d9005180407442071134041001800300c0004110001c000e0009031040740180004411600c0d0703c1083c040c542d455140440260f20341c009041154410a40c08515495800c941c06c0f15400c1c06690114446603296001c00c49804402d0702140c840d22000d0006100385d9081200d22060325058101800e0b80900c4003000c80244050307a10401800355810f0240c181c2922000100800141803003509075004064024045941d171076620385881c3d115040502d449000e02490603400c03611aa491b148140c00010440300034161 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 202165773 1250 202164523 202164533
    0xa0c05220f050610020a080f180907210c120b01050f0d061a12010b0a09150206040501060902040b0409051509090a05070b0403080a0c0f081804051005031905010216 72
    0x4411100e25001d4035208440c10b510510001b508017060382c000054a080076204840e0040c1130707020840e00d004100b68040c440c02950390b084805400344015071980025106001030800700d0082c00321608107050718141c010240e0b182c1085064400070502e00001480d00600b10041c0c0b028001c40e040028101030200d55600a107559a001d5000c1d2581c0440c102c801c0d102d4068401070510030410303440000c0c010140100101415070f4050040c8040a04001028070380300d034010080c2148048030316005a20840c01e020a11501380300c0c00c0c010b0480c4410561806007400f0540b400b0348144e01c030b10003640c3e640b8000613000ba80f580b00500246003009200401600f000700109987e1072107181c2c150345e2405104030004182403030a00703c408480c0d000ca805801c0070360518080d80c0c07448000801307603000d50880c0d0b6128006428600104034003400640b074900145051010f000440b8001008045500c400340c0303051010f9940010780351041a00e11100d510030800500d869806400750004040320800c8000311001000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 202167023 1250 202165773 202165781
    0x5150f01030e160603060f050a1d090705150406170103031d060909010b0a09081635070f08011401030206130807090209090a0b010806010503090a0b09010b010306080a0c05220f 77
    0x107185107c081e40c00c585503010402081094420004001c0c02030703550b00c2301c1c1c8145401540c1d001181e8411f44130f0059580d004101c80f030081d050401d10203c8002014445950000808050030844a0414a60f1342c11680c01610304c5000700700b00c05541c8003640300e0409a40e20b0740c1c1103412a41d0b01600308401560359030034510070790700050b507202c0100382d50a03804903680d280061900301e40c106416020500c5417800400314240c05503600240c4860074111508001c0038280c00b541e4202c01358a0fc010401649466045c2c0001040c54008403d140d050448640c42043c2c104407850540350100c42c0c66540e02640c202841465075a030740042070351f025a1600048401e02903000d04403d2000740d80303101c6655681d4100a007100c00101c00315020441040204840754451000365030f1004042c003c54000002c03644609442d0b1a085642c1510740e0744800000780c465906000f440001c0c0182402000b0b10849039a070000c1c540618010580035aa03018481380380001a1070ba40d401c4110505000c10401c2c51400621000d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 202168273 1250 202167023 202167029
    0x32e0303031107150b0a080f0a061d120a03060f06110705010c0b04150e031210090e1005040305070c080d030501050f010518030a0209090a0605150f01030e16060306 72
    0x401c1c0b0b4900801c06403100352080740c1440b5440448103407040b03521030f0036500501000000582008051001181054007003000b40844c080740001000c291000749020000d643c500d01d140440c0d803a208068100d1060000f44d000300d064001c038035990b00c035100414102c00603c02507004600990030f242002802c180c10044622030725a400040d52041c903145c100666007000d115400800d908041400500820740c440e9514019401201010800d500060791852a64201480c9040c030a90304900703001e41003145160442c02000081014400f44000703000080d114103054214081803600d610008081620900440f81f441341c0c4021440e40b169140c203400f680d902011491400828603050010805140c0540c41d048504030503568580303052111030031140b04c9180050000c4d00b5205505900300141e4800ba00e840c0f0030b00407a80207050440791424241d06450000d4100740c041c112030818075481d03132a5041280c404203801c1c200419a021151080341c80e00c410b032241d01040340003400000c40c031660303d030708210b0031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 202169523 1250 202168273 202168277
    0xb0f060a0f0e0301110d0c09091d0c030c0102061305190b01090c030e060105010c1403030702060714090109050f030f12030618010b0301030609080c030403031809050405070506032e0303 81
    0x80c0d8040e02c145404c035510300c129a1041d50050281c10300c443c180c0e8200d4009008240b40c114401c90380c03818050180d0740030900c01d914031001800076000100c400c00035443c814070120001e00b0142a03400020b03450310800f401040c801c040301440310041c0442007020210440c040503101d01a0912400c01022002083c01002c41c01ea060480c41000c1520031b00501483c1c2c122400601542e9180c040113413815071001c00c041340c480800e5541e00e050000244040c0d442807401d40c016120304c7c42d054000411600d01351200c3d01e1640c00511564520b41d91220800c01a1042a5041d1400729910340c00207160000149148000b441480842e1107044a81e80c041c0d4003410060300d0280c1a096102d981a03400e0000340280a1000340900041021070138541044030401c1c0070b006a00c0c0790030b0b03204d0405821a801030b0001c0e80498101c00c1d0240345444800004001403610076810009400c0c581d03105a16a80c840c85482d11070f500210206528240b0074010403160361500c0d0a405000f00100560300e43ca0072b4a02c400d0b00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 202170773 1250 202169523 202169537
    0x5030307260402010206190e030d150e040515041e11010f0203040e150d080307020106031a04080304060510090c0804020312030f0c071109040b180c01120b0f060a0f 72
    0x100e0382040c00c05030b0050f54160050400d070703076800308113200c110144001d20600740d86079441010480014001080d02c400f800f6030200c2d40190001d0b031015550441c3e0301544054001c2010080404c101080810040284400b03080c060313100c3d410310304c0305903900c25101c2111130303502e0b0f81c60020042c03401c0c41200720540c280c9032030f00c1c0f03000d1360542a078480c0954820016540111030010b0150680b0346582d000d640c40040807820405c1c40764498003032030b8104640030000f5039900c210034020300003e0780303030b40040204140040640e4941a0f42e5400f007408050b00c014807032a242c0703000c5041007050700c4011000c0c01204004110350068504002c1114005482c20b030b01a001d6501c405038401c20b0301003201e00c510704e65060001c05888200490384c06a2210005890340308800308594480e54800310518000d9000b40381c2c0c048107090840004804121810820900713502c0390032100d4199811028800b04035400b0440005c3c41c880d154040348030303030701c00c6503070180e00c46400501c1c00084d94106140c0020700e616030707036045 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 202172023 1250 202170773 202170827
    0xb0c070309172d070b0c06090a1109070e1e010305180601061209061532120102090d0303090b010f0f230a150e0306060913050a05030307 60
    0x301416682d100c002003560086081950f82c41034540e400380c0a1034219415282502030300c030303c1a00700006500040e44440d40001c1d81d0341c000f482007024a03002828007020301511b0f89195a451510200c0c041c0c658003070320201000820302030040e01d54245090002c1c241084696201e280caa01c1180c544020a0110740340c0400b01e81c80c05864117480e01c18000a04c01082071b6420214103441240d940740c2c501b04103941f5030064000240c09405500ca28501b9080c003940d0082c18814400c42d03440c07000c0840b010020b1041d41402d110792019654681c664400e58030014200b8059049502a03c02c4642c6a41c024811102d80400c055040d8400c1100602403044040d543c0d803181003480304058240302d040018031380c2d03100500101541968591400c3e00400001143c03c0c81000130400b1010f490344141c101d1840003100c401060707000102080240d40460150000d072900d48000780d40c445014203180c100d0600c001d00342041000070051000010b80080403a80c40c0c0c6086900117060b101010041d08101c02010030300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 202173273 1250 202172023 202172039
    0x5090d0503040206070b040512120103030906021605010305072006042603010303030c0504080a1a0a060e041104020405030a080c0d0309050606010f03060b040e0a0c08040302120310030b0c070309 85
    0x14070b01581d8020441031815886840f4040140000f60041e101800707111920740030f801c802c5000781050240d00601008039855030070040d01c0407101d035012405540000000059201402344400d0680c6c1003420002403988039070408a070481a100044004a03409000f00402c0748800501503100300d11540a039030040c03000202e40b0402c40203d09242860724024030042c40081d000390040350540ca051f00d855801c00d07540b045207601d840d213403803001d59142105924075030400c8194101a40e01c514030113401d100f46407402400b001500c400420145c070301e00c03400200c050107070b035240c04641c002c00c0024100c400800035800c100d601c65002d00c1000c0d019214001e074a0121314003078002c0d4840700c0d40090150440b075403610010360f11a0908481e00e001c15a8441010a2219240001d0400b5000500203480603240a0003410101c40307040501000340018602044000303580002c040d4060a162452152282c8031100528040d00c280e400042c07480124000300405c00d140c110242013420b005e0754036043c6080da00c03040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 202174523 1250 202173273 202173277
    0x6140c0c030301030f060b0a060f030c2f03040306021308010b030604080a0518041a182710050c09090604060303140c0a140106080d0f08010608060d1505090d05 70
    0x1400344a42080c00108081900c522656251500443e00400d0030244500041e4040c0450b03000352010407001d201a00c0202c1e80751280b110800c4d17841c10720450640c1445140290a14110400210542428660210020180241c41c02141e0251095450f81400802c0e03190821341d9005007a001e61900f0760052140c507000500b14003880d0404201d07480d1540c142e8044481e81e01240007100c601c0303d020150055a112845038042800c144415010245a03070340402c840341c1c2c003807203440c0c88a83d80b241c14414040015a072003504029a0003690134481c0b202682507042c90412090761980b02d14000c2000815200c00e030060000100c01c0340d440e1810307070f1040c0400c4100d1b83c0c84d01003d00010301000191009140c2c0000a201008401c030841300042840d50300c01414400c2e00611889036511048100b28010003040040c6d002059418a00071020304250001d048080520030141081001c0d008105035842c5c0300c1e0610350558020b114031180740401d43d001c1c03020b0401540c000505101d01041c000e031403441241 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 202175773 1250 202174523 202174537
    0x405060a110904021809010311040608060103020609040230040b091b040c05040e0c0912120a0c061e2901020c0f060405220b0d0f14030903070306140c 66
    0xe440e0030030b084001404001d410002c4004264480f00b41c0c2000f5541c0c4502c00c00340254414810f8620229810090000303440e2154007000b42c6078041001440180d64020588507514002d03140141c490005410110130044030220b040e04c0d02c41c400007a403040802079441c07d8030450080d880c820141d101d076000c95540b20f03e801114644004101031802c581d14140c2c002c26030900413860901d040135143c80c1e00e60322515064030003900300c400001d5031910714109401c01c1d565404100c03002d41549801c41c4020f002c68844e203c4c1c00c01c100608610300b1800c200f036943c042d1000d5585c62102040c024417000c0414020301d40a90f84100c0010380c1100d0f8900c0305401100c1d1101d00106901400800e0a00000c0c0311114100b00d4841c1d5107c4403c0c003000ca541d8031502c080c00d070b4183d0380f49140ca50760100c041c04a01151001c40e0094015101d20102742c02052150080c21140c9601c0f81d00707503010304e100c0000103040d80607802c0c005a150023414400010702085400540c004000a5210800b589950a1300718851140003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 202177023 1250 202175773 202175801
    0x7021c030215160c0309080f010501090b0105041a07080d0c05031008011518240f060201060608190f02130509060603010503060403051309090c06081e0c0d0f140405060a 74
    0x40c90f0b001880c07280c820003c50610908000e07100030744a4481c10b040a03170454119585e1ba650b000104180000c070300600080035001c0c00d05c00c0c546030502140d14824141c00c03503400e054800c0001c0c61410003040d40304403114100754050420002c1b240c0d100080c52a03105440c8440d40102040c0003242200041c480d620483e070342840c3d41c9078042d10309400c0340e00d03da4295041100700f03a038a400301d8900b049011080f044103070ba11240031400c01d04142c5ca000d618802d98200c4070071685400701c14010709030400082900860324507011180d284541c408480688060744a400c5007034004580c503c2d0340e480f801c0e0b8401c10b84100703c0c1c950803540d40c1c0d0000d000113400b0900c109545070340010b01050119009500402c0c06402d40155000821b40390100d1000341c1e4410802181c510003601d40c2049881e900c030389016003115010122000718021180f14021204001d081900011000182e500c6c00d80c42d55031003203002080c450800d0003445213400c000c1012140c111030640346400b030080040c0020407948a440e122501503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 202178273 1250 202177023 202177051
    0xb040515031009030c06150320060a110109150f060902070818010215010e0a0b090403020a03050913050103210513350105090c0a030b010e070507021c030215 69
    0x901c2d40e1010b0440d5070810740611801d1200003000c07034110301035100c42d030320a400b006017114914036143c80c2480c20b5003454440c03800b0040000340d43e0b41c0c440d000c440e070710707155031070888031030054840a40c2c01009100b000038032541c80080b05240100a940110005030310b506000c10009030340d0003007102a4400c0e881c0081c00c8000801c140c900b1050392000d60b40c6040c46c184100d600400c203402100c0c411040a0300301d0035001c03442c1020000c4411560191004185050300d500105003410794005e55151170058008042c410042088803030f40d00c0c0d10303502d81c2e02d0380782c844010322680d40d684c02d0400c0b2200c64042c003980c0310000c0300d55013030a44d4000c400329158650342041600c0c0c2e1610701074600ea041030442158801c1c1b0301c0c04012074400d4500d0040082000c07007203040001081d0900b480c84a24000c0e00703000850242071000c0b810000301e10950071190458644d402400c40e01c0d61021011101d500c0317000ea000b540046110b0340022070040030310a000304103100f03400700c9904500d50405910062001c8410f18203140711 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 202179523 1250 202178273 202178293
    0x170a0302030f160206270f0303090409030302130306020d0c0302030c1e0405060705060f010609050105120a02041e031514150414010801090318060915050408030a030b04051503 77
    0x151400416041c0b04003410f0102495182d40000d9540e805100d100c158048032900c52619640000304070802001b0446242e0800e0700101c021a03100e005d02d0183c544a5a59091800c040c0341c000c0c0c04072011a2144419010b0303980d2a03181040003900040c0404030311a15103400800c00c0e40c00707482140d001d084401c40041c10400000390340c00c98086007a55084a19405110004036912000040d0031420f20503000b60200340351100b003249066005038002c2c42084540d40c002c000b0340e40c00c04200e40d1428812001d11001d580c41c50740d8000a8441d6034031070b00018024480170500d4480c13500961094a100743c00c0d0262800b01540e1020544104241d22044042c020340810390981200726410300c1d824002e4004907015a042c1001694500241d0140c45165120b502010805510440345c003406403411084541c0e250a196005100400c1c034056030640d5070f40c805810754a2030040d01136800a252a000b00c0b995002e04170342c0203000e0113400704000c2c001d40c2840003051060480e0509a030018901034020540448 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 202180773 1250 202179523 202179547
    0x3052a07030504030c06051809240a050d12080907030c05121908030115030905030d0e0a0f1a011203020a060b01030b0307030803060918060c0d02040b030a06170a030203 74
    0xc81990214180b0904120000004420700d0140b00100b101d80c8505440341103490130100100c001380b003c3c03031244100d18104000315071000c40d9040d401188103650342a40207010045881001d1581007103512006c00c004030010400705000b100e03907145103942ea20400740c46d00d40c1c03d190b99050900008160814021090000f8100a01d11400d10103075201160140980c8034083c4071821010b50054504420000c014404903000c0210780c03841c24042e18003080842030b55154186c507030094100c42c001d243e885940014aa03041000701032a1603170000c1f42c807030001c0b00c07510302a1070304e0b8940c0382145082d00b016000040c001d40d240070140007c130b8142d0060002088107070307205801004040105810f266a8040c13550701c540f001c11012002c0c1d80f06045040c0d0380d0401d030041003a1407d00501c0c038034001c6a00802a41c0008000c03406640202c450781009403920b003d070200380080c0c007941d00300c10306858001c020081204002e8010b034088840e135194418002e0f08444050fa1600c849100180241e4010046c002e600c00b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 202182023 1250 202180773 202180777
    0x303020309100302160609030e010c08070b18030d020d0b090c0d0b1c11030c04090f120c0b0a14010506030126010b0910090b060306011b03110d0f03052a 67
    0x20b030325442d0041c502846002060495102600b00744c5039030380d036408440c0415421980e40c021b142d82c2401c020040c0300031a540c01049d03112b50300d80144011601c00c00301b600e40d50141c401e40ea035540c1d4013094945030307030041851038000e402081039001024103100c0c0d2880c81e41000c0c0800da009058586800d8a041340b04172452019120041010f50402d5458103814145080725020703143d518880c00c8801030650036201090300c0c106200242e244160300c5c0c000340d800014811040107a415a11903e8494890f100c0380081d0390704d156540b000780c80c840840d800c000c0705241a6114003055038101444010f40e0341c9400500055000c00d005104840301e19011a80881c1d411001d04170f0744070b400d0400031810451480209d0381807038094a010355101c82160f010f10080c40e8174015220807a005840791030441c90010002810b0204800c003016a07079444512240501d4441d0301741001c0800c890301220440d1003400402008184c2400c104400245030002091108210403c4043c0e21068800c00140d91084078141a07865 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 202183273 1250 202182023 202182049
    0x601030207020f030706020f10050c2502090a0b1e0f04150b07030306050a06021b01120b0d030815030703020306041205041a0703110303040c0314010f0609050405160303020309 77
    0x1c40701d075882000144c0d80400c03650380500303c0c5a01803c4080000d050003440c2090fa0004881d1940c1008100a1080705e140c098034050003a02e034214441040c401510700304100800c50282d041030038002000403200464002a10f904400d940d20101c1444048010010700100c0c0d0f6006d5110511003103d150914090704641004c1c000340242108460380c90340c02c0f05040c1d01c50403045001c40c0d00c0c1d0300200b0440c600031084400030b201600240040f2654103102c45460030217280614180800b50301c004880b0a960703444500f03404009803510301400c10387e00f00582241401c44004044065510007401c0605003c2818002c80e580a002000d0303540f640e507100c0303012068407c9071500b0030100303000004400700c0202201c00a02140c240c03543c1d0b1881c003800c0c01000315060301140d10481c0d0041003404005410f400040d000c4903045032401581c42214045c2e40d01500d150311500c0030413420711001040c91003095102e580203c1c0f284080b100b0300c5225100c10704402c03c00b4840035016030428040c11409041101c480059 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 202184523 1250 202183273 202183279
    0xf0904022d040e060a0b0306040c031b03080703090f06050705030706020a0c02130501030b0610020d0c02030c06040b3001180219050a080a060b0d020c030d050408030a060504060b03060103020702 85
    0x21032051940410215038402c2c03440943c661011013408a0041503200e408030448098010300b03854a469110b00e01020440e10006001c0c1500c070501060703481706000360001840c1c0c800ea44580e541c1da1801c0041c82c0540034001c810000d9201d900000b02c150080044555903940b02e40a90f0038000c3e26201c40000790000e4540070300b80302c40c45220f0401a514040ca459000c21000400a49941141020741c140b00c40241501d00a00c0c0f002c90000009400103010680d00300300749007491560013079101280c1805071000c1c6194000c00c1c04a008903044113a1400340c0101c2c07034405850560640c1c41c071101d60580030480c0308030400400b80700042c4807011aa40c4049001900080058035201441d2001c884501c0c0d0381604000046001c540600e58950041e0300c0368001c0c8460000707000c5542000070003c51072003240c000c01c010715030004000c40400380a001395203032048500c404010924282c200701f83d15600490381c641c091440e080000c0340506d0144900003e80e41e1548400b4110f964140056000b036201c2c0105981c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 202185773 1250 202184523 202184599
    0x1030e1b0d0c1211010203070c090e1e010c080a02070f0f06020405030a06020a030b0a080d0c02041413020102070602060709030201050702130908130611032a0604110f090402 76
    0x450a460b615100401000184080b201d04908044c881c0010003041e81381150405c000500100b104014803800756102c170440003800458090100d450103036104c0300c04114102d440c20360f5031010070660000b00d1081454031401c4003541c990203250202e20505100502c0340706109003910102d2a404043e02441d44110310040c60281c9500020b403030800004012038409400140302001141e0601802c8001c0400303840c00c6000358186441103440308070340610780c410000c140c1040b2003550788130340003811700b2140595410340c5810120040300302040c03110426030151040490025005100040d641d01c259180d03070301c1e905001c0c215401182d20754002c0038241c1e400310f0100108003040b043d900c2140762061041040c1f69403a4880d01d18401d481c030700d0f03070302000074070a00100b8501011004800ca5005200200e00524a0142c5081550207142c07105003403803c500c50035080000f0050001c3c088030040c1402c55040031841c120a0410541c0f0b0401c4400940250b0900c4032411036650344846d00c219040d114110030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 202187023 1250 202185773 202185799
    0x4230c0a090c12020f0910030b0a060815060301090617032104020d06020d0b1306050901150504080f0601030303142512020a090f0f03020102060c09010207170a0303060501030e1b 78
    0x40c0d0300296005d102c0442c0000c0c0410a070310309200c0500160800d41401d109810b1018000760344046240f040301c081c00202e0b00001c039415010356103030110a10043c001a10395840d02244401007616014281101e2400c40d07419103d16000000ea40d8928094140b0100100c401a03420004d401b000c2c10480c2c000802000c16000031b0b8050002e401c00032242d001c00550748006004000583e12210020407045181032001d006644481c0145410356001d564604a4580c00c0c40040303034284941d6110880c0d60280da081545031000104581d4120382c000e6505110380d0019006940340d201c415540c500b862916041001c489040c00501c061002505040002402019100d800300fa40d02102d0441c0000340000414440b0200d6410707900080c3c501040d000003a0b074110746c0040e50700d02c03024002c001c00000c04a645282d580c8200100c0c00506061070801d0300007403400c80c4580d5100c103060021008203061080114245d44a4420310820f800002c00400000c1040540b0900800466103440d42024040381d580f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 202188273 1250 202187023 202187057
    0x3040f030309032606030721060203061903030c0516050f010c0203100f020c07080303040b060118050301060b190804020109050d050114040c060f0e180705070b04230c0a090c 76
    0x2441215020b0031380621140b4080e0704060502000d50005001407031a00b907100241c40c100812050401e07803164005983c2e2f1620000111081c0301361800036402800c03000c010082582c4864203542051041088403240071203506441c0c4101203900401c0e80080800028100c0741d80309a800b405035900290944964491001aa0007560746d0704024003459500000c640115a204001a000a007031040165044d81000d0741e8201c4c0e4000d01070600f50400c50114054082014141241e2006002c010700800c030341d0f59200010b00e00ea41142a040059000380071001040d0703409103100500c2a80e05a5034074103c00d04002c200001e1000c1e440e425101590382e1003201803407200c0304c50b5003030050740510100ca07444d61a0040050a440c20108140200a1510f102002e41e0707c40810084d44440302072003031a02031b43e4420080b11f0034050048040c10900001051105100c458004000e44043d4144030420740088042e4840d80ccc8d8001c1d401c03558001a403414100b051400380d51046004a009282030400c00f0b90440e14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 202189523 1250 202188273 202188317
    0x5091206040501051621110c0f16050603060d060c0e0306090309210303160311070f12030204081504060608030a080a050f04050c0f03030906071103010605040203040f03030903 77
    0x4110b425070b546500707002c46200c140790003402c150340f0340c07400b2030700642018071484400781014800140c3c1911840c144032410007400c15a10100c40220071205000100e10320280d54520381c0c2540e04041980401c0480c2c40e00340700e03048a00c07486000d440b034800e140302540c6c0c3e000104101d101d42001c024600f80d6808880c0d80c1404501c0c0034401c00402103460700070100401c50040c0300f0b0b042e940803c158012644054503c08801e80c0d0b80304203000c10f20003504103c40c8080e005070415964800345610001040d00420610a06c42400c0f140501002c24030814201c00680407440b65014411855000c030503013a00a04a141c422680705228440c00328005a03240c803103030f1941c1c00441c51707040802c0180040220106492003a5603110440d107041c001e4506090b02d480e52a402607a0040e40103d001d0344241445807400c00880d512844003400d01580c410032400c1040704584e50404881c8a035003842c0d000210b034585402540d000369000a203913004054030b030340c0903401010022021403e0140c20841103442199103c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 202190773 1250 202189523 202189531
    0x30b100e04110f180102060402090f04020301020d2d020c0a02060705070e010e070f09030b0103020907090f0b0c061b0f03040f06050a0608241b07020402070305070203161505091206 79
    0x40745540390514144d641207404501013401d811540034004010143c0d81b0101c4540c3c02034109219a07596407030741e0002c03d000e031003422081c184040c00e00340214134081e01d68050000f00385407900000704500b101000d100991080302d40091403544800c1648001d80b4105008205c00c84c441d008545403169a081c90302d009010036848085a60710300c200700310503183c00094000030440240b5003820307410704541d10820111703c10302000c1e0041c2c071183e000030012405070b090300b4060500c07039500054207a83c0701c03030703c02656010f05c001d89510b02030a404074440f65440705804490b01c05501c3c156080840c18000c90005400081095460140c0001e12202050305442514060f2056900100c1c1d85410010f04514160865100c00340341c1103000d07031074140343c0d06043c43c640d0001c903891a22004e031258040e8007081d070300a8072000f0f580548001184810980c01034028503a09200381c00751903110112034028546000395114032002580c10031a03000b61113200d000100581702009100ca0f0482d03004550892404100711 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 202192023 1250 202190773 202190797
    0x30b0105090a060503030f0703050918070914030c1c0b010603020d230403030b01111005150619030b06120f071e050405121207050715030b100e0411 65
    0x44014485030926000d050b9104800d00b0060050758031306004aa0303684550000c84100d0340000c1910b13020107205078207c2d071701e12034005d00184280540b00c1080303110f18401d68000700450841c00d000246a6900c0321080b0301807800401400540450105202c082035280c1d015001858045042c0000152001e000c44e018044070b82e00140c80361589282c1400b200e0040e0342c4811400c40b000300c40d1070071010090711030703030f02a40c5440d002c01c059003e440143d07500d0300f00425445c1c00380100307103d4440314001580001d2180c1000300c111401e000405003445418890300071140e240000c5d44681600d4907020307400042030604064582481c001d01d03429120038040042c0d84452a6940000074070000d03650000c110342424903e81e15000c4624001d80024080d17100d18402d00b4020010981040440302c824810303010318010800103c0c1c1c0c1d40c4120700d8407035140c600d1806401043e1902070845845684248105400450041e202416050700d001094904401c02e46489500680f1483e0740640c000814000d44400b170a65 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 202193273 1250 202192023 202192043
    0x18020f0c060a0b011b02040e010b03011e0c030e0330160f050f0412020d0501020c060406060e0103151a060c0708011119110a080403110102060702010e060a021c050103 73
    0xc590384080d03c01c0b0b400340300c1c100f000004200b1032003d014203540c00b4450381103800044890440e1a058090204405004e506501e0280c03010007a071b140b40c403012501d003140d940400400b01c1c41c0009404540903a402040654403d00ca100740254100c030070443c0341014403000010584004407146002d140c1110a03004005002c00a444040d410002100d040c00303c03400e0490030082d1408455000d40114851000c03014030080208041d500c4000b8401d0401d41c01000965680c0041000c0b15600c4c1000e8070103c0c0c100e450103400080c4c40c10340040ca241600e9000d8081a8102400580900500b10380100c0f50344086104110502d640c1c1c5120007415400203650240c40c0061a00c1c03015070031a9203205413500b0401c000c10040c840c50b00c0c216080840d010181c242920f01d002251012840d0140b280e000030054180041c010080c03140441c1c013011081026402ca810503513410808031f0a8911a18a4815641c0101c000c10000101900907011403c0e4840403044d05800340c10300300303090b40d0003a80191144181 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 202194523 1250 202193273 202193281
    0x30c07021e0d0c06030c0905060a050a050f04030b190911010302071103061f05150a18031506090f0212040308090a06050408130512070302150c0d0206060f041518020f0c06 75
    0x11b0241400d03c03a107505006084900d0080420b8261280b40c400c0350030031000044e1560468090b41c00d1710003840d20480510f850ba5180c0c81c1052a1442c2a104c05140400c641c100032002107490248030312040c3e105c000604005c1d52800154040d4121802c1142c5400032840282600d0f10208181442408103813501952a00540c56041041450390869400b6103921122200001c00b10310845000d05094030f024244540303140004a4010210b0b040103205103020b00302031040e107095401c94020f541000104100c400c880c3d6003018200d01c40c500007500c1c070390907038000a80883d01408901c0ea00000490980e01c003c0f01c00d0381c0b44c008540d011601100ca441011801c640b1644020811401030709050300c4204500c404070b9486607441310b09102c002e10414090202801c03a682000980d0320141151086070324003022003001945861040301d0311030045000c0580c4100034682402100f0301124544c3c0000840750600499441080300741c101070442079003c01c4280d10507044000100386003402c0c00050216414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 202195773 1250 202194523 202194527
    0x18030307030c12020c0f1519030f050f010518150d050106030b01051909020a02010f0903050c060f1b250c08070b0a0504060507050f060108010c030b0303030c07021e0d0c06 75
    0x1a503c1e54403400c5502c03400e0000810f44071500303a00300c8003004031280140d01200f940003074000e204251100140b9000e041c245800241c05421940d8800c0c83c4072010301241d501d011110148000c02d201d4164010a0346040e018010444040c80340c0046025840101c10100310001c80c1c1c081c0d040c514100c8442c0c0d540c00081090004040c04903000d40350482e00d101312400b000c1403481c54400719004841c0e040d5400529080c105000354050941c405c075070b031000c0c41300c2505810b0140468110702101c0400340110800544803001c07440c05588a110201e82c0000b41e000307262200310b01c9400c1240e2451036400000071080c0c40494204000141510500c00358860030f003412812810a181380d440f82628072014014150350941240070744059a00303603d070050b10b51820b401c00d01d103083c0c19040b030b504d480c2c000e0100100d01840b06401c800075405903510107003c1c000c10402495500c0c4821030714000024800d1114078010b1400701c500810060540d40111540d2411200040da40361900d407045580403080c507010802c01e0303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 202197023 1250 202195773 202195793
    0x906090429040e010203090d050c0c030a080a1b02011202090a09020c0a0c0b0a0203030a0905160906080d05180f06210a0c08130b06120f0f010e2118030307030c 70
    0x1c903c0d00c020342c194240300c07001d030f42e98841551082090080110f0742400d504020012031500110013401c13143e641d070b80380c1028419a1301c140d990000180300c0040301840d04e110908480710959042e0350b0100d90440c0b04c080e410080d0801c200e01944140c3c4207e001403404051300180105026403400b80000300041d1030300805030740d01070344005402171051002c60466030300070081d25804100080017041a003c540b0b0040d00748100620410304a045544001c90608641c5d070101054441c00400c07035164090b071050035159800b886402d4803034420f03c840214454145007801200408026046c4d42c100403468201c0085918000108070b00c00d00d1000070080c021800d80200c404075962810054401c2c20120500d03d04040065000303045500c603200400c0803a11644c05800300e0400100039204506e81c3c2101607902d9030400982400312790300b05510411100401b040d00786100074640300e43d03401400200d460050a401011a070110450a0188400c3e40d482c10300050810501c6035032418071850480c0f40c03a04c804 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 202198273 1250 202197023 202197041
    0x7080c090f041a04020f090f24030a060b01020106121406070309050604031112040915051002150a020405040507230c071211150a090b030c090609042904 67
    0x790070101444042900c20707845680204100b0700c1d0203429507941c0046003036080710404107038015012404110403211010081400380044a85020407110000140f407041e0300c24850103581508030881c0f00c8001b905c194003c001055060001051a554507a00c2814000058a09660303100140c0445204040240461644450340d424200b000c0c805584a4642c0d0b10f0004100800f4002c40d5400740c4a0507600708919404125112500c075550340d10b03424844090309012a81c00f1042030101c1001c9030030710704010518101c040c0d0754000c00304610001d8603a0f104540282189205650801c0049230307035100c0780101c80c8140c07080c3c0c44100c6598080040c8009000140c0703507141c129041801001e0300500d01042e001c080f0381c0281019042071900381800c0701e8041602c24041c0d440310004850340043c00030301d0058100e00d90107860b001d050355601c1204c62424802200c003844032080400c41005c0324a400d201030024000701400c0040c542c04144004000100082211040d40307240320880406494140038495036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 202199523 1250 202198273 202198291
    0x100f11160510051003120306031b03030201050a09031b0809032e090201090603230403091a03060d140307061e0e010b1804050a21120903020601151107080c09 69
    0xf42d24001e911100c001095000007001c22402044c0700045c10b1003904490041c51700011120342000611204034190079592100710b02550802c400030b5600d45030f5100314080340340c154550f5134a0540311003c4a496403080c06085a00c4041803054070500c1d1020880c00340120001014103d06251341801c03d1130001c02c1d081d444c80c096090004440061340d0145808046603068240400c08801143ca03980038480c2d001e0302102440c1d240b00c02c100515038052052021507080c92036001d25200d000f000020140b0048500b43c3e00a541440b051001894080341c8800c02e403480c0050300e0600c00d0700c0d44ca1205680c245d141185041a02048180102d0f184c0d1284c5190400100c1c001c2010600ca0000304980b0002e080c42504644100c1001138207100040c0144004164000d00c4015008821010008180ca000704891b00080c02c0000c9480d072a12944281310901e81c0680040070281e10300b031949030020b04509120300402600c46a100200c010401ca04000343c0b1240c0003400f00714a0100c18001407540080007810 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 202200773 1250 202199523 202199531
    0xd090605010509070c11062502010e0108040506011a0705010912120c140f0c0709021206040608030712090801060e04060f0606050a030903021f0b030d02030c100f11160510 75
    0x39065004494005c0c0203a010040146510a42d8005403a50140308410307941c02c0c4507030422000c0c10307250320003042085100b41c84078010000c0c0c0303000442d14030b01c007102c0040c0180c0c82407005110703800810244031841000e20300031034600081682d501e0b096401030302080b1500081d01e21210613041d040040000401c0321064100103001c4600d000400100303440d40707030891048000600c9a0010f144030100e4441100c3c4808640d04603680302c0a0100075441289100114075040303001c98880e00e414040c0c00210b030305081c001d40c04c000b1140c41d03030400e0100e000d4100c0700b0702003840350004000d40c00b0300900000f0000d4554a401c81d19050910009840480003823007425403a0110030721a01d034110b0251605c0507405d1800045080903446e042e49070000c54250034a01440c1a0145000001241c10000400c0004d6083d5411440c5100090341c0c0d0b80100384003000c107a0440c822840c60790125500591003201074040200c1c001030040a01841540844100341c82e00c46010004e4060200401c907200703240d001458104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 202202023 1250 202200773 202200781
    0xf0f1a04050c1206031039050403030e2418040c091823090f0f030a0c060209060703020102031f0608070c050c1002010204051822030210020d090605010509 68
    0x9054482c656811180905100209989403000c000010342c1030a0340703d080040c101200204000c0300340780415203d547d1144108107114501f8455045100c07081900c8203410942103550035545c0f01c2c2e44080c3c00d40c101c00700410f0000d46c405d040018120b85040c4518190b5110b0300082e444900c46564004640160704001d090140207621a40c0344080b01d1442b0600b801615140300020050809101039251520f40311b03808032441c5088003030a07401000710204858140c0c000f818055140e80d26104110380540082c001800c40c035000e203201c1405a881440c1c01072420324130000040e0a50000e10b019001030b0b501000304810300030200c44c00108095903c80c2c923180e49240c0b40005045250080c074107010040c20742814004c00c501044100780c06000200821041805100000d00035045807103824441c00300741f80d5804090641d140c031a40211700542380209044c00550030206040d1002e0303000c0f42103215904252192900601c0682400c4045407404a0029040c0c1054829110103800041c4100a035000384 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 202203273 1250 202202023 202202041
    0x50a060e1204150302090d0606151e120209030325140a121d1e04050a0c0e040b010e03030403060207020a0b030108151825360f0f1a0405 60
    0xe40c3c2000b9480c0303005070b5622401e401003051400c5604008101d103003081d00202e00781008641059002005607985050750410011704882d0003c5a4041300c04101c0f91280b00d16141d070190001c04411402404407860301d60201c81807103048600700d0f81d003800300b1310100c040030400541c0348015541c040510014403155815031503511004031401080c03414009100900380c0032000164101d80e40d0440101264481c80c8048108000545040d030501d2044e803420300092090002d500c176000c00c6c3c20b5a40e4480c00d410803401e042c0310040441500e018103004104955031050f0760104000e001a51080c1c40260701c54030f00b4414484410240d4000f46107400042c0018455110002400b40001d500f02a061600d0b840f09111100301c0d034401d201c1e003001c0b4022519104013400b11540350101d5006100245040a03581c0c002c89000120000440224000c400b21541110004c45c01c004614419040340090024030900034001121400e0403e0100d03161200c40c41e40d9035114142181d015034500340c40c01e10840c80d0440003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 202204523 1250 202203273 202203299
    0x106030c1407020a0906030501020d0b010f0c0b1906061d0a0506160c0e09030c06090f0604022206120210020a02130906140c041e060801060813050a060e1204 69
    0x3904024030700210b0924190364641181600410030000200182e1380c40c1e041142c040d40c400700641442c24209147c40c0c0300384d441003480c08412091a0386010044400380e80381580c00c0c02c0030301900443c900141041d029010103100d100c00504103622613001c0c003098501c2502181d40f010b91100d1107050101010040c9480340381c01c0303400c000608032141c2689803146c602114030314183d0300403000d604030b51420400a00c80000080c001c0d25000000c507406550b650400c3d40e628102040103d002d80c1004021400500706050781100010700d0b0150031401002550203017041300c410390b01140300ea0303c17800303011001d5051440d80f4200d80e9810b8170141c4030147d26034000c40c0d200503a500448484030360300c0203d10700340159a40110001341b541248807507a0b0810b404d002c220780e0824080c040340109049c413400b40d411340c42040071003140d10703030b4071441c807540e280030411360f4a400000d1903800e010341c0f51805000000e50500400800c00c1c0300d000c00203442807d8900a07403034040d103600d500c40070110800c01400040f640c801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 202205773 1250 202204523 202204547
    0x40314032203020a0507090213090e030f0c070806041a090d09050f040b131b09081b0a080f0105010f05010201060b040b0706091403091003020a05090d1e0b09060106030c 74
    0x150780401030180d00d0124a020b1412501134028014404c1c0400e4a010391340042807501c00703c40f01d803841d86864080b40800c8a0942d42c00c00c003280d00402c42e91480c40103910140104c50812030584642c01d60b90f480a50800000315400c448070915002201400341c82c00f0b500a400c41d00d030b00002c00c1000c44000016141b04c1050284503c110022001c06450340d98942004031200310107015004010007a5407813030701410700e4041c240d11030319100646117446840b4501d0346086418940c020201120401602802078201d00051900000344a030b020841080801900e005400d10400000307041d0b151040380110419940c00050459061523020003580480100380c5054a411807200d43d0b03280c2d1140f4000d0024406031038001c11002c0c07050301d0a108810088084e10585809640a1041e40b0f41280b04408030b12464826070301141c0e0500c4108820f041080004542c28450801c0345001030440c00c6100280c0042e0302c045071927200000801aa014003404100d00420300e5090074072101925401c05851242421 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 202207023 1250 202205773 202205821
    0xe1005190503071b050708010c020703021c0203030406050708040f03080c060106030b10080a0212091e01020f0403060e010605060f0a020c06070503070311120d141e0a020901140a0804031403 83
    0x139207805015060181c0d40040440200030040e4410b000c2c0301a4030b584061005910415680387c10300000c02c3e80e040c5420034154010061854941000420394640e000440b007910705d12021303c00401d07103840d0011040090360142002e5610b5001b01000b16103007110507040541010300f028402a003545545c8042d441500441c1088055950303890a40b000a00075011922400040801841080440811a40e00c540800c08152446555080b00e2034240c3c80781400072120000200010404100305130b007c482842e0320030b00040380d110340d5030001900340e40203601d044151100c00038268070300c40d4040042c00c43ca84019107503582006d2064a55075240d003c2e41a001c3c060155034400b0000d0007005020a001c55182003681035103d58030b40c03500c94024040c00f0301400365040703640049100d83c1d0b11058000c400c0f40420003400e00545c2c58050703a4011350010302407941400f42c0080d8510345041144064500c41d0320b103954150340c520300307400c009190002c01e1080c155015000c00610180041310b01d1201c42400038a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 202208273 1250 202207023 202207067
    0x70504021b06070e130203010501020a030f21020d0605030a020303030c22081b0102010203090c040f0f020f0921030313020a0801020c2a09060d030e100519050307 71
    0x1085526100003031002074071501440c000c10030750380d03041140d4032207000c0284c07800a41c02d03070015900742c00c91200b80121409070380035981120000703210303845001401c0030520340b4000101c290078200040c1d40c20006180455a00411018940102403041c00c0003018100e0043c0f038401e03c940c0101740c482c070010340410215500003c41510559140303241c001b5507550450003441042d50340f10180d80f07d00127003981940380703000c100c4100c1e010f61050095038015003016001e05160654441004001d092002112516030385503014442440702500c090000d007a103000226554074000401c01204410030506181c2c64444c0c2094018640400001d03641d0001e241c82d0700070240c04203030001900c80386903980320340e403e0b600005400c10350715404a8051004904088512403603c240a501080907444140700703a048040300001450791300d46032064100340ca0117414240e5100220201141c1c40718041b000000200340d0002d1a4042c10440301d44055030892149490340c258288841c009001800030b10340d4044a10007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 202209523 1250 202208273 202208287
    0x1020c0a170a0b04030f08060a0509070c0309090f0603050105010f0614030402061603021c080c2b0c0807020601140d0210020f030a17130308010e1b07030305060f1207050402 76
    0x1082000740780b141d4101d50400c0c0c0d0b504e0b05103002413048180b0140000052640b1000c50708600744944107c050700c100524901e80d0755100d042c101c860140f010703020b404002880c40009a021050310035492004941c21020803103a04500304107094480603880070175903d00d104002c1044940c00081c0b2007020120944059690700c1c2e5000013101030044c42503003034068804800b18010550002902261400d400c11048503005aa28041c1c410002c12900e802062038104640020402d5041c0b0100d00040403040c1c503202c40300708c0c50314a0101e85440502d0713004a17100300c06111109404026146c01429000094a242d0b82c800c80495400c01009000a00540301c120700340c10002e000b400412501c90720b85007103984800380e102c001070441040d001c3c409855214900030462042c007200c40050a2605500e822942d41d181020ba4903500e0001040c002400081304001030002440400800a0b94020340d00451a800c1050402605444465600e03210304034a42c2c601449440100b9070b0310844108880058031054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 202210773 1250 202209523 202209569
    0xf060c08070816051912030905120f0a08010e0610030c05160809040b010809070608130c090501060e031f0c090306060e04030201140106020c0907031d0f0c01020c0a 72
    0x39451008181440225401000d103080700c1003420b0f142e02400c00c64001759400341d200040f00181d00809440412810502d0780c0072030098002030b50691184d4100c81c01c19502800c11003c0340c00604031035440c40d40005500320007a070f010444d5809042c0b84100541503040030341c0010351505056449000345a2a1144404411f014009a5140c030500c81c03000ea41c0030703600c1e20b02500ca0f40d00010506203d1460001807901c55440344000511440c40342004080a03070a001341554891002001e00c102c001c1664031039800500b1144140d801040c0c4a00c021559504044002e4034442c0f401400c1d41c06a07002c6640d00e641c00014458035640700501380d20024620f03e1644080716210510742000c1c1c841c07420301e080000c08138000c0554500c00c60083d4020000e82d58080000e039001c01c02032140c10010703400b00c2d1409015261038540b083d000385032030400261920b404a10740d08200c022002c1280a5005500e41c003240c02001c0c80048050079003440601004001100041d00c60b2070103014003815000f42078000000380c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 202212023 1250 202210773 202210777
    0x807031109130e01050a060303080c310501170601020a0b1801020a020606150309150a140112020f2407050106031e060b040203041707020a0e09030901090f0f060c08 72
    0x204010b8003290b01c9003030070078116010b04a6580054410762030100000c10129881c865581a258035550315015610303074a03065622504074491141f0249180d03070031650040d020368545043d40341303540c900410b0146802c00250441c030310540411504103041040000c2c90f179010401901c5030750321801001c601d8980c01c180c030107071002e2241a10002e600c0064a68106a000551070780b1a0b001150301380c0c40308500760202d000c0d5000c1038840c1103181c0c0c40000100300301115a076a80358007904c0400000340300404460781024002c420703802015000301071407543c070030340c1444501e0070079440b810b540010f800c11549004400c15061400107020400020501d002006800e403c0304c80155001204107002c4640f454030540300454000e41128a00e14001030141e0740d060500980b4071071904041c410411070b0700800c5070340c05644404412a03100c044240045400300c13070007d07106e01a0500304015038482501c00005050a2243e03080305a072040c1050b003c0024071034002e0240c041d141d10b4980705295980034540000d41e4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 202213273 1250 202212023 202212037
    0x170a030c02090403140307090f1202030d050a0311040e04030e040c050a0e010c0f03030b090a060f030b0408070b040b181603081608040b0306041b0206150303070b0109050f06090708070311 82
    0xa500001480003d2398440d50000689000e101d814041980d61154000701601420000b5050340111405d102e0a50040d800b90031030030361303d0502044c10059a4501021a802074003c03402c03070182c4070107020a043d44015065000481510f003041003045c00031010781540910000c040030440c85050643d080d92068410564043d404100b003060004c0514025000e00a14400d1500801d12040001c0006a142c0500d030300700c421580c1da407070616080d604c61201d25a4001c005882e89401000741000081d04019542d120303034000d044211850070021542c620440ca008508001075024450321003550710210b0350700d82201d61015050b42d58602d498640304202d0103109001e080660080f500080041000e8000c5208010446041201e80349401d14883e10094200480006a10020005074100da80380c000315014200281280e04005280e92410034481090b0000110940c8580a018000245c0c0c0c0740281c210400310355012403843d01800c010720070b02000b001c03002010f8a51202e160b101a0712421a028 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 202214523 1250 202213273 202213307
    0x309050307051e03121f0b1306090609080303060d020f03100b03060f0c03150109090606030204050901050406080d0c0303090c06181e0306020c07050a0f170a030c02090403 75
    0x5501c4141821501c8a286982120f400f00310400c02910150011048511148402c2002e40b07050321642d200c1602000c0c4050510001d6100c1ea03c003040301070900e0050510005216182080341d400c00fa0000c040c000683d002000b80540d40c1402e111800b0003100b0b0300d6100c80c0903a140c0c1c0640d48a4000a0f01700300382d01160607094082c5405064210455030404c00725014150304486240c4c686840a001e0482c00f02c50554100000384082001c0240c540d0314900040b2051501d43d00c0c66440e500741e01c08440782ca50088001c2540058208820b0804501e00f0b401860119000c00c40a0b261401c03898031200c49a08840c1006510b0909100f0140658480d0072401d40140c4024021621124040c040380f154900500909410110019552141e69602d0414540740204004c001c1d01d1035485801039086884071281380c0c0150031000c1441c2e2941c0603600d00400c0c4441030003824514048001907054900c0030108ac00da0804c000308400301350000782090880c1d0b4107969100c03030703603a5504080764081d07521058206 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 202215773 1250 202214523 202214527
    0x9130312022a120304080c0d180e1825090209010c0f03030f060308030601080a06060f050922090309210209061f020c030c190605030907090e030a081501120b0103090503 74
    0xa0128078405070601f003580e54100c401280c0f00000070740300c00300307950940a44004940c5040c05150900020181c2203040741c00c0103081807401c07a00d480d040c60400e5400700442a020354480700300820005407000181025a011482d105101c6c0009092071040040640b14400021800c0200b501ca86d01244064000040402405031a0302d0b164415034000da0f40b0500040384034020a0141e1340070b125400c21214140ca4098049040d200c0079640707070f00545006544490884108007003109100c41d440b1403100c0041e40080c00c140940703030142005c000e03034110441c400040c081400b180e44284022004443d011129101c0c25130303500340001c540c09158401c69141020b80c284c1130850179000280703885903510450a480b100103d0348c0501c0f00e80c1d142d0030200c0441042c20b680070806d280c001c0008503040030018041d9140192100601402d40ea559400225030760300001301c000f000c41c0e0015401e908201070704065915208900002030002100444601c10580e4481001400368003e92224501540c03100c1566 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 202217023 1250 202215773 202215781
    0xa06110a0c061805060c101a030a1a0c030f13060f180b06030d0912030e0a060e27040204111c0905010b030a03050d0e0a0209130312022a1203 62
    0x10f224040340710320b18800c03440c8010080744614010041d180e021003900000d02e1590b1044840901070002d82d03a031483c07802101785800169490520084091a00803040c0d0821007200c4031841208040003030060000c942d090043c44031600118640320740250418078444080026400c048008050100c080c1c614a80f038016610794040404444000d058012036129425680300010302d078855520420100c0010000c1c081400030200000c0c691510038024a010a0400c1c46000443e83e07034095900310f04045060b002200d115850901d2420030f400324010741d41c00c054850641e600d148403001510091085488100d6043c502a100e4140c0751094a1100181c240390700e6506183d004286150040c1c0d03080d405c00300108407504001600c00000c503030550742c0c2e6107000701100c00c01d0000d001d05000d05055010303064003400503980e0b011065008650801102e0081d0120f03107400f808940c083c0800e001064014042003802d10012002e002d80041c1c5510300c0161150781d03444950500100704101c241c0760502000340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 202218273 1250 202217023 202217027
    0xf02120a0f030b031209190308033c0c211006020106050a08030702090406090807030302090906031c111204060903030f0201060e041509050a2f0a06110a0c06 69
    0x24048112003910104280703c005000d0540740c4500346245140100108001180f504011407030540041c0c0d03501210b04070395207030359500c12150300c00c2e00e08014001c40a21003a6801c8500d100e8a100f5450210048210905003600d240d0189801810540700d4800800d004500f031020321619444140500300e088003d18107102c5403661191540200c02c0150b181c503070b0104036410001e035002c007a1034041c40114213115290b401c01c413584000500c1150a680c0b515030344400074800c40007621030144a80c9001d6110f080354802c0c48104000140b403107200e580501c1802c50300b02c12110280e0219049071402403813003018140e80d2441c0c60300e440c100d0500b881c0005800101b0aa20000c0304040e070344a9a10102c480c18202400c83c01d8462900030701c100b0342800000324000079810a06104003810311000499200d00b1515100d081140c289002d40d6074810162280f40c410004041c0601c3c070014001800301501c074101e020a02806140c002c10051100700140e00c15503820800c06180440c0d800307084c2c0c100e1340f42c9a100c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 202219523 1250 202218273 202218287
    0x601060507110d03020708071a0301050f010908010216110f0109090507020a020a0e04025107030e0a0603061a03180f01020a0807080603031603140705062403030a0f02120a 75
    0x61540d250140350004203908800318100b00d103440840f0320301d032b0540e4240000c02120140903031242d8184241d44500160300c0e0700a0011b070608143e200c4d007800782c3c1c00b4070703040c036910080010f244540f080f90a0f034124403040ea00605000140c84107010300080d075654130b0760203a10b80703d07080401130740c0306e0f8540a000408442004015100780d20a03a610010700d42400d40901200901d0403101c407050403034150705a902d58041c5258184665006032042c100b540b0300c1c034180380d1a80a90000d0300000c48001c640709103401c14bd09060000c01191800304940c601d4078100881003d0300001d020314040c0000b001c038180c47c03804050820f0610320032081e00d40640620021038000d40c00b414044c0c0205000c4030002c1e40300350080d0841c1c1c0c401d0703070701801540c540f602041581c01c050301d0344030342101400103c0246045032000c040140841034072500050106083c07081c1c2d84c0820200080d901442d5101420100e015078030f012080d01d4020f59076062001c1107821006040e410300701c00042d45181c0c108041440c1c11760790351041c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 202220773 1250 202219523 202219529
    0xb1c0b0a0c0507030c0f0206070803010e04060c050a0e130e01021c06060801050a09050405100c11070b09180709080a08030601030e062a0d0e0606090a09050601060507110d030207 78
    0xc010000ca108001e0b12140203645025003c00d207040b40346008a2044507220b85004d2005040130b02c0c184240d070740c0880030781080e0000e501c101c03049000c00081166511840c403844406043c0242030440852000f01042d10072501c40380513a10151502c45401015048680711641c8400250344886004030a2040700150701c08500d112400c011000900a00942046069400c050801070b40c039400c00b081c48001c1c20000c1c008071210b1081e00c0c0208608400c911407801548240d40c0c400150800c5040009d2400550780c004071090b4a04000c40c0b0080d070b55000c1c2c18241c60044074450300302035450724025514030819510064007405414417000800482030011031003500240c8081210640310205281e50301801c0701c2c1444031aa482141071815000c1720b529080345c250704007115280c4000350980c4016904000312000d10303030b8440700c24080f96280c0014150741c040504034003001b1181040d1a02070b52000123120303000034000001401014001034028003401d202016007003a2248059280003035942150744 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 202222023 1250 202220773 202220791
    0x60905011e0f0e16020316050c10021c0e060d020d05060901081906151d07020d02030f07060b040b04090f03020d0e0603060f0102030c0d03061e05010c060b1c0b 70
    0x115001c41d10b481e00c4401c21059407500200140140e0f00c50041050800c9000b21000a601c0b061002c006a07004515140c2d640501c00c1000d0a040348690052105030188416660300359005070061860b03a1400c141c01c1c2040702000c0c0b40410f030004842c00071404511503228600c0825000003076441100906411041c0200b40135599141c1e41c1c0e1744c3d00351103600d8445004543d20120710140d100000b03d40540c020900301a0a41a0131110969030200143c0700a1035150714039070001488200700c20390760140304218403088030b070000d507242041440141c00584510702d07005005640d50900c3d03032200d40740c0d81d00ca4143d40c44040d00c10403001010b410202f03490680d41004038014851031240408032440b5030584a1b03080d5014140381c0c00c54903068100490b25104030006130440c4023722050000e01800c011610503100103480c0001c0c114180506c1100c481ca840c40005a4001100307820002079034400e1180e0846030b00a2000038010f5a084005105501350361000e40c2d00c400c50030000e0b82804403660301540910708003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 202223273 1250 202222023 202222079
    0xe0c100513151e0e010810091a0306060a0e01171e01020c060702011a0f0d02090c0d0c050901090918020a060e0a0e010b040509090a02030712050d02070e011806090501 73
    0x1030000d204010710b21140143c0041c02811003401c4550003102c00c1c941003a1281104d540003600c2d142120211004002c0710110075003d80e4070800030303040c00e001582d005401503800340b091a051a80d1040c8030300703040c455070360f0030002a032010000c3e1500b8400205d6202c2040600300b203011808021a020750440703211200140600703404202c9079401485407012181468001c01c07180081101084a2502504c1540c0c0d040a000741c007500041c0c0c0d92078a414401c01740d810300107480b00b2004190ba0100c942403260b100610400b0000700c2e4050383c0140e11302086410400d0f020a000d40056182c07c0e060031fa0383d034005d401100d00c1030049811034002c00e50813440d060980d040a101c40d60f0b14038610290200388942d1708800401c00c0148100d0030b00405150b8010340e00c40407590a40b030140c0c0400d1400304150300420f03000c54402c07070b10701c100207091000d200b0a90b070510041081d1403c050805400180600c940241881d80c00798203600a429034000d803004004501040140b50703910030904030302281c070011455441e02a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 202224523 1250 202223273 202223297
    0x15020105100806011802130f0e0703050405100911130e010c030510030605060114030f0402040608030901081503150c1206030318010f0516050715030e0c10051315 71
    0x159000e4004030760382ca038020b102d281d1030004026000041e007041c0343c040c1e503000c000041c0702c14801740c010802041018400300005280030640304c3c0094024143ea000c140c181310912000c5040050f01b0200c1c2c14080e00001000482803400e040c02da003108251680000104c00020300d0018254031001140d81004024025a03000702d004604444080343c0b80580d0340340c201c0041c400300b0902c0d13000550040303040c100074440740d07054500b944441d08116004000511104c040204500b040d004200050900400543c20300e125030b40040c2c04440014a411070501452201506a5904100e482c60b040502d0725500628103007005000e0060707001102c1c02c0d09092106011400605000007200d04030040b441c21400c1070a0303401c004490744407100442204100c0140170351459999084c02c040c451501c144000e0091514012511403210f042c00b40b07101c2410706d4140d00701e403a4200443d021114502c125001807100c0d461020a6400b4040c2001a0001c451031500c0031070107880b5904100c130042510780360040300d0705c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 202225773 1250 202224523 202224541
    0xf06100803040308180306100f0b031e0a06090c110d0c02090a02090103110c01150b030c04050d0f080c0703150203010b0405010305040303110a020714040b030c06070f0c15020105 78
    0x121a11624029a10400c030400106040c400a000b040100750820460a4000b100203441c08405a03504900c40fa03056034104885000365100d80010143c4940207421440c0070038410b59600101c4c4259418562040000349070002c15900c6803000e0b00344032030308102110368032400a180741d42142042c6402c1c03146410411400f0300880340400d000e81e0003080c4071000d46c0d80040c68006900314480c3c0a05041e101c8c3d01c55410f0102a0000e003040764401000007900c9a04018030514450155000b42072001040041c0585403150000300d0b01034034400e030344070344107a021480d02c100501e074280d03405800d03e000496941403130305c0c011850380100c074090100c0100245041c1e0034101244000c1c0300e0001650420803080086500903042a6445030103800d00203406000045100715640c007030408031005820061003408be0104010389007040f03140950b01040319002e0075000c00c0d9114085079403648202404284401001326112080205943c0310b00047c042541e0341c01014242c00c900c410781d44c0994200400510300c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 202227023 1250 202225773 202225801
    0x60909020a050a1a071a2d0108030a0c0f060603080c101e0e160b0405101b02041107050d030605040c080609060108071101051006020106120b0f061309050f06 69
    0x250034400c040c1c08100102c4c610340420b03403000000704c65800d28403400039900070700103e800e8400c90000d100c0e031204100b0020030070007159081c00040d4041c04804010300240074004250395580ca024200241d4040b01c5062402c68a15034a2000340f00908168010041110704800f801b080d150050407608407400514089059030002c14100c50249420480440340e80065001100c401c04818113a80403145845140070303041c00c1c81c1c3c03c4007840c880c000404209601309801c002e0b14201407031a007045841120302ca4280c00265044e4080d21a940b1801600a0141c22008482c4416440700803502c151003c1500900607082d1032103090312403858480741210305402544010f202c1c0c540140840070780c0c0d4610006444444010704041e0802801c299164800c007800d10071240551015403607000541e01d4003d0003820340c1d001d40c00145040c40c00030a1240096043c50205070071517034081508140355542c0020070300303060040d4036034a81c1d641061003178014070502140e10743d00d0f001c54406131002a50340f035031401019 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 202228273 1250 202227023 202227029
    0x7080105101404111606060602160605120705130602010606080604020702101d030d090e01060f120c0e060d1d1903120209041b2304090b1201060909020a050a 69
    0x940c24000031201e1502e05030380303d400c0c0018018030326805c041d41080d440a01c081001801c4505c0c0e903840d2803e000294042140c8040a044205280c41c41030928a0040507030140e0303140040d01c0001d0002180c2500d008200b90351900000d40c010898160303442000902810380340c821140843e1601001c02d44d141010300880302d0403030b0060051314021018150444805928408645100800e01d0952103580e50030701040ca4280c86560b50105600d06111411101c501c06a00c500b051006058404d0011600101c803c859180072820000c0c1c10041c0b108282d600c94038190800e603011600245060040300c0c5079000340107a504076488041e030b2903e880c0030b103644c407890900050110405030340c3c40c07c0020b12a5407420350002d005123000d8180307904400030a080d12801040d80040100718014a20707419400104002c010f51480c0e5444060f0110011b4407601e44101c0c0221415a80c075241e240d00b0584411864080300b42400008000045d6a10318400003001194012403003880e00c400300003594540100c1001c10303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 202229523 1250 202228273 202228289
    0x51f05150a290d0b040b0405040209040b15030304090203150d020913060603020d050f2802010e031e0309010e12070512070b04080307030f0305040327080109050708010510 75
    0x1c0203041c10307550700a0314000310707040b8090200b810005042d09010000360101020084000c5040d044103000c100943d60300412041c002c52401c010400569284070090b17030415001154410f44e516a42140958491100d0203103816120000d40020b6034801913006500c02c040705a070b102e110b800f910781003004400c5111b5000e54445018400700340861402000c10050783d00c2100f0020b6619580d60100b600302a03050825981a0005032114410950501c80410700e8010324102d0207040c429070240100700c04110001074100054903051503c0d688042240c4030440c1011044032303004020800f100d6a40c6d07888960f002d80081c10008804555003002107121000104000c0a008641c1c10310050000b6200b078140501514032500400003131615654000f08060202c2b9006545d480c00c0c1c5041c0a4551603e0f49000b0040525200c00c00000ca0740c410400303006003104d034101040e41418050764641c3c040c0c0e90b0b040000503510b09000e179410071400007009812a01908000d0089940e48100281c06104600c51411 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 202230773 1250 202229523 202229539
    0x240801030303050901090c09090b070c120305041a09010506010f0306080709090512070303050f1302090f090f0d170a18121b03030f0b120309010c020409051f0515 71
    0x64020b4104961141c1d04c18000510100103460320003910002d50b01c08900655600074482c14400815886a8000c0180c00c04080b247d40301c2e600c5100040c41c00d140c41e002c269940001c1020000311003124055107910031044015420305201c002c0c02000140ea040340400c42190405001e0303030007806800300720b65103880075099440c6090580000f524a10f042100c1d18002c0403080291140c000002c1d180b524069600051603103001d940c80220300d83d01230070307000c02822280199070060b90b0707540855030f00c4a2459038803812920b9590300350b8900302c13a5a1460340745020b01484000c955601c03c0d2102c0307440c1c00c07441d40207009403103003042801124103545a94500ca003a22565002251222820000410031850104100c1002d4500c0c690005050309088000944620190f0440340c801c2c0160f0000440c00c40350004c80445807000560743c2c0c861020b456043c010000c8110f0259a00e640c000400b00d50400107484268600d00310841400034407400c40a82940b810001c1144000c0002e0034854030000a04140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 202232023 1250 202230773 202230779
    0x30b01091a0c030a020f01050a020f0409020d0e0d050a030b180408070c1e031a0601020c010e03010f0f090b07140a11010f09120e0f0f0409050f1501240801 68
    0x50341c0c1180d000d245210308010802800100000c000510284a079603018020302192409010b00f135590141c0a01e07032882c0148940900014443c0484049030501d10307006a80382d010040325406000111903d201c20300a5181202e4410b82000040454000e950703020442400b80004200707803400d8400c030030140c281841e400a00001d02c840000c041c0c0602890b0301c1d03031030240d0321070050b0380000d109032441c111b07108402010001c001c2900b040c100e5011207201001901c0c50b000000039039034001125014108190180c01c21200d84084d800302c000d111a900c018805500540c00c000302411003504202ea60101040000e03640600c51003011440360150310201e03140c4500100c0c12500f0042c1c05030211150755a035001a400001c0e03600c0742008843c07282003100503410044d40041c081c441481d10090191101407038114160755289085030703110104032000640001c00d414100d103051018007400c5100e00ca5004da203040c1e8407582504a040310004402c1c030320300c0d0b0030600c000e000c2c00c1e040c9914900410310001c014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 202233273 1250 202232023 202232039
    0xd031110020412080f0d020705010c0f080f06010516021203130b0c0303010b03040212010507020601050a0f0e0a020d020c060f0604050612152a0409060504020a090308090102011517060601030b0109 86
    0xc182e840e0105011030309064030340046c10100c1c0d01540b41200d040c0c0d5140356100c07159800c651448038199440c10800b0162400b0724032486000c00050a4604010700000c0c0e00c00c00c40780d4184c00c4482d5a4015100c180c01c0715201407115a268000044084131150000d40040c004500c0c0048600e441d412001850440e46018540000e0fa04007a00480c0d004000061090b508603007485598403802d207170350042085501d08030038072a8440041e0000d45894105100034059107900100503038015160420059582182945040082c01051111940350007100180a07003d03541200440c025401200d040109880341801c1280d41c6101d5031a04d031140c3c0042000303074941c426182980f940548210041c0c8881c050800b80d5049039500a00d0316040c0740d40109092100440c01d108050152900317590071841c000582d08040c0108404c2d1000400041001800da00350741d200b1340009402d034880b00d10300031100b6281d01c840c00c1400d00300b51b1030001ca840b488000641d103620130301803030b0000c01c410385500d8030303180c280024 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 202234523 1250 202233273 202233277
    0xf12031205040320150f070c08030901091205040305010b0303040e0402010c0c050306090a03080f090a02150d050103060207021003150b0c030c1b19051e0f0d03111002041208 76
    0x2c10f405011101104401052014034924845101540074006004120241065000024220040c15000c1c2410068044c3e0031002c070003c60b54000391142e880799a104040f070302503c0c0000d4011302281ca0010810044c94000e0b02600540780314030024021200490107050342da020343c0c0f00d00f00c2c07400c9102c03010502650040300100d01450068a5280500381c90380042440d08605a0341841e82d0340c131011800c01407590181a1139003141e02800680703080d060003064a9601c11102d403004c3e10415618203040400b08d21101111429822580d09000c80c0da5a800d104000f504500c0c3d05a018142ca051800d0b030702803187c880c0d0140850302081209000e400d220f0b1b500d6554009003614030b00d42c1300030080c2000c2c014040003010345032070401038410300c420740c41c8007030100300081e018401b020309141140038401070351026032000a240310300b2003101c0e400740f0b031000140d080c041c001d120310b402141140a15007410340c4280340030b040e9540304088a00f50582e840c40c00c0b040388030718130030350308800b01c0c10803120001011240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 202235773 1250 202234523 202234531
    0x507050f01030b03070b041d0f040308060a03050f070329070e03120d0f0605150d05070903120807021216020d0611040b03150913030804080c12040f12031205 69
    0x900001c0f01c140c210003003450003000b50050001d0700310120302000410444990440807401401019003541807118801900c0e070b401400080901000c40c0001d40307140c842c1200a802140c1050841d40d54200702c640c2652520010300050759144414500844005c440101e041085000c1c006220301c103079200102103a5020104d10301a03818090356420700000702c40900508580030301e80c040014503041e159940c104448241d444240600d08910851b03c205142e6802d07a80c9215072070f0800310b05551000c8044901000c2c6810050049a04644030389441d90300a10030307413183c40190210380c0002c0c0d00340701c0c24209025009000d42d20001056000005003401c02402d20400c5c80780c000400c4606403542d01c556950800d802c0090303502c2e400300030071461504031040c41c0d00600c0282c1d581001030401c0311306a4100c0a103c10054140500800410100b1510340101c031100350b5410141c0380c20040588144406a1043c4a01d00c0c005c0c026280124403145c914088407080f992644400c4030380200701e4515809044018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 202237023 1250 202235773 202235777
    0xa0806061504180f06140d080903071502030a0f0315060c0c0806040516330c05100c1707080f10080d09060237050c0303210a090507050f01 61
    0x101c0001a4002c503a80e40309500d00c4040300110740c69142904d428101e400540c001c0840e0440a000c0c82501e4860301d8407040400e40016000d030340d400885002c45d19213851544400c2d07842c080c0a6003014010350100140407100d040741d41341016110540e0040701034032074800040d40c040601c5103040280c98021411003081300e01c41c0d94046146580d58103128148002200d043d1482c2c1c0007000307460b480305040c045540180810710007080c0207008075003100c405a059003403400741e20080517000fa2310b0103000e00d81023805558030000700c4018a000c0d901c40e0004d04404036005e00801d0301480e40c0c2c811200310180d06489000c2c1655400032560301c4290141c03000c0c1c0040c0c261016508980400b1806800900210211120035103600468500d0817074000d2030100101031200061200d070082158403110703a041852001c901504030300104000c4e083c840d00346500f03400400d078184000190141d65000000c40000d020b034a08410700040e58500200c00103803550710000400c207400441d001c0c0300758580b030298001c0c850018 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 202238273 1250 202237023 202237027
    0x70510031b0905090906090a080a0507050d0e040b0a03020622030c06050a1407050a08030c040e040c08010b010f0f18030605041103010e010e0606060a0c080301060c030e0a08060615 79
    0x1a800700303070301401c4a444400005071103a50600a0f8104031013159008106040200141d20b081180e207922144a286c004185880006543c0308a40c450317004d031820550088291481140004000f40c00c0880100900b8020742c202451031015290481e200b204498020784401e00d0844000c0d4807000d1004440c508000c0d4012122010003c5240180403202404caa5100c442d680c0701c0002c1d002d030000300c008040c2406038100700030100009801140c13854407542c1c8151219140c0c0c445104080141c00303903802603201400c5c000c04100501030707005800c80440c1c44080c020450008840011681221800340d0040490b9405880c10f450901c01d4010f034184284507090110255107940e11401640c0040c5c5040c1d4240c00840400c01540c44c080c410b00500107505002042003048031012503440d0080104641c2c4154800300f0700007000380c06490701c181e44e19031088c0c90350b41d40c2da107860010300f1034201c2d01410b4000902511a1690a0405101500503680034100038022070b40c42c00304000403200c80003401707075841d001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 202239523 1250 202238273 202238291
    0xf03041704080c0913030203070213020f0d0f0b0103060e011e030209160f0503010f030312020c010903050c070504020f070f021923040c0807082e030b100807051003 72
    0x400d0040c0c0007034401a400b9149a60a4108100c400f20f405031042d100038819100d0580026000412185000e5060b5000170700b805003803907200d009008050b10710b5440240020740c6030051409a0100c1d03003111004008110056003500110110703101d50080882c1850180014440703483c000d4090006080383d0180c0503102030700e950210300850000c0d06c5180e0001d4050503505650f40c1c0204901c4101210303890002c2c00e540c50040d100000100512010b4240a03400b2180302203801c00b50103c9500c0241c040003030100401c14603004003141d00c070110410701806544800720f25494070b07000302c5244110140c425400e00d101a1120711040900440032a071000700001c48403c1d01c60280d00240040c00c5006d821a090701e003071a02901c145400c041d04600c690724242d04c01303001c940c010040e00d030070540798078081c0019604c000f504030300d10840041c0a0811000e45559003405a100030f8241c054078442c1c1d1800030300740c80f06000c211030015035003d4210503804c4000c4c03c0c405070501e200103240300300703480c907010414142d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 202240773 1250 202239523 202239563
    0x219050d060929010c0305030c09041b05040f060c0f0b06130908190201020c1e121c0b010302070c0e060a030803040b0402030f0303040c0620030313030f0f02030f0304 73
    0x164090b080e5500c1411400040c001043d0351149102c084013800c01c2903514040d950300401d03d01c0300425a584408010500d10f5003510360341d01c125003890000c6407541d1030920a01000d40107400911800740b00c1c10341c810001c0f94251140a0344410281e00404004402c0c2959441c08420b9800410312f0340c10480d1101e03002c000c0800c500602000500480c4090341d94892101300482c00c000191050007560700411142400150014100c40000c3c002d442c040c00c5800d141c0c4090b42042d1800385040d45000011601034035000d241441d5620070a00400100207210714230700117400303034040c181028010840411080080c02c1d061200c4a50080000f0500344e00c15490790b540c05000e40080c2d0b01505c096a26100304000c60504024190803609440000c508501c0c2c0f954030725800c0c40103030261008015070700c01020080108818410417140009003641d45034a448181280c0a82c1004010b03000030b00031100c00300101e4000c50340e001c00c071051a805145414143d4400d64242e5101a004035221540d490712001500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 202242023 1250 202240773 202240781
    0x3020c0115050f0d0201050d020304020a180c0905012f010b030a0308100e0c07082203060902030d0809030409050606070209040302031222061503021504030309090219050d0609 77
    0x80300d2090741d14580d40c1050280101e02000301c0e2500d020384480c25041c0d000d43e801c40180c2e14125801c8901680c4ca50702d0b4400b198030004c00b50311880200780113804042c004c103100d4014100c007000300e55900c440107585000440d071000d040450164039881c3c002e2160583c07030030882c944000034803540c000315214001d000031a1401044010a800050100081c068114902c55a1000800c1a0110110ba9007402074050b8558850944014403402c400070349160090966064281600581130135480e85c103589040803400b0301041c80b0101c0c8240540d4404e8020076002d44089400307444000001c1d130074030781080000001404058070030f56002c0320601184005a480c41040c0780316a119074007550300d640072101400f4002c00013610100300c49025541400c145145100b040b0140303500b02a010622200041210882c070126400107500b00da1700e4140b01d00e8070036400c4000c2044034401c1d902c02c06201d03a80e0508800301c1c0103070b20020101c50035041c90b1240c650310410141a04c510418400103a0359540e154441c119 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 202243273 1250 202242023 202242041
    0xf030705210c040303090f080c0d031812060c08040b0619081e120708030a0504060e0609011b0201060302100c150f0f0c080603060a0e010e25051503011503020c01 71
    0x1040000406008246d400420100104456815401440d08150101d41c44100ca140034a010b800000035540900d0301c98002d108212320107448404076103490f42515418070a0b00c01c001d0380c402d8100324502c894a44200544c0d031065030494034110380c9441d45000c100c01d80c500c0707400000b171000c803584010070251030921462003003140740c4845014032500305114608084400c18225603075034091110402066003502103d9000c403c030000040c0d0f03565076141100040c0204071114034648113010400540701015800320200000150840204070927a1808134245d942038000250031030780c61508510420f018000860f4400e11521905801c448401006812110b864011380d41e16511982c02840c080450300c620141d000f1603103803540c031303a14141010a60f5200d01030280302c2d03900c4d56054004101c403000e41c095051015804195548003084810381032000b055841c0c841803500c4603010001d05071030b04c2401c01040030701d04600c060445c0e21b017a09007062141e10011302030925800b0402e004103044c3c02e110b42d10b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 202244523 1250 202243273 202243291
    0x709050f0301020d02130e0702070602120d090f0507080c0406050d080d0e1005010f050405010305190510090b01170613030f02010b100c0309090203090c060f070c12060e030f03070521 80
    0x2c1e01d14015003408007c001410702e10a54014000038031801d41e0200300844001200201c842e901c800c0c8c814071200070050b100d0301501c410071041c02d00c0d08003c00030440004841942e0f04450350f103640070041004807a10f62148a6000651541e01d400085000016000c07090030144002101142d0300755180c1003134003c2d10b2901403241c1c1c40006221000301081d4503009040162070400c91981161340b010380c1d071440f03c4040307000704081e800c0306810010100b22540e6814440c600c140001161454074840c2c05200f8020035180d6406a0300908045030700082040c444d134603401d245ca40d0300341140c44c00d4401a10f0854a035045540302c0191a0141d12a003080301c2c2194800d5440810300c28407406c0c0100720b09615040b81c40242d00400500007200750004003000c08882c01c541981e074543c0c812003440c84612901c6802040c406500b05e00140c1e1803029000309052030700031078040c41404040380d0825103038450b460b1152038035401440450030030340c8140040d12030501c00901c070080002000e050300d1070700c3d002107070766802c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 202245773 1250 202244523 202244557
    0x3050703050601120308011e0504020a05120108010902030a150b060a08180d0f050c01090b0a021b0c0105040303030b030a02030a150c0801080606040e07090f020415080709050f0301020d02 82
    0x104029040000c240101808200940602c05a179002804074506129a9a803003400340700c000311041c0b00090760001090000e004650b22002c245001d0310540104200300c0b0000d544c0e200004821178103020b1900d00c5907000713024000b110071950300e040d13101e4406030300a4140365840c51240340646a1030000d24008005444411603440c2c0481c9101c4201d8041082c81840e41103035a280414a81144a440071445941801525504120440b0340181110700300909604107490510003001400d03402403540407001d18030030ac0c244400890300e40d41c403803e84000382e000840812041022034131903130200280500c02410317101c03c1100741d00000d20300112040183c600c0c094001c05030407070045910581100d0351250828408561400450700d48814000300101e001c1c5840c0c1c41e40060b210030521110000e030032501030400140da654256800290028002e50220200d4107001245071801003000d00d1003045282d65400c07450f403c003001e012010120351144c642543d001d00c04540c41c01c5081c0080c041d415040c8170410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 202247023 1250 202245773 202245779
    0xc0305040c05190b0d15170d0809150414030705070906170a230f0304090606080906061212181e06030a05090a080a050a0e01030c2a0c030507 62
    0x1480d8038801d03a000d81d2007810340700b40c083c4450410416580c00c0710903100b0801d4403015020018005040460000c00c80c002c442000840e048a40c000134198641d00201141c2911181d10016100840140d840c0a8240d0008615100103030302c0c4208140d1042c45400710024600315041c7e4185140c01081d0211031580200d2414040502688541c2005100b412510b416503004038045030744980200301c01038420741b035429403040c0f00a07030700c400c1e00e8007035034510225440ca40320800b107292660402e0085a0060b0700b8400c00152280c8501350305801010ba1801800080e01d500c001c0003803640a401ca40340351809547c1002c030380c882c004c201900c1084450702c55280142c090300104940303402203404904030702c03100c0c2d010103085480f0700040e01d0380600c59000001d040e131520070300b041c5012660a0007c00110000030f19002080d40140642641462601c4055003808014010740654601a007a03c00103501c40f80151803c6000740812400907901c00500c009845d4a91220f6404580c43e070000d0f901a803040d0300030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 202248273 1250 202247023 202247033
    0x19050d0e04150513110406090801110403170c070b0d090309050a060f11030405060301090b040f0b010e010311040902030a0617030403020109050906011716110f0304150507060c030504 80
    0x110312010112001c00c40000032014010080c2c4683c001c280c00307030144104101c2844450740c0f0042e84125409101e9890f265100070003000710341180103a02c255401c01007048104041e060554054980c00030110748000e040031202a055040008000d1003481201d2001401d6800000180000c1c09804c4021892004a04004c0c11301314550344102c0c05000003841c10004154060b5024800c0006403519032444200c0c00040e80c03841c015070f00072a031700002c00000000c440d046680542c004004c10b8030300348400c1c4100c851603021600210445400300b010700d1010300c2198803e901a985454000d10440d0800b40c44a11000c00c981084401e051402d43d42c260601116032400b441d56141c8014000461800341540d000038012141d038403555005c0c0c150b51000c14150303801008840c5070110204520392062901c4c00480c0c00b000e00ba000100c0100e10704a038018812000031481d03228070121180118500f5141c4007a00351000c00d1105500100101805102c0c00119980540c1c078034603200d5a40425030341464101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 202249523 1250 202248273 202248287
    0xb0c030a181b0501020715050c1204090f0e0c10050a02010603050a0f14030412020607020402090d0f06062c0402010c1704030501110403031b0c0906030804140103050708010e040519050d 81
    0x3c0355043d0741c00040108400807000da50b400444616203851764a03074101d022424505140800e0203907e851002c1004602c44183e0f600c80c803d000e410f03407800e02c861001007400310303120b002c101c0d60160080185105461b0060090f4010100c0701a544000121169039481303841c20840452022201180303405050003d014038203482840325030380e40c00074618291a040d500b00407221081e400900440010910350705562740e81d170607282c4803900500440b00640d07062070006800307040b82c1d0701120a41e1900e02d000ca0484001e000446640c068240b407220310402001c0c0c0c402034284002c1c000c134108200c0c40504400030742156511540405c2ca0048107407658118038055003554900138000c49441020b0108101107513204c40c42e01d66504050760081c0907000340f801c220b60441d495400541132a0b0501e0400020481801c008104981f10948028417400e02c030303c011002d5882c00d07219400010b20310030041c4000d4046440c441e40043c814001c844c1744d9140780c038101070218110901078910b600110301d202c00c41030704144 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 202250773 1250 202249523 202249529
    0x4080f0d020d08130611040602100c08060f040f020c0f240c070213060f120b01050a03240e0d08010e16050307030c030204170a02010f08040b0c030a181b 67
    0x41c1c074106001a20080c0000c2c0b006000c0c8010160030400a001e200c40ca82c40440b91b119103541c00746e075844e21040040c0d07440300e00319900d1704041e02d49080c0c2d404040c40348113414043d02006048212000407001000042c20001d4108007111342d00b04018441c1641c10001c03130f0176540c1042d018014109090018018107c0c61480c00c41e5032520744406c0010080101c0e044541469040389d048000e2900d180900004080c43d0300003121914107031030040350000034a81c151b86140d1041c540c100840e0f80307440a1180045c00d5100007054400040450b4101d0130305004407140c40f804000f0002901401010b00700e1401c2200c1c0780c0600840c1001005001032103604540d26407107030302c801180200d80d4904400900c0c5204c0108108101941e0301c02ca0400ca51190701160010710105442c08181c407000119a6280d080100c0b00700c0c0801c0c0383e5669524440d01a040c003912550b042218010140c2e601c41d4000e100750f1006117007484560740d481d5040d219400c061080b0b01c0090050103424100c8440d9030300d000001030160 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 202252023 1250 202250773 202250777
    0x50c0d0f090f0f06081905010e0a1514010e1f03020d0c030b33040803042103020309040207060f0519050114060316020a0f0302010b09010f0b03072304080f0d 69
    0x14001c2c0603010340040305408032400b500e07103043d09640c0c00501691207940c61b40d94201050402c00001030001d080c01c8840e02400181100700000c04031100c1c8500d850f40c1c107206011040c0c03140d1013901e00540c05201940404c12018141c40c0c01102e84410500030314115500c00400300e980842c0e5840c0301c0c07803170f44140103000001d81002c01155100100196404201c1e5030129060800ca450b1072203015010184501400d0030120f005864640320364115480b074110740241540c1d2003980390380d4600854201103000394250150003940c5001e66510620005e0740c00400c090700c03059100d98929a50192600c11f482c8143c849140d149400f0103980390320700668030f06030712510018030469004c00ca03079030307800c41220b4100310704100d94000d0b5455294142c0c1000fa880354050f050801c100328110034590103401003003826030121106e8449a0f21035035001c1d001181400344240c00c000c00d20001e10002d0160a0000031441c40c241c11415010441d40100348507445600840c4581d000341d104640903500801143d40465864 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 202253273 1250 202252023 202252049
    0xc0303160f0c0506040f0503040521011406010f0503090c060c0d020111090f040b030106030807150b010804080f0306240901021504020321160308090f01140a0c050c0d0f09 75
    0xa03142c066590b603000d017019004e2a1000c0d40e410402c0340400841d00140b10243c22140c05150010400310500c007103440b04902e9509041110903d000e0801c11180300c0c8505844444040129280071682c50704020114091032007503a0410803941c0c0c5850251004008110007004100c000500017802e450101c06114500e04042c846800c05a840f80c14114103640c0666002030504540c00000307001d000282c3c03001d00b40d4400001c04605214460001005005540c0400d02500e101ca20045880b01c4c0d084401a244007018804400303c00343c50402150000320040100c403140f4401095086002e0340708503049118200010382c103e107941c050204070b4841c070001030201a80d2900b900803039100d045048064962200c00c2052060b548480c100f594414007401d185043c01074094900a0147c40095501c20900d11030300220403075a180500480d940301d414203015501d66140c2a00c04005001c42c082e012080c04001c2c450000303143c0d41005550030382c40c000e5842e1030989a1119000d44450740ad81c120142082c51 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 202254523 1250 202253273 202253297
    0x40f150f02070e19090b0f100b091309110916030e0708030d05040309030605010e0402010912023a0804090e0703050307110a05060a030f050a09050c090604020c0303160f 74
    0x1543c60055100040203001ca0b20260303603520100040c911090010030748110752003400340f42c40d1200c030340601c51b0f85072481e100d40d155114061120303e40034001c051a400350740c03030004600240c95604050101d83c4124014410541d1000014040c10411540c1080041c290110904c000e6490b001e030541070401d10b009841110309280210b40c6070301c11280303081221522000441c01b01441612040c0c01560868000c006558490750110301c034000c103070390990010740d0319440490007620003440154172641c010410b09c10b8101398101d40694102000112091807a420902000e030010030340c80040f490b00c9640516921402c0c40300200c21200f5544001d022940949410b00004d0800002c840301aa00300c1012900b416007000080c4070300c801c076002107410100c0481c03e410f0307080c0c168001c4c403107001c803001003840250382e449070040485085182c040c00b254002d198903d840d0038400030f07803600103101a2015250281042c0780b50300d964070603910042c00c201000144282c2c103900c80340030780c414041403400c400c0000e6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 202255773 1250 202254523 202254539
    0xc0607120b1e1e030a060902030d050a0503041106090d030507060e03130306020c100e06060906041509020912060f040519110103020307020c0415030b16050f0c03040f150f0207 77
    0x540710a164054595000688035040c02c54005410030743c8000c04171060344000349425405416034820480c040e10828600144c00c50040b8203030b6140c0401a50742138150754440d183e902a10001d5218290052800c000188450b10344504010126009032170b0365590b004a03140040499505494000b080d070800d000704011189650380711012250411005600c0d58071000201b800c000120b83d40794016440e00c1c0100c4009003000c9040c81c400e00c0215182da4180d5600b00a10085d564491026603911103c40f2040c88060255070140c00c0141e00a0304040c1c03d201481070f100d15040094507001d50b4003840c00100300c2042420000d040c0018004135001009070701c50340d20880d02e5200c1041c0181815004000103501e81e1003040066810040244180651642c101c1c02404002460000307503500c1d85203000180010248c030107400e0030081c0c1035480c80d1900c525500c180d000c40d0130002004095020400c00019200d505d003801e031000d41560729196111098440001d00406d84a047d0355003550807440d4100036040b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 202257023 1250 202255773 202255819
    0x250308040b0901060b0313050c0121022b021917010303032304031d010309050309060901050412080a1101051e0a020c010f0606090e13030c080c0607120b 67
    0x81e900c03100480e0503880d000066409480150420500940c0203c00c1000d442c0c001c004480e080c84c0203002341c456007007044004648140058410860390700c00031030b40c00c241c0c5440398000e040d40e480608a04902e560802c3c0d81c0c10341d000440c0c80b10070300a034000c10103445140501180300318141c00b9003071105154403800f0003266a000144005801e1654410b0b00260b1140e80c0c1c10031000078200f031040002c01c0e1410746000b42140c803a0380c911009030440381a8144855000e88100400641c0040c000c0d404c14044104000450b48540800f40c1044000e200029400c0c43c01c0d4800210342e80b090034020b4030b07001040300c003c1220b8041000050b29a04050a21034280140c585c0c00410b100c5400f44500300d55283c0e003c130000713032140c0500c02c40f49602c0c4c0012142140e81662160f070035074099994003403080d030b40c0711010781102c03100351140d103050601e040c070800000340079030020020188120324990400c2c0c140d0505500f401030488460002c600d10b40a00e995042e4507110381c22b03800f801101c0f010084d04147c40340203420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 202258273 1250 202257023 202257031
    0x10608071e05070b0702160b04030209011707030804080109021e060306040906022203021503070912050c1e040e01050106020a03080a0e0a0c03060c0504050f040b01030e070605250308 80
    0x8441d0404411000e10310800459144a800580424940c01d085a00941d201c00b00c0381f14054503c40040c011401c7c070082c0c0c048400300c03034005000036050703403d00c0b4221190031107100c0c030900355104035040000000c900c2c1c0003900042c07601030000946240c0ba80140f0001c400c01d90358600815500c1d01280c040e44d901c0348123503034014a094400141100c114034169000b84280000c8124607001c68410400000503402100c050300d20a4400b8404250600740482040c0011380d10758022950035102030011100401070300410a00070411155505024000328035450007245091117407208000c1c1c02c2c41d075030510380608800161000002c004540c07401900a445000c01c003801410046108007054404515402401c0031241d2503043d640002d00303501d01032208001303511044600a04240490303040d00d000340113031000c0703801c007a003580040740b000c00410005001d0035841ca8103155840c144611046420054407018213200c0c2c0301c00799500e01107c0c00d0341c624103040d04004050701d01d00e0740c4440000d500200b00380e00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 202259523 1250 202258273 202258307
    0x10509100503060d020604080a050114060109050111030919061e0f050a0e041103040210030203010e1305030d05072102160b0c04030b070509010912020916030b04020c0a0b01060807 79
    0xc03034607443c000403021600c1c0d0b4006540080c02141c085074000740426000c50480c81035008011a02070704c4d00320b1100040c22a1710b035000c15018041004954014204180a102c5000a40b07140c90301c5540002e021201155101d0061078642105228143d000082030414080707241d48038181e0346141c4401000c2c41c2c8280803100802401241107503019001314515260fa000080080c003882030140c0c1d507042942c0003194140e2151000000020a650107407013202d041c2c44800071110340c1682c481480281b420309440d01155244010024604800080e224490148079147c0d10b100c6010800412007840e480704050603200d0274810407514101481d0788015501e82540020701c0c0000340e032200546803260082e5440544203541140c10400303843d900c000104003204098a42007111a1541208075481c1d00030300c00250020f400e500440d800903030407034054144c0031340b510300801c0026200c80400c0903a00400203041c210390184444030100140c00f40202c2c050301e59450000301c58039221000501a01002d009001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 202260773 1250 202259523 202259527
    0xe090d0e0102101e0501050a03050a0b070c060e0a030806060f030a0f060b04080c040f0501061d0406081b04060e0c04120302070e0c0306180106020c040b0f0a080d0e0105091005 77
    0x52240d0092004070380003c500c9008000081d0034500d880b80c540310b2520091030083c5420000704e800d2800481ca00140d80d0060000c0c0000318565550311040c00015000805000c00c40300c040c0002502402000c200700c0410025040a00c40d07840c01610900010b0709079480390740309010b070b5484e0b01c4600d0207407544000c90001c0864001d2480c022407004000b039400c402d60501000602081c03071100000c400c410150141c404000e0710240000321400c5030428010705d4001120545c0f0300d03030100041040c803c0300c2c0800400000d4070f80e036540d40c01c80c903104038815800d407601032190b2142d655241034822803005002c0346045204902d0440e804945070310a60107110b40e200701d8841d4140034107208010150141030410910708143c00c0c1101c41c0002600100c41e610322030301c803400e58048a02c03485a1694129021034000300344080d0320720204000307803c41d04400303600f00300021800051035135000d40c00001001001d01500c41441483c10050804e82c688806505020007040040e40c562078501c003401269500b8a4425 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 202262023 1250 202260773 202260797
    0x7080c09040b0f102c06090d1a01080c09090613120306030c060e13110405061e0a270308030601030903030e07061808070302130903120f0507090e090d 66
    0x11240300010583c5a0403c0e10101c541d01210f0700540301144a041c0e44030741841700c1184c003d60080126070798050b0fa4000400f40700c0c074001424034045a088240c40781031480740c074549644290b004032100341d004450680c464100c5001c41d00b412603c41341c0240d03200020f0003031031030125110400350300040c4006200c80e2482e112001c00520a80c04840503507403004260540e140c0d03840d001000c841003c22810720903803888040d4804081148566101d5060240c040340c01c103403a0500300800703500b124602c070100e0140101c0b48800242e01c18001c02c54250300e5211180d03404c0c00c1a000c0840845420030312010b00c800d814061021034180015640e022209113400300380d00d003680c42e040740a8079802508004901c600d000129443e43c00c2041e51480c294160082d40c003656443d01030f00d0f0f49074020710005e5000103180d21100d020b00e00f0342c4c102d62540790203810442c07124085190385404544e0091070f0300041b103a6170024014015403203a0844010034001c06243d4032400c1c640724854840e10800d40d0041807007900a410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 202263273 1250 202262023 202262029
    0x100302120f06011d0c0705070b0a02030904180303061208040504020d09050a03020f160b0f07020a1a04140405040209070c1b0e180304150f0302120411010807080c09040b 74
    0x207032403060344010554005507521324a288103206280c01454000e28514001007101000c40180c40c9001d80000c000d048035454030b280004e060340025009403c500040008400030307100d5020300c4403076841511117800001a1820000e0440e9081d030030078050001d450f414100818090030965080d500121801a510006541d4000007800d0310b1100511500511100b6000e2580106000800000150560f00282c0c0c9031848013507100603602078620b0014092046100043d145805800006d1001c0c00081001d038440c100c0041184a519021002a80016043c454641001c000c40081c4006690501c49030900750b0004a0240300189070b64100034124440409108120740b416007240ea12030340f01b1004a80764001d07804101c808459024100c05d1a034080f4903048000411102100e08651040411031102a011940a841400c500e01056001e006460740e080001e4452409144038042910011841c80009818013100825240a0009a20800c884075010000b00c4800307800031100040d6081c090000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 202264523 1250 202263273 202263283
    0x51615020409110a14270604030812070e2205090109230f060105090f071e03090302060a1103010b0702030319171605071e15020a090b0310030212 64
    0x104000e014100030f000b010007900d980080c420070841d566506520340a0315483c41451003041821680180b07100c441c40e0b4840c04000e403414075110001e03c220300e450f40d40c1e207813141075400050b10070072a50f1041c41440506600b0914254042000f540e401544040b03c1c55404e40800d0015040109192107400040d0802406c1d4415081950f03c030204d007100c1904404040c036011040300801005114140c0341681c420400541e0380e0486000803c4004030313941d0440041c050100c06031201d000c0c440c840b890150840f81e003800d102840c881e02c0c3e8001500d091241402803401c030b4081d1101400c1458400c540c04007200c0f031001c0381d064880d024807031030340c5580d2440401e19512460f40305440d41c0703048020388600c10368040d44060f2207152141001059031a801d000001c25098000d201c1e003c80c804000840024801e522a1840c4c6440d0000c04001421540c840504010382d08d8807442c1c10720343c0012100f00c0300b60095121405820514003450a628128403061000a540e01000c1d110f00e1002400c2c0e1905407080003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 202265773 1250 202264523 202264529
    0x30603010207141f050f0c090a030b0f04060515030c040b010504080a2303030f060d1406090a050d18120602041805090723010f11031b07060516150204 66
    0x40e5a0f200b018040303400e1512404d070b81880361324024076482016095403a90103914010307000b203011000291030f4082114200d91141c1c1032903800c24082c50001000c45c4444121922407603264198407414035042c07801d40c0461b0801040c0d911301210001d540304668400044c0040071607025140064050100785c0140c0305070141c2d81c001070141c410000d040b0100030a03a40c027204000e00d80d882c41c0c01220700811403151280001c1360214000e440c800300241e03451504080f070340380d0140104a10310021407040714843c1882000c540d50040c503881200c504003040000c01c60709008200901e45515200304c9210b80c003603038811034441c80c910b940e0304020300024803480380d0403280103020100000302c141501b0300098002c1d04084402018900681c600001c200750b5100148200300310312705807110801a140e005543d203007400305800007007109000c3c3d600800f00041006149080b581c1d244a180d84200900807460031490b500103008000091100301c22484124100c00704066020781040b142401e41c8880c40000d00442e4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 202267023 1250 202265773 202265783
    0x6231302060d1109030d030c050f1309050c18010f0903060f02190f0201140f060409140d02070504050603070308071707050d08040501051b0a050904290a060c0314030603010207 77
    0x80b203d100d00c0601c2c9030081a0f04c40303050b0292150741c0c00e40c000c15400c54003003881c4480807441c1000b44841030540e0000400d00300041e11149482a503e60425004a07a403c81e4140000d5034005102c400c1e141075901000d240840910b407203601c1c41d1140400401030035562000410b0251074944c20100c8408540584002c48440ca50001c200c1d0b40e41040204010112101c85026520b0b003070050440e6244020920301c55800b02d140e460840e01c0c0c074800d0000610306003100b501e02246800d1440c041032014048803103180c644c1d03401001d015040a04110480c0c0d0003525491107036100e003400704005500304050342d55207604501402d151000c50030100c0428400d1000081440c0202080c4090064001c0d104d1401107000318000c000580e200602c49081e10000b00702001d885600f40900d07091140702e40001e02001c20f0181c000b040041c40c0800060410321815501c103a02060b09001c48414203002038008010441c3d072404852004c2070f9140549612040440080002400000a01c0b56107013501100c400503844 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 202268273 1250 202267023 202267031
    0x3140f04090e03030708010f05091602010b040504060b10020102090916021e0607120c091404140a0603020102190b0604051005090405210a050f0310030506040f06231302060d 76
    0x102c58054072540f04840c0400031507449800420403400350100b020030341d94007912149407511005900380441da200485a001c42d900d404900d521629980103031400b40d0300c00c100103da401541e004024a100202c0000d40c210ba1050014600f980d40b40e401041c2c002c0c400d0a5941041644180101d080c100700340e110101c04943c07502c20400301070000076018402c0b0901c2ea201c0301401d000c0c81007030080d14840207070900003a484103005e10400081b250310700305460000380700003265007840c1038291070010202c0700781c44042c0c0d03101000c00940d60140400010008000c00402c102d15440c0d840040720350025050300c1c0150354401c0080c941000220182025000081c82007685142c507262503a5038080d110704809100b0004405155582141026108601110386a4508041c603226808159400052441e602e054180c0c1000011545c10322615004d203001e1540c05812800ca400c00c6410f45041d0004c0c60146c103044440d003021070030360802d41600700c03203081c041d0403004155000040b540c0c0650784080845601d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 202269523 1250 202268273 202268291
    0x6060313020a0e04050705120a1419050a05060f0103031b0305040b0d020c010b060903120c0c041143151d070509070e060f0705010614190303140f0409 66
    0x184201441341e4803c000721000c2a442c1c1007440801c20031011007142580c0301d0302d0100001030030f40034404041b8510740e0031281030641341c409101c85409080011b40d01c682001510b1414480305100b02d0764040c440900745980340d4590351b4020700100c0d0040394500000041c44c0c0800030144a40d0803174000704100512035840301c01d0a2507100080d07106500307050441d072074580d02030200d0424005031655120001d0141600c0701c07252908110540c400c840300401801880005806541c07076100c1c10000e4240b4203216519103401d0f0043c080120006050080100d80c5151400502c00342d4403d0828030704418600c440e1820030301d14115240c00001210004004d0420380307801a540c7d0f149041501404400b01141d00c010b680c1c0c0180200302a041d03c00c00c0005031000c80000c9035090020080210520060400d80750120946500f0b00710b03001a080310383c3c08890a58011102d00e00240c00c1000d418500d105490f000e4030750354010b8030784a5101d16200ba810f0020440c0c20400c81c60100b81c0300106201d900170b100e40e0301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 202270773 1250 202269523 202269539
    0x301060801150206190905070308130e09060603030a030b010203090414160c0c0510020a080304050c0103050a0b1315090204080303250e0d0c031202010605121506060313020a 76
    0x3000d0095000c0c40c0e60055056a0729840000c030716002e80d0b0101c2440c1420601c000e10b20000c1c0035004401d81e07252183e5840080081c909400910360301c1840040310740018144001000103260240820740154070101c284042542c002c0211910f5219078280000c440380c200e001070b4194000c400b40d5990040c90064202c08100012032040c0c450f0316001ca1240c01290011740540f2000001040903260341642082440785090080044900014600441d5490b0040e90354860036076000b11011940d940000c41450322035601401440c0d001400700300103102c150403240c003250b0000c8185021800450b118141c0c01c4008040200402c06005000700a40d45da584490a040e40e95105a589070044240303080c14081c500c1c0440f0609010b1010707662051320315101d10081109200e11120160740d001c07100c410003c0090b824002c03440090701c103a0004281a40b51030100400341502403120305503070f00310340300050403001c025001a0b4440c0040b50910703100e8584058003d000811580c000f500302440c2e20303021540c1d103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 202272023 1250 202270773 202270787
    0x81311060d0e06070f0905040908120c070506090c040b06090306150f0307030c05100302070507030326010e0f010801060807050411090303070c0918112101060b0a1d010c080f0f030106 80
    0xb42c660711410709a03560342090208270f40e0040000351a20b03009000e81000032002d118004e03003294850542c2401c0c07010301e443d07140c1050317020784e2201416404025180c910341014001c00795843c07021032b801410080d5182c040b0381c90b000010b0440e00d41550301e50b101d1000f80d5400316480814403000c1c00311841e8645074545900540001d001e500c3c42a8241c0721101c448034400c2c001c48803030039802406040c00c20725640e82aa0081c00e400302001210011702c80105800c2c1e098095140207100030540700c409410906241c1959003810f03002025580d05003141440002c03800241041103800039200001d0481000c0c1d030400341d40c0118000150305001c0015408148948408000c06849060000b00a9039107110110103a40c2484a4000c7c102640800d02c00307120b203042034007091180013401780340444510000c142c908403007982c1c201c03051809020441441d429400b2000500c2013003003418070201c000c60000080c0c40103100075801009040c0000385086000606400c0e912103582e0030f80010303240e50b11040c0103010b403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 202273273 1250 202272023 202272047
    0x209100e07020f06150609010c08041206020432010f05041509051908060109180609141509210c06070203091206100b090d051c081311060d0e0607 64
    0xc1c4030718004179800319620002d600500c90010300103407428050708010b41d18110307552425521360b1014480000c070488108120781403103210302001607070f8a040c90078109081000c203014040d20051180008202d0035100b560582c1c01c00309003026000070503c424101c0f110302c41c80d00910b1000c1002e045c4203007600d800891010a4560887c0c080022003006051300000d021076100303c4c0c04550080004004401ca00d41c00604285141c1c0a1194007005c262604403d55600050440c2c800f23541400741c01101c0340a01101454413840003141c009030405496882c1d540d130f0300b45184e83c0050b202d0942d01e0041d4a201040300c0b0050a0482594494a40484e000e5203136004100903d010317081d001d07500c20030340102254003407064401191001d60582001c12902068110b85006a00104202c0501d03022440030010844044481400b40001c50003401e4010103a120240c49102e100c8080702d0303098002051010300d40341c101c1040d200561149501d030880307800741c134001142c160580140018401c0b01a4483d10507011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 202274523 1250 202273273 202273303
    0x4090c09050105060313060b0d02030313090501090e03091c1a100f030822081f0b030d1704060f0507020307020306010803031303050f0f21090303070c0209100e0702 72
    0x346a0341c580500131148021106a454816401c0c112000a2803a41c002010200081e000b0301c0f54841613404249980e200301c185551000034141c0402815a482c040c403030241c01c4500013031200c4070000a00555900450400b284182c201d21400e01c100034204669544046c0c11500200207075450b10b03800d801005050b02e0012000e9800340c0b0101d103d24a81d2030301c0049035409002a40340c4115110f50102e803841c1000a0110b000d4400c03800220f00208000d61311804000b03080210883d5442c2040004039200c0103070b92406604002046040d0704d0704402d4200001a40040000c91a6264a4980300030004a40707004c0c036aa103860103020310140d000014005c88c038030a0b004c945003644c0303900e0990760b00c1c00101c40002d42176032498400800a8816009080d00055a03440107081681504000c1c0141c8c10211540319001c901c2d000503441007170000d00268210881c100910b00d117080400e0700030540d211001000c0e00510f9500041050035200d5145200208500d02d43d4101c3c03801c0c104002500c900300030141d150 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 202275773 1250 202274523 202274531
    0x61206060b030403050904091401050703020a110a021f030209030601030309090c0206040b0705090613080a120903020604091e06230118060f110f030909010806040f11040b04090c09 79
    0x180500c600d2048a0043e609a100d540c201085032040001a21b003514084404c280491051100071009002c0d041c020702582d01d000d61030380408078005100710542c1400f100d096010f80c104034003607299900000c201a0641c0b41c030f4011170035140e2054001e40308a80c007007509445120000001d041d8004420704c252050b4103000c1c0700d40289003004a94441c0280c0340940a100e494000c142110301800090461374006001d85040c003000645003913058109034400c20380c139000380d200c400c2003010a0340c120049030203e0408006050558001c9102e9000d94058a074041d96501da81c4805d0700c00441c4d0340070481240420500c0a151141000a0040401c040c0840c00d42c41c00c122030001d45d801942202c074070301c00d00e070700b91800305261010817519482100921000d0207000501042100f00038003000c05620501c0307005540c0c0f542c80e50103010402e401640141c003d60003903c140300008045505062500341c0005030100da00360b01c8000140104641c18440768041e15046d44041089050f01aa000711108194100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 202277023 1250 202275773 202275779
    0x40b0606030405070608071808010b120d050f0310050405191d150720070f0617150301060f1707060302040303020a06150b03010306021b010b0d110f0406120606 70
    0x1184a00080d40c00904a13005018144a01e500c80d8103500c0c1d001c015494141c02204c41c50740c0c0c07034900751030075009120340383d4680c0601c400b54104480420a8480044020241040202c10040c030500840780c0941c088507000000c04e107403590070b02010001d014000c0c020800c1b0b0a0502d2440381c05e407001e9403000d80c0c2504050241d804207049000398480c016080000e403503009085540c01e01c0700500100400c091240c0101011500c081030a021000d07520000002c104060800d00840b54032480341c1c0c015070800c00214003c20700000a43c05443d00801101c00154190304460000390142c00642c0104442026404000900074005092090402c0300c01094681044e12001d08030207a03c6907010140240e0710000d1418005492580603500800d07403200109a8a602c1e400d400400d03500a92090f1112500402c100350000010b40c5940000920903008000f0304000a01050a5206020000d4508070101c1e40714070007501d44030141c2444480007030080081d981c0702c070445446101d001000342d59240c5000c0000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 202278273 1250 202277023 202277029
    0x3091002010b06040605030c070506100e0a05060a1214060a1a100215091c030911031c050c0106080f03130b031e060102030702100f0e15030c030705040f0e040b06 71
    0x2d00848240984414a040d0800c81d003a1450362000e444d5104140f82001040d010680030321501c0e0091081085040c9c2c0d10380340a40c030034500c64000e44400c2c8040d2030181030150a68440781c03d901250010300e02c2c1c6440e2086030030314030307611040482111018003c00c810003030005519030000544941900340c001c00407410209024035001e0100c0702c880980d0103103100e20141014640030643c000648401c4407000507009490711544001c2c000d9240109445600d11420031130340104c0d60170380d0b900540c0101103801c085c603409003410340744500440034810001404da110500a40011000d81420022a0340c8401036203101503583d48403c05c40a410140e0907404501002850f04403405501c0c0b00e480040351080b02141300031652800b40000e4158401000010300603200c14100f41d110101540780c005060141e0000504001d10007607060b40300f0003000c1e0819205203081c070705481d0801e040d03013402c0b5101d03030710b1035016140c80c0300b1504200c40f03400b0307184800500550a41c481ea48664450f26002d20a5103030359041c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 202279523 1250 202278273 202278281
    0x1703120a0e190503090906150c06060103181109060a0302150403260405150d050414010e0102070305070803071803081806091e04021309060e070f0f0305270309100201 73
    0x83c610307002049130303020170303e82a15200d4000d00014480d24003200c06200400403070344010040380d80d0303400c040100005580c0620076244021030701100f0b2080b4091560b00c2064400781c5410481c4035030101000f0808686460300e82802a44d4054808035004850003042039854010b4401202c40080c84038801610f90002c0c0410300030301d030201d0b0120f81040e08000810a1708841001034001005c0b0500c205c50443d80b450003042d0141d8010324000d5101d00c240c0314203509560001316200e9850307004102d00310029030300030708403580c850300600b000f9180d031108502180d0310a034012182140060782c50000c0b080c4950640144803084002001c00e0426407800d040c040b0320300441d01c4241e170200311251401c488040c105480001504001c00041c13501000d6900b80303241c80102d80082c15903030781c0c400050114410b000301807600002c181c1000c0050a9025800174104480411000101901c0300081560a0b400303458042c00c102d0354030001c0d14090100c0c681d45580760400c400700381c80342c9040d1012100e0140103100d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 202280773 1250 202279523 202279573
    0x605010c1101260702070f080d0c0f050d110d0e090604020309120c03040915050d02062512020607080609240a0914010e010f1703120a0e 60
    0x58403503009905848055085500d10011414031580040c02d9410360000d8904a0080041d004095100c4c105448004d2520500781c21220702504044028480d0840005101c84c2c522403910700301c515100140707001292002d003900c4c02401c2d4031603101c104214a40100c02c21031240d400208807565240052422034800d407080c422141c20228a0020505070709103500111b5105000f001100c400c2401d40d00040070300d9001502102c3c0c9508045024010b8000901496500600c01428403c403641080e000440201245034001d220300c5001800881e00b1040c980780b2040003100361b0300400c1c5002c413800c024401605224072100180204000562064000c0101a000d000041c140c184180e5441e5034510307015a0a030025154902054000b2103240c0d00c01d00400050070b4a41ca012901030410700040040c03000c180c00030100b503480b000c014410109a03800b10b6044410002c88258901210244281503101d011010603c60300820300b006a08106504203111000448080b05c841c1c22480c1d4214048180501c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 202282023 1250 202280773 202280777
    0x903030f09280303020c120301090606020705090c0715050c09040c360e090a0506010503030a050703030b0406051804020f01020c0102190201022e150e040303091412041701060501 78
    0xb9038a0665418540c021440c0c10b4420300740149850203a070b08051078140401110001072174004014000368071036000e4240244280c2c001444d4060a0000240c00301c4402480800c09140203d5600184520309601000510b805401009541414000c082560b480340588901031802d00003c04001d510070368480416160300c0201c0341c802c8400c15100b11851068640360030100c43d00c42404225500c030144c0345030054141c0c20040c1550030892501506050050340410311079002807000f6810306411070b08039102c041e45803800292210010b130008008000641280b600600b40d81c4500f03203509242880d150299000300c82c040c00c4245001e00481c1e4455814421600580100222400070be0070303980b0010b0003e2050041d06c9052030704020130401c601455214010355031402c0100c2c000c0107007900c502c1c1c000d508200c0b8007150345420401041600e0f1005031006040664601c000e0041c803e0782e60804170360410f50025103c8080031929006034980180c02480031130712945c00c1240a0050511a42044540603 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 202283273 1250 202282023 202282063
    0x170a0203070609050f030c03030a050a060f0608100905041a010e190b0f12030a0f050a0f1d030d0f02101803110a020a0f1706040503030109020a05040506030903030f09 73
    0x80e5504400340c0003203001200c4e40d200d808131030405004180068020540000000c5441340750201c44441aa030b400f070109034055142030818860441e15440850503200c680c14024505d844e0300344000405003031503020408580c6010240300c00c00010282040ca98ac0d441c1010078800c1c0d0b00c3c0c3d02c5a900c0c409054804150601c6d88015a0810003000d4202507070686000b000c20ba82c0c0300c224008500c8032a480031404e82d01d03800028805110a40200000003140d006180050800c2d2003080043c0070302d44141401d00c00e101c05284410781407407081e010080b4202c0040d06946440c0d0b00300c1d602601c688600c1102e1400b41c01038100b183c0070086c15200303005900b041c14440000540c502e44040c1d03050941c03032808d500c09018011041025031105014000102007000e030b04400305140c4040c0b0802400400d0030000e07560408420702001c5070f800000e981c1512048840141d6034114004207480d04d1040c0c0d0710403500104c0202c100a040f08002c0080d42c0b203060704100d05071055030781040058403049a201652040c03009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 202284523 1250 202283273 202283287
    0x50a200d030c02010f0c08010503070807031502031312030609111828030b0117010504050709110d06030c0504050115120b120105040b01050f0d11060f07081303170a0203 74
    0x1180e00030110110b154000014011040070107241030720300500604021660f4440100024101045040c0003420040c0180c50080d046035104402d6040c3e122504150720b40100c0450402d07140b4107130b0381c80550341c0701c4000c01403402c40741c0d4064098815403240143c020b10700b003921280030b007120003200c0705014011600c0c01030030061010005021100c10803480500b10b0089002d0503415170400303090203103008172185000d5600d404040c4c4810351107030702504202c0e41040188000107600041c1c840c144c03596084003190074010144040000e00850010ba21400e0a02c040042444981c88555060710400d0b901800707140e81750b540d17902c40d03080320802e4840014954801140403080550041c2c1988000600c01c03224120301080719404c0d10782c00d84090700c108c003518004100f946060144c08508020550700303020045215181c5000b010030081d00740b40503410010f0000c0c140b220203001c80300c94540c044000c0c0c0d25883c0c2c81003021880d1902c0d000441c0d4a01d0499802c9403546a00c0d82a00e540004617401980341c40740b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 202285773 1250 202284523 202284527
    0x5060901050d050a080d1d070e060105210a110a050d05060f060a08060415090b01021b030d05030612030304140705010203120105100207090203010b07060b0a06020a0f150c050a200d 79
    0x1b0240a212410310340e03440907211910341c0c1000f1003144500140040c9000c3d8106000e080001c0342c0540100d0600204210b25644c00e2002c00d440d412048020540e0b800a903103000c009400307488403c0e41c1d42d00700385001032104042500500036202d40407050004100a41e6100d05210751000c56140351030340240c09200e072441c40c3d80300356103a40d4010006000820490b00030b0492030600d940b603421080025131120b007c0152940e0400602c0c100b160070700001c55012403988082900c9540e1648050301700a000400501d60381c440405440c0c0100f40c0c4400c0720740d6480e05042180300c12034079040300081d03401401c1c000156988000306580580748110b04504031a480c1500b000030421581c040032084d0b0003001800201c1294500c00b5600070803108100660341c00c424079004089030420805d0500c188503098060007075a50004000c00d050f45c0c0941000c04541c19428052041031040c41590b807002e0608001031091988000a80740e0481c943e03d4542d50b0700c11481100e01e515590780e0154001e03502101401d00c44034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 202287023 1250 202285773 202285777
    0xf09060305030f0a35060a0b0d09020a03020607060b0108180d110a020a08030901110a0510091505071d01020a020906010516080c071a030c0708090a0b030a05060901050d050a08 77
    0x20b030400807010441442e0130941481150348074052171685440b83d2001151a200b501c2d803007401290010655800c0980320107080c002c4100c844500340e95080110210346035000c80d00095a0020001034880000d0b15000300980550781070f980c00079001401042101401620301590400d07941c01410000c69501002c44881c40d019018161600c11620400090303200d413020385000e090884059555400c1400c00500169a25040504564002000e84020400201c0d41104d640100b05000c00d001113682490b101400500440841e000d14184c14071801c40d80240d4041d40c00048840d042071f00070042001a0389802d10304070b010350000c48040c0041c0f40b40d0300c0f402c0102084148140c2060808041c2d4031b440c003891f001840c2c4c0c0c031035680c00080c041c08160000200c80d04d0103101071003403d1852400410601c081d00418500824001000c41e9544513a03031110403900140c00c412840b03503241d1800009080c090801a20114062804880003040307500380040c0740005250803400400601440d981e03416515 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 202288273 1250 202287023 202287037
    0x111060709030f1509120828020a050708040b180d0f060504050f01020c010608061303021902010207050409030e1807140f071209171902060a0c0b100f09060305030f 72
    0x420301380448041c90704014130403e1010317801880310500c9541032003401390010f0300180004151000d00c2090354069909555501d81060285402503111280c500c400e80d0540140c04000b096440e003c940401c0c1c4199000c058880100149100104991200c0c03d00c08583e130145000780c12a60102820300105d90141c110035041441807040b40c0480304001040e0b42241c203c80c03442e4580f40d441c0d200c200252401080016000348235180015001d090a80e40a9580e41a04111a01c00700d81210f20100f9a0300920658000300310140c02803080b02017910307004280c4240706060600c15501d4844420300f11905d048814881c6000d40c981019012402d296003229402c448044c0250100800c01d41d00003500c10417514070b035a0301e584c956001450a20982400c3c5034500246008664070607090741022504d050340708660f00e9015510540d540054600c111451851001d003d1300180858092140d004814103404048071400c2c0511141030b6101d00c20901528071920016000758014400c0b0400ca1040200078485 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 202289523 1250 202288273 202288283
    0x9010c030501060e06071a010803120c0c0322080706030e060a0614190302060d020304120c050a0b060102211c020340050a030905010806221103040804050111060709030f 74
    0x3002100320048600341f0240c2040329583c0000c1600d0b41e81c0d00305040c84030f41090104808601303003814203491541d2409940b1015002122054400301280701242090000d06001d2083d243c2e030030749880e009006850f151003689010300c125000a1041c61052259005a8242074407100094000318100003110314010700000342030303414080002c0142d41d0345005081d0028035102c0540c0760702d41410184020180005c1400501541d408881e00055020480044080d03101c000c40c4100e4560342c0c0101d240428041d2600f0860300d00c4060550b80707208030800f42c80029010722091129000340902d03c010780c08190703071000810010b20b007030781c80d100c50042001d480400c14903011664049658046950032303994a4050303880e90040310880d0141540507100b039002e447d007801c121025042920216200c0203015200204818440000c00c0313110032960041c2c001c500800c0c0f01d0541740d0419040c0005140e0080c0704080c040341283c110980c4000d40401c803288244419241e1400c240d1940d00e079035130f0200d102d50040310 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 202290773 1250 202289523 202289543
    0x230903031308060402010f1103040e130b090c0a0603090309090c0e06040b0307080a020c030702011206260601060809101a0604090203040614060609040e010b0a06050309010c030501060e0607 83
    0x201845440401c00d000300034403001004a41000e000242801c8078404081007001210031043c9041440001150211106a02c02032216502c481c5c0c80000090482002010714002d203041c40103401d000a40d02d01c82d0f00e02284c4401070240d80f1041070f012120040d0b0018041034420008020641d0950b000341701032407a5041c04050755080c0000030343c482d40507800a042550000c000c2c40f1005a00001c0302d40c0c440c404070401c501d000001d84a540e0f8901a48000074100f10f904004c0940c00003268008100804180c1400140e007020546031384520000d24020721001d1180e600001012845032100b180102d91044c05030906d041100640c4020303002645140250300e5950842c0005901c0b99402440146055040180c5034102454000151075845044001d00c88980b41071010540e00c038401c45055110031100080c55141e00381c22030340035185098540703500a076421000070b56242c006c0d00851280701da00c40208800c0703c0f250f40507812110300b8050000080c80394006180e190070088000d102c2d00d405546080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 202292023 1250 202290773 202290787
    0x40c0306061d01050301060f03080703110105090706020f06060f1002030c15041110050a21020703020609070f1802030712110406020f0102040e0604110409180201090623090303 77
    0x34065a8081c1c0c0304075030b4845109080d01c1d01944100c0240e0241c00e08500078080e0b01d01d0f00e8070040c01020b1030301010b07182c140d0016841c0300f0140141050345202072400002d21071890b001c58100c0d101c82952241c0300c05030003483d952060700c042c0454480d00c90000149000320b007540d40f0003803013101e00b40c1c00380f004150301c410040e000c903100003048200d010f0484001414500d00d03080c03520242d03030002a1000c85c020f8400703100301449581c100c82911111001072500280c003201103a4a500490503460800c00c40342d20001d180000d0650100f1128803580c800b900b10b410190740d442a860245049108100010103018a01602d084041d002143c004c0d4140c5001d03d4080c15040403401180c00207204801d2800700024100890f90f0144401c0c03001120990003141414644100004170010041845108595401c2c004040110103000c1e90003600e501401000012040198000a18113040080c1c1c00b1845804000560520031313984484a00c006084280540e094020b20350002e03000001056810b010501c001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 202293273 1250 202292023 202292033
    0x7171507120e070515120a0b0a0504060905180609120711030115030c0f0e040615120c080105150d0201030b0301110c031c0203070c1407031401050702070b030915040c03 74
    0x1c01034151800000e40903082c40c1108106085d01a80410301100b4130902044580ea245030b541e0b968896482c401c0030401000340800903a40c0b03000380d001254840c0c6450008100c0805662041e8416003511140394080603e030701003180c2d00c04046518908a610240c6a44d818114034000703455030a11544042c80c4d0800c0c80c40000c3c2c01c1d640305c0d0486540d9400619010005d0002e455190401059600000d80c0c5032070a00c08c0100d4598801080a00015103800c0e4413008a00718424801c01410800210394900d403045c0307440845820306100e400c80075828600820041d40590b2080c4244200c01000140300d44480e40c015005448142d030441ea06542e03070082c3d46540300c204002440c01c5020311004c1c41d0340b940c0058507005516012040e96504900c18030800c10181d03000079580441540040c10001050030301c042c1245848200d4000500c003400c85c108031207550f04150805401400142c007a50413054070744d80d0b406914001155044000c0c0d0100305012100110f07000b000d5001402081003480b45a141d8883e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 202294523 1250 202293273 202293281
    0x2040f050108010c1e0e01200105010b1b07050108010314010615051c060302060403020607050c03030409060503060906040305090613050d0803041b080a15090c08010e0717150712 78
    0x2c0c1101e0794640301488807260384998070004004d4807594021001c04003580041c02c01840c64409410321120b0803c0c0e40c03003d0740e62103000880407078620081c4001d60b101c511607036049c0c014104400c44114401180b003101640800c5a605440341a0742c1c020130f0381c2ca191234500041501b141c40880d9556100380c0400c02c0116200070a80c5510f207900d0300c59a91580704882002e003481d015603000034a2038030b14140b0041e80c81c4001c54084036012209207131074514a08110341040724420500b90301d031200040008510441e500544200e96040f0240d40d515558425580d031111011540240061801c00c4503c00c02e140c404043c0c01010944010300d0701c651b4942001c540e240b489920152a1082c01000b04000c200d5042c544041580404495040e85031505010a64460000301d006046625170221310003209081d0b4003004100b074109200e02a00350391450014020280d08440d407590b4041c02d50f0125070380113148805170684502400401c00c510444000e0481c101d4094050000c1001c1050595130322016030003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 202295773 1250 202294523 202294529
    0x60201060f090506090402012a1506150e040f1e02030a0c0207030b0a0f140a1a03030405210705130e060112120305040206090a14090601020703150902040f0501 70
    0x1514505159040280d07440070350045020700c0c101010440151940d64000d0741003942800d100c0c03030f0900312020f401d1090440400e0901c021203500c140e1000c0c0480052050725900d07980808001017a00c5281241c070355a540044003012601c01400300c641c1c3e040a42c010a6148010040010b241004107e0b040700c01c19211a0030500b5900801072000c860300703c0c42034038203402807400140740180c03440e52000e5500301300920740011036555407081c0051140c1e54000d00310b0800b4061986c1d040d4905140c88400034070300640d0700c595551107211030315550b050000844041c2c2d0300090180c4240030380c0c081e1034411050000c000e0003080c000c80500041c20345486102d281380800405d0041030500410852924150059000992642c1a001d400c0d0129016104030400600c0520f40410303240e445001044c0c0c070f80318000c032030f507005011048005190034001424100503d02120030f0707506900c900303004a070b40d040d1600020302481303104d02000d110403180d58000300c0301ca1f2001d0400300b0a00c0c00985030904a680981c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 202297023 1250 202295773 202295777
    0x90610030608070b07060e0303070933120b0103050717101e030303050a090c050d0c081f0e06040321060504020a0504080606094f0302070e070212090d0b0106 69
    0x451998101b165a000b003c91007410b25000354194138181c40b00418559961007003802154810000400d402c443c14452020050501c144041c1094500d4000300340070148150300340c400745040c4030481075600c02d000340350151205590318801c0041d200c1d21030450141c040c1100f40d08a00920300001c41c070103e04101501101e00c41c983d04020b516604015040d240f004196035070003803070540d55100286000c0a40c10a0b0744056450b0f0356545184e140c03408110fa880d40014020707200320020900035040410740c42155109a20080c80401310007090940e8512003a1801400300b90440c58000e02c4060705203041c0c5c0c08041c008804680c1c03e1b46d46001c0381c201d910006441000a03c0082c09016440041104540000040e0317003072005442c00c40150f1501502902820b507610340640c0d0415002201600b01003110000c2d400304420725031007054074403408804280218003500941c900010240d010a0780c50348600d40d42e4003d00320042c034042c0c240c0c4040e40458139580d4054401c08c03501c40401d502c05007440c0604034279 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 202298273 1250 202297023 202297027
    0x1c0b1617041208090303060109060c0f022d03030403050307030f0212030c0301030b01060c02030a0b0a060504140604060b070b0103030c020d060507020f07140f10111b1806090610030608070b 83
    0x2d1803006010342c00c010010400c0e980b040041c0596640d1241000c41110a00e02c0c0c00e09210105251590038071035400c038042c1d8080c520020b400f03a400c294440b200703441a400800200150f201c9014075891f030080b484041c0c1150070500c61040440e0083c1a000012502d84c81a20540c612001c010140d80d08150364038404013001200610400060b330304e90f24094042410102083c0c85a58000b946d035440c003110007400710b071000011619a030f0b460b4100202910b402041440314440404518040b088200d0b005841582443c40c0014040641d10807a48082e03004a040c511503800e54801303031211626001d080341c00c001c0b246600001304940b032160500401d0304e58082c161034070090405c649420001d42018205481000303050000e40d0781c0c1901c0c1d101e610004d070351144655028003c1540e00c000060064101800b40c0007640d0182c4200b2044030143c1072040320a461071403112640304240703e00444141380c12000c504080380300c9180c1440300d1403500c01640b60216056440e80501c0c0e04040301031380226462000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 202299523 1250 202298273 202298303
    0x10030902030705040525030e07060c06060b0307140702060702090406020304060c02070b12061f020a06050f0f070804060e0708010b032406090903071205091c0b161704 73
    0xe100c1c2c80010441242c05101350b0600d180300b20b1720000c1c5100a245500310781075560450710700940201400121081c10307901c0c440c0d43c840c001f4018540705a401ca62052505501003142100c03102039074045c0080b5954681c0c00b803444460385c0c005500c9800180d0380501c0a02011006956814040d0320480c4103110240e12810700d4074003041600c1c640e504001c155004000706004a07064841035130003818440700030340101c0e100d1101045d0381196050324040c1004620b117000f00010340001c1d110003010300c194010007042d0f4030b01b0350440016030705079600001040da40e8041071025110b2032020750041d02542001034841c0310b50401f207281500b96130040e03516945500d0308100c01c1c40d085c41040041d002c10804071016205a2039000e40394400205185c2c070407031030000801c0300b400f8108259000c19034020b90009030014100009001b942200c045980b103030003001049045081c00e03619880000f5880300605503da2a0315030170700c0c10b44510031400420021000d50106c040e0384500c1e81503029038010340742980c0481c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 202300773 1250 202299523 202299529
    0x6070f090807170d080c0d0903110f03031603060b04060f2705120a08030412020a060f02090a050303070b06010f030915090320150613020d1e0608070306091110030902 73
    0xaa80100144140002003181c0151850704440e0b00b0341c154400048c048240346019140c4103d40c0f041d1139442e12941001c4074240d00d00000843c00350301180841140004166030071003d4800500a10700701080c140000c100060180034007415403a11030038a0000405151780100d01501c000c0c485250403406844100203c3c20300301000c620b41290302014060098080d15410039910007c0c1008108080e40da43e0384400c144280400d0003190f0b4030010034042041c0c2000440017940018084034414182c0d0080090300d85000402c03210703441d902a54803130042d030b510707030042d07602000c1c501e89842070503241d0291030001001000e54a0b10800c03410300000e0320401600b001002c9649100340090700516442404100600000d0007081c00d103815070003101156110008240c00280c00c1541004050010441100c002d2281e0054951064a00e411f00422143d0002d54002d032407591141301d529821031401807000c202c0c1070b0400c0000c82e0040800e920010b000c0c10214906a21180c07911000030340d00e101100848c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 202302023 1250 202300773 202300783
    0xf030e0a0c050a330203090306090705101110050c13060207030b0a02130e19090f111f03020c010209030a0c0306051302061b0705090108160b030906070f09080717 71
    0x1030364001d003c4c2c80303c843e9106181c0080c1c3d008500085500440020807410b20810031103040e00d0000d000e0303520504109030003e99441c42c81c000e42d44650306480c0c001c0c607218403a4440054184207080101054540407207802c004080141061109020030040701850021500401c0700500003680103000c072510350b0500010a4030003034502006035004005004520704517200b4407094900120300110076485800754020684540540010304a00b007596090501561410091555004042101300b0304070120401c030100c0f0043c001e00c2a441c507203041491a2074030a0f805810381c407070644001813400010301d000070304d49040010201c40414900000b44104240c5000b010303085004032000c480ac3d0312240d40043c2642c0034003603a002a0b4020000c1d190505030081040c207000300005042c1007104d50311015000c2d100e03070101e40c0c90440c03110104000180c00c14084201c0b8490f2034400d0207050306803180007049501e0340508000504100c10039401140c1400c007800140010f00100a19404048990135528100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 202303273 1250 202302023 202302029
    0xd120501080c150a050d091101030e0f10090302030c0a060c0f03020f18040b0409030f200a0308100b040f03060c0e0907080901110301090504020a0e040c060f030e0a0c050a 75
    0x42e005072889a030726445003000001060300c074025560f01c1e0500014221154007440051403145418070b01050240002040407403035002007070360103100940c005040da17507448505c5c0c0d140c4a850760002d0000095940a544a64a5180300f44140ca00c0c00003520906454005105c009a17441c80e55130002000d030b02d4200b140100021380c182800e504190341c01d403c000c058003803802c01604400964a090345240d0300e540c048044100010070402520351541402005911120401d402260380c4d04007040f078250801100b45250301100e030041c500302d00660350491300000050f0030301c100c4050f41c80380850070242e0000500060000f0f80c41d503260349461824003400751400030420001b801480c400b540010748842c0e00031648140942070551032900c49400d0580142100050b1444c20400400003080d11651500000d00440c001c8904890342510744401da03101010a54009084842c41c04040040701c1c0982c0c0403020350020b50800069400000e240d8a0502103107250403170b604154548140000e00d000000b107009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 202304523 1250 202303273 202303289
    0x2030903030a060e01080d050a120212191434020609070e090c0d0503040801020708070c0b19030c02030904060b0706060b0c0703080c01060510090312050f030f040f050d120501 77
    0xc4c6500d00765196490300100b802c0d17001001400580c1a02aa00440c0b49407825840b5100c11503541c800201d00e0104d008003620016690350b22200d00c503800602902a201100701b030185048095100c071860907807003410440702e81041c100e03051001141000700320f1400d402072155401804581c44c1408010342001c90725000060400011010b00011a80000d88503181c0e040950f90100c0460103420504e02e140655408945203600004094041110800240c541c3e98450840040d03026254102c2c207200d802440300150301c2c8008551003040c024801c1d00310300d80703400d00c50065a14100102020a040e9800340d003090240b03100c0041c4103005c05c502441070200a02d64a6001402c0602c1850f0075611030a0601c0060007070403000c075802c0c10781c41d4203510003001088014a4a1031010091314048c044a070301d0310095482e0705004040c40180341c0100c08842c02a620035420070310315910014400700b042c0c005442920350340070881d141d20000f0700411000488503013944400c5280480e07401502c01781d40c8140c21102c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 202305773 1250 202304523 202304549
    0x20a0f140904080d150302040e16090204030807200405100302030c100e0f130e06041b06021f0932070513050c0c07090f06060e0a050603100302030102030903030a06 72
    0x1000c11480b109884d0b03000207200300861046256103044002003503a0b00081e500c00d16220101200140028090102170b04003004001c0c40303a030350b038010022402280700103010001d00704035010015164500d07104103100100252404110313008041000c44100b10707034010401d41640c5040c004e40c5406c01c04010700c0317102260030709683c00c00654004e04e038041d44007004c2d000300c0030800314041da5594040401c031b0803010b1250410044503130140300703981c0b8038054405441805800d03805da8550403040140005441c0f280e001000049041c0e5075071052110108503d4032810340d035a0302e1302c00190502902013000358110003195000380191040014030040c006c13202c01d0710f60003a041003006440d00c0e4070172500240c40410000b5190344070100b26225105a01c00044907000311040854601ca039079100c0c258020000c5070820403551200c1082c0c030f81c0015182c51603131201d0003450810491601c180219406040c00302c0188403244d40c0d50100b400c2e0b82003a13b0065080d0804020441d02169511440004110500042c2c1c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 202307023 1250 202305773 202305781
    0x60f09020f04050702150f070e030a0c12030504080105040c26060a0b040e06040c0321050306040f110a080a0b10120207031e05070507060513050105090409020a0f1409 73
    0x560714030444420349004680352000140c03800c0c000d0041450309480507076010f480e490f115107400307086c9208561038800b1404882d030343c8015040010711000380301c1c2d004130031040890400d01c1255402482200450402004100110b050340003030180c14000c134405c00c00c9400803402c056510761204200f484071003045041040f0600c2c2158009a03090308844241c0d40000c0803c101400716001d0007090340405d03043d10420b818001002001414102181e00510504071110000540c03000610740a820b0000000d0050010032441d25107a80000e1185418400001d42d5402100d10f0403220340040d420000892503020401c460401c1600543c542c0340d0040794001d0240700c0c10640034100f8482e100ca2260b9203a40402e1100405001c2e0041038449110030516034050b02d03140c580100300d40d00c0907404549502034020b00017995402134080d10171404044440c521442c0c01c00004403040c0e003110034042c3d480740d11030f59010301507107031361403040c0103030117030100e45e4140f40d007002200204500406030550040116000304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 202308273 1250 202307023 202307029
    0x907050f0315040606050a06050a02060708040b070f030e0717011a0901030b0408071e02010210050403231201080d110303070c23060a0c0306140d03050c0703080c0604060f0902 77
    0x1407400003850b400c03202a0707111814400001d01e25a005690010324412002c143c0c2c5804c03034041c0c4480020b0343d084800740c0d91003080071102c1c42ea00b034038010b0001035010085200c13180100c01c0420500b00c41d2800040000a001407140382401540c811500c2c1c5055a4440030005001e02600d00015141413030711203800d01e4500030130700010051101415442c544000710b0100f02c42c94003205d6400350401007526003500255002d2a80850303100e400c0b400362040039060000600213000303903481141c06460328002c2c50f1040e20032810002c1d0000003209650010480c0030000702010000714060722213071000386003c5195000161500704000b40508090340300b4800c2044840c0c5c070a284904451341b2124004903c501003003554090038098801107041d0044404000d80317400c059000104150302543d00303000546d1340d079661513205c80340010b0158019209180b8407010a0168008000741e41c0c205046902c426aa9111118a41c00c00c903012003503074200c00c05110038000107000da0310100c04040e000b001120b0303582d400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 202309523 1250 202308273 202308283
    0xc02011e0b010906170105120a0f08091305040f020f010c140d030c0203040e0c0a0905041d0607090810020304050c0904050607020c0f010f0e0103061d37050621060907050f03 76
    0x317114030625a0364807003230000f4002e0014004895000c0b007020045e007031038640b00465030408003103d4082d96009501c4103c06c410f60080c5801160040050702100703400f80c090203c01203c180000c1c0c1030204600811002032040c0e1030001640c1e414001400d0464100f003c024152559426040110740c81440b09000c604819100140c0146110100c00d6031828a414203440da25207540c0070315480780c50080c2d0803044d01010744410103904c142d10b0030380700a950b4002054810340090b0044032060384c052540170702020b40590045420600072002c54000a41010004103903080c2101c0848164020f5000c4c40941901000107840c0340724119003060011501d240020007806c40b0301d65440400503d02c0858219034001d41c400b4001d8002c0007680485103800744c0040720000c50958282821940707d5221502c41c0c4040c0301082044180881000d401c0544600e855010340030141c0032983c1f00c0740e00c107200249410441580020494010060b05540c41d14500b05814007442d81e000e03034001e207850b8800f66199a00450 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 202310773 1250 202309523 202309529
    0x1090e13021302160507060801060c11060909091c0305132411040f0801060e01030b1510090503010e0f100e030c0d0305040c090b130c02011e0b0109061701 68
    0x1200102088600019115a030b503014081252480003d40c0380b4407940d000700114441c1d01032000c403a0f82a584200888040c81d091186034006500004084c0024080484405983d04010b001038103003030106000500360381050714950728980c4003203075003001a412070343c407000800c1d882d040030040d620b80768410403d800003004000b40075000070421015000c149c2107c40290700040c0314204040c61510081d10401d610a029845046140741d5000648070b1050085400355200b2071001081c5900e160b440080041d0040d0450103545440b10124000e5290700001c9155141190703a07000381145800145421200d4920f02808140c20004080c1c1ca24130000980d4890f0074112140010b0252001a86508501801c10b4100041c014510940d80156040d00480c1c0500c0c01001030006d0300c0d80d181212000c80c1e0f58880c8445d00000d1180e000c9850188540c450014820140000b1071500b18400302c0d0f2100c407214071000352466558265650302541d10019032030192105090540d142c800702001c100107544144 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 202312023 1250 202310773 202310791
    0x507050d0206160b1911040b0918070909110c0a03050c15010312020606030d09090c1205130302011113150c0c03051b0619141b0102030a0b01090e 64
    0xd140e940454444100703c0b40c8040541640086103d080c2c03811000d004410b41d81c0190140130810140d800030454400c0314445640c12050502d00352030810000707000d42040c810340ba80003618075031060030840d9000382c581c810b0362680c1c0c5104030103050888190458001d14040360300314009120050a600c800100c21180b1340d0542090b6440742c0c0b130700c4422440c040401281e284503500d0b400001040154070300d0240300c50784180e000d951240d500c450038103507929520a103450000c1c0b4051410000580a0360261506428074503248515101e134403811002d031041521a150640328901e500001d1650a2103000548289c85035920b1601408140742080f9000d6030240d015005900c01103104050f00a500d061400c7c1d40c443c000740c1030fa070703542d080881c1c0b601120701e807207100328a16900750952803405408a80c010140701080001900c11001e080700d14003140c0c0c225024402c0300b000b8070182810200c015007584407000c0005a5a85011840d01e800c2c1c6404012803411b10408040a000f05007030f1118869000f003101c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 202313273 1250 202312023 202312039
    0x30605100305060613080c03010e0a02010f0f170c0a02062202090a0207061803140a050a0e012102070302120f04050105070f0804170606010212031909060f06170a050705 74
    0x1070f41c0011100d00c9001030310441562450b600050648006c140b04498200c100c008002c890203180c0e8203511500050350007400502d40e04800d5252034007825011182c40860b140003880e44555058503c030030001910000d0b0200404550118003076410800310b90f0250f500c01c5800000300780c44100101a00c10703a10003d11031101800010304003011030781920303a03035a00500d0512541000880915821511007425070003d4202120700000504075030841c4c6400000f40e5629140200c000b100325010080071884904114040c00207800d24003c103614411001981038005984942c20318020b4941507200e00810103103201030000c295462400030544040341d5080c06c0c80d0ba56038550b4603190900420740c04000b45140340225001c41c0b05000355200340c10542c418821142c2c6912074200582c0d940c400242c20124000c01000010048240a881d4a0341c1070040000451440c0c503070b0380d444007610020445030400968602003040f0b2000e0100a041010080c03602400022801c1d031a4a9145c10302d501070740340074240d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 202314523 1250 202313273 202313281
    0x403150b03030d0f02071e0b07050403110d0203010b090a050a0e010b0609101407050606090604090209070e0607080f1801140a03090f080703020a050127140a080307050405040606030605100305 84
    0x11358048421240c2c0c48461001c0303040c00c45504051040d8a51000d4540d0030014000075401400b07401100c3c10f1b6170308a8441010700c002d0310100240b03e00c540d070342242c00d95201c0c00310050545440e0450390043c848843d0100d00381c82c0c5070301c00c80211981e5506844942e8148000f0100944840b0308885d54950309881c141041c40e070f04113068032011780a000e01051890001081c2041c4403020038600d0007450b00300c9480105895110400c41640e88640c4060343c80111180407030b40e840d0054031251202d4001170a45410810356447e110701541003503543e9a80f00e0030001d003079041c504a40b544510b40070401d080c2040c0300f40e98a415082d050103414030800c141607941ea10401800840c0c0a05800d05a100c404150790311070602d03009486220540c821a0310790300300100800c00103000802115200d410050000e4141d01726181d00070b010056000343d050f54040c0f4100d104c00304a0005c001c501c514010740fa01a952854602840708407207803980500201450544140400d0b03036030094031a22600140340c0841e00380c0b1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 202315773 1250 202314523 202314551
    0xa020310080d050c37031b0b0105040506010c080d0c0c0c080f070b0910050304021201061d060105071a06040e0106081f09030f050a0e03060c0403150b03030d 69
    0x16560403680d100d02c500841c0c0c90030750b40d01c20000d0561a000c0020359002e0005101903807049401103014150612a00d410305080c00300b80001a103065000740f4180f910202156124440c11605000a5422034480001800103042600649030004030a11702505600882d07150b04425000301030080342141d41303c1c080f41074594800c0c1424000030360003541904850707585d401c0c0256180d48510300c0c681240120000002d00d4841c02c4166592820003a00d464070302500c5086c00c07a4142d0008204981c0a0030999024003001d009229a2000d4413186020000b440c01c10320320000007500041c15181084010070801300081c4200c03074040040c0d203074001c4040183e00c4040009000d0003000340f113485a58039113a000203c01c280060380c41c401e0800800c00d042c42025030f90018047d58010940500415909000c4d070300000d100c1d00062602c1c040c90b1416445812100c1c001a0a0020070381d0800b44680c1c0120f000d105201418022120940a60b8810080900c41c0b0b0042030720383c0141180c01c2550b40e902c10302201400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 202317023 1250 202315773 202315801
    0x3031207020f0d0f110a05030409110d0e0607020724030515030604060c12020f040b0310090e070515030411060f0c010e0f0d020f0a06050c07020409060b040506010f05030a0203 77
    0x540403820f0360030b8039107019801407402100100c00000618040c1104040410220b4041c2c00d0b190000050b601c0c05003402c2c1000701170245004040c901080822000303422608900c241c00d04c0740e441d03034007a004a040c5035100034503150f45c81d081045110f040111044484001215200c210720aa05000c10b4555030300702c248290a4000701c1c11501802140200405c02186911110f20342c1c2d40d07500c401c1d115082c4000610120702031407200303c1e060002007005100b0442d01d031018580c4041c10941001241d42c90b5a850400d641d85610040f03034513445590709201604d0b0241080f460036501c2488a400d61825855480b544604144001c1c0a1040042c020302040d06c054211949403804130f00038452045003a403087ea461141c400001c0b1075008490352082c100e44042000d206100ca202c006003404070751920342c0360007440050620308444070200800d40041e01c45009600c3c0c418050040000d440048105000688000500540c10007000304091100ca942101c01d990f0010540200182c4aa4650010381880 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 202318273 1250 202317023 202317043
    0x10f0e0a110309070603050106050708070813050613051c080307030b03030d0606170105010215070806030c091303080109150303050714160906080316080a031410050913020303120702 80
    0x740400208100d180c02000a4560407030711256000c10003680d817503100312254040c0e4000107141c00c00400c0704201203103043c0c0140540b1900d031611101d2030355803040010155807103400300c2204540306810821903032502c607615404644403139845640c10022680c421442d13100c01004407040c1540c3e032820350559102003007a03c0700036081d86001c100139503c0f5440500303c100480300c0c2c08038104c1c10000104165101050703020030b402080b95044613640303031007000341e400f041d0040c40503403d4800c0407c0082e0365502c0c04400350040c05280c245541d1701c071881c1030080c205c074016000ba0200c3c40c01c02e405245903810040c0808100ea81500d0469103808151508552822250100120b00c0c81040c1103510302d520308640d10f908481c0f0b603880800050381c4c2c1e545080d86a000f010702800c5c0c0000d032030301c4003804201c0150041000800d076140010f521401d4815419203c03000b540c00c884144440002032019080031541035030043c8000c090342c032244006600003030380c80c890440c1c1c0413141d400b4140402c018a008001500030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 202319523 1250 202318273 202318301
    0x103030527060c07141005031b0c01020301090b03060a090308070c0c03020405100810090c0b0912010f1d031213140a03030203040b0f0712111c060617010f0e0a 70
    0xd80d1034035103d01650f4080c14002c00d81480a01d00d420821458003d08580e990059905c41c1c03411503031643c420b04d24062110151036555081000400e031242000c0c4000d40c064249200001031803e415030a02d4500380e4010641403020745000d030542e020070780200c9100da000c4203a281032850225107217848504104035500013900103041400340810103410115000580d562001200c20b41600400c041081e2000c60300f000c0c1c801c004440c400d01481a000b00103129050014141c07a403401c040002d114216526100d0120320340d03035105a0754107100c0d404050322481c603441100460900038199234415100001420071905000480c0d00c1d8410000300381490401802080b0035220003c00d5418050082d6000300c1d07088450f0910100010728110340f601209001e600d8903a02c1410110b81c03010400300030804580300305003100b000d2064401100e90500040c076500b40c0f030280450179130b16018015220010403000d907103040b00072000521910544015030400c9802d02400802d4540316a030f45c40b4010812912400c403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 202320773 1250 202319523 202319527
    0x114010e1804060b061206010804021203180a090c0512040204060806010b07020103050c0a021c021024082a060d020403030c05061b0a05090a05030706020615030105010303052706 78
    0x1c0c4401001a001e4400c0f030040500744091011034007044441c0c8074102003481400240301c0824450b521402009038800c0c40605012040d03041d07406824990f0700103031003101442541021038411401d280910390000c22040d4400d002c4d043c0d40d510082c1c00c9000d0f001c40c1c03040e05198640020103656840c0c0241005220036016203045585034101c21400c1e82c0582030503400320f400c00c004207101c1c1854074121145d4000c0c5038040c00c8014403070103169a42e00c000220650441c8189203500d4610340803031140d2a1840e0005c1c40f2800e401c2001c1070760100c849085c0d40418000c2d0411860765450b0780042040c40641007680e2040f0681215000c0010315600580c20007600303080c40400e01008141d08540101405401002250320f15034030001d00c2c3c80b00c00361301c0010034919002401445100307070140c4081e050101e0014041c840340381e00e420100e45800c2d520340c044801a0701c4141405890050201820a070030401d800901266040d514003a006200d01c1080000d14101c46840d503900410f544060180d5400060401c0c1e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 202322023 1250 202320773 202320799
    0x910050619020c0321032a0a020c0d0b18070308030a0c030e0a0c14030f0105070201140907052d03010f0608010c0306120605130516030b01050102060f0114010e 70
    0x1203503034030301c5070a20000b6101d080d5994940303180000b15484c2903a1200b41c4504183e030540300341d080c140c201800361070007048915840c0d8000d02e140d032000e01c0c10509261381ca5850700d00c0110001d1a000420120314001c00700c2903816004140341404955012800c103910300e044462003e140c1c0c0c5410400da001405002c0084144403440b0403a80028034401c0d215901030140140380241991112500c500061031a25002d0040180d10500442c0b003210000050039100050100d401d00340c00d6031011034060300141d644000b43c03410401044210741d044442d91005008041c144008502c50480803c101058145203590f00c00c01003611a0100d21080c1c4007038001c0c014074050b40e03d480090b14050244650f1542410340010070548603116a40451b00080b0000b1001c0440b038886a0080001030034020f07021300403030074410216104200400c804694070004c1e0860074514200103030b03080d0060b0401d038110340103441401080529001c0035070660f0f80f0346503005014a01c4800607205a000c5591640c0c100350250084 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 202323273 1250 202322023 202322047
    0x60e010501030209250e03070308040306050117070e01050603060d120206040201120c080c0a030603050703030816050304022218060204090e06040c290c010518010509030909100506 79
    0x105048920a40e00d218403900c3d04ea42600d200c5c10644072034094600320440c00082a0f02c501c0c94035130300c403401500751541540c80e901c9240b51644183c1055034459103400c0100400d0750f1a081c018142d5801c00b0103001a076041c203a20340510407061081c2c601c20000400404c0090b0381e8003000a03401b0b948040c840202440503500030f91500002c880590202c0c01802d100b101b00c0c0c8290182c840c0d4000325a4841c1c446075200406e40c0f6443e000b039009102050b41c0d03880007000250702080a40041c60283d06d0f802401d240040120403207001c800d1017141001000d005101c01a00c0d50400320485031040680f40c2e80681c03062030741c071008040340d200545090381420b0b02d00c001d0000b5136008109485100000b80421a400a511651602c0940e40204403c0c0128000c03c003489800d291a81c4107050b8000c58090b2800410442406401c11400590665526400e00450203001d9a060814603070040c0203001918101342e80c651a0f010303e818403070191203c1c00c001640c0207048044200a0a802030101e47c54044200313403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 202324523 1250 202323273 202323281
    0x10905061b1315120f2406020a0f0c080d021605010c15090203010f1d0c092707090c030e0d08040b0112020d02060705030a230304060b030c1201020d1107150203040807060e01 76
    0x40400100346c113062003100b003091889000c2613500a4008040c0100d0030f90761403403100b555a00507182c040c04203a0100d16008103000c0448900d105500030045600c03081c0383c0c110701030140d521031030503c46140010317000200c0700d4042c06450b8041120015407200c40e4001700c0d0150803400d0700a0462842c01c8180c101c8040071300085a5408444000c980507100c11074207000420380c041c1e900614030050760313042c0701c00442c5003021003d40c0d50303901c0c083c1c41e02c083e0b90f4800c440903035403610b40c900d0202e80c80760b085035044c01007000f0220300d0550a21703040c03509003415140c008c0b400e441030044d003a1080c800051642951640300d4a00c0707410741c2c0030b000c0075076a4100d420840c0c0c0325045035803a080020281300c41028240300b004d9691101424400300b081c61500d440c0e0300c490007842681d103040e07010b0044010002807640c5000c042802d1344c046c1e00015030341c1d01080700383e00212420100a001d251340e092042c1350101d01a00c452045047d013000f00165a6110303030800c0101402424002000300341031140c1d0034951201900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 202325773 1250 202324523 202324541
    0x90b0108030a2015060a03120816231806030f0117070303121a060705010504030807020706090b0c01020f040906090501230d080c010905061b1315120f 66
    0x15950110404003c03150b11840c200c0c040c0d00099a1000d0215400340e1800d00070030382c00c0b80e00207048140103940d95560300c48500200802d034010032070040c00c000c10242152000401d1811070301d080c04040c81403a06101c00300c00d10358645003403140c1c049070306e44d444031601448000b2094000c151589a24041400024950742402209156019034803110041900010000705517541a11410901c41c03c00c1c104c00001c00300610752100b5122201d104245948401d0002c0418a0203840081142e113024140034141400250aa00441d0302c411410440564000a80360589030001d118540e0f41585500e810302a01030a400400d03c1d420000380040e080400b54880800c6480503c8180410380e640d036641e501d13451401c034036048801c239600b424461a160202d155440c06204150560a00b81d04103400c03070031500035001c01c50303496000c4000d01c2550511984101c41940020101070301d4460b00d8040c0034808080d80c8910f00015080d1f40c9030740e9010340104811039003940e6003c0200810541c00078850080e0032145 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 202327023 1250 202325773 202325777
    0x118020f0102010c120b0a03150b010f020c061606020d060f03210509091306020c0a05060105030a050d0f050c0115091505030d0507140f0d02060a05151003090b0108030a 74
    0x812000d02035006028000103218962250060740c0d15400e8104003404408802c1c561102e800500803000810302c0c0b80d541d1900301001c4002800c0c0060500142c255002c501e00e6809661000e10a10443d03076502d4201d03541c0c1403400445590158082c500200a4050000034007c0c45082ca030001c1046042e12a1640031640184138680c103030300c036080c1c0809214500700c0030312000400c01c09c00102c1c2030510709101078015200304400381100044c0c0c0c4401040717801502c9000c001741c210762809410301c40108440f40c09010110050312845400c0d030b84280d500c0045455040c184201c00354042078150185c0203540400b1503480090299140388030b2042165011070041900003850883d0204181420303802502c15150042d0081802202c510000c0c1d9213a00403070030844140300c07034441c072a080510a2010ba405044110000c0ca00b070481e03010080d080090081292807400e1400b401c20450894800384404641c10070748143c11159035011084014107048040a0b114441c0040000780740300d0000018a4040129 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 202328273 1250 202327023 202327039
    0xb070e0102241501051905191b060507090e0406060e150307171006030804030506090a0c03060b060d0c180b09010806150903070905010303020111030115080a020408011802 75
    0xc041942e00000341c400800c2004621100140060069945900d11400705050503420001000c6c401d24110000d0320f81c800c005078010a03408003440c082d08000101c40da49040c0580d000110b030788c0c141c0001940401c0900602c0e21600450203042c0a0000da1000e403417000342c480390510b0541801d1010704100d00c01d03a0401ca80c144001010f4403100440d503c0300400080180c80c3c000d1411100c01420303506800648c50500030841000050000d42c400c44000350300c5aa071480d00c403461410246c0c1003d10040034802507401c0781003160300003506101c0c100203031707039000a000481076002000300701d041c080c40c403099504a00d0200340a52140c1c00c000d001071a42c504888110805444a020150b0342c010750565601050803040413900b185030420005400070801c1e8011406d1105481c0000d01e050840e90100341107559030301c014400d0590a0095200404207240440d18551604805901103600c104102d800c01c0600c001103015031882d43c040f240102280002800300d603e4500c44099207191401e0200c0c850003003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 202329523 1250 202328273 202328293
    0x1060f02060a092a091e050109060b070b072c0f030d02031b010209030a0b0103030215010b0a0503070e060d060f09060f2c0a0f140606090d060204030b070e0102 70
    0x195018071112941c2c03000d81c0050ba13003030f14800390030610421004422000201000030510022600c00c20b160f002403280704225046090720350808440c01071300940c04031401c240c004e1108000540444000d02e0b407020850100d40d0f80c50100311200d41e0032600000005803052200c00500803680c041417a1100c003100c0416888041ea02019038030000050008056013051000740c0c82d80a14541c015810b00008001610f8000c01c840084d040c40342000c0d04a4007001036100500a00d42d042090000400c5c1a0b54030b2801941002800c41c03070307030040c483c1c10010010300100151056101c1c4084403d07078407029140c1510752540e0303041280900003c0c02001000380c452440052141c0d098003541041f514a01032001415040c90108000213a414121400540201c1404d05910b110004024071880d2150800034010709d0702c07181f00c81600c0b0f00000d01c2d10f03000142c5003404460703030740d0310308541c02c00300201d07803440100025140ca41c0180c0100c0d80b0280c504001c28040100c42034200c2c01481e90088240d081e41d51080d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 202330773 1250 202329523 202329541
    0xd030e0105090d0806101809050106020601060305071409031006080714031f05060616032003070302060105100c05060c0403140f071514030a0b040b04090201080604020306041401060f0206 82
    0x100c040f4907500000d4003500490307881c1c101080040068405407519186c0c0c10869031000190812540c070141c0c00a564800401c0425414090117000d094980b03002e1184e401d0511000700b080030001d050050342e400001d010107c55600708103003002500c42000c24091740b6a210590307078440500388610000c0e800e20940a5440c1d04d0b0100d120781c0005c2001d500160480d9003030360000d00400e001001035400200c00c110081099105071410244280f280e5542c0310603801040ca60b1301d856003424041107040e44180128000a600030a687c0d040d5041079980031100f002854007200c240c1c112103006407170360151409005075001134000030001c0d207015104110f030010850041641e122100b292409494000700030a02c00309003111f04610780902e003440c0c065907003041c2000c200b45562003540c403c4200f81da280b401d241e80f41070a0044602c07640040311b082003600c69580010b00160401403942e4415540040040c2e0599142c3e40000d036441d1103128403000960716410080d2081c402e101509000d44518000030704a50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 202332023 1250 202330773 202330783
    0xa4217150904060b010c051203011d0c0712140d020405031204080307030509060f12040b06010206071b080705010c05031b070305041503200702150408060106050c0f0d030e010509 78
    0x5003019003203965998032901c03000018641c9007005410012101d031100b001c18810403607424000400251180d89503d440610b981d41410321000103840b5448400300a402c12050b0207a603101030b04020407095070305a0410444407000d01c0600b850340c4c500049150198001d55074068030565074181c08452a07107403444a294001e02642c8195009644100301a000103407184000c0c00060f207000c0c0802d4185080800e200c1c500e9000160b00d18401c0c260300003040144031511488540050342800034040c40e08148100a040ca84c14500e030f08903059614101c141080244001c03201d030785420000030002ca98003070a0007000c0d54020342c2c41c00540300d144142e03980300001d00401c450313001c2c0c0d06489a5150600c6c00600c3c84c80145c41050351014140c3d0781e589062040502d8403c41d801d02000c1d4000e0342d032017590b031040004900d03401100c0000b0f10001c2c081801300c0f441c00548241541e44c207081c1142c41c0c0060002003840c0c111400c00112040c002d0071856800150981c11000c038014640001348036a50703d52051550350 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 202333273 1250 202332023 202332061
    0x150d180807031101090609110103050f0709050f0a08030f0a0908070b070b04081b030a1206082524030b04020307020d110109051b0f0a4217 61
    0x5001c00c55100001d005924544106400d00c0001c1a101001e40f2043d040722200201902c1c80c00d880e1001d2011580e15120700c6a01801e4080b0454131420312280003040112103000c2e07203001c0c01c11002044401e0340c07603006076402409110100c2e9525000c9000301540c0c3c0e0050311002d0701085548001003a0108086100c20682d03c1940c000c0e0704044480c2c4400080c004040d01c00d0740e4003042045200d030220024001d00b40101c5080c001580d580c072140c000100320103a0a2030103014140f03810001d224090020800110900316050101054841218000c4084035a6440031019440064500c3d1031441c00c4890445074610340d032010855042030354144016423004039112401078004030f07114010203000b0100c4020a90380d100002440c03610903038900d0b10b0500483c0b1a580d500b80c020005003414034150611001842041c0e5201140c139242c43c005007004025100303510607400c1c41515049582404030b0200b1083d035103104030199100342480d8050410541403040303617843c1030f401001a00c84449007802ca464 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 202334523 1250 202333273 202333283
    0x108060d05100f0b060a1d041a0906030c0604030521041503090c05030a0c03060b0315130206130b0702030106090606050f0903030d111902010c08040f05010b150d18 72
    0xc02262000c8480c003c01d0070719420000c856440c03500004648410015103025071040e2200c2c10158400c0c080703409400444a5450f210b681000360341059a030b5420181d0842580958030a000741e190000020b040c1101a0140740e085500482c0010600c0b40c0050310382059820380b0060f4010001c10030b050f203c40d228a018080b2450b000e003101c0046144203070300070070459000c1c0c0d4440c0042911000020700700f100c41801510150495031b000d0050002c1d52052440500040f0011b28800f0704965000f20312501c000c1c10002c661070214019010b5440d000c0845d141281030004114a9075104e180c0740003e82c21680c02640a0741c0f038141c020038000c40911034082a1296526a40d0420900b50f0340c0990940c0050b844682600060000c0c10000410b4000d104803000788004143e2580040c1000020008013244220210780c10303c0b5042e5100c3d50400c40503030300503811228885600d406401c001f4054404903010a0304104141c40e0400980c01c010023a02d80e1450242e000d00607048202881840d842903400702801c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 202335773 1250 202334523 202334533
    0x2131b031107030804110d0210030e07140306070f030e0a03030e0c0d170a090306060f06020d030605090415090f0506150d0b0606030717150a050303311a090108060d05 73
    0xc049000b1602000b507000009007c07403280c507601d50100d110341c1d031181c0700b00f0080ba8480214040f02c6900b40310610241c41d510464079066400000066520301024003607006100c10960003c6941e48246c1040340100210300840d02407841900d001002000129407810f018080c0c007443c020350b480e044a00c2d500564121459140d030602c81021288a58440a4000b003840340d54200080001c245004040080621408440e0104d1600c1070103410180d545488500f094a4110140300329601e0b41d52041c2c00607080019200b040d582c400d0034000508009801402607080d4042c0c0310100304c0c000600901c01c0c40e0a900270350015050100b13102c07210704000310050141d20700c0000540141402c10141d07038811100e01c0d009031010f8181071400300c07a90701650340712421410440b028030306040c2441200300610b0281c0065181030800c1e44241103056a1050a06807070082003010038550030030700019030150640424079001c4000c6c030a041070b072a40c0003190442c04510030390b002032018503200d4045040c254004010306 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 202337023 1250 202335773 202335781
    0x1208070c0b010b090102011401030b010f060c03052d120a0e01020a09210209040503070501380103110a08041401020c060c16080415020114090c090402131b0311070308 73
    0x78507150042004e00303045640c1c8070320600c501c41031010024000c3d40500b410800ca5410407450090820343c6400000c1400780482210300000d91090032a04031864072a11010700000800d8004034915008030007210a95000c600400c004015003101c40c015410841c00700044a041400c2c03038241d000d5000d418011a003064410080b2a50141001c508521500108103440c20349500082c0740307000558050f54141d0012440d4400c0200074402c1584010a5004070741e0b01201410081075a040e54080d200d0a100564002c41c4031a4040d401010100b021400368035200c1e618800300911442c4125410f940b040a9140006620401803084488009024000d4101503840c030308400b01c1a84000118158101c0809031000401c0180d8007900c040d00210130b10805504c1404002820340380d5114807018014a0041440801c1c0c01c00500d210303100109480c0315a02d5551400041c1e02032505400340307001142456082c03080500f42c82c004440461583e281082020304203108094a07016980d001004501014041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 202338129 1106 202337023 202337039
    0x905071a07110127150909020f070813030501110d0510080c1e04050405010c0f0212040509090a0210020102090307080a02061e161208070c0b01 63
    0x14504201e110344501c9018108681c1040c107126204c4510103089540310760402c141007160341081922039aa40894110f0300304514043d00180c903a803004111500c00d07100381e41050080102250800244d541c41c104a0380c043c0e8940300440c161101c0c0000000d03024061400000e01817100c654a8610001c4020152036000e4440c94400c4030441041c4000d9000140030528040708440007400d496810002038240015041d185401504040404c010320205402092075811588d584c141008802c000c100e0315a246a40040c44807003040108000701d20b0300360005601708102c1d4064a80380e0030554006075031040e12040c00c90240c0d40215400c0c0c2d48e031070140048001404030380c0142035070f0032071607000034114407681081d104035185107608200c1070450081605c800011840c64004d60176854241008036041c01100d0000041e64400040c0c8100c0c803d02d1280c0e0707919840041d050b8030b40d08100c0d00c = true := by decide +kernel

theorem cover : BRFrame.Cov 202158273 202338129 := by
  have h0 := BRFrame.cov_init 202158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 202158273 ≤ n) (h2 : n < 202338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
